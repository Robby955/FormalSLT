#!/usr/bin/env python3
"""Prepare the frozen UCI-357 Brier-monitor stream and optional local baselines.

This is a data and arithmetic protocol, not a statistical certificate.  The
downloaded archive, canonical stream, and local model result stay under the
ignored ``applications/brier_monitor/local`` directory.  The tracked manifest
binds their hashes without redistributing the dataset.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import os
import platform
import re
import sys
import tempfile
import urllib.error
import urllib.parse
import urllib.request
import warnings
import zipfile
from collections import Counter
from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROTOCOL = ROOT / "applications/brier_monitor/uci357-protocol-v1.json"
DEFAULT_ARCHIVE = (
    ROOT / "applications/brier_monitor/local/uci357/occupancy-detection.zip"
)
DEFAULT_CANONICAL_STREAM = (
    ROOT / "applications/brier_monitor/local/uci357/canonical-stream-v1.csv"
)
DEFAULT_LOCAL_RESULT = (
    ROOT / "applications/brier_monitor/local/uci357/baseline-result-v1.json"
)
DEFAULT_MANIFEST = (
    ROOT / "applications/brier_monitor/generated/uci357-protocol-v1-manifest.json"
)

PROTOCOL_SCHEMA = "formalslt.brier-monitor.uci357-protocol.v1"
MANIFEST_SCHEMA = "formalslt.brier-monitor.uci357-manifest.v1"
LOCAL_RESULT_SCHEMA = "formalslt.brier-monitor.uci357-local-baselines.v1"
PROBABILITY_DENOMINATOR = 65_535
MAX_ARCHIVE_BYTES = 2_000_000
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}\Z")

SOURCE_FEATURES = ("Temperature", "Humidity", "Light", "CO2", "HumidityRatio")
RAW_MODEL_FEATURES = frozenset(("Temperature", "Humidity", "Light", "CO2"))
DERIVED_MODEL_FEATURES = frozenset(
    ("minute_of_day_sin", "minute_of_day_cos", "weekday_one_hot")
)
EXPECTED_ALLOWLISTS = {
    "all_sensor": ["Temperature", "Humidity", "Light", "CO2"],
    "calendar": ["minute_of_day_sin", "minute_of_day_cos", "weekday_one_hot"],
    "environment_without_light": ["Temperature", "Humidity", "CO2"],
}
EXPECTED_FORBIDDEN = {
    "Occupancy",
    "HumidityRatio",
    "record_id",
    "source_line",
    "source_member",
    "timestamp",
}
EXPECTED_CANONICAL_COLUMNS = [
    "source_member",
    "source_line",
    "record_id",
    "timestamp",
    "Temperature",
    "Humidity",
    "Light",
    "CO2",
    "HumidityRatio",
    "Occupancy",
]
EXPECTED_NONCLAIMS = [
    "this protocol is not a FormalSLT statistical certificate",
    "the task detects contemporaneous occupancy and does not certify future occupancy or deployment risk",
    "the replay order does not prove how labels were delayed in the original data collection",
    "chronological data do not by themselves establish concept drift",
    "local baseline performance is descriptive and is not a population or generalization guarantee",
]
FROZEN_ARCHIVE = {
    "bytes": 335_713,
    "sha256": "4ae3f46aa98eedff564a9f6924d1635173e2fd2c816004342a9be93076d3a81a",
    "url": "https://archive.ics.uci.edu/static/public/357/occupancy+detection.zip",
}
FROZEN_MEMBERS = [
    {
        "bytes": 200_766,
        "name": "datatest.txt",
        "rows": 2_665,
        "sha256": "1b92c7c1b2838963464fa891a610cf3c5db4becb7189189b29b330107a584c7f",
    },
    {
        "bytes": 596_674,
        "name": "datatraining.txt",
        "rows": 8_143,
        "sha256": "b2c4d0ce2b9e4e453c476f7125ef31aeec2d1f5c7f5572d0e80de3df6521ab56",
    },
    {
        "bytes": 699_664,
        "name": "datatest2.txt",
        "rows": 9_752,
        "sha256": "d026d1bd5aeccd4aff4f3b3710d48e40613bd5fc370db7e61bbdcaa50d985095",
    },
]
FROZEN_SPLITS = [
    {"count": 8_224, "name": "train", "start": 0, "stop": 8_224},
    {"count": 4_112, "name": "validation", "start": 8_224, "stop": 12_336},
    {"count": 8_224, "name": "monitor", "start": 12_336, "stop": 20_560},
]


class ProtocolError(ValueError):
    """Raised when source data or protocol metadata fail closed."""


@dataclass(frozen=True)
class Observation:
    source_member: str
    source_line: int
    record_id: int
    timestamp: datetime
    temperature: Decimal
    humidity: Decimal
    light: Decimal
    co2: Decimal
    humidity_ratio: Decimal
    occupancy: int


@dataclass(frozen=True)
class PreparedDataset:
    observations: tuple[Observation, ...]
    archive_sha256: str
    archive_bytes: int
    member_digests: dict[str, tuple[int, str]]


def canonical_json_bytes(value: Any) -> bytes:
    try:
        text = json.dumps(
            value,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise ProtocolError(f"value is not canonical JSON: {error}") from error
    return (text + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _reject_float(value: str) -> None:
    raise ProtocolError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise ProtocolError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ProtocolError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json_bytes(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError(f"invalid UTF-8 JSON in {where}: {error}") from error


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ProtocolError(f"{where} must be an object")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ProtocolError(f"{where} must be an array")
    return value


def _integer(value: Any, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ProtocolError(f"{where} must be an integer")
    return value


def _string(value: Any, where: str) -> str:
    if not isinstance(value, str):
        raise ProtocolError(f"{where} must be a string")
    return value


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    if actual != expected:
        raise ProtocolError(
            f"{where} keys mismatch; missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise ProtocolError(f"{where} must be {expected!r}, got {actual!r}")


def _sha256(value: Any, where: str) -> str:
    result = _string(value, where)
    if SHA256_PATTERN.fullmatch(result) is None:
        raise ProtocolError(f"{where} must be a lowercase SHA-256 digest")
    return result


def _fraction_text(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _load_protocol(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise ProtocolError(f"cannot read protocol {path}: {error}") from error
    value = _object(parse_json_bytes(raw, str(path)), "protocol")
    if raw != canonical_json_bytes(value):
        raise ProtocolError(f"protocol is not canonical JSON: {path}")
    validate_protocol(value, enforce_frozen_identity=True)
    return value, raw


def validate_protocol(
    protocol: dict[str, Any], *, enforce_frozen_identity: bool = True
) -> None:
    _keys(
        protocol,
        {
            "artifact_status",
            "dataset",
            "feature_contract",
            "nonclaims",
            "posterior",
            "preprocessing",
            "probability",
            "schema",
            "splits",
        },
        "protocol",
    )
    _exact(protocol["schema"], PROTOCOL_SCHEMA, "protocol schema")
    _exact(
        protocol["artifact_status"],
        "FROZEN REAL-DATA PROTOCOL; NO STATISTICAL CERTIFICATE",
        "artifact status",
    )

    dataset = _object(protocol["dataset"], "dataset")
    _keys(
        dataset,
        {
            "archive",
            "doi",
            "landing_page",
            "license",
            "members",
            "name",
            "observed_at_utc",
            "source_header",
            "source_row_fields",
            "uci_dataset_id",
        },
        "dataset",
    )
    _exact(dataset["name"], "Occupancy Detection", "dataset name")
    _exact(dataset["uci_dataset_id"], 357, "UCI dataset id")
    _exact(dataset["doi"], "10.24432/C5X01N", "dataset DOI")
    _exact(
        dataset["landing_page"],
        "https://archive.ics.uci.edu/dataset/357/occupancy+detection",
        "dataset landing page",
    )
    archive = _object(dataset["archive"], "dataset archive")
    _keys(archive, {"bytes", "sha256", "url"}, "dataset archive")
    archive_url = _string(archive["url"], "dataset archive URL")
    parsed_url = urllib.parse.urlparse(archive_url)
    if parsed_url.scheme != "https" or parsed_url.hostname != "archive.ics.uci.edu":
        raise ProtocolError("dataset archive URL must use HTTPS on archive.ics.uci.edu")
    if _integer(archive["bytes"], "dataset archive bytes") <= 0:
        raise ProtocolError("dataset archive bytes must be positive")
    _sha256(archive["sha256"], "dataset archive SHA-256")
    if enforce_frozen_identity and archive != FROZEN_ARCHIVE:
        raise ProtocolError("dataset archive identity differs from the frozen UCI-357 bytes")

    license_value = _object(dataset["license"], "dataset license")
    _keys(license_value, {"name", "spdx", "url"}, "dataset license")
    _exact(license_value["spdx"], "CC-BY-4.0", "dataset licence SPDX id")
    _exact(
        license_value["url"],
        "https://creativecommons.org/licenses/by/4.0/",
        "dataset licence URL",
    )

    expected_header = [
        "date",
        "Temperature",
        "Humidity",
        "Light",
        "CO2",
        "HumidityRatio",
        "Occupancy",
    ]
    expected_row_fields = [
        "record_id",
        "date",
        "Temperature",
        "Humidity",
        "Light",
        "CO2",
        "HumidityRatio",
        "Occupancy",
    ]
    _exact(dataset["source_header"], expected_header, "source header")
    _exact(dataset["source_row_fields"], expected_row_fields, "source row fields")

    members = _array(dataset["members"], "dataset members")
    member_names: list[str] = []
    member_rows = 0
    for index, member_raw in enumerate(members):
        member = _object(member_raw, f"dataset member {index}")
        _keys(member, {"bytes", "name", "rows", "sha256"}, f"dataset member {index}")
        name = _string(member["name"], f"dataset member {index} name")
        if Path(name).name != name:
            raise ProtocolError(f"dataset member {name!r} is not a flat filename")
        if name in member_names:
            raise ProtocolError(f"duplicate dataset member name: {name}")
        member_names.append(name)
        if _integer(member["bytes"], f"dataset member {name} bytes") <= 0:
            raise ProtocolError(f"dataset member {name} bytes must be positive")
        rows = _integer(member["rows"], f"dataset member {name} rows")
        if rows <= 0:
            raise ProtocolError(f"dataset member {name} rows must be positive")
        member_rows += rows
        _sha256(member["sha256"], f"dataset member {name} SHA-256")
    if enforce_frozen_identity and members != FROZEN_MEMBERS:
        raise ProtocolError("dataset member identities differ from the frozen UCI-357 bytes")

    preprocessing = _object(protocol["preprocessing"], "preprocessing")
    _keys(
        preprocessing,
        {
            "canonical_columns",
            "duplicate_timestamp_policy",
            "expected_rows",
            "member_order",
            "missing_value_policy",
            "sort_key",
            "timestamp_format",
        },
        "preprocessing",
    )
    _exact(preprocessing["member_order"], member_names, "member order")
    expected_rows = _integer(preprocessing["expected_rows"], "expected rows")
    if expected_rows != member_rows:
        raise ProtocolError("member row counts do not sum to expected rows")
    _exact(preprocessing["duplicate_timestamp_policy"], "reject", "duplicate policy")
    _exact(preprocessing["missing_value_policy"], "reject", "missing-value policy")
    _exact(preprocessing["timestamp_format"], "%Y-%m-%d %H:%M:%S", "timestamp format")
    _exact(preprocessing["canonical_columns"], EXPECTED_CANONICAL_COLUMNS, "canonical columns")
    _exact(
        preprocessing["sort_key"],
        ["timestamp", "member_order", "source_line"],
        "canonical sort key",
    )

    feature_contract = _object(protocol["feature_contract"], "feature contract")
    _keys(
        feature_contract,
        {"allowlists", "baseline_logistic_allowlist", "forbidden_model_inputs", "target"},
        "feature contract",
    )
    allowlists = _object(feature_contract["allowlists"], "feature allowlists")
    _exact(allowlists, EXPECTED_ALLOWLISTS, "feature allowlists")
    _exact(feature_contract["target"], "Occupancy", "feature target")
    _exact(
        feature_contract["baseline_logistic_allowlist"],
        "all_sensor",
        "baseline logistic allowlist",
    )
    forbidden = set(_array(feature_contract["forbidden_model_inputs"], "forbidden inputs"))
    if forbidden != EXPECTED_FORBIDDEN:
        raise ProtocolError("forbidden model inputs do not match the frozen leakage guard")
    for name, columns_raw in allowlists.items():
        columns = _array(columns_raw, f"feature allowlist {name}")
        if len(columns) != len(set(columns)):
            raise ProtocolError(f"duplicate entry in feature allowlist {name}")
        unexpected = set(columns) - RAW_MODEL_FEATURES - DERIVED_MODEL_FEATURES
        if unexpected:
            raise ProtocolError(f"feature allowlist {name} contains forbidden columns: {sorted(unexpected)}")
        if set(columns) & forbidden:
            raise ProtocolError(f"feature allowlist {name} intersects forbidden inputs")

    probability = _object(protocol["probability"], "probability")
    _keys(probability, {"denominator", "loss", "out_of_range_policy", "quantization"}, "probability")
    _exact(probability["denominator"], PROBABILITY_DENOMINATOR, "probability denominator")
    _exact(probability["out_of_range_policy"], "reject", "probability range policy")
    _exact(
        probability["quantization"],
        "q = floor(denominator * p + 1/2)",
        "probability quantization",
    )
    _exact(
        probability["loss"],
        "(q - denominator * y)^2 / denominator^2",
        "Brier loss definition",
    )

    posterior = _object(protocol["posterior"], "posterior")
    _keys(posterior, {"loser_mass_rule", "selection", "winner_mass"}, "posterior")
    _exact(posterior["winner_mass"], "3/5", "posterior winner mass")
    _exact(
        posterior["selection"],
        "smallest exact cumulative Brier numerator, then declared model order",
        "posterior selection rule",
    )
    _exact(
        posterior["loser_mass_rule"],
        "divide the residual mass equally among all nonwinners",
        "posterior loser mass rule",
    )

    splits = _array(protocol["splits"], "splits")
    expected_start = 0
    seen_names: set[str] = set()
    for index, split_raw in enumerate(splits):
        split = _object(split_raw, f"split {index}")
        _keys(split, {"count", "name", "start", "stop"}, f"split {index}")
        name = _string(split["name"], f"split {index} name")
        if name in seen_names:
            raise ProtocolError(f"duplicate split name: {name}")
        seen_names.add(name)
        start = _integer(split["start"], f"split {name} start")
        stop = _integer(split["stop"], f"split {name} stop")
        count = _integer(split["count"], f"split {name} count")
        if start != expected_start or stop <= start or stop - start != count:
            raise ProtocolError(f"split {name} is not a contiguous exact slice")
        expected_start = stop
    if expected_start != expected_rows or seen_names != {"train", "validation", "monitor"}:
        raise ProtocolError("splits must cover the exact stream as train/validation/monitor")
    if enforce_frozen_identity and splits != FROZEN_SPLITS:
        raise ProtocolError("splits differ from the frozen 8224/4112/8224 protocol")

    _exact(protocol["nonclaims"], EXPECTED_NONCLAIMS, "nonclaim boundary")


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            temporary.unlink(missing_ok=True)
        finally:
            raise


def download_archive(protocol: dict[str, Any], destination: Path) -> bytes:
    archive = _object(_object(protocol["dataset"], "dataset")["archive"], "archive")
    url = _string(archive["url"], "archive URL")
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "FormalSLT-UCI357-protocol/1"},
        method="GET",
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            final_url = response.geturl()
            if final_url != url:
                raise ProtocolError(f"archive URL redirected unexpectedly to {final_url}")
            raw = response.read(MAX_ARCHIVE_BYTES + 1)
    except (OSError, urllib.error.URLError) as error:
        raise ProtocolError(f"authoritative archive download failed: {error}") from error
    if len(raw) > MAX_ARCHIVE_BYTES:
        raise ProtocolError("authoritative archive exceeded the download byte cap")
    verify_archive_identity(raw, protocol)
    _atomic_write(destination, raw)
    return raw


def verify_archive_identity(raw: bytes, protocol: dict[str, Any]) -> None:
    archive = _object(_object(protocol["dataset"], "dataset")["archive"], "archive")
    expected_bytes = _integer(archive["bytes"], "archive bytes")
    expected_sha = _sha256(archive["sha256"], "archive SHA-256")
    if len(raw) != expected_bytes:
        raise ProtocolError(f"archive byte count is {len(raw)}, expected {expected_bytes}")
    actual_sha = sha256_bytes(raw)
    if actual_sha != expected_sha:
        raise ProtocolError(f"archive SHA-256 is {actual_sha}, expected {expected_sha}")


def _parse_decimal(value: str, where: str) -> Decimal:
    if value != value.strip() or value == "":
        raise ProtocolError(f"missing or whitespace-padded value at {where}")
    try:
        result = Decimal(value)
    except InvalidOperation as error:
        raise ProtocolError(f"invalid decimal at {where}: {value!r}") from error
    if not result.is_finite():
        raise ProtocolError(f"non-finite decimal at {where}")
    return result


def _parse_member(
    raw: bytes,
    member: dict[str, Any],
    protocol: dict[str, Any],
) -> list[Observation]:
    name = _string(member["name"], "member name")
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as error:
        raise ProtocolError(f"member {name} is not UTF-8: {error}") from error
    if "\x00" in text:
        raise ProtocolError(f"member {name} contains a NUL byte")
    reader = csv.reader(io.StringIO(text, newline=""), strict=True)
    try:
        header = next(reader)
    except StopIteration as error:
        raise ProtocolError(f"member {name} is empty") from error
    expected_header = _array(_object(protocol["dataset"], "dataset")["source_header"], "source header")
    if header != expected_header:
        raise ProtocolError(f"member {name} header mismatch: {header!r}")

    timestamp_format = _string(
        _object(protocol["preprocessing"], "preprocessing")["timestamp_format"],
        "timestamp format",
    )
    observations: list[Observation] = []
    previous_timestamp: datetime | None = None
    previous_record_id: int | None = None
    for line_number, row in enumerate(reader, start=2):
        if len(row) != 8:
            raise ProtocolError(
                f"member {name} line {line_number} has {len(row)} fields, expected 8"
            )
        if any(value == "" or value != value.strip() for value in row):
            raise ProtocolError(f"member {name} line {line_number} has a missing or padded field")
        record_id_text, timestamp_text, *numeric_text, occupancy_text = row
        try:
            record_id = int(record_id_text)
        except ValueError as error:
            raise ProtocolError(f"member {name} line {line_number} has invalid record id") from error
        if record_id <= 0 or str(record_id) != record_id_text:
            raise ProtocolError(f"member {name} line {line_number} has noncanonical record id")
        if previous_record_id is not None and record_id <= previous_record_id:
            raise ProtocolError(f"member {name} record ids are not strictly increasing")
        previous_record_id = record_id
        try:
            timestamp = datetime.strptime(timestamp_text, timestamp_format)
        except ValueError as error:
            raise ProtocolError(
                f"member {name} line {line_number} has invalid timestamp {timestamp_text!r}"
            ) from error
        if timestamp.strftime(timestamp_format) != timestamp_text:
            raise ProtocolError(f"member {name} line {line_number} timestamp is noncanonical")
        if previous_timestamp is not None and timestamp <= previous_timestamp:
            raise ProtocolError(f"member {name} timestamps are not strictly increasing")
        previous_timestamp = timestamp
        numeric = [
            _parse_decimal(value, f"{name}:{line_number}:{SOURCE_FEATURES[index]}")
            for index, value in enumerate(numeric_text)
        ]
        if occupancy_text not in {"0", "1"}:
            raise ProtocolError(f"member {name} line {line_number} has invalid Occupancy label")
        observations.append(
            Observation(
                source_member=name,
                source_line=line_number,
                record_id=record_id,
                timestamp=timestamp,
                temperature=numeric[0],
                humidity=numeric[1],
                light=numeric[2],
                co2=numeric[3],
                humidity_ratio=numeric[4],
                occupancy=int(occupancy_text),
            )
        )
    expected_rows = _integer(member["rows"], f"member {name} rows")
    if len(observations) != expected_rows:
        raise ProtocolError(f"member {name} has {len(observations)} rows, expected {expected_rows}")
    return observations


def prepare_archive(raw: bytes, protocol: dict[str, Any]) -> PreparedDataset:
    verify_archive_identity(raw, protocol)
    dataset = _object(protocol["dataset"], "dataset")
    members = [_object(value, f"member {index}") for index, value in enumerate(_array(dataset["members"], "members"))]
    expected_by_name = {_string(member["name"], "member name"): member for member in members}
    try:
        archive = zipfile.ZipFile(io.BytesIO(raw))
    except zipfile.BadZipFile as error:
        raise ProtocolError(f"archive is not a valid ZIP file: {error}") from error
    with archive:
        infos = archive.infolist()
        names = [info.filename for info in infos]
        if len(names) != len(set(names)):
            raise ProtocolError("ZIP archive contains duplicate member names")
        if set(names) != set(expected_by_name):
            raise ProtocolError(
                f"ZIP member set mismatch; missing={sorted(set(expected_by_name) - set(names))}, "
                f"extra={sorted(set(names) - set(expected_by_name))}"
            )
        raw_members: dict[str, bytes] = {}
        member_digests: dict[str, tuple[int, str]] = {}
        for info in infos:
            if info.is_dir() or Path(info.filename).name != info.filename:
                raise ProtocolError(f"ZIP member is not a flat regular file: {info.filename!r}")
            member = expected_by_name[info.filename]
            expected_bytes = _integer(member["bytes"], f"member {info.filename} bytes")
            if info.file_size != expected_bytes:
                raise ProtocolError(
                    f"member {info.filename} ZIP size is {info.file_size}, expected {expected_bytes}"
                )
            member_raw = archive.read(info)
            member_sha = sha256_bytes(member_raw)
            expected_sha = _sha256(member["sha256"], f"member {info.filename} SHA-256")
            if len(member_raw) != expected_bytes or member_sha != expected_sha:
                raise ProtocolError(f"member {info.filename} does not match its frozen byte identity")
            raw_members[info.filename] = member_raw
            member_digests[info.filename] = (len(member_raw), member_sha)

    preprocessing = _object(protocol["preprocessing"], "preprocessing")
    member_order = [_string(value, "member order entry") for value in _array(preprocessing["member_order"], "member order")]
    observations: list[Observation] = []
    for name in member_order:
        observations.extend(_parse_member(raw_members[name], expected_by_name[name], protocol))
    expected_rows = _integer(preprocessing["expected_rows"], "expected rows")
    if len(observations) != expected_rows:
        raise ProtocolError(f"merged stream has {len(observations)} rows, expected {expected_rows}")

    member_rank = {name: index for index, name in enumerate(member_order)}
    ordered = sorted(
        observations,
        key=lambda row: (row.timestamp, member_rank[row.source_member], row.source_line),
    )
    duplicates = [timestamp for timestamp, count in Counter(row.timestamp for row in ordered).items() if count != 1]
    if duplicates:
        raise ProtocolError(f"merged stream contains {len(duplicates)} duplicate timestamps")
    if any(ordered[index].timestamp >= ordered[index + 1].timestamp for index in range(len(ordered) - 1)):
        raise ProtocolError("canonical stream timestamps are not strictly increasing")
    if any(row.occupancy not in (0, 1) for row in ordered):
        raise ProtocolError("canonical stream contains a nonbinary label")
    return PreparedDataset(
        observations=tuple(ordered),
        archive_sha256=sha256_bytes(raw),
        archive_bytes=len(raw),
        member_digests=member_digests,
    )


def _decimal_text(value: Decimal) -> str:
    if not value.is_finite():
        raise ProtocolError("cannot serialize a non-finite decimal")
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    if text in {"", "-0"}:
        return "0"
    return text


def canonical_stream_bytes(observations: Sequence[Observation]) -> bytes:
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(
        [
            "source_member",
            "source_line",
            "record_id",
            "timestamp",
            "Temperature",
            "Humidity",
            "Light",
            "CO2",
            "HumidityRatio",
            "Occupancy",
        ]
    )
    for row in observations:
        writer.writerow(
            [
                row.source_member,
                row.source_line,
                row.record_id,
                row.timestamp.isoformat(timespec="seconds"),
                _decimal_text(row.temperature),
                _decimal_text(row.humidity),
                _decimal_text(row.light),
                _decimal_text(row.co2),
                _decimal_text(row.humidity_ratio),
                row.occupancy,
            ]
        )
    return output.getvalue().encode("utf-8")


def split_slices(protocol: dict[str, Any]) -> dict[str, tuple[int, int]]:
    result: dict[str, tuple[int, int]] = {}
    for split_raw in _array(protocol["splits"], "splits"):
        split = _object(split_raw, "split")
        result[_string(split["name"], "split name")] = (
            _integer(split["start"], "split start"),
            _integer(split["stop"], "split stop"),
        )
    return result


def _gap_summary(observations: Sequence[Observation]) -> dict[str, Any]:
    gaps = [
        int((observations[index + 1].timestamp - observations[index].timestamp).total_seconds())
        for index in range(len(observations) - 1)
    ]
    counts = Counter(gaps)
    exceptional = [
        {"after": observations[index].timestamp.isoformat(timespec="seconds"), "seconds": gap}
        for index, gap in enumerate(gaps)
        if gap not in {59, 60, 61}
    ]
    return {
        "exceptional": exceptional,
        "max_seconds": max(gaps, default=0),
        "seconds_histogram": {str(key): counts[key] for key in sorted(counts)},
    }


def build_manifest(
    prepared: PreparedDataset,
    protocol: dict[str, Any],
    protocol_raw: bytes,
    script_raw: bytes,
) -> dict[str, Any]:
    observations = prepared.observations
    stream_raw = canonical_stream_bytes(observations)
    split_rows: list[dict[str, Any]] = []
    for name, (start, stop) in split_slices(protocol).items():
        subset = observations[start:stop]
        subset_raw = canonical_stream_bytes(subset)
        labels = Counter(row.occupancy for row in subset)
        split_rows.append(
            {
                "bytes": len(subset_raw),
                "count": len(subset),
                "first_timestamp": subset[0].timestamp.isoformat(timespec="seconds"),
                "label_counts": {"0": labels[0], "1": labels[1]},
                "last_timestamp": subset[-1].timestamp.isoformat(timespec="seconds"),
                "name": name,
                "sha256": sha256_bytes(subset_raw),
                "start": start,
                "stop": stop,
            }
        )
    dataset = _object(protocol["dataset"], "dataset")
    members = _array(dataset["members"], "members")
    member_rows = []
    for member_raw in members:
        member = _object(member_raw, "member")
        name = _string(member["name"], "member name")
        actual_bytes, actual_sha = prepared.member_digests[name]
        member_rows.append(
            {
                "bytes": actual_bytes,
                "name": name,
                "rows": _integer(member["rows"], f"member {name} rows"),
                "sha256": actual_sha,
            }
        )
    return {
        "artifact_status": "DATA IDENTITY AND CHRONOLOGY CHECKED; NO STATISTICAL CERTIFICATE",
        "canonical_stream": {
            "bytes": len(stream_raw),
            "columns": _object(protocol["preprocessing"], "preprocessing")["canonical_columns"],
            "first_timestamp": observations[0].timestamp.isoformat(timespec="seconds"),
            "last_timestamp": observations[-1].timestamp.isoformat(timespec="seconds"),
            "rows": len(observations),
            "sha256": sha256_bytes(stream_raw),
        },
        "dataset": {
            "archive": {
                "bytes": prepared.archive_bytes,
                "sha256": prepared.archive_sha256,
                "url": _object(dataset["archive"], "archive")["url"],
            },
            "doi": dataset["doi"],
            "landing_page": dataset["landing_page"],
            "license": dataset["license"],
            "members": member_rows,
            "name": dataset["name"],
            "uci_dataset_id": dataset["uci_dataset_id"],
        },
        "files": [
            {
                "path": "applications/brier_monitor/uci357-protocol-v1.json",
                "role": "protocol",
                "sha256": sha256_bytes(protocol_raw),
            },
            {
                "path": "scripts/prepare_brier_monitor_uci357.py",
                "role": "preparer",
                "sha256": sha256_bytes(script_raw),
            },
        ],
        "gap_diagnostics": _gap_summary(observations),
        "manifest_schema": MANIFEST_SCHEMA,
        "nonclaims": protocol["nonclaims"],
        "posterior": protocol["posterior"],
        "probability": protocol["probability"],
        "splits": split_rows,
        "validation": {
            "duplicate_timestamps": 0,
            "missing_values": 0,
            "strictly_increasing_timestamps": True,
            "total_rows": len(observations),
        },
    }


def _as_fraction_probability(value: Decimal | Fraction | int | float | str) -> Fraction:
    if isinstance(value, bool):
        raise ProtocolError("boolean is not a probability")
    if isinstance(value, Fraction):
        result = value
    elif isinstance(value, int):
        result = Fraction(value)
    elif isinstance(value, float):
        if not math.isfinite(value):
            raise ProtocolError("probability must be finite")
        result = Fraction(*value.as_integer_ratio())
    elif isinstance(value, Decimal):
        if not value.is_finite():
            raise ProtocolError("probability must be finite")
        result = Fraction(*value.as_integer_ratio())
    elif isinstance(value, str):
        try:
            decimal_value = Decimal(value)
        except InvalidOperation as error:
            raise ProtocolError(f"invalid probability: {value!r}") from error
        if not decimal_value.is_finite():
            raise ProtocolError("probability must be finite")
        result = Fraction(*decimal_value.as_integer_ratio())
    else:
        raise ProtocolError(f"unsupported probability type: {type(value).__name__}")
    if not 0 <= result <= 1:
        raise ProtocolError(f"probability is outside [0,1]: {result}")
    return result


def quantize_probability(value: Decimal | Fraction | int | float | str) -> int:
    probability = _as_fraction_probability(value)
    quantized = (
        2 * PROBABILITY_DENOMINATOR * probability.numerator
        + probability.denominator
    ) // (2 * probability.denominator)
    if not 0 <= quantized <= PROBABILITY_DENOMINATOR:
        raise ProtocolError("quantized probability escaped its integer range")
    return quantized


def _fit_rejecting_warning(
    estimator: Any,
    features: Any,
    outcomes: Any,
    warning_category: type[Warning],
) -> None:
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("error", warning_category)
            estimator.fit(features, outcomes)
    except warning_category as error:
        raise ProtocolError("baseline model emitted a convergence warning") from error


def brier_loss_numerator(quantized_probability: int, outcome: int) -> int:
    if isinstance(quantized_probability, bool) or not isinstance(quantized_probability, int):
        raise ProtocolError("quantized probability must be an integer")
    if not 0 <= quantized_probability <= PROBABILITY_DENOMINATOR:
        raise ProtocolError("quantized probability is out of range")
    if outcome not in (0, 1):
        raise ProtocolError("Brier outcome must be 0 or 1")
    return (quantized_probability - PROBABILITY_DENOMINATOR * outcome) ** 2


def brier_loss(quantized_probability: int, outcome: int) -> Fraction:
    return Fraction(
        brier_loss_numerator(quantized_probability, outcome),
        PROBABILITY_DENOMINATOR**2,
    )


def deterministic_soft_winner_posterior(
    model_order: Sequence[str], cumulative_brier_numerators: dict[str, int]
) -> dict[str, Fraction]:
    if len(model_order) < 2 or len(set(model_order)) != len(model_order):
        raise ProtocolError("posterior requires at least two uniquely ordered models")
    if set(cumulative_brier_numerators) != set(model_order):
        raise ProtocolError("posterior losses must cover the exact declared model order")
    for model_id, loss in cumulative_brier_numerators.items():
        if isinstance(loss, bool) or not isinstance(loss, int) or loss < 0:
            raise ProtocolError(f"posterior loss for {model_id} must be a nonnegative integer")
    winner = min(model_order, key=lambda model_id: cumulative_brier_numerators[model_id])
    winner_mass = Fraction(3, 5)
    loser_mass = (1 - winner_mass) / (len(model_order) - 1)
    posterior = {
        model_id: winner_mass if model_id == winner else loser_mass
        for model_id in model_order
    }
    if sum(posterior.values(), Fraction(0)) != 1:
        raise AssertionError("posterior construction failed to normalize")
    return posterior


def _prediction_digest(predictions: Iterable[int]) -> str:
    payload = bytearray()
    for prediction in predictions:
        if not 0 <= prediction <= PROBABILITY_DENOMINATOR:
            raise ProtocolError("prediction digest received an out-of-range value")
        payload.extend(prediction.to_bytes(2, byteorder="big", signed=False))
    return sha256_bytes(bytes(payload))


def _metric_row(predictions: Sequence[int], outcomes: Sequence[int]) -> dict[str, Any]:
    if len(predictions) != len(outcomes) or not outcomes:
        raise ProtocolError("metric inputs must have equal nonzero length")
    numerator = sum(
        brier_loss_numerator(prediction, outcome)
        for prediction, outcome in zip(predictions, outcomes, strict=True)
    )
    denominator = len(outcomes) * PROBABILITY_DENOMINATOR**2
    risk = Fraction(numerator, denominator)
    return {
        "brier_decimal": format(float(risk), ".15f"),
        "brier_rational": _fraction_text(risk),
        "count": len(outcomes),
        "loss_numerator_sum": numerator,
        "prediction_sha256_uint16_be": _prediction_digest(predictions),
    }


def build_local_baseline_result(
    prepared: PreparedDataset,
    protocol: dict[str, Any],
    protocol_raw: bytes,
    manifest: dict[str, Any],
) -> dict[str, Any]:
    try:
        import numpy as np
        import sklearn  # type: ignore[import-untyped]
        from sklearn.exceptions import ConvergenceWarning  # type: ignore[import-untyped]
        from sklearn.linear_model import LogisticRegression  # type: ignore[import-untyped]
        from sklearn.pipeline import Pipeline  # type: ignore[import-untyped]
        from sklearn.preprocessing import StandardScaler  # type: ignore[import-untyped]
    except ImportError as error:
        raise ProtocolError("scikit-learn and NumPy are unavailable for local baselines") from error

    observations = prepared.observations
    slices = split_slices(protocol)
    allowlist_name = _string(
        _object(protocol["feature_contract"], "feature contract")["baseline_logistic_allowlist"],
        "baseline logistic allowlist",
    )
    feature_names = _array(
        _object(_object(protocol["feature_contract"], "feature contract")["allowlists"], "allowlists")[allowlist_name],
        "baseline feature allowlist",
    )
    accessors = {
        "Temperature": lambda row: row.temperature,
        "Humidity": lambda row: row.humidity,
        "Light": lambda row: row.light,
        "CO2": lambda row: row.co2,
    }
    if any(name not in accessors for name in feature_names):
        raise ProtocolError("baseline feature allowlist includes an unsupported or leaked field")

    def matrix(rows: Sequence[Observation]) -> Any:
        return np.asarray(
            [[float(accessors[name](row)) for name in feature_names] for row in rows],
            dtype=np.float64,
        )

    def outcomes(rows: Sequence[Observation]) -> Any:
        return np.asarray([row.occupancy for row in rows], dtype=np.int64)

    train_start, train_stop = slices["train"]
    train_rows = observations[train_start:train_stop]
    train_outcomes = outcomes(train_rows)
    if set(train_outcomes.tolist()) != {0, 1}:
        raise ProtocolError("training split must contain both labels")
    logistic = Pipeline(
        steps=[
            ("scale", StandardScaler()),
            (
                "model",
                LogisticRegression(
                    C=1.0,
                    max_iter=2000,
                    random_state=0,
                    solver="lbfgs",
                    tol=1e-12,
                ),
            ),
        ]
    )
    _fit_rejecting_warning(
        logistic,
        matrix(train_rows),
        train_outcomes,
        ConvergenceWarning,
    )
    prevalence = Fraction(int(train_outcomes.sum()), len(train_outcomes))
    constant_q = quantize_probability(prevalence)

    model_order = ["constant_train_prevalence", "logistic_all_sensor"]
    split_metrics: dict[str, dict[str, Any]] = {}
    monitor_loss_sums: dict[str, int] = {}
    for split_name, (start, stop) in slices.items():
        rows = observations[start:stop]
        y = [row.occupancy for row in rows]
        logistic_probabilities = logistic.predict_proba(matrix(rows))[:, 1]
        logistic_q = [quantize_probability(float(value)) for value in logistic_probabilities]
        constant_predictions = [constant_q] * len(rows)
        constant_metric = _metric_row(constant_predictions, y)
        logistic_metric = _metric_row(logistic_q, y)
        split_metrics[split_name] = {
            "constant_train_prevalence": constant_metric,
            "label_counts": {
                "0": sum(outcome == 0 for outcome in y),
                "1": sum(outcome == 1 for outcome in y),
            },
            "logistic_all_sensor": logistic_metric,
        }
        if split_name == "monitor":
            monitor_loss_sums = {
                "constant_train_prevalence": _integer(
                    constant_metric["loss_numerator_sum"], "constant monitor loss"
                ),
                "logistic_all_sensor": _integer(
                    logistic_metric["loss_numerator_sum"], "logistic monitor loss"
                ),
            }

    posterior = deterministic_soft_winner_posterior(model_order, monitor_loss_sums)
    logistic_model = logistic.named_steps["model"]
    scaler = logistic.named_steps["scale"]
    return {
        "artifact_status": "LOCAL NON-PUBLIC BASELINES; NOT A FORMALSLT CERTIFICATE",
        "canonical_stream_sha256": _object(manifest["canonical_stream"], "canonical stream")["sha256"],
        "dataset_archive_sha256": prepared.archive_sha256,
        "model_order": model_order,
        "models": {
            "constant_train_prevalence": {
                "probability_quantized": constant_q,
                "probability_rational": _fraction_text(Fraction(constant_q, PROBABILITY_DENOMINATOR)),
                "training_prevalence": _fraction_text(prevalence),
            },
            "logistic_all_sensor": {
                "allowlist": allowlist_name,
                "coefficient_repr": [repr(float(value)) for value in logistic_model.coef_[0]],
                "intercept_repr": repr(float(logistic_model.intercept_[0])),
                "parameters": {
                    "C": "1",
                    "max_iter": 2000,
                    "random_state": 0,
                    "solver": "lbfgs",
                    "tol": "1e-12",
                },
                "scaler_mean_repr": [repr(float(value)) for value in scaler.mean_],
                "scaler_scale_repr": [repr(float(value)) for value in scaler.scale_],
            },
        },
        "nonclaims": protocol["nonclaims"],
        "posterior_after_monitor": {
            "selection_rule": protocol["posterior"],
            "weights": {model_id: _fraction_text(posterior[model_id]) for model_id in model_order},
            "winner": max(model_order, key=lambda model_id: posterior[model_id]),
        },
        "probability_denominator": PROBABILITY_DENOMINATOR,
        "protocol_sha256": sha256_bytes(protocol_raw),
        "runtime": {
            "numpy": np.__version__,
            "platform": platform.platform(),
            "python": platform.python_version(),
            "scikit_learn": sklearn.__version__,
        },
        "schema": LOCAL_RESULT_SCHEMA,
        "splits": split_metrics,
    }


def _load_or_download_archive(
    protocol: dict[str, Any], archive_path: Path, allow_download: bool
) -> bytes:
    if archive_path.exists():
        try:
            raw = archive_path.read_bytes()
        except OSError as error:
            raise ProtocolError(f"cannot read local archive {archive_path}: {error}") from error
        verify_archive_identity(raw, protocol)
        return raw
    if not allow_download:
        raise ProtocolError(
            f"local archive is absent: {archive_path}; rerun with --download"
        )
    return download_archive(protocol, archive_path)


def _compare_bytes(path: Path, expected: bytes, role: str) -> None:
    try:
        actual = path.read_bytes()
    except OSError as error:
        raise ProtocolError(f"cannot read tracked {role} {path}: {error}") from error
    if actual != expected:
        raise ProtocolError(f"tracked {role} is stale: {path}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare and verify the frozen UCI-357 Brier-monitor data protocol"
    )
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--archive", type=Path, default=DEFAULT_ARCHIVE)
    parser.add_argument("--canonical-stream", type=Path, default=DEFAULT_CANONICAL_STREAM)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--local-result", type=Path, default=DEFAULT_LOCAL_RESULT)
    parser.add_argument("--download", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--baselines",
        action="store_true",
        help="also compute the optional local scikit-learn baselines",
    )
    arguments = parser.parse_args(argv)
    try:
        if arguments.protocol.resolve() != DEFAULT_PROTOCOL.resolve():
            raise ProtocolError(
                "--protocol must resolve to the frozen tracked UCI-357 protocol"
            )
        protocol, protocol_raw = _load_protocol(arguments.protocol)
        archive_raw = _load_or_download_archive(protocol, arguments.archive, arguments.download)
        prepared = prepare_archive(archive_raw, protocol)
        script_raw = Path(__file__).read_bytes()
        manifest = build_manifest(prepared, protocol, protocol_raw, script_raw)
        manifest_raw = canonical_json_bytes(manifest)
        stream_raw = canonical_stream_bytes(prepared.observations)
        if arguments.check:
            _compare_bytes(arguments.manifest, manifest_raw, "manifest")
            if arguments.canonical_stream.exists():
                _compare_bytes(arguments.canonical_stream, stream_raw, "canonical stream")
        else:
            _atomic_write(arguments.canonical_stream, stream_raw)
            _atomic_write(arguments.manifest, manifest_raw)
        if arguments.baselines:
            result = build_local_baseline_result(
                prepared, protocol, protocol_raw, manifest
            )
            result_raw = canonical_json_bytes(result)
            if arguments.check:
                if arguments.local_result.exists():
                    _compare_bytes(arguments.local_result, result_raw, "local baseline result")
            else:
                _atomic_write(arguments.local_result, result_raw)
    except ProtocolError as error:
        print(f"ERROR: UCI-357 protocol refused: {error}", file=sys.stderr)
        return 1
    print(
        "UCI-357 protocol verified: "
        f"{len(prepared.observations)} rows, archive {prepared.archive_sha256}, "
        f"canonical stream {manifest['canonical_stream']['sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
