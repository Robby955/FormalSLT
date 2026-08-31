#!/usr/bin/env python3
"""Prepare exact Brier-monitor summaries from CSV or Parquet predictions.

This module performs data ingestion and exact rational arithmetic only.  Its
output is explicitly not a FormalSLT certificate: a registered theorem profile
and an independent replay checker must consume the preparation before the
Lean verification status can become PASS.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Iterator


PROTOCOL_SCHEMA = "formalslt.brier-tabular-protocol.v1"
PREPARATION_SCHEMA = "formalslt.brier-tabular-preparation.v1"
STATUS = "PREPARED_NOT_CERTIFIED"
CLAIM_QUANTITY = "posterior-averaged encountered conditional prefix Brier risk"
LOG_TERMS = 32
SUPPORTED_FORMATS = {"csv", "parquet"}
NONCLAIMS = [
    "data ingestion and exact arithmetic only; this preparation is not a certificate",
    "no Lean kernel check or statistical coverage theorem is attached",
    "input ordering and provenance are declared by the caller, not externally established",
    "the candidate expression is not future, stationary, population, or deployment risk",
    "the fixed half-tilt preparation is not coin betting or post-hoc strategy selection",
]


class PreparationError(ValueError):
    """Raised when a tabular protocol or prediction stream is invalid."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise PreparationError(f"cannot hash input: {path}") from error
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def parse_fraction(value: Any, label: str) -> Fraction:
    if not isinstance(value, str):
        raise PreparationError(f"{label} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise PreparationError(f"invalid rational at {label}: {value!r}") from error
    if rational_text(result) != value:
        raise PreparationError(f"noncanonical rational at {label}: {value!r}")
    return result


def _keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise PreparationError(
            f"{label} keys mismatch; missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def _object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise PreparationError(f"{label} must be an object")
    return value


def _array(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise PreparationError(f"{label} must be an array")
    return value


def _integer(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise PreparationError(f"{label} must be an integer")
    return value


def _load_json(raw: bytes, label: str) -> dict[str, Any]:
    def reject_float(value: str) -> None:
        raise PreparationError(f"floating-point numbers are forbidden in {label}: {value}")

    def reject_constant(value: str) -> None:
        raise PreparationError(f"non-finite numbers are forbidden in {label}: {value}")

    def unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise PreparationError(f"duplicate key in {label}: {key}")
            result[key] = value
        return result

    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=reject_float,
            parse_constant=reject_constant,
            object_pairs_hook=unique_pairs,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise PreparationError(f"invalid JSON in {label}: {error}") from error
    return _object(value, label)


def _load_yaml(raw: bytes, label: str) -> dict[str, Any]:
    try:
        import yaml
    except ImportError as error:
        raise PreparationError(
            "YAML input requires PyYAML; install requirements-cli.txt or use canonical JSON"
        ) from error

    class UniqueLoader(yaml.SafeLoader):
        pass

    def construct_mapping(loader: Any, node: Any, deep: bool = False) -> dict[str, Any]:
        pairs = loader.construct_pairs(node, deep=deep)
        result: dict[str, Any] = {}
        for key, value in pairs:
            if not isinstance(key, str):
                raise PreparationError(f"non-string key in {label}")
            if key in result:
                raise PreparationError(f"duplicate key in {label}: {key}")
            result[key] = value
        return result

    UniqueLoader.add_constructor(
        yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
        construct_mapping,
    )
    try:
        value = yaml.load(raw.decode("utf-8"), Loader=UniqueLoader)
    except (UnicodeDecodeError, yaml.YAMLError) as error:
        raise PreparationError(f"invalid YAML in {label}: {error}") from error
    return _object(value, label)


def load_protocol(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise PreparationError(f"cannot read protocol: {path}") from error
    suffix = path.suffix.lower()
    if suffix == ".json":
        value = _load_json(raw, "protocol")
    elif suffix in {".yaml", ".yml"}:
        value = _load_yaml(raw, "protocol")
    else:
        raise PreparationError("protocol must use .json, .yaml, or .yml")
    _keys(
        value,
        {"analysis", "claim", "data", "models", "protocol_id", "schema_version", "statistics"},
        "protocol",
    )
    if value["schema_version"] != PROTOCOL_SCHEMA:
        raise PreparationError(f"unsupported protocol schema: {value['schema_version']!r}")
    if value["analysis"] != "brier_monitor":
        raise PreparationError("protocol analysis must be 'brier_monitor'")
    if not isinstance(value["protocol_id"], str) or not value["protocol_id"]:
        raise PreparationError("protocol_id must be a nonempty string")

    data = _object(value["data"], "protocol.data")
    _keys(
        data,
        {
            "input_format",
            "outcome_column",
            "prediction_encoding",
            "prediction_scale",
            "require_strict_time_order",
            "time_column",
        },
        "protocol.data",
    )
    if data["input_format"] not in SUPPORTED_FORMATS:
        raise PreparationError(f"unsupported input format: {data['input_format']!r}")
    if data["prediction_encoding"] != "scaled_integer":
        raise PreparationError("prediction_encoding must be 'scaled_integer'")
    scale = _integer(data["prediction_scale"], "protocol.data.prediction_scale")
    if scale <= 0:
        raise PreparationError("prediction_scale must be positive")
    if data["require_strict_time_order"] is not True:
        raise PreparationError("require_strict_time_order must be true")
    for field in ("time_column", "outcome_column"):
        if not isinstance(data[field], str) or not data[field]:
            raise PreparationError(f"protocol.data.{field} must be a nonempty string")

    models = _array(value["models"], "protocol.models")
    if not models:
        raise PreparationError("protocol.models must not be empty")
    model_ids: list[str] = []
    columns: list[str] = []
    for index, raw_model in enumerate(models):
        model = _object(raw_model, f"protocol.models[{index}]")
        _keys(model, {"column", "id"}, f"protocol.models[{index}]")
        model_id, column = model["id"], model["column"]
        if not isinstance(model_id, str) or not model_id:
            raise PreparationError(f"protocol.models[{index}].id must be nonempty")
        if not isinstance(column, str) or not column:
            raise PreparationError(f"protocol.models[{index}].column must be nonempty")
        model_ids.append(model_id)
        columns.append(column)
    if len(set(model_ids)) != len(model_ids):
        raise PreparationError("model ids must be unique")
    if len(set(columns)) != len(columns):
        raise PreparationError("prediction columns must be unique")

    statistics = _object(value["statistics"], "protocol.statistics")
    _keys(statistics, {"delta", "posterior", "prior", "tilt", "wake"}, "protocol.statistics")
    if _integer(statistics["wake"], "protocol.statistics.wake") != 0:
        raise PreparationError("tabular preparation v1 supports wake 0 only")
    delta = parse_fraction(statistics["delta"], "protocol.statistics.delta")
    tilt = parse_fraction(statistics["tilt"], "protocol.statistics.tilt")
    if not 0 < delta < 1:
        raise PreparationError("delta must lie in (0,1)")
    if tilt != Fraction(1, 2):
        raise PreparationError("tabular preparation v1 supports tilt 1/2 only")
    for name in ("prior", "posterior"):
        weights = _object(statistics[name], f"protocol.statistics.{name}")
        if set(weights) != set(model_ids):
            raise PreparationError(f"{name} keys must equal the model ids")
        parsed = [parse_fraction(weights[model], f"{name}.{model}") for model in model_ids]
        if name == "prior" and any(weight <= 0 for weight in parsed):
            raise PreparationError("prior weights must be positive")
        if name == "posterior" and any(weight < 0 for weight in parsed):
            raise PreparationError("posterior weights must be nonnegative")
        if sum(parsed, Fraction(0)) != 1:
            raise PreparationError(f"{name} weights must sum to one")

    claim = _object(value["claim"], "protocol.claim")
    _keys(claim, {"quantity"}, "protocol.claim")
    if claim["quantity"] != CLAIM_QUANTITY:
        raise PreparationError(f"unsupported claim quantity: {claim['quantity']!r}")
    return value, raw


def _int_cell(value: Any, label: str) -> int:
    if isinstance(value, bool):
        raise PreparationError(f"{label} must be an integer")
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        stripped = value.strip()
        if stripped and (stripped.isdigit() or (stripped[0] == "-" and stripped[1:].isdigit())):
            return int(stripped)
    raise PreparationError(f"{label} must be an integer")


def _csv_rows(path: Path, columns: list[str]) -> Iterator[dict[str, Any]]:
    try:
        handle = path.open("r", encoding="utf-8", newline="")
    except OSError as error:
        raise PreparationError(f"cannot open CSV input: {path}") from error
    with handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise PreparationError("CSV has no header")
        if len(set(reader.fieldnames)) != len(reader.fieldnames):
            raise PreparationError("CSV header contains duplicate columns")
        missing = sorted(set(columns) - set(reader.fieldnames))
        if missing:
            raise PreparationError("CSV is missing columns: " + ", ".join(missing))
        yield from reader


def _parquet_rows(path: Path, columns: list[str]) -> Iterator[dict[str, Any]]:
    try:
        import pyarrow.parquet as parquet
    except ImportError as error:
        raise PreparationError(
            "Parquet input requires pyarrow; install requirements-cli.txt or use CSV"
        ) from error
    try:
        parquet_file = parquet.ParquetFile(path)
    except Exception as error:
        raise PreparationError(f"cannot open Parquet input: {path}") from error
    missing = sorted(set(columns) - set(parquet_file.schema.names))
    if missing:
        raise PreparationError("Parquet input is missing columns: " + ", ".join(missing))
    try:
        for batch in parquet_file.iter_batches(batch_size=65536, columns=columns):
            yield from batch.to_pylist()
    except Exception as error:
        raise PreparationError("cannot stream Parquet rows") from error


def iter_rows(protocol: dict[str, Any], path: Path) -> Iterator[dict[str, Any]]:
    data = protocol["data"]
    columns = [data["time_column"], data["outcome_column"]] + [
        model["column"] for model in protocol["models"]
    ]
    expected_suffix = ".csv" if data["input_format"] == "csv" else ".parquet"
    if path.suffix.lower() != expected_suffix:
        raise PreparationError(
            f"input extension must be {expected_suffix} for protocol format {data['input_format']}"
        )
    if data["input_format"] == "csv":
        yield from _csv_rows(path, columns)
    else:
        yield from _parquet_rows(path, columns)


def _log_unit_interval(value: Fraction) -> tuple[Fraction, Fraction]:
    if not 1 <= value <= 2:
        raise AssertionError("log range reduction failed")
    z = (value - 1) / (value + 1)
    partial = Fraction(0)
    for index in range(LOG_TERMS):
        partial += 2 * z ** (2 * index + 1) / (2 * index + 1)
    remainder = 2 * z ** (2 * LOG_TERMS + 1) / (
        (2 * LOG_TERMS + 1) * (1 - z * z)
    )
    return partial, partial + remainder


def log_interval(value: Fraction) -> tuple[Fraction, Fraction]:
    if value <= 0:
        raise PreparationError("log input must be positive")
    if value == 1:
        return Fraction(0), Fraction(0)
    if value < 1:
        low, high = log_interval(1 / value)
        return -high, -low
    exponent = 0
    reduced = value
    while reduced >= 2:
        reduced /= 2
        exponent += 1
    log_two_low, log_two_high = _log_unit_interval(Fraction(2))
    reduced_low, reduced_high = _log_unit_interval(reduced)
    return (
        exponent * log_two_low + reduced_low,
        exponent * log_two_high + reduced_high,
    )


def _interval_record(interval: tuple[Fraction, Fraction]) -> dict[str, str]:
    return {"lower": rational_text(interval[0]), "upper": rational_text(interval[1])}


def _kl_interval(posterior: list[Fraction], prior: list[Fraction]) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho == 0:
            continue
        term_low, term_high = log_interval(rho / pi)
        low += rho * term_low
        high += rho * term_high
    return low, high


def _psi_interval(tilt: Fraction) -> tuple[Fraction, Fraction]:
    log_low, log_high = log_interval(1 - tilt)
    return -log_high - tilt, -log_low - tilt


def prepare(protocol_path: Path, data_path: Path) -> dict[str, Any]:
    protocol, protocol_raw = load_protocol(protocol_path)
    data = protocol["data"]
    models = protocol["models"]
    model_ids = [model["id"] for model in models]
    columns = {model["id"]: model["column"] for model in models}
    scale = data["prediction_scale"]
    statistics = protocol["statistics"]
    prior = [parse_fraction(statistics["prior"][model], f"prior.{model}") for model in model_ids]
    posterior = [
        parse_fraction(statistics["posterior"][model], f"posterior.{model}")
        for model in model_ids
    ]
    delta = parse_fraction(statistics["delta"], "delta")
    tilt = parse_fraction(statistics["tilt"], "tilt")
    prefix_sums = [Fraction(0) for _ in model_ids]
    posterior_loss_sum = Fraction(0)
    posterior_quadratic_variation = Fraction(0)
    normalized_stream = hashlib.sha256()
    previous_time: int | None = None
    count = 0

    for count, row in enumerate(iter_rows(protocol, data_path), start=1):
        time_value = _int_cell(row.get(data["time_column"]), f"row {count} time")
        if previous_time is not None and time_value <= previous_time:
            raise PreparationError(f"row {count} time is not strictly increasing")
        previous_time = time_value
        outcome = _int_cell(row.get(data["outcome_column"]), f"row {count} outcome")
        if outcome not in (0, 1):
            raise PreparationError(f"row {count} outcome must be 0 or 1")
        scaled_predictions: list[int] = []
        losses: list[Fraction] = []
        for index, model_id in enumerate(model_ids):
            scaled = _int_cell(row.get(columns[model_id]), f"row {count} prediction {model_id}")
            if not 0 <= scaled <= scale:
                raise PreparationError(
                    f"row {count} prediction {model_id} must lie in [0,{scale}]"
                )
            scaled_predictions.append(scaled)
            prediction = Fraction(scaled, scale)
            loss = (prediction - outcome) ** 2
            predictor = Fraction(1, 2) if count == 1 else prefix_sums[index] / (count - 1)
            posterior_quadratic_variation += posterior[index] * (loss - predictor) ** 2
            prefix_sums[index] += loss
            losses.append(loss)
        posterior_loss_sum += sum(
            (posterior[index] * loss for index, loss in enumerate(losses)),
            Fraction(0),
        )
        normalized_stream.update(
            canonical_json_bytes(
                {"outcome": outcome, "predictions": scaled_predictions, "time": time_value}
            )
        )

    if count < 4:
        raise PreparationError("at least four observations are required")
    empirical = posterior_loss_sum / count
    kl_bounds = _kl_interval(posterior, prior)
    confidence_bounds = log_interval(1 / delta)
    psi_bounds = _psi_interval(tilt)
    candidate_upper = empirical + (
        kl_bounds[1] + confidence_bounds[1] + psi_bounds[1] * posterior_quadratic_variation
    ) / (tilt * count)
    source_path = Path(__file__).resolve()
    return {
        "artifact_status": STATUS,
        "candidate": {
            "boundary_upper": rational_text(candidate_upper),
            "confidence_log_interval": _interval_record(confidence_bounds),
            "kl_interval": _interval_record(kl_bounds),
            "psi_interval": _interval_record(psi_bounds),
        },
        "claim": {"quantity": CLAIM_QUANTITY, "status": "NOT_CERTIFIED"},
        "data": {
            "input_format": data["input_format"],
            "input_sha256": sha256_file(data_path),
            "normalized_stream_sha256": normalized_stream.hexdigest(),
            "observations": count,
            "prediction_encoding": "scaled_integer",
            "prediction_scale": scale,
        },
        "nonclaims": NONCLAIMS,
        "protocol": {
            "protocol_id": protocol["protocol_id"],
            "sha256": sha256_bytes(protocol_raw),
        },
        "schema_version": PREPARATION_SCHEMA,
        "statistics": {
            "delta": rational_text(delta),
            "posterior_empirical_brier_risk": rational_text(empirical),
            "posterior_suffix_predictor_quadratic_variation": rational_text(
                posterior_quadratic_variation
            ),
            "tilt": rational_text(tilt),
            "wake": 0,
        },
        "verification": {
            "data_parser": "PASS",
            "independent_replay": "NOT_RUN",
            "lean_kernel": "NOT_RUN",
            "source": {
                "path": source_path.relative_to(Path(__file__).resolve().parents[1]).as_posix(),
                "sha256": sha256_file(source_path),
            },
        },
    }


def atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
