#!/usr/bin/env python3
"""Independently replay and verify the external GJP Brier artifacts.

This verifier intentionally duplicates the replay arithmetic. It does not
import the builder or the prospective protocol checker. It reads the pinned
raw inputs, protocol, and three external artifacts; it never writes a file,
downloads data, invokes Lean, or mutates the repository.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import inspect
import json
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, time, timedelta
from decimal import Decimal, InvalidOperation, ROUND_FLOOR, ROUND_HALF_EVEN, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROTOCOL = (
    ROOT / "applications" / "brier_monitor" / "realdata" / "gjp-brier-protocol-v1.json"
)
DEFAULT_PROTOCOL_MD = (
    ROOT / "applications" / "brier_monitor" / "realdata" / "gjp-brier-protocol-v1.md"
)
BUILDER = ROOT / "scripts" / "build_gjp_brier_replay.py"
PROTOCOL_CHECKER = ROOT / "scripts" / "check_gjp_brier_protocol.py"
INPUT_FETCHER = ROOT / "scripts" / "fetch_gjp_brier_inputs.py"
REPLAY_TEST = ROOT / "tests" / "test_gjp_brier_replay.py"
PROTOCOL_TEST = ROOT / "tests" / "test_gjp_brier_protocol.py"

STREAM_NAME = "gjp-brier-monitor-v1-stream.json"
RECEIPT_NAME = "gjp-brier-monitor-v1-receipt.json"
MANIFEST_NAME = "gjp-brier-monitor-v1-manifest.json"
STREAM_SCHEMA = "formalslt.brier-monitor.gjp-stream.v1"
RECEIPT_SCHEMA = "formalslt.brier-monitor.gjp-receipt.v1"
MANIFEST_SCHEMA = "formalslt.brier-monitor.gjp-manifest.v1"
ARTIFACT_STATUS = "REAL-DATA REPLAY; ARITHMETIC NOT YET LEAN-INSTANTIATED"
PROTOCOL_STATUS = "PROSPECTIVE PROTOCOL ONLY - NO STREAM, RECEIPT, OR RESULT"
PROTOCOL_VERSION = "gjp-brier-monitor-protocol-v1.2"
PROTOCOL_SCHEMA = "formalslt.brier-monitor.realdata-preregistration.v1"

MODEL_IDS = [
    "constant-train-baserate",
    "first-week-mean",
    "final-consensus-median",
    "extremized-final-consensus",
]
POSTERIOR_DECIMAL_PRECISION = 80
LOG_TERMS = 32
ABLATION_DAYS = (1, 3, 7, 14)
SHUFFLE_NAMESPACE = b"formalslt-gjp-shuffled-time-control-v1\0"
IFP_FIELDS = [
    "ifp_id",
    "q_type",
    "q_text",
    "q_desc",
    "q_status",
    "date_start",
    "date_suspend",
    "date_to_close",
    "date_closed",
    "outcome",
    "short_title",
    "days_open",
    "n_opts",
    "options",
]
FORECAST_FIELDS = [
    "ifp_id",
    "ctt",
    "cond",
    "training",
    "team",
    "user_id",
    "forecast_id",
    "fcast_type",
    "answer_option",
    "value",
    "fcast_date",
    "expertise",
    "q_status",
    "viewtime",
    "year",
    "timestamp",
]
EXPECTED_DATASET_FILES = [
    (2917330, "ifps.csv", "5c703d02284f8b563399967c554f1417", 1072153,
     "questions_and_outcomes"),
    (2917350, "readme.txt", "304832fa3e6b06861897f31eda69ba1f", 4382,
     "survey_forecast_codebook"),
    (2917351, "survey_fcasts.yr1.tab", "091ae92c90ec426772ea784a906d7ddb",
     30495631, "individual_forecasts"),
    (2917352, "survey_fcasts.yr2.tab", "528d1bfbff2ab8da6ba2b599b3b80e26",
     None, "individual_forecasts"),
    (2917353, "survey_fcasts.yr3.tab", "e5837d12b2a17d3ffd0f0bf1f46e61b0",
     None, "individual_forecasts"),
    (2917354, "survey_fcasts.yr4.tab", "47041be832baed547963c0ffd0d71a9d",
     None, "individual_forecasts"),
]
EXPECTED_ROUNDING = {
    "confidence_log": "up",
    "denominator_suffix_length_times_tilt": "exact",
    "empirical_suffix_risk": "exact",
    "kl_divergence": "up",
    "psi": "up",
    "suffix_quadratic_variation": "exact",
}


class VerificationError(ValueError):
    """Raised when independent replay finds a contract mismatch."""


def reject_float(value: str) -> None:
    raise VerificationError(f"floating-point JSON numbers are forbidden: {value}")


def reject_constant(value: str) -> None:
    raise VerificationError(f"non-finite JSON number is forbidden: {value}")


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise VerificationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def decode_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=reject_float,
            parse_constant=reject_constant,
            object_pairs_hook=unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid UTF-8 JSON in {label}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def load_canonical_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    value = decode_json(raw, label)
    if not isinstance(value, dict):
        raise VerificationError(f"{label} must be a JSON object")
    if raw != canonical_json_bytes(value):
        raise VerificationError(f"{label} is not canonical JSON")
    return value, raw


def require_equal(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise VerificationError(f"{label} mismatch: expected {expected!r}, got {actual!r}")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def file_digest(path: Path, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    reduced = Fraction(value)
    if reduced.denominator == 1:
        return str(reduced.numerator)
    return f"{reduced.numerator}/{reduced.denominator}"


def parse_fraction(value: Any, label: str) -> Fraction:
    if not isinstance(value, str):
        raise VerificationError(f"{label} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {label}: {value!r}") from error
    if rational_text(result) != value:
        raise VerificationError(f"noncanonical rational at {label}: {value!r}")
    return result


def parse_decimal(value: str, label: str) -> Decimal:
    try:
        result = Decimal(value)
    except InvalidOperation as error:
        raise VerificationError(f"invalid decimal at {label}: {value!r}") from error
    if not result.is_finite():
        raise VerificationError(f"non-finite decimal at {label}: {value!r}")
    return result


def parse_datetime(value: str, label: str) -> datetime:
    text = value.strip()
    for pattern in ("%m/%d/%y %H:%M", "%m/%d/%y", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(text, pattern)
        except ValueError:
            pass
    raise VerificationError(f"unsupported timestamp at {label}: {value!r}")


def iso_timestamp(value: datetime) -> str:
    return value.strftime("%Y-%m-%dT%H:%M:%S")


def round_ties_even(value: Fraction, denominator: int) -> Fraction:
    if denominator <= 0:
        raise VerificationError("rounding denominator must be positive")
    scaled = value * denominator
    quotient, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    if twice > scaled.denominator or (twice == scaled.denominator and quotient % 2):
        quotient += 1
    return Fraction(quotient, denominator)


def max_geometric_atom(suffix_length: int) -> int:
    logarithm = 0
    threshold = 4
    while threshold <= suffix_length:
        logarithm += 1
        threshold *= 4
    return max(logarithm - 1, 0) + 2


def validate_protocol(protocol: dict[str, Any]) -> None:
    require_equal(protocol.get("artifact_status"), PROTOCOL_STATUS, "protocol status")
    require_equal(protocol.get("protocol_version"), PROTOCOL_VERSION, "protocol version")
    require_equal(protocol.get("schema_version"), PROTOCOL_SCHEMA, "protocol schema")
    dataset = protocol["dataset"]
    require_equal(dataset["persistent_id"], "doi:10.7910/DVN/BPCDH5", "persistent id")
    require_equal(dataset["version"], "1.0", "dataset version")
    require_equal(dataset["version_state"], "RELEASED", "dataset state")
    require_equal(dataset["license"], "CC0-1.0", "dataset license")
    require_equal(
        dataset["access_route"],
        "https://dataverse.harvard.edu/api/access/datafile/{id}?format=original",
        "dataset access route",
    )
    actual_files = [
        (
            row["dataverse_id"], row["filename"], row["md5"],
            row["original_bytes_confirmed"], row["role"],
        )
        for row in dataset["files"]
    ]
    require_equal(actual_files, EXPECTED_DATASET_FILES, "dataset file pins")
    split = protocol["chronological_split"]
    split_counts = {name: split[name]["expected_count"] for name in ("train", "calibration", "monitor")}
    require_equal(split_counts, {"train": 122, "calibration": 83, "monitor": 175}, "split counts")
    eligibility = protocol["eligibility_after_temporal_amendment"]
    require_equal(eligibility["candidate_count"], 382, "candidate count")
    require_equal(eligibility["included_count"], 380, "included count")
    require_equal(eligibility["excluded_ifp_ids"], ["5008-0", "5009-0"], "excluded ids")
    require_equal(
        eligibility["split_counts"],
        {"calibration": 83, "monitor": 175, "train": 122},
        "eligible split counts",
    )
    catalog_ids = [row["id"] for row in protocol["model_catalog"]["models"]]
    require_equal(catalog_ids, MODEL_IDS, "model catalog")
    require_equal(protocol["model_catalog"]["prior"], ["1/4"] * 4, "prior")
    posterior = protocol["posterior_rule"]
    require_equal(posterior["decimal_precision"], 80, "posterior precision")
    require_equal(posterior["decimal_rounding"], "ROUND_HALF_EVEN", "posterior rounding")
    require_equal(posterior["quantization_denominator"], 10**15, "posterior grid")
    if "largest-remainder" not in posterior["quantization_rule"]:
        raise VerificationError("posterior quantization is not largest-remainder")
    before = protocol["prediction_before_outcome"]
    require_equal(before["effective_cutoff_formula"], "min(date_suspend, start-of-date_closed)", "cutoff")
    require_equal(before["survey_forecast_event_types"]["allowed"], [0, 1, 2, 4], "event types")
    require_equal(
        before["same_user_last_event_tie_break"],
        ["timestamp", "numeric forecast_id", "source year", "source line"],
        "last-event tie break",
    )
    if before["receipt_records_per_observation_min_consumed_timestamp"] is not True:
        raise VerificationError("protocol does not require minimum consumed timestamps")
    if before["receipt_records_per_observation_max_consumed_timestamp"] is not True:
        raise VerificationError("protocol does not require maximum consumed timestamps")
    require_equal(
        [row["id"] for row in protocol["protocol_amendments"]],
        [
            "gjp-temporal-window-amendment-2026-08-28",
            "gjp-rational-posterior-amendment-2026-08-28",
            "gjp-null-replay-amendment-2026-08-28",
        ],
        "protocol amendments",
    )
    if any(row["result_existed_before_amendment"] is not False for row in protocol["protocol_amendments"]):
        raise VerificationError("a protocol amendment postdates a numerical result")
    quant = protocol["quantization"]
    require_equal(quant["denominator"], 10**6, "forecast denominator")
    require_equal(quant["loss_denominator"], 10**12, "loss denominator")
    require_equal(quant["output_grid_denominator"], 10**15, "output denominator")
    require_equal(quant["rounding_directions"], EXPECTED_ROUNDING, "rounding directions")
    confidence = protocol["confidence_contract"]
    require_equal(confidence["delta"], "1/160", "confidence delta")
    require_equal(confidence["wake_grid"], [0, 8, 32, 128], "wake grid")
    if not confidence["wake_shopping_outside_grid_voids_the_allocation"]:
        raise VerificationError("wake allocation is not fail-closed")
    if protocol["lean_binding"]["certified"] is not False:
        raise VerificationError("prospective protocol self-declares Lean certification")
    baselines = protocol["baselines"]
    require_equal(baselines["null_replicates"], 2000, "null replicate count")
    require_equal(
        baselines["train_base_rate_definition"],
        "the exact quantized probability emitted by constant-train-baserate, an integer multiple of 1/1000000",
        "null base-rate definition",
    )
    null_generator = baselines["null_generator"]
    require_equal(null_generator["algorithm"], "SplitMix64", "null generator")
    require_equal(null_generator["word_bits"], 64, "null generator word size")
    require_equal(
        null_generator["seed_u64_hex"], "0x46534c54474a5031", "null generator seed"
    )
    require_equal(
        null_generator["draw_order"],
        "replicate index ascending, then monitor index ascending; rejected words consume stream positions",
        "null draw order",
    )
    require_equal(
        null_generator["bernoulli_rule"],
        "for reduced q = numerator/denominator, set limit = floor(2^64 / denominator) * denominator; reject words >= limit; otherwise y = 1 iff word mod denominator < numerator",
        "exact Bernoulli rule",
    )
    require_equal(
        [row["id"] for row in protocol["leakage_tests"]],
        [
            "timestamp_assertion",
            "deliberately_leaked_tripwire",
            "future_feature_ablation",
            "shuffled_time_control",
            "parametric_null_replay",
        ],
        "leakage test catalog",
    )
    for relative in protocol["fresh_output_paths"]:
        candidate = (ROOT / relative).resolve()
        try:
            candidate.relative_to(ROOT.resolve())
        except ValueError as error:
            raise VerificationError(f"reserved path escapes repository: {relative}") from error
        if candidate.exists():
            raise VerificationError(f"reserved prospective output exists: {relative}")


def verify_raw_inputs(
    protocol: dict[str, Any], input_dir: Path
) -> tuple[dict[str, Path], list[dict[str, Any]]]:
    paths: dict[str, Path] = {}
    records: list[dict[str, Any]] = []
    for entry in protocol["dataset"]["files"]:
        path = input_dir / entry["filename"]
        if not path.is_file():
            raise VerificationError(f"missing pinned raw input: {path}")
        md5 = file_digest(path, "md5")
        require_equal(md5, entry["md5"], f"{path.name} MD5")
        size = path.stat().st_size
        expected_size = entry["original_bytes_confirmed"]
        if expected_size is not None:
            require_equal(size, expected_size, f"{path.name} byte count")
        paths[path.name] = path
        records.append(
            {
                "bytes": size,
                "dataverse_id": entry["dataverse_id"],
                "filename": path.name,
                "md5": md5,
                "sha256": file_digest(path, "sha256"),
            }
        )
    return paths, records


@dataclass(frozen=True)
class Question:
    ifp_id: str
    date_start: datetime
    date_suspend: datetime
    date_closed: datetime
    effective_cutoff: datetime
    source_date_start: str
    source_date_suspend: str
    source_date_closed: str
    split: str


@dataclass(frozen=True)
class Forecast:
    filename: str
    source_year: int
    line: int
    timestamp: datetime
    user_id: str
    forecast_id: Decimal
    forecast_id_text: str
    fcast_type: str
    value: Fraction

    @property
    def selection_key(self) -> tuple[datetime, Decimal, int, int]:
        return self.timestamp, self.forecast_id, self.source_year, self.line


@dataclass
class WindowAudit:
    total: Fraction = Fraction(0)
    count: int = 0
    minimum: datetime | None = None
    maximum: datetime | None = None
    hasher: Any = field(default_factory=hashlib.sha256)


def fresh_window_audits() -> dict[int, WindowAudit]:
    return {days: WindowAudit() for days in ABLATION_DAYS}


@dataclass
class Accumulator:
    first_week_sum: Fraction = Fraction(0)
    first_week_count: int = 0
    first_week_min: datetime | None = None
    first_week_max: datetime | None = None
    first_week_hasher: Any = field(default_factory=hashlib.sha256)
    eligible_count: int = 0
    eligible_min: datetime | None = None
    eligible_max: datetime | None = None
    latest_by_user: dict[str, Forecast] = field(default_factory=dict)
    latest_timestamp_rows_by_user: dict[str, list[Forecast]] = field(default_factory=dict)
    max_timestamp_ties: int = 0
    differing_value_ties: int = 0
    window_audits: dict[int, WindowAudit] = field(default_factory=fresh_window_audits)


def split_for_date(closed: datetime, protocol: dict[str, Any]) -> str:
    day = closed.date().isoformat()
    split = protocol["chronological_split"]
    if day <= split["train"]["date_closed_through"]:
        return "train"
    if split["calibration"]["date_closed_from"] <= day <= split["calibration"]["date_closed_through"]:
        return "calibration"
    if day >= split["monitor"]["date_closed_from"]:
        return "monitor"
    raise VerificationError(f"date_closed {day} belongs to no declared split")


def read_questions(
    protocol: dict[str, Any], path: Path
) -> tuple[dict[str, Question], dict[str, int], dict[str, Any]]:
    questions: dict[str, Question] = {}
    outcomes: dict[str, int] = {}
    selected: Counter[str] = Counter()
    total_rows = 0
    with path.open("r", encoding="latin-1", newline="") as handle:
        reader = csv.DictReader(handle)
        require_equal(reader.fieldnames, IFP_FIELDS, "ifps.csv header")
        for line, row in enumerate(reader, 2):
            total_rows += 1
            if not (
                row["q_status"] == "closed"
                and row["n_opts"] == "2"
                and row["outcome"] in {"a", "b"}
            ):
                continue
            ifp_id = row["ifp_id"]
            if not ifp_id or ifp_id in questions:
                raise VerificationError(f"missing or duplicate ifp_id at ifps.csv:{line}")
            start = parse_datetime(row["date_start"], f"ifps.csv:{line}:date_start")
            suspend = parse_datetime(row["date_suspend"], f"ifps.csv:{line}:date_suspend")
            source_closed = parse_datetime(row["date_closed"], f"ifps.csv:{line}:date_closed")
            closed = datetime.combine(source_closed.date(), time.min)
            split = split_for_date(closed, protocol)
            questions[ifp_id] = Question(
                ifp_id=ifp_id,
                date_start=start,
                date_suspend=suspend,
                date_closed=closed,
                effective_cutoff=min(suspend, closed),
                source_date_start=row["date_start"],
                source_date_suspend=row["date_suspend"],
                source_date_closed=row["date_closed"],
                split=split,
            )
            outcomes[ifp_id] = 1 if row["outcome"] == "a" else 0
            selected[split] += 1
    return questions, outcomes, {
        "ifps_rows": total_rows,
        "outcome_selected_questions": len(questions),
        "outcome_selected_by_split": dict(sorted(selected.items())),
    }


def forecast_payload(row: Forecast) -> dict[str, Any]:
    return {
        "fcast_type": row.fcast_type,
        "filename": row.filename,
        "forecast_id": row.forecast_id_text,
        "line": row.line,
        "source_year": row.source_year,
        "timestamp": iso_timestamp(row.timestamp),
        "user_id": row.user_id,
        "value": rational_text(row.value),
    }


def scan_forecasts(
    questions: dict[str, Question], paths: list[Path], allowed_types: set[int]
) -> tuple[dict[str, Accumulator], dict[str, Any]]:
    accumulators = {ifp_id: Accumulator() for ifp_id in questions}
    counts: Counter[str] = Counter()
    eligible_types: Counter[str] = Counter()
    for path in paths:
        with path.open("r", encoding="latin-1", newline="") as handle:
            reader = csv.DictReader(handle)
            require_equal(reader.fieldnames, FORECAST_FIELDS, f"{path.name} header")
            for line, row in enumerate(reader, 2):
                counts["raw_forecast_rows"] += 1
                question = questions.get(row["ifp_id"])
                if question is None:
                    continue
                counts["outcome_selected_question_rows"] += 1
                try:
                    event_type = int(row["fcast_type"])
                except ValueError as error:
                    raise VerificationError(
                        f"invalid fcast_type at {path.name}:{line}: {row['fcast_type']!r}"
                    ) from error
                if event_type not in allowed_types:
                    raise VerificationError(
                        f"unrecognized fcast_type at {path.name}:{line}: {event_type}"
                    )
                if row["answer_option"] != "a":
                    counts["non_a_answer_option_rows"] += 1
                    continue
                counts["option_a_rows"] += 1
                timestamp = parse_datetime(row["timestamp"], f"{path.name}:{line}:timestamp")
                if timestamp < question.date_start:
                    counts["excluded_before_date_start"] += 1
                    continue
                if timestamp >= question.effective_cutoff:
                    counts["excluded_at_or_after_effective_cutoff"] += 1
                    if timestamp >= question.date_suspend:
                        counts["excluded_at_or_after_date_suspend"] += 1
                    if timestamp >= question.date_closed:
                        counts["excluded_at_or_after_date_closed_midnight"] += 1
                    continue
                value = Fraction(parse_decimal(row["value"], f"{path.name}:{line}:value"))
                if not 0 <= value <= 1:
                    raise VerificationError(f"forecast outside [0,1] at {path.name}:{line}")
                user_id = row["user_id"]
                if not user_id or user_id == "NA":
                    raise VerificationError(f"missing user_id at {path.name}:{line}")
                forecast_id_text = row["forecast_id"]
                forecast_id = parse_decimal(
                    forecast_id_text, f"{path.name}:{line}:forecast_id"
                )
                try:
                    source_year = int(row["year"])
                except ValueError as error:
                    raise VerificationError(
                        f"invalid source year at {path.name}:{line}: {row['year']!r}"
                    ) from error
                forecast = Forecast(
                    filename=path.name,
                    source_year=source_year,
                    line=line,
                    timestamp=timestamp,
                    user_id=user_id,
                    forecast_id=forecast_id,
                    forecast_id_text=forecast_id_text,
                    fcast_type=row["fcast_type"],
                    value=value,
                )
                accumulator = accumulators[question.ifp_id]
                accumulator.eligible_count += 1
                if accumulator.eligible_min is None or timestamp < accumulator.eligible_min:
                    accumulator.eligible_min = timestamp
                if accumulator.eligible_max is None or timestamp > accumulator.eligible_max:
                    accumulator.eligible_max = timestamp
                counts["eligible_rows"] += 1
                eligible_types[str(event_type)] += 1
                for days, window_audit in accumulator.window_audits.items():
                    window_end = min(
                        question.date_start + timedelta(days=days),
                        question.effective_cutoff,
                    )
                    if timestamp < window_end:
                        window_audit.total += value
                        window_audit.count += 1
                        if window_audit.minimum is None or timestamp < window_audit.minimum:
                            window_audit.minimum = timestamp
                        if window_audit.maximum is None or timestamp > window_audit.maximum:
                            window_audit.maximum = timestamp
                        window_audit.hasher.update(
                            canonical_json_bytes(forecast_payload(forecast))
                        )
                if timestamp < question.date_start + timedelta(days=7):
                    accumulator.first_week_sum += value
                    accumulator.first_week_count += 1
                    if accumulator.first_week_min is None or timestamp < accumulator.first_week_min:
                        accumulator.first_week_min = timestamp
                    if accumulator.first_week_max is None or timestamp > accumulator.first_week_max:
                        accumulator.first_week_max = timestamp
                    accumulator.first_week_hasher.update(
                        canonical_json_bytes(forecast_payload(forecast))
                    )
                    counts["first_week_rows"] += 1
                group = accumulator.latest_timestamp_rows_by_user.get(user_id)
                if group is None or timestamp > group[0].timestamp:
                    group = [forecast]
                    accumulator.latest_timestamp_rows_by_user[user_id] = group
                elif timestamp == group[0].timestamp:
                    group.append(forecast)
                if timestamp >= group[0].timestamp:
                    accumulator.latest_by_user[user_id] = max(
                        group, key=lambda item: item.selection_key
                    )
    for accumulator in accumulators.values():
        accumulator.max_timestamp_ties = sum(
            len(group) - 1 for group in accumulator.latest_timestamp_rows_by_user.values()
        )
        accumulator.differing_value_ties = sum(
            1
            for group in accumulator.latest_timestamp_rows_by_user.values()
            if len({row.value for row in group}) > 1
        )
        counts["same_user_max_timestamp_tie_rows"] += accumulator.max_timestamp_ties
        counts["same_user_max_timestamp_differing_value_groups"] += (
            accumulator.differing_value_ties
        )
    return accumulators, {
        "counts": dict(sorted(counts.items())),
        "eligible_fcast_type_counts": dict(sorted(eligible_types.items())),
        "fcast_type_rule": "all source fcast_type values are included",
        "final_tie_rule": (
            "for each user choose the maximum tuple "
            "(timestamp, numeric forecast_id, source year, source line)"
        ),
    }


def median(values: list[Fraction]) -> Fraction:
    if not values:
        raise VerificationError("median of empty forecast values")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return (ordered[middle - 1] + ordered[middle]) / 2


def digest_rows(rows: list[dict[str, Any]]) -> str:
    return sha256_bytes(canonical_json_bytes(rows))


def build_crowd_predictions(
    questions: dict[str, Question],
    accumulators: dict[str, Accumulator],
    denominator: int,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    predictions: dict[str, dict[str, Any]] = {}
    missing: dict[str, list[str]] = {
        "first-week-mean": [],
        "final-consensus-median": [],
        "extremized-final-consensus": [],
    }
    for ifp_id in sorted(questions):
        accumulator = accumulators[ifp_id]
        if accumulator.first_week_count == 0:
            missing["first-week-mean"].append(ifp_id)
        if not accumulator.latest_by_user:
            missing["final-consensus-median"].append(ifp_id)
            missing["extremized-final-consensus"].append(ifp_id)
        if accumulator.first_week_count == 0 or not accumulator.latest_by_user:
            continue
        first_raw = accumulator.first_week_sum / accumulator.first_week_count
        first = round_ties_even(first_raw, denominator)
        latest = sorted(accumulator.latest_by_user.values(), key=lambda row: row.user_id)
        final_raw = median([row.value for row in latest])
        final = round_ties_even(final_raw, denominator)
        extreme_denominator = final * final + (1 - final) * (1 - final)
        extreme_raw = final * final / extreme_denominator
        extreme_clipped = min(max(extreme_raw, Fraction(1, 100)), Fraction(99, 100))
        extreme = round_ties_even(extreme_clipped, denominator)
        predictions[ifp_id] = {
            "first-week-mean": first,
            "final-consensus-median": final,
            "extremized-final-consensus": extreme,
            "provenance": {
                "effective_cutoff": iso_timestamp(questions[ifp_id].effective_cutoff),
                "first_week": {
                    "consumed_rows": accumulator.first_week_count,
                    "consumed_rows_sha256": accumulator.first_week_hasher.hexdigest(),
                    "digest_method": "SHA-256 over concatenated canonical JSON row records",
                    "min_consumed_timestamp": iso_timestamp(accumulator.first_week_min),
                    "max_consumed_timestamp": iso_timestamp(accumulator.first_week_max),
                    "raw_mean": rational_text(first_raw),
                },
                "final_consensus": {
                    "eligible_rows": accumulator.eligible_count,
                    "forecasters": len(latest),
                    "latest_rows_sha256": digest_rows(
                        [forecast_payload(row) for row in latest]
                    ),
                    "latest_rows_digest_method": "SHA-256 of canonical JSON array",
                    "max_consumed_timestamp": iso_timestamp(accumulator.eligible_max),
                    "min_consumed_timestamp": iso_timestamp(accumulator.eligible_min),
                    "selected_latest_max_timestamp": iso_timestamp(
                        max(row.timestamp for row in latest)
                    ),
                    "raw_median": rational_text(final_raw),
                    "same_user_max_timestamp_differing_value_ties": (
                        accumulator.differing_value_ties
                    ),
                    "same_user_max_timestamp_ties": accumulator.max_timestamp_ties,
                },
            },
        }
    return predictions, {
        "missing_by_model": missing,
        "missing_count_by_model": {key: len(value) for key, value in missing.items()},
    }


def assemble_stream(
    protocol: dict[str, Any],
    protocol_commit: str,
    implementation_commit: str,
    implementation_tree: str,
    protocol_sha256: str,
    questions: dict[str, Question],
    outcomes: dict[str, int],
    crowd: dict[str, dict[str, Any]],
    question_audit: dict[str, Any],
    forecast_audit: dict[str, Any],
    missingness: dict[str, Any],
) -> tuple[dict[str, Any], list[list[Fraction]]]:
    denominator = int(protocol["quantization"]["denominator"])
    included = sorted(crowd, key=lambda key: (questions[key].date_closed, key))
    split_counts = Counter(questions[key].split for key in included)
    expected = {
        name: int(protocol["chronological_split"][name]["expected_count"])
        for name in ("train", "calibration", "monitor")
    }
    require_equal(dict(split_counts), expected, "complete-case split counts")
    eligibility = protocol["eligibility_after_temporal_amendment"]
    require_equal(len(questions), eligibility["candidate_count"], "candidate count")
    require_equal(len(included), eligibility["included_count"], "complete-case count")
    require_equal(
        sorted(set(questions) - set(included)),
        eligibility["excluded_ifp_ids"],
        "complete-case exclusions",
    )
    train = [key for key in included if questions[key].split == "train"]
    if not train:
        raise VerificationError("complete-case train split is empty")
    base_raw = Fraction(sum(outcomes[key] for key in train), len(train))
    base = round_ties_even(base_raw, denominator)
    rows: list[dict[str, Any]] = []
    numeric_predictions: list[list[Fraction]] = []
    for index, ifp_id in enumerate(included):
        question = questions[ifp_id]
        crowd_row = crowd[ifp_id]
        values = [
            base,
            crowd_row["first-week-mean"],
            crowd_row["final-consensus-median"],
            crowd_row["extremized-final-consensus"],
        ]
        numeric_predictions.append(values)
        rows.append(
            {
                "date_closed": iso_timestamp(question.date_closed),
                "date_start": iso_timestamp(question.date_start),
                "date_suspend": iso_timestamp(question.date_suspend),
                "effective_cutoff": iso_timestamp(question.effective_cutoff),
                "ifp_id": ifp_id,
                "index": index,
                "outcome": outcomes[ifp_id],
                "predictions": {
                    model: rational_text(value)
                    for model, value in zip(MODEL_IDS, values, strict=True)
                },
                "provenance": crowd_row["provenance"],
                "source_date_closed": question.source_date_closed,
                "source_date_start": question.source_date_start,
                "source_date_suspend": question.source_date_suspend,
                "split": question.split,
            }
        )
    excluded = sorted(set(questions) - set(included))
    exclusion_rows = [
        {
            "ifp_id": key,
            "missing_models": sorted(
                model
                for model, identifiers in missingness["missing_by_model"].items()
                if key in identifiers
            ),
            "split": questions[key].split,
        }
        for key in excluded
    ]
    stream = {
        "artifact_status": ARTIFACT_STATUS,
        "audit": {
            "complete_case_exclusions": exclusion_rows,
            "forecast_scan": forecast_audit,
            "missingness": missingness,
            "questions": question_audit,
            "split_counts_after_complete_case_exclusion": dict(sorted(split_counts.items())),
        },
        "models": MODEL_IDS,
        "implementation_commit": implementation_commit,
        "implementation_tree": implementation_tree,
        "observations": rows,
        "prediction_construction": {
            "csv_contract": {
                "encoding": "latin-1",
                "ifps_dialect": "comma-separated CSV with CR record separators",
                "survey_dialect": "comma-separated CSV despite .tab filename",
            },
            "forecast_reducer_accepts_outcomes": False,
            "outcomes_joined_after_crowd_prediction_reduction": True,
            "train_base_rate_uses_train_outcomes": True,
            "train_base_rate_is_frozen_before_calibration_and_monitor": True,
        },
        "protocol_commit": protocol_commit,
        "protocol_sha256": protocol_sha256,
        "quantization": {"denominator": denominator, "tie_rule": "ties to even"},
        "schema_version": STREAM_SCHEMA,
        "train_base_rate": {
            "raw": rational_text(base_raw),
            "quantized": rational_text(base),
            "training_questions": len(train),
        },
    }
    return stream, numeric_predictions


def rationalize_posterior(
    prior: list[Fraction], calibration_sums: list[Fraction], denominator: int
) -> tuple[list[Fraction], dict[str, Any]]:
    if len(prior) != len(MODEL_IDS) or len(calibration_sums) != len(MODEL_IDS):
        raise VerificationError("posterior dimensions disagree")
    with localcontext() as context:
        context.prec = POSTERIOR_DECIMAL_PRECISION
        context.rounding = ROUND_HALF_EVEN
        scores: list[Decimal] = []
        for pi, loss in zip(prior, calibration_sums, strict=True):
            pi_decimal = Decimal(pi.numerator) / Decimal(pi.denominator)
            loss_decimal = Decimal(loss.numerator) / Decimal(loss.denominator)
            scores.append(pi_decimal * context.exp(-loss_decimal))
        total = sum(scores, Decimal(0))
        ideal = [score / total for score in scores]
        ideal_total = sum(ideal, Decimal(0))
        ideal = [weight / ideal_total for weight in ideal]
        scaled = [weight * denominator for weight in ideal]
        floors = [int(value.to_integral_value(rounding=ROUND_FLOOR)) for value in scaled]
        remainder = denominator - sum(floors)
        if not 0 <= remainder <= len(MODEL_IDS):
            raise VerificationError(f"posterior remainder {remainder} is invalid")
        order = sorted(
            range(len(MODEL_IDS)),
            key=lambda index: (-(scaled[index] - floors[index]), MODEL_IDS[index]),
        )
        units = floors[:]
        for index in order[:remainder]:
            units[index] += 1
        posterior = [Fraction(unit, denominator) for unit in units]
        if sum(posterior, Fraction(0)) != 1:
            raise VerificationError("rationalized posterior is not a PMF")
        return posterior, {
            "decimal_precision": POSTERIOR_DECIMAL_PRECISION,
            "decimal_rounding": "ROUND_HALF_EVEN",
            "ideal_weight_diagnostics": [format(weight, "f") for weight in ideal],
            "method": (
                "Decimal exp softmax followed by largest-remainder simplex quantization; "
                "ties use ascending model id"
            ),
            "simplex_grid_denominator": denominator,
            "simplex_units": units,
        }


def unit_log_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
    if not 1 <= value <= 2:
        raise AssertionError("logarithm range reduction failed")
    z = (value - 1) / (value + 1)
    partial = Fraction(0)
    for index in range(LOG_TERMS):
        partial += 2 * z ** (2 * index + 1) / (2 * index + 1)
    remainder = 2 * z ** (2 * LOG_TERMS + 1) / (
        (2 * LOG_TERMS + 1) * (1 - z * z)
    )
    return partial, partial + remainder


def log_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
    if value <= 0:
        raise VerificationError("log input must be positive")
    if value == 1:
        return Fraction(0), Fraction(0)
    if value < 1:
        low, high = log_bounds(1 / value)
        return -high, -low
    exponent = 0
    reduced = value
    while reduced >= 2:
        reduced /= 2
        exponent += 1
    two_low, two_high = unit_log_bounds(Fraction(2))
    reduced_low, reduced_high = unit_log_bounds(reduced)
    return exponent * two_low + reduced_low, exponent * two_high + reduced_high


def relative_entropy_bounds(
    posterior: list[Fraction], prior: list[Fraction]
) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho:
            term_low, term_high = log_bounds(rho / pi)
            low += rho * term_low
            high += rho * term_high
    return low, high


def psi_bounds(tilt: Fraction) -> tuple[Fraction, Fraction]:
    low, high = log_bounds(1 - tilt)
    return -high - tilt, -low - tilt


def round_down(value: Fraction, denominator: int) -> Fraction:
    scaled = value * denominator
    return Fraction(scaled.numerator // scaled.denominator, denominator)


def round_up(value: Fraction, denominator: int) -> Fraction:
    return -round_down(-value, denominator)


def interval_record(
    bounds: tuple[Fraction, Fraction], denominator: int
) -> dict[str, str]:
    return {
        "lower": rational_text(round_down(bounds[0], denominator)),
        "upper": rational_text(round_up(bounds[1], denominator)),
    }


def expected_model_prediction_vectors(
    observations: list[dict[str, Any]],
    crowd: dict[str, dict[str, Any]],
    train_base_rate: Fraction,
) -> dict[str, list[Fraction]]:
    """Independently rebuild vectors from the raw forecast reduction."""

    identifiers = [str(row["ifp_id"]) for row in observations]
    missing = [ifp_id for ifp_id in identifiers if ifp_id not in crowd]
    if missing:
        raise VerificationError(
            f"outcome-inaccessible forecast reduction is missing {missing[0]!r}"
        )
    return {
        "constant-train-baserate": [train_base_rate] * len(observations),
        "first-week-mean": [
            Fraction(crowd[ifp_id]["first-week-mean"]) for ifp_id in identifiers
        ],
        "final-consensus-median": [
            Fraction(crowd[ifp_id]["final-consensus-median"])
            for ifp_id in identifiers
        ],
        "extremized-final-consensus": [
            Fraction(crowd[ifp_id]["extremized-final-consensus"])
            for ifp_id in identifiers
        ],
    }


def loss_matrix(
    observations: list[dict[str, Any]],
    predictions: list[list[Fraction]],
    expected_predictions: dict[str, list[Fraction]],
) -> list[list[Fraction]]:
    if len(observations) != len(predictions):
        raise VerificationError("observation and prediction row counts disagree")
    if any(len(row) != len(MODEL_IDS) for row in predictions):
        raise VerificationError("prediction row does not match model catalog")
    matrix: list[list[Fraction]] = []
    for model_index, model_id in enumerate(MODEL_IDS):
        vector = ingest_prediction_vector(
            model_id,
            [row[model_index] for row in predictions],
            expected_predictions.get(model_id),
        )
        matrix.append(
            [
                score_safe_prediction(prediction, Fraction(observation["outcome"]))
                for observation, prediction in zip(observations, vector, strict=True)
            ]
        )
    return matrix


def ingest_prediction_vector(
    model_id: str,
    predictions: list[Fraction],
    expected_predictions: list[Fraction] | None,
) -> list[Fraction]:
    if model_id not in MODEL_IDS:
        raise VerificationError(f"undeclared model id at ingestion: {model_id!r}")
    values = [Fraction(value) for value in predictions]
    if expected_predictions is None:
        raise VerificationError(
            f"model {model_id!r} has no independently rebuilt prediction vector"
        )
    expected = [Fraction(value) for value in expected_predictions]
    if len(values) != len(expected):
        raise VerificationError(
            f"model {model_id!r} prediction length disagrees with its rebuild"
        )
    if any(not 0 <= value <= 1 for value in values):
        raise VerificationError(f"model {model_id!r} emitted a prediction outside [0,1]")
    if values != expected:
        raise VerificationError(
            f"model {model_id!r} predictions differ from the independently rebuilt "
            "outcome-inaccessible construction"
        )
    return values


def score_safe_prediction(
    prediction: Fraction, outcome: Fraction
) -> Fraction:
    if not 0 <= prediction <= 1 or outcome not in {0, 1}:
        raise VerificationError("Brier scorer received an invalid prediction or outcome")
    return (prediction - outcome) ** 2


def leaked_model_tripwire(
    observations: list[dict[str, Any]],
    expected_predictions: dict[str, list[Fraction]],
    reducer: Any = scan_forecasts,
    ingestor: Any = ingest_prediction_vector,
) -> dict[str, Any]:
    outcomes = [int(row["outcome"]) for row in observations]
    reducer_signature = inspect.signature(reducer)
    reducer_parameters = list(reducer_signature.parameters)
    if "outcomes" in reducer_parameters or any(
        parameter.kind is inspect.Parameter.VAR_KEYWORD
        for parameter in reducer_signature.parameters.values()
    ):
        raise VerificationError("forecast reducer exposes an outcome argument")
    try:
        reducer({}, [], set(), outcomes=outcomes)
    except TypeError:
        pass
    else:
        raise VerificationError("forecast reducer accepted an attempted outcome injection")

    oracle = [
        Fraction(99, 100) if outcome == 1 else Fraction(1, 100)
        for outcome in outcomes
    ]
    safe_reference = expected_predictions.get("first-week-mean")
    if safe_reference is None:
        raise VerificationError("tripwire lacks the rebuilt first-week reference vector")
    if oracle == [Fraction(value) for value in safe_reference]:
        raise VerificationError("tripwire is nondiscriminating on this observation sequence")

    try:
        ingestor("oracle-leak", oracle, safe_reference)
    except VerificationError:
        pass
    else:
        raise VerificationError("outcome-derived oracle passed the shared ingestion gate")

    try:
        ingestor("first-week-mean", oracle, safe_reference)
    except VerificationError:
        pass
    else:
        raise VerificationError(
            "relabeled outcome-derived oracle passed the shared ingestion gate"
        )

    return {
        "attempted_dependency": "outcomes",
        "attempted_model_id": "oracle-leak",
        "caller_source_labels_accepted_as_provenance": False,
        "declared_model_relabel_attempt": "first-week-mean",
        "definition": "p=99/100 if outcome=a else 1/100",
        "ingestion_callable": "shared exact-vector model ingestion gate",
        "oracle_prediction_count": len(oracle),
        "oracle_predictions_sha256": sha256_bytes(
            canonical_json_bytes([rational_text(value) for value in oracle])
        ),
        "outcome_keyword_injection_reason_code": "reducer_signature_excludes_outcomes",
        "outcome_keyword_injection_refused": True,
        "reducer_accepts_outcomes": False,
        "relabeled_vector_refusal_reason_code": (
            "candidate_differs_from_outcome_inaccessible_rebuild"
        ),
        "relabeled_vector_refused": True,
        "undeclared_model_refusal_reason_code": "undeclared_model_id",
        "undeclared_model_refused": True,
        "refused_before_scoring": True,
        "scored": False,
        "status": "PASS",
    }


def audit_timestamps(observations: list[dict[str, Any]]) -> dict[str, Any]:
    audited_reducers = 0
    for row in observations:
        start = datetime.fromisoformat(row["date_start"])
        cutoff = datetime.fromisoformat(row["effective_cutoff"])
        first = row["provenance"]["first_week"]
        final = row["provenance"]["final_consensus"]
        first_minimum = datetime.fromisoformat(first["min_consumed_timestamp"])
        first_maximum = datetime.fromisoformat(first["max_consumed_timestamp"])
        final_minimum = datetime.fromisoformat(final["min_consumed_timestamp"])
        final_maximum = datetime.fromisoformat(final["max_consumed_timestamp"])
        if not (
            start
            <= first_minimum
            <= first_maximum
            < min(start + timedelta(days=7), cutoff)
        ):
            raise VerificationError(f"first-week receipt timestamps fail for {row['ifp_id']}")
        if not start <= final_minimum <= final_maximum < cutoff:
            raise VerificationError(
                f"final-consensus receipt timestamps fail for {row['ifp_id']}"
            )
        audited_reducers += 2
    return {
        "audited_observations": len(observations),
        "audited_reducers": audited_reducers,
        "rule": "date_start <= every consumed timestamp < the reducer cutoff",
        "status": "PASS",
    }


def reconstruct_feature_ablation(
    protocol: dict[str, Any],
    questions: dict[str, Question],
    accumulators: dict[str, Accumulator],
    crowd: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    declared = next(
        row for row in protocol["leakage_tests"] if row["id"] == "future_feature_ablation"
    )["windows_days"]
    require_equal(declared, list(ABLATION_DAYS), "future-feature windows")
    denominator = int(protocol["quantization"]["denominator"])
    window_records: list[dict[str, Any]] = []
    seven_day_matches = True
    nested = True
    previous = {ifp_id: 0 for ifp_id in questions}
    for days in ABLATION_DAYS:
        defined: Counter[str] = Counter()
        missing: Counter[str] = Counter()
        missing_ids: list[str] = []
        detail: list[dict[str, Any]] = []
        total_rows = 0
        minimum: datetime | None = None
        maximum: datetime | None = None
        for ifp_id, question in questions.items():
            audit = accumulators[ifp_id].window_audits[days]
            if audit.count < previous[ifp_id]:
                nested = False
            previous[ifp_id] = audit.count
            if audit.count == 0:
                missing[question.split] += 1
                missing_ids.append(ifp_id)
                continue
            end = min(
                question.date_start + timedelta(days=days), question.effective_cutoff
            )
            if not question.date_start <= audit.minimum <= audit.maximum < end:
                raise VerificationError(
                    f"{days}-day ablation consumed a future row for {ifp_id}"
                )
            prediction = round_ties_even(audit.total / audit.count, denominator)
            defined[question.split] += 1
            total_rows += audit.count
            if minimum is None or audit.minimum < minimum:
                minimum = audit.minimum
            if maximum is None or audit.maximum > maximum:
                maximum = audit.maximum
            if days == 7 and ifp_id in crowd:
                primary = crowd[ifp_id]
                provenance = primary["provenance"]["first_week"]
                seven_day_matches = seven_day_matches and all(
                    (
                        prediction == primary["first-week-mean"],
                        audit.count == provenance["consumed_rows"],
                        audit.hasher.hexdigest() == provenance["consumed_rows_sha256"],
                        iso_timestamp(audit.minimum)
                        == provenance["min_consumed_timestamp"],
                        iso_timestamp(audit.maximum)
                        == provenance["max_consumed_timestamp"],
                    )
                )
            detail.append(
                {
                    "consumed_rows": audit.count,
                    "consumed_rows_sha256": audit.hasher.hexdigest(),
                    "effective_window_end": iso_timestamp(end),
                    "ifp_id": ifp_id,
                    "max_consumed_timestamp": iso_timestamp(audit.maximum),
                    "min_consumed_timestamp": iso_timestamp(audit.minimum),
                    "quantized_prediction": rational_text(prediction),
                    "raw_mean": rational_text(audit.total / audit.count),
                    "split": question.split,
                }
            )
        window_records.append(
            {
                "consumed_rows": total_rows,
                "defined_questions_by_split": dict(sorted(defined.items())),
                "max_consumed_timestamp": (
                    iso_timestamp(maximum) if maximum is not None else None
                ),
                "min_consumed_timestamp": (
                    iso_timestamp(minimum) if minimum is not None else None
                ),
                "missing_ifp_ids": sorted(missing_ids),
                "missing_questions_by_split": {
                    split: missing[split]
                    for split in ("train", "calibration", "monitor")
                },
                "observations": sorted(
                    detail, key=lambda row: (row["split"], row["ifp_id"])
                ),
                "prediction_rows_sha256": sha256_bytes(
                    canonical_json_bytes(sorted(detail, key=lambda row: row["ifp_id"]))
                ),
                "window_days": days,
            }
        )
    if not seven_day_matches:
        raise VerificationError("7-day ablation does not reproduce the primary model")
    if not nested:
        raise VerificationError("ablation counts are not nested")
    return {
        "cutoff_assertion_passed": True,
        "missingness_policy": (
            "leakage-only diagnostic; report each undefined question and do not "
            "change the primary complete-case set or compare Brier performance"
        ),
        "nested_consumed_row_counts": True,
        "primary_7_day_predictions_match": True,
        "status": "PASS",
        "windows_days": list(ABLATION_DAYS),
        "windows": window_records,
    }


def posthoc_shuffle_sensitivity(
    monitor_ids: list[str], monitor_losses: list[list[Fraction]], posterior: list[Fraction]
) -> dict[str, Any]:
    count = 200
    horizon = len(monitor_ids)
    if not horizon or any(len(row) != horizon for row in monitor_losses):
        raise VerificationError("shuffled-time input dimensions disagree")
    weighted: list[Fraction] = []
    for time_index in range(horizon):
        value = Fraction(0)
        for model_index in range(len(monitor_losses)):
            value += posterior[model_index] * monitor_losses[model_index][time_index]
        weighted.append(value)
    reference_loss_prefix, reference_quadratic_prefix = posterior_prefix_statistics(
        monitor_losses, posterior
    )
    reference = reference_loss_prefix[-1] / horizon
    if reference != sum(weighted, Fraction(0)) / horizon:
        raise VerificationError("shuffled-time reference risk reconstruction disagrees")
    reference_quadratic = reference_quadratic_prefix[-1]
    digest = hashlib.sha256()
    seen: set[tuple[int, ...]] = set()
    quadratic_values: list[Fraction] = []
    for replicate in range(count):
        prefix = SHUFFLE_NAMESPACE + replicate.to_bytes(4, "big") + b"\0"
        order = tuple(
            sorted(
                range(horizon),
                key=lambda index: (
                    hashlib.sha256(prefix + monitor_ids[index].encode("utf-8")).digest(),
                    index,
                ),
            )
        )
        if order in seen:
            raise VerificationError("duplicate post-hoc permutation")
        seen.add(order)
        for index in order:
            digest.update(index.to_bytes(4, "big"))
        permuted_losses = [
            [model_losses[index] for index in order]
            for model_losses in monitor_losses
        ]
        permuted_prefix, permuted_quadratic = posterior_prefix_statistics(
            permuted_losses, posterior
        )
        if permuted_prefix[-1] / horizon != reference:
            raise VerificationError("exact empirical risk changed under permutation")
        quadratic_values.append(permuted_quadratic[-1])
    ordered_quadratics = sorted(quadratic_values)
    quadratic_text = [rational_text(value) for value in ordered_quadratics]
    return {
        "algorithm": (
            "for replicate r, sort monitor indices by "
            "SHA-256('formalslt-gjp-shuffled-time-control-v1\\0' || "
            "uint32be(r) || '\\0' || ifp_id), breaking digest ties by index"
        ),
        "all_exact_empirical_risks_equal": True,
        "distinct_permutations": len(seen),
        "every_order_is_bijection": True,
        "order_matrix_sha256": digest.hexdigest(),
        "permutations": count,
        "quadratic_variation_changed_in_observed_sample": (
            len(set(quadratic_values + [reference_quadratic])) > 1
        ),
        "quadratic_variation_distribution": {
            "maximum": rational_text(ordered_quadratics[-1]),
            "median": rational_text(median(ordered_quadratics)),
            "minimum": rational_text(ordered_quadratics[0]),
            "sorted_exact_values": quadratic_text,
            "sorted_exact_values_sha256": sha256_bytes(
                canonical_json_bytes(quadratic_text)
            ),
        },
        "reference_posterior_empirical_brier": rational_text(reference),
        "reference_posterior_predictor_quadratic_variation": rational_text(
            reference_quadratic
        ),
        "status": "PASS",
        "statistical_status": "POSTHOC SENSITIVITY; NOT A PREREGISTERED REPLAY",
    }


def posterior_prefix_statistics(
    losses: list[list[Fraction]], posterior: list[Fraction]
) -> tuple[list[Fraction], list[Fraction]]:
    if not losses:
        raise VerificationError("loss matrix is empty")
    horizon = len(losses[0])
    if any(len(row) != horizon for row in losses):
        raise VerificationError("loss matrix rows have unequal lengths")
    loss_prefix = [Fraction(0) for _ in range(horizon + 1)]
    quadratic_prefix = [Fraction(0) for _ in range(horizon + 1)]
    for weight, model_losses in zip(posterior, losses, strict=True):
        running_loss = Fraction(0)
        running_quadratic = Fraction(0)
        for index, loss in enumerate(model_losses):
            predictor = Fraction(1, 2) if index == 0 else running_loss / index
            running_quadratic += (loss - predictor) ** 2
            running_loss += loss
            loss_prefix[index + 1] += weight * running_loss
            quadratic_prefix[index + 1] += weight * running_quadratic
    return loss_prefix, quadratic_prefix


def prefix_suffix_statistics(
    loss_prefix: list[Fraction],
    quadratic_prefix: list[Fraction],
    wake: int,
    horizon: int,
) -> tuple[Fraction, Fraction]:
    if not (0 <= wake < horizon < len(loss_prefix)):
        raise VerificationError(f"invalid suffix [{wake},{horizon})")
    suffix_length = horizon - wake
    empirical = (loss_prefix[horizon] - loss_prefix[wake]) / suffix_length
    quadratic = quadratic_prefix[horizon] - quadratic_prefix[wake]
    return empirical, quadratic


def boundary_candidates(
    loss_prefix: list[Fraction],
    quadratic_prefix: list[Fraction],
    entropy: tuple[Fraction, Fraction],
    effective_delta: Fraction,
    wake: int,
    horizon: int,
    output_denominator: int,
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ],
) -> list[tuple[Fraction, Fraction, Fraction, dict[str, Any]]]:
    suffix_length = horizon - wake
    if suffix_length < 4:
        raise VerificationError("a boundary suffix must contain at least four observations")
    empirical, quadratic = prefix_suffix_statistics(
        loss_prefix, quadratic_prefix, wake, horizon
    )
    candidates: list[tuple[Fraction, Fraction, Fraction, dict[str, Any]]] = []
    for atom in range(max_geometric_atom(suffix_length) + 1):
        tilt = Fraction(1, 2 ** (atom + 1))
        cache_key = effective_delta, atom
        if cache_key not in interval_cache:
            confidence_ratio = Fraction((atom + 1) * (atom + 2), 1) / effective_delta
            interval_cache[cache_key] = (
                log_bounds(confidence_ratio),
                psi_bounds(tilt),
            )
        confidence, psi = interval_cache[cache_key]
        denominator = suffix_length * tilt
        excess = (
            (entropy[0] + confidence[0] + psi[0] * quadratic) / denominator,
            (entropy[1] + confidence[1] + psi[1] * quadratic) / denominator,
        )
        boundary = empirical + excess[0], empirical + excess[1]
        row = {
            "boundary_interval": interval_record(boundary, output_denominator),
            "confidence_log_interval": interval_record(confidence, output_denominator),
            "effective_delta": rational_text(effective_delta),
            "excess_interval": interval_record(excess, output_denominator),
            "horizon": horizon,
            "kl_interval": interval_record(entropy, output_denominator),
            "posterior_empirical_brier_risk": rational_text(empirical),
            "psi_interval": interval_record(psi, output_denominator),
            "suffix_length": suffix_length,
            "suffix_predictor_quadratic_variation": rational_text(quadratic),
            "tilt": rational_text(tilt),
            "tilt_atom": atom,
            "wake": wake,
        }
        reported_lower = parse_fraction(
            row["boundary_interval"]["lower"], "boundary lower"
        )
        reported_upper = parse_fraction(
            row["boundary_interval"]["upper"], "boundary upper"
        )
        candidates.append((reported_upper, reported_lower, boundary[1], row))
    return candidates


def select_candidate(
    candidates: list[tuple[Fraction, Fraction, Fraction, dict[str, Any]]]
) -> dict[str, Any]:
    if not candidates:
        raise VerificationError("cannot select from an empty boundary catalog")
    selected = min(
        candidates,
        key=lambda item: (item[0], item[3]["wake"], item[3]["tilt_atom"]),
    )
    competitor_lowers = [item[1] for item in candidates if item is not selected]
    margin = min(competitor_lowers) - selected[0] if competitor_lowers else Fraction(0)
    return {
        **selected[3],
        "reported_selection_margin_lower": rational_text(margin),
        "selection_rule": "minimum reported upper, then wake, then tilt atom",
        "selection_unique_from_reported_intervals": margin > 0,
    }


def first_crossing(
    selected_rows: list[dict[str, Any]], threshold: Fraction
) -> int | None:
    for row in selected_rows:
        upper = parse_fraction(row["boundary_interval"]["upper"], "boundary upper")
        if upper < threshold:
            return int(row["horizon"])
    return None


class IndependentSplitMix64:
    """Unsigned SplitMix64 implementation pinned by protocol v1.2."""

    MASK = (1 << 64) - 1

    def __init__(self, seed: int):
        if not 0 <= seed <= self.MASK:
            raise VerificationError("SplitMix64 seed is outside the unsigned 64-bit range")
        self.state = seed
        self.words = 0

    def next_word(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & self.MASK
        mixed = self.state
        mixed = ((mixed ^ (mixed >> 30)) * 0xBF58476D1CE4E5B9) & self.MASK
        mixed = ((mixed ^ (mixed >> 27)) * 0x94D049BB133111EB) & self.MASK
        mixed ^= mixed >> 31
        self.words += 1
        return mixed & self.MASK


def exact_bernoulli(
    generator: IndependentSplitMix64, probability: Fraction
) -> tuple[int, int]:
    probability = Fraction(probability)
    if not 0 <= probability <= 1:
        raise VerificationError("Bernoulli probability is outside [0,1]")
    acceptance_limit = ((1 << 64) // probability.denominator) * probability.denominator
    rejected = 0
    while True:
        word = generator.next_word()
        if word < acceptance_limit:
            outcome = word % probability.denominator < probability.numerator
            return int(outcome), rejected
        rejected += 1


def reported_endpoint(
    loss_prefix: list[Fraction],
    quadratic_prefix: list[Fraction],
    entropy: tuple[Fraction, Fraction],
    wake_confidences: list[tuple[int, Fraction]],
    horizon: int,
    output_denominator: int,
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ],
) -> tuple[Fraction, Fraction, int, int]:
    best: tuple[Fraction, Fraction, int, int] | None = None
    for wake, effective_delta in wake_confidences:
        empirical, quadratic = prefix_suffix_statistics(
            loss_prefix, quadratic_prefix, wake, horizon
        )
        suffix_length = horizon - wake
        for atom in range(max_geometric_atom(suffix_length) + 1):
            tilt = Fraction(1, 2 ** (atom + 1))
            cache_key = effective_delta, atom
            if cache_key not in interval_cache:
                ratio = Fraction((atom + 1) * (atom + 2), 1) / effective_delta
                interval_cache[cache_key] = log_bounds(ratio), psi_bounds(tilt)
            confidence, psi = interval_cache[cache_key]
            excess_upper = (
                entropy[1] + confidence[1] + psi[1] * quadratic
            ) / (suffix_length * tilt)
            endpoint = empirical + excess_upper
            candidate = endpoint, excess_upper, wake, atom
            if best is None or (endpoint, wake, atom) < (best[0], best[2], best[3]):
                best = candidate
    if best is None:
        raise VerificationError("no admissible endpoint")
    return (
        round_up(best[0], output_denominator),
        round_up(best[1], output_denominator),
        best[2],
        best[3],
    )


def replay_null_diagnostic(
    protocol: dict[str, Any],
    monitor_predictions: list[list[Fraction]],
    posterior: list[Fraction],
    prior: list[Fraction],
    base_rate: Fraction,
    threshold: Fraction,
    observed_width_ratio: Fraction,
) -> dict[str, Any]:
    baseline = protocol["baselines"]
    replicates = int(baseline["null_replicates"])
    horizon = len(monitor_predictions)
    delta = parse_fraction(protocol["confidence_contract"]["delta"], "delta")
    wakes = list(protocol["confidence_contract"]["wake_grid"])
    output_denominator = int(protocol["quantization"]["output_grid_denominator"])
    entropy = relative_entropy_bounds(posterior, prior)
    generator = IndependentSplitMix64(
        int(baseline["null_generator"]["seed_u64_hex"], 16)
    )
    outcome_digest = hashlib.sha256()
    rejected_words = 0
    declaration_counts = {"B1": 0, "B2": 0, "B3": 0}
    crossing_histograms: dict[str, Counter[int]] = {
        "B2": Counter(),
        "B3": Counter(),
    }
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ] = {}
    for _replicate in range(replicates):
        outcomes: list[int] = []
        for _index in range(horizon):
            outcome, rejected = exact_bernoulli(generator, base_rate)
            outcomes.append(outcome)
            rejected_words += rejected
        outcome_digest.update(bytes(outcomes))

        null_losses = [[] for _ in MODEL_IDS]
        for outcome, row_predictions in zip(
            outcomes, monitor_predictions, strict=True
        ):
            for model_index, prediction in enumerate(row_predictions):
                null_losses[model_index].append((prediction - outcome) ** 2)
        loss_prefix, quadratic_prefix = posterior_prefix_statistics(
            null_losses, posterior
        )

        b2_crossing: int | None = None
        b3_crossing: int | None = None
        b1_final: Fraction | None = None
        for report_time in range(4, horizon + 1):
            if b2_crossing is None or report_time == horizon:
                fixed = reported_endpoint(
                    loss_prefix,
                    quadratic_prefix,
                    entropy,
                    [(0, delta)],
                    report_time,
                    output_denominator,
                    interval_cache,
                )
                if report_time == horizon:
                    b1_final = fixed[0]
                if b2_crossing is None and fixed[0] < threshold:
                    b2_crossing = report_time
            if b3_crossing is None:
                admitted = [
                    (wake, delta / ((wake + 1) * (wake + 2)))
                    for wake in wakes
                    if wake <= report_time - 4
                ]
                anytime = reported_endpoint(
                    loss_prefix,
                    quadratic_prefix,
                    entropy,
                    admitted,
                    report_time,
                    output_denominator,
                    interval_cache,
                )
                if anytime[0] < threshold:
                    b3_crossing = report_time
        if b1_final is None:
            raise VerificationError("final B1 endpoint was not evaluated")
        if b1_final < threshold:
            declaration_counts["B1"] += 1
        if b2_crossing is not None:
            declaration_counts["B2"] += 1
            crossing_histograms["B2"][b2_crossing] += 1
        if b3_crossing is not None:
            declaration_counts["B3"] += 1
            crossing_histograms["B3"][b3_crossing] += 1

    nominal_product = replicates * delta
    nominal_ceiling = nominal_product.numerator // nominal_product.denominator
    checks = {
        "B1_count_at_most_nominal_ceiling": (
            declaration_counts["B1"] <= nominal_ceiling
        ),
        "B2_count_at_least_25": declaration_counts["B2"] >= 25,
        "B3_count_at_most_nominal_ceiling": (
            declaration_counts["B3"] <= nominal_ceiling
        ),
        "B3_final_width_at_most_twice_B1": observed_width_ratio <= 2,
    }
    procedures: dict[str, dict[str, Any]] = {}
    for name, count in declaration_counts.items():
        procedure: dict[str, Any] = {
            "declaration_count": count,
            "declaration_fraction": rational_text(Fraction(count, replicates)),
        }
        if name in crossing_histograms:
            procedure["first_crossing_histogram"] = {
                str(time): frequency
                for time, frequency in sorted(crossing_histograms[name].items())
            }
        procedures[name] = procedure
    return {
        "declaration_threshold": rational_text(threshold),
        "generator": {
            "algorithm": "SplitMix64",
            "outcome_matrix_digest_method": (
                "SHA-256 over replicate-major raw 0/1 bytes, fixed row length equal to horizon"
            ),
            "outcome_matrix_sha256": outcome_digest.hexdigest(),
            "rejected_words": rejected_words,
            "seed_u64_hex": baseline["null_generator"]["seed_u64_hex"],
            "words_consumed": generator.words,
        },
        "horizon": horizon,
        "nominal_count_ceiling": nominal_ceiling,
        "procedures": procedures,
        "replicates": replicates,
        "win_condition_checks": checks,
        "win_condition_passed": all(checks.values()),
    }


def overall_preregistered_verdict(
    null_replay: dict[str, Any], leakage_tests: dict[str, Any]
) -> dict[str, Any]:
    checks = null_replay["win_condition_checks"]
    failed = sorted(name for name, passed in checks.items() if not passed)
    incomplete = sorted(
        name
        for name, result in leakage_tests.items()
        if str(result["status"]).startswith("UNDERSPECIFIED")
    )
    win_passed = bool(null_replay["win_condition_passed"])
    overall_passed = win_passed and not incomplete
    status = "PASS" if overall_passed else ("INCOMPLETE" if win_passed else "FAIL")
    return {
        "control_completion": "INCOMPLETE" if incomplete else "COMPLETE",
        "failed_win_condition_checks": failed,
        "incomplete_controls": incomplete,
        "null_win_condition_passed": win_passed,
        "overall_preregistered_passed": overall_passed,
        "status": status,
    }


def build_receipt(
    protocol: dict[str, Any],
    stream: dict[str, Any],
    predictions: list[list[Fraction]],
    questions: dict[str, Question],
    accumulators: dict[str, Accumulator],
    crowd: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    observations = stream["observations"]
    base_rate = parse_fraction(stream["train_base_rate"]["quantized"], "train base rate")
    expected_predictions = expected_model_prediction_vectors(
        observations, crowd, base_rate
    )
    losses = loss_matrix(observations, predictions, expected_predictions)
    indices = {
        name: [index for index, row in enumerate(observations) if row["split"] == name]
        for name in ("train", "calibration", "monitor")
    }
    calibration = indices["calibration"]
    monitor = indices["monitor"]
    if not calibration or not monitor:
        raise VerificationError("calibration and monitor splits must be nonempty")
    calibration_sums = [
        sum((values[index] for index in calibration), Fraction(0)) for values in losses
    ]
    calibration_means = [value / len(calibration) for value in calibration_sums]
    prior = [
        parse_fraction(value, f"prior[{index}]")
        for index, value in enumerate(protocol["model_catalog"]["prior"])
    ]
    output_denominator = int(protocol["quantization"]["output_grid_denominator"])
    posterior, posterior_audit = rationalize_posterior(
        prior, calibration_sums, output_denominator
    )
    monitor_predictions = [predictions[index] for index in monitor]
    monitor_losses = [[values[index] for index in monitor] for values in losses]
    delta = parse_fraction(protocol["confidence_contract"]["delta"], "delta")
    wakes = list(protocol["confidence_contract"]["wake_grid"])
    entropy = relative_entropy_bounds(posterior, prior)
    horizon = len(monitor)
    loss_prefix, quadratic_prefix = posterior_prefix_statistics(
        monitor_losses, posterior
    )
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ] = {}

    b1_candidates = boundary_candidates(
        loss_prefix,
        quadratic_prefix,
        entropy,
        delta,
        0,
        horizon,
        output_denominator,
        interval_cache,
    )
    b1_selected = select_candidate(b1_candidates)
    b2_atom_rows: list[dict[str, Any]] = []
    b2_selected_by_time: list[dict[str, Any]] = []
    b3_atom_rows: list[dict[str, Any]] = []
    b3_selected_by_time: list[dict[str, Any]] = []
    for report_time in range(4, horizon + 1):
        fixed_candidates = boundary_candidates(
            loss_prefix,
            quadratic_prefix,
            entropy,
            delta,
            0,
            report_time,
            output_denominator,
            interval_cache,
        )
        b2_atom_rows.extend(candidate[3] for candidate in fixed_candidates)
        b2_selected_by_time.append(select_candidate(fixed_candidates))

        anytime_candidates: list[
            tuple[Fraction, Fraction, Fraction, dict[str, Any]]
        ] = []
        for wake in wakes:
            if wake > report_time - 4:
                continue
            effective_delta = delta / ((wake + 1) * (wake + 2))
            anytime_candidates.extend(
                boundary_candidates(
                    loss_prefix,
                    quadratic_prefix,
                    entropy,
                    effective_delta,
                    wake,
                    report_time,
                    output_denominator,
                    interval_cache,
                )
            )
        b3_atom_rows.extend(candidate[3] for candidate in anytime_candidates)
        b3_selected_by_time.append(select_candidate(anytime_candidates))

    declaration_threshold = base_rate * (1 - base_rate)
    b2_crossing = first_crossing(b2_selected_by_time, declaration_threshold)
    b3_crossing = first_crossing(b3_selected_by_time, declaration_threshold)
    b3_selected = b3_selected_by_time[-1]
    b1_upper = parse_fraction(
        b1_selected["boundary_interval"]["upper"], "B1 upper"
    )
    b3_upper = parse_fraction(
        b3_selected["boundary_interval"]["upper"], "B3 upper"
    )
    b1_width = parse_fraction(
        b1_selected["excess_interval"]["upper"], "B1 width"
    )
    b3_width = parse_fraction(
        b3_selected["excess_interval"]["upper"], "B3 width"
    )
    width_ratio = b3_width / b1_width
    null_replay = replay_null_diagnostic(
        protocol,
        monitor_predictions,
        posterior,
        prior,
        base_rate,
        declaration_threshold,
        width_ratio,
    )
    timestamp_control = audit_timestamps(observations)
    tripwire = leaked_model_tripwire(observations, expected_predictions)
    ablation = reconstruct_feature_ablation(
        protocol, questions, accumulators, crowd
    )
    monitor_ids = [observations[index]["ifp_id"] for index in monitor]
    shuffled_sensitivity = posthoc_shuffle_sensitivity(
        monitor_ids, monitor_losses, posterior
    )
    b3_null_passed = null_replay["win_condition_checks"][
        "B3_count_at_most_nominal_ceiling"
    ]
    leakage_tests = {
        "deliberately_leaked_tripwire": tripwire,
        "future_feature_ablation": ablation,
        "parametric_null_replay": {
            "declaration_count": null_replay["procedures"]["B3"][
                "declaration_count"
            ],
            "nominal_count_ceiling": null_replay["nominal_count_ceiling"],
            "status": "PASS" if b3_null_passed else "FAIL",
        },
        "shuffled_time_control": {
            "reason": (
                "protocol v1.2 pins 200 permutations but no permutation generator, "
                "seed, draw order, or explicit permutation list"
            ),
            "status": "UNDERSPECIFIED_NOT_UNIQUELY_REPLAYABLE",
        },
        "timestamp_assertion": timestamp_control,
    }
    overall_verdict = overall_preregistered_verdict(null_replay, leakage_tests)
    constant_mean = sum(monitor_losses[0], Fraction(0)) / horizon
    monitor_means = [sum(values, Fraction(0)) / horizon for values in monitor_losses]
    return {
        "artifact_status": ARTIFACT_STATUS,
        "anytime_boundary_rows": b3_atom_rows,
        "baselines": {
            "B1_fixed_time": {
                "atom_rows": [candidate[3] for candidate in b1_candidates],
                "declares_below_train_base_rate_brier": (
                    b1_upper < declaration_threshold
                ),
                "selected": b1_selected,
            },
            "B2_naive_repeated_look": {
                "atom_rows": b2_atom_rows,
                "first_crossing": b2_crossing,
                "selected_by_time": b2_selected_by_time,
                "statistical_status": (
                    "invalid under repeated inspection; diagnostic only"
                ),
            },
            "B3_anytime_valid": {
                "first_crossing": b3_crossing,
                "selected_by_time": b3_selected_by_time,
            },
            "declaration_threshold": rational_text(declaration_threshold),
            "final_excess_width_ratio_B3_over_B1": rational_text(width_ratio),
            "null_replay": null_replay,
        },
        "calibration": {
            "model_empirical_brier": {
                model: rational_text(value)
                for model, value in zip(MODEL_IDS, calibration_means, strict=True)
            },
            "model_loss_sums": {
                model: rational_text(value)
                for model, value in zip(MODEL_IDS, calibration_sums, strict=True)
            },
            "observations": len(calibration),
            "posterior": {
                "audit": posterior_audit,
                "exact_rational_weights": {
                    model: rational_text(weight)
                    for model, weight in zip(MODEL_IDS, posterior, strict=True)
                },
                "theorem_object": "exact_rational_weights",
            },
        },
        "confidence_delta": rational_text(delta),
        "implementation_commit": stream["implementation_commit"],
        "implementation_tree": stream["implementation_tree"],
        "leakage_tests": leakage_tests,
        "log_enclosure": {
            "method": "range-reduced atanh series with exact rational remainder bound",
            "output_denominator": output_denominator,
            "terms": LOG_TERMS,
        },
        "models": MODEL_IDS,
        "monitor": {
            "model_empirical_brier": {
                model: rational_text(value)
                for model, value in zip(MODEL_IDS, monitor_means, strict=True)
            },
            "observations": horizon,
        },
        "nonclaims": [
            "the arithmetic receipt is not yet a Lean instantiation of the coverage theorem",
            "the endpoint concerns posterior-averaged encountered suffix risk, not future or population risk",
            "the ideal Decimal posterior weights are diagnostics; the exact rationalized posterior is certified",
            "the deterministic null replay is an implementation diagnostic, not a proof of statistical validity",
            "B2 repeatedly reuses a fixed-time bound and is statistically invalid",
        ],
        "overall_preregistered_verdict": overall_verdict,
        "prior": {
            model: rational_text(weight) for model, weight in zip(MODEL_IDS, prior, strict=True)
        },
        "receipt_schema": RECEIPT_SCHEMA,
        "protocol_commit": stream["protocol_commit"],
        "protocol_sha256": stream["protocol_sha256"],
        "posthoc_shuffled_time_sensitivity": shuffled_sensitivity,
        "selected_witness": {
            **b3_selected,
            "constant_model_monitor_empirical_brier": rational_text(constant_mean),
            "informative_against_train_base_rate_brier": (
                b3_upper < declaration_threshold
            ),
            "nonvacuous_against_brier_loss_ceiling": b3_upper < 1,
            "train_base_rate_brier_threshold": rational_text(declaration_threshold),
        },
        "stream_sha256": sha256_bytes(canonical_json_bytes(stream)),
    }


def resolve_protocol_commit(protocol_path: Path, protocol_raw: bytes) -> str:
    try:
        relative = protocol_path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as error:
        raise VerificationError("protocol must be a tracked repository file") from error
    try:
        process = subprocess.run(
            ["git", "log", "-1", "--format=%H", "--", relative],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError("cannot resolve committed protocol revision") from error
    commit = process.stdout.strip()
    if len(commit) != 40 or any(char not in "0123456789abcdef" for char in commit):
        raise VerificationError("protocol has no lowercase 40-hex committed revision")
    try:
        frozen = subprocess.run(
            ["git", "show", f"{commit}:{relative}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError("cannot read committed protocol bytes") from error
    if frozen != protocol_raw:
        raise VerificationError("working protocol differs from latest committed revision")
    return commit


def resolve_implementation_commit(paths: list[Path], protocol_commit: str) -> str:
    try:
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD^{commit}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        dirty = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError("cannot inspect the implementation checkout") from error
    if len(commit) != 40 or any(character not in "0123456789abcdef" for character in commit):
        raise VerificationError("implementation commit is not lowercase 40-hex")
    if dirty:
        raise VerificationError("implementation checkout must be clean")
    try:
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", protocol_commit, commit],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError(
            "implementation commit does not descend from the protocol freeze"
        ) from error
    for path in paths:
        try:
            relative = path.resolve().relative_to(ROOT.resolve()).as_posix()
        except ValueError as error:
            raise VerificationError(f"implementation file escapes repository: {path}") from error
        if not path.is_file():
            raise VerificationError(f"implementation file is absent: {path}")
        try:
            frozen = subprocess.run(
                ["git", "show", f"{commit}:{relative}"],
                cwd=ROOT,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            ).stdout
        except (OSError, subprocess.CalledProcessError) as error:
            raise VerificationError(
                f"implementation file is absent from {commit}: {relative}"
            ) from error
        if frozen != path.read_bytes():
            raise VerificationError(
                f"working implementation bytes differ from {commit}: {relative}"
            )
    return commit


def resolve_commit_tree(commit: str) -> str:
    try:
        tree = subprocess.run(
            ["git", "show", "-s", "--format=%T", commit],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise VerificationError(f"cannot resolve implementation tree for {commit}") from error
    if len(tree) != 40 or any(character not in "0123456789abcdef" for character in tree):
        raise VerificationError("implementation tree is not lowercase 40-hex")
    return tree


def manifest_file(role: str, name: str, raw: bytes) -> dict[str, Any]:
    return {"bytes": len(raw), "name": name, "role": role, "sha256": sha256_bytes(raw)}


def reconstruct_artifacts(
    protocol_path: Path, input_dir: Path
) -> tuple[bytes, bytes, bytes]:
    protocol, protocol_raw = load_canonical_json(protocol_path, "protocol")
    validate_protocol(protocol)
    protocol_commit = resolve_protocol_commit(protocol_path, protocol_raw)
    verifier_path = Path(__file__).resolve()
    implementation_paths = [
        protocol_path,
        DEFAULT_PROTOCOL_MD,
        PROTOCOL_CHECKER,
        INPUT_FETCHER,
        BUILDER,
        verifier_path,
        PROTOCOL_TEST,
        REPLAY_TEST,
    ]
    implementation_commit = resolve_implementation_commit(
        implementation_paths, protocol_commit
    )
    implementation_tree = resolve_commit_tree(implementation_commit)
    raw_paths, raw_records = verify_raw_inputs(protocol, input_dir)
    questions, outcomes, question_audit = read_questions(protocol, raw_paths["ifps.csv"])
    forecast_paths = [
        raw_paths[entry["filename"]]
        for entry in protocol["dataset"]["files"]
        if entry["role"] == "individual_forecasts"
    ]
    allowed_types = set(
        protocol["prediction_before_outcome"]["survey_forecast_event_types"]["allowed"]
    )
    accumulators, forecast_audit = scan_forecasts(
        questions, forecast_paths, allowed_types
    )
    crowd, missingness = build_crowd_predictions(
        questions, accumulators, int(protocol["quantization"]["denominator"])
    )
    stream, predictions = assemble_stream(
        protocol,
        protocol_commit,
        implementation_commit,
        implementation_tree,
        sha256_bytes(protocol_raw),
        questions,
        outcomes,
        crowd,
        question_audit,
        forecast_audit,
        missingness,
    )
    stream_raw = canonical_json_bytes(stream)
    receipt_raw = canonical_json_bytes(
        build_receipt(
            protocol,
            stream,
            predictions,
            questions,
            accumulators,
            crowd,
        )
    )
    if not BUILDER.is_file():
        raise VerificationError(f"replay builder is absent: {BUILDER}")
    manifest = {
        "artifact_status": ARTIFACT_STATUS,
        "dataset": {
            "license": protocol["dataset"]["license"],
            "persistent_id": protocol["dataset"]["persistent_id"],
            "raw_files": raw_records,
            "version": protocol["dataset"]["version"],
        },
        "files": [
            manifest_file("protocol", protocol_path.name, protocol_raw),
            manifest_file("builder", BUILDER.name, BUILDER.read_bytes()),
            manifest_file("independent_verifier", verifier_path.name, verifier_path.read_bytes()),
            manifest_file("implementation_test", REPLAY_TEST.name, REPLAY_TEST.read_bytes()),
            manifest_file(
                "protocol_companion", DEFAULT_PROTOCOL_MD.name, DEFAULT_PROTOCOL_MD.read_bytes()
            ),
            manifest_file(
                "protocol_checker", PROTOCOL_CHECKER.name, PROTOCOL_CHECKER.read_bytes()
            ),
            manifest_file("input_fetcher", INPUT_FETCHER.name, INPUT_FETCHER.read_bytes()),
            manifest_file("protocol_test", PROTOCOL_TEST.name, PROTOCOL_TEST.read_bytes()),
            manifest_file("stream", STREAM_NAME, stream_raw),
            manifest_file("receipt", RECEIPT_NAME, receipt_raw),
        ],
        "manifest_schema": MANIFEST_SCHEMA,
        "implementation_commit": implementation_commit,
        "implementation_tree": implementation_tree,
        "protocol_commit": protocol_commit,
        "replay_commands": {
            "build": (
                "python3 scripts/build_gjp_brier_replay.py --inputs "
                "/tmp/formalslt-gjp-v1 --out /tmp/formalslt-gjp-replay-v1"
            ),
            "checkout": f"git checkout --detach {implementation_commit}",
            "fetch": (
                "python3 scripts/fetch_gjp_brier_inputs.py --out "
                "/tmp/formalslt-gjp-v1"
            ),
            "focused_tests": (
                "python3 -m pytest -q tests/test_gjp_brier_protocol.py "
                "tests/test_gjp_brier_replay.py"
            ),
            "verify": (
                "python3 scripts/verify_gjp_brier_replay.py --inputs "
                "/tmp/formalslt-gjp-v1 --artifacts /tmp/formalslt-gjp-replay-v1"
            ),
        },
    }
    return stream_raw, receipt_raw, canonical_json_bytes(manifest)


def preflight_artifacts(
    artifact_dir: Path, protocol_path: Path
) -> dict[str, bytes]:
    if not artifact_dir.is_dir():
        raise VerificationError(f"artifact directory is absent: {artifact_dir}")
    paths = {
        STREAM_NAME: artifact_dir / STREAM_NAME,
        RECEIPT_NAME: artifact_dir / RECEIPT_NAME,
        MANIFEST_NAME: artifact_dir / MANIFEST_NAME,
    }
    parsed: dict[str, dict[str, Any]] = {}
    raw: dict[str, bytes] = {}
    for name, path in paths.items():
        if not path.is_file():
            raise VerificationError(f"expected artifact is absent: {path}")
        parsed[name], raw[name] = load_canonical_json(path, name)
    stream = parsed[STREAM_NAME]
    receipt = parsed[RECEIPT_NAME]
    manifest = parsed[MANIFEST_NAME]
    require_equal(stream.get("schema_version"), STREAM_SCHEMA, "stream schema")
    require_equal(receipt.get("receipt_schema"), RECEIPT_SCHEMA, "receipt schema")
    require_equal(manifest.get("manifest_schema"), MANIFEST_SCHEMA, "manifest schema")
    for label, value in (("stream", stream), ("receipt", receipt), ("manifest", manifest)):
        require_equal(value.get("artifact_status"), ARTIFACT_STATUS, f"{label} status")
    require_equal(receipt.get("stream_sha256"), sha256_bytes(raw[STREAM_NAME]), "receipt stream hash")
    require_equal(receipt.get("protocol_sha256"), stream.get("protocol_sha256"), "protocol hash link")
    require_equal(receipt.get("protocol_commit"), stream.get("protocol_commit"), "protocol commit link")
    require_equal(
        receipt.get("implementation_commit"),
        stream.get("implementation_commit"),
        "implementation commit link",
    )
    require_equal(
        receipt.get("implementation_tree"),
        stream.get("implementation_tree"),
        "implementation tree link",
    )
    require_equal(
        manifest.get("implementation_commit"),
        stream.get("implementation_commit"),
        "manifest implementation commit link",
    )
    require_equal(
        manifest.get("implementation_tree"),
        stream.get("implementation_tree"),
        "manifest implementation tree link",
    )
    roles = {row["role"]: row for row in manifest["files"]}
    require_equal(
        set(roles),
        {
            "protocol",
            "builder",
            "independent_verifier",
            "implementation_test",
            "protocol_companion",
            "protocol_checker",
            "input_fetcher",
            "protocol_test",
            "stream",
            "receipt",
        },
        "manifest file roles",
    )
    require_equal(roles["stream"]["sha256"], sha256_bytes(raw[STREAM_NAME]), "manifest stream hash")
    require_equal(roles["receipt"]["sha256"], sha256_bytes(raw[RECEIPT_NAME]), "manifest receipt hash")
    require_equal(roles["protocol"]["sha256"], sha256_bytes(protocol_path.read_bytes()), "manifest protocol hash")
    require_equal(roles["builder"]["sha256"], file_digest(BUILDER, "sha256"), "manifest builder hash")
    require_equal(
        roles["independent_verifier"]["sha256"],
        file_digest(Path(__file__).resolve(), "sha256"),
        "manifest verifier hash",
    )
    for role, path in (
        ("implementation_test", REPLAY_TEST),
        ("protocol_companion", DEFAULT_PROTOCOL_MD),
        ("protocol_checker", PROTOCOL_CHECKER),
        ("input_fetcher", INPUT_FETCHER),
        ("protocol_test", PROTOCOL_TEST),
    ):
        require_equal(
            roles[role]["sha256"], file_digest(path, "sha256"), f"manifest {role} hash"
        )
    return raw


def verify_replay(protocol_path: Path, input_dir: Path, artifact_dir: Path) -> None:
    actual = preflight_artifacts(artifact_dir, protocol_path)
    stream_raw, receipt_raw, manifest_raw = reconstruct_artifacts(protocol_path, input_dir)
    expected = {
        STREAM_NAME: stream_raw,
        RECEIPT_NAME: receipt_raw,
        MANIFEST_NAME: manifest_raw,
    }
    for name in (STREAM_NAME, RECEIPT_NAME, MANIFEST_NAME):
        if actual[name] != expected[name]:
            raise VerificationError(f"artifact is stale, mutated, or non-replayable: {artifact_dir / name}")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        verify_replay(
            args.protocol.resolve(), args.inputs.resolve(), args.artifacts.resolve()
        )
    except (OSError, KeyError, TypeError, VerificationError) as error:
        print(f"ERROR: independent GJP Brier replay refused: {error}", file=sys.stderr)
        return 1
    print(f"independent GJP Brier replay verified under {args.artifacts.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
