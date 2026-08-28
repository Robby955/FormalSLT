#!/usr/bin/env python3
"""Build a deterministic exact-rational replay of the GJP Brier protocol.

The raw GJP files remain external to the repository.  This program verifies
their pinned bytes, constructs the two crowd forecasts without accepting an
outcome argument, joins outcomes only after forecast reduction, and writes a
canonical stream, receipt, and manifest to a caller-supplied external
directory.  It never writes the preregistered repository output paths.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import inspect
import json
import os
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, time, timedelta
from decimal import Decimal, InvalidOperation, ROUND_FLOOR, ROUND_HALF_EVEN, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import check_gjp_brier_protocol as protocol_checker


DEFAULT_PROTOCOL = (
    ROOT / "applications/brier_monitor/realdata/gjp-brier-protocol-v1.json"
)
DEFAULT_PROTOCOL_MD = (
    ROOT / "applications/brier_monitor/realdata/gjp-brier-protocol-v1.md"
)
DEFAULT_VERIFIER = ROOT / "scripts/verify_gjp_brier_replay.py"
DEFAULT_TEST = ROOT / "tests/test_gjp_brier_replay.py"
DEFAULT_PROTOCOL_CHECKER = ROOT / "scripts/check_gjp_brier_protocol.py"
DEFAULT_FETCHER = ROOT / "scripts/fetch_gjp_brier_inputs.py"
DEFAULT_PROTOCOL_TEST = ROOT / "tests/test_gjp_brier_protocol.py"

STREAM_NAME = "gjp-brier-monitor-v1-stream.json"
RECEIPT_NAME = "gjp-brier-monitor-v1-receipt.json"
MANIFEST_NAME = "gjp-brier-monitor-v1-manifest.json"
STREAM_SCHEMA = "formalslt.brier-monitor.gjp-stream.v1"
RECEIPT_SCHEMA = "formalslt.brier-monitor.gjp-receipt.v1"
MANIFEST_SCHEMA = "formalslt.brier-monitor.gjp-manifest.v1"
ARTIFACT_STATUS = "REAL-DATA REPLAY; ARITHMETIC NOT YET LEAN-INSTANTIATED"

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


class ReplayError(ValueError):
    """Raised when raw data or an artifact violates the replay contract."""


def _reject_float(value: str) -> None:
    raise ReplayError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise ReplayError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReplayError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReplayError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def file_digest(path: Path, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rational_text(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def parse_fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise ReplayError(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ReplayError(f"invalid rational at {where}: {value!r}") from error
    if rational_text(result) != value:
        raise ReplayError(f"noncanonical rational at {where}: {value!r}")
    return result


def _decimal(value: str, where: str) -> Decimal:
    try:
        result = Decimal(value)
    except InvalidOperation as error:
        raise ReplayError(f"invalid decimal at {where}: {value!r}") from error
    if not result.is_finite():
        raise ReplayError(f"non-finite decimal at {where}: {value!r}")
    return result


def parse_datetime(value: str, where: str) -> datetime:
    text = value.strip()
    for pattern in ("%m/%d/%y %H:%M", "%m/%d/%y", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(text, pattern)
        except ValueError:
            pass
    raise ReplayError(f"unsupported timestamp at {where}: {value!r}")


def iso_timestamp(value: datetime) -> str:
    return value.strftime("%Y-%m-%dT%H:%M:%S")


def round_fraction_ties_even(value: Fraction, denominator: int) -> Fraction:
    if denominator <= 0:
        raise ReplayError("rounding denominator must be positive")
    scaled = value * denominator
    quotient, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    if twice > scaled.denominator or (twice == scaled.denominator and quotient % 2):
        quotient += 1
    return Fraction(quotient, denominator)


def _row_digest_payload(row: "ForecastRow") -> dict[str, Any]:
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


@dataclass(frozen=True)
class QuestionWindow:
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
class ForecastRow:
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
class WindowAccumulator:
    total: Fraction = Fraction(0)
    count: int = 0
    minimum: datetime | None = None
    maximum: datetime | None = None
    hasher: Any = field(default_factory=hashlib.sha256)


def _empty_window_accumulators() -> dict[int, WindowAccumulator]:
    return {days: WindowAccumulator() for days in ABLATION_DAYS}


@dataclass
class ForecastAccumulator:
    first_week_sum: Fraction = Fraction(0)
    first_week_count: int = 0
    first_week_min: datetime | None = None
    first_week_max: datetime | None = None
    first_week_hasher: Any = field(default_factory=hashlib.sha256)
    eligible_count: int = 0
    eligible_min: datetime | None = None
    eligible_max: datetime | None = None
    latest_by_user: dict[str, ForecastRow] = field(default_factory=dict)
    latest_timestamp_rows_by_user: dict[str, list[ForecastRow]] = field(default_factory=dict)
    max_timestamp_ties: int = 0
    differing_value_ties: int = 0
    window_accumulators: dict[int, WindowAccumulator] = field(
        default_factory=_empty_window_accumulators
    )


def _split_for_date(closed: datetime, protocol: dict[str, Any]) -> str:
    split = protocol["chronological_split"]
    day = closed.date().isoformat()
    train_end = split["train"]["date_closed_through"]
    cal_start = split["calibration"]["date_closed_from"]
    cal_end = split["calibration"]["date_closed_through"]
    monitor_start = split["monitor"]["date_closed_from"]
    if train_end is not None and day <= train_end:
        return "train"
    if cal_start <= day <= cal_end:
        return "calibration"
    if day >= monitor_start:
        return "monitor"
    raise ReplayError(f"date_closed {day} falls outside every declared split")


def load_questions(
    protocol: dict[str, Any], ifps_path: Path
) -> tuple[dict[str, QuestionWindow], dict[str, int], dict[str, Any]]:
    windows: dict[str, QuestionWindow] = {}
    outcomes: dict[str, int] = {}
    total_rows = 0
    selected_by_split: Counter[str] = Counter()
    with ifps_path.open("r", encoding="latin-1", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != IFP_FIELDS:
            raise ReplayError(f"unexpected ifps.csv header: {reader.fieldnames!r}")
        for line, row in enumerate(reader, 2):
            total_rows += 1
            if not (
                row["q_status"] == "closed"
                and row["n_opts"] == "2"
                and row["outcome"] in {"a", "b"}
            ):
                continue
            ifp_id = row["ifp_id"]
            if not ifp_id or ifp_id in windows:
                raise ReplayError(f"missing or duplicate selected ifp_id at ifps.csv:{line}")
            date_start = parse_datetime(row["date_start"], f"ifps.csv:{line}:date_start")
            date_suspend = parse_datetime(row["date_suspend"], f"ifps.csv:{line}:date_suspend")
            source_closed = parse_datetime(row["date_closed"], f"ifps.csv:{line}:date_closed")
            date_closed = datetime.combine(source_closed.date(), time.min)
            effective_cutoff = min(date_suspend, date_closed)
            split = _split_for_date(date_closed, protocol)
            windows[ifp_id] = QuestionWindow(
                ifp_id=ifp_id,
                date_start=date_start,
                date_suspend=date_suspend,
                date_closed=date_closed,
                effective_cutoff=effective_cutoff,
                source_date_start=row["date_start"],
                source_date_suspend=row["date_suspend"],
                source_date_closed=row["date_closed"],
                split=split,
            )
            outcomes[ifp_id] = 1 if row["outcome"] == "a" else 0
            selected_by_split[split] += 1
    return windows, outcomes, {
        "ifps_rows": total_rows,
        "outcome_selected_questions": len(windows),
        "outcome_selected_by_split": dict(sorted(selected_by_split.items())),
    }


def reduce_forecasts(
    windows: dict[str, QuestionWindow],
    forecast_paths: list[Path],
    allowed_event_types: set[int],
) -> tuple[dict[str, ForecastAccumulator], dict[str, Any]]:
    """Reduce forecasts without accepting, reading, or deriving from outcomes."""

    accumulators = {ifp_id: ForecastAccumulator() for ifp_id in windows}
    counts: Counter[str] = Counter()
    eligible_types: Counter[str] = Counter()
    for path in forecast_paths:
        with path.open("r", encoding="latin-1", newline="") as handle:
            reader = csv.DictReader(handle)
            if reader.fieldnames != FORECAST_FIELDS:
                raise ReplayError(f"unexpected forecast header in {path.name}: {reader.fieldnames!r}")
            for line, row in enumerate(reader, 2):
                counts["raw_forecast_rows"] += 1
                window = windows.get(row["ifp_id"])
                if window is None:
                    continue
                counts["outcome_selected_question_rows"] += 1
                try:
                    event_type = int(row["fcast_type"])
                except ValueError as error:
                    raise ReplayError(
                        f"invalid fcast_type at {path.name}:{line}: {row['fcast_type']!r}"
                    ) from error
                if event_type not in allowed_event_types:
                    raise ReplayError(
                        f"unrecognized fcast_type at {path.name}:{line}: {event_type}"
                    )
                if row["answer_option"] != "a":
                    counts["non_a_answer_option_rows"] += 1
                    continue
                counts["option_a_rows"] += 1
                timestamp = parse_datetime(
                    row["timestamp"], f"{path.name}:{line}:timestamp"
                )
                if timestamp < window.date_start:
                    counts["excluded_before_date_start"] += 1
                    continue
                if timestamp >= window.effective_cutoff:
                    counts["excluded_at_or_after_effective_cutoff"] += 1
                    if timestamp >= window.date_suspend:
                        counts["excluded_at_or_after_date_suspend"] += 1
                    if timestamp >= window.date_closed:
                        counts["excluded_at_or_after_date_closed_midnight"] += 1
                    continue
                value_decimal = _decimal(row["value"], f"{path.name}:{line}:value")
                value = Fraction(value_decimal)
                if not 0 <= value <= 1:
                    raise ReplayError(f"forecast outside [0,1] at {path.name}:{line}")
                user_id = row["user_id"]
                if not user_id or user_id == "NA":
                    raise ReplayError(f"missing user_id at {path.name}:{line}")
                forecast_id_text = row["forecast_id"]
                forecast_id = _decimal(
                    forecast_id_text, f"{path.name}:{line}:forecast_id"
                )
                try:
                    source_year = int(row["year"])
                except ValueError as error:
                    raise ReplayError(
                        f"invalid source year at {path.name}:{line}: {row['year']!r}"
                    ) from error
                forecast = ForecastRow(
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
                accumulator = accumulators[window.ifp_id]
                accumulator.eligible_count += 1
                if accumulator.eligible_min is None or timestamp < accumulator.eligible_min:
                    accumulator.eligible_min = timestamp
                if accumulator.eligible_max is None or timestamp > accumulator.eligible_max:
                    accumulator.eligible_max = timestamp
                eligible_types[str(event_type)] += 1
                counts["eligible_rows"] += 1

                for days, window_accumulator in accumulator.window_accumulators.items():
                    window_cutoff = min(
                        window.date_start + timedelta(days=days),
                        window.effective_cutoff,
                    )
                    if timestamp < window_cutoff:
                        window_accumulator.total += value
                        window_accumulator.count += 1
                        if (
                            window_accumulator.minimum is None
                            or timestamp < window_accumulator.minimum
                        ):
                            window_accumulator.minimum = timestamp
                        if (
                            window_accumulator.maximum is None
                            or timestamp > window_accumulator.maximum
                        ):
                            window_accumulator.maximum = timestamp
                        window_accumulator.hasher.update(
                            canonical_json_bytes(_row_digest_payload(forecast))
                        )

                if timestamp < window.date_start + timedelta(days=7):
                    accumulator.first_week_sum += value
                    accumulator.first_week_count += 1
                    if accumulator.first_week_min is None or timestamp < accumulator.first_week_min:
                        accumulator.first_week_min = timestamp
                    if accumulator.first_week_max is None or timestamp > accumulator.first_week_max:
                        accumulator.first_week_max = timestamp
                    accumulator.first_week_hasher.update(
                        canonical_json_bytes(_row_digest_payload(forecast))
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


def _median(values: list[Fraction]) -> Fraction:
    if not values:
        raise ReplayError("median of an empty forecast collection")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return (ordered[middle - 1] + ordered[middle]) / 2


def _digest_rows(rows: list[dict[str, Any]]) -> str:
    return sha256_bytes(canonical_json_bytes(rows))


def crowd_predictions(
    windows: dict[str, QuestionWindow],
    accumulators: dict[str, ForecastAccumulator],
    denominator: int,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    predictions: dict[str, dict[str, Any]] = {}
    missing: dict[str, list[str]] = {
        "first-week-mean": [],
        "final-consensus-median": [],
        "extremized-final-consensus": [],
    }
    for ifp_id in sorted(windows):
        accumulator = accumulators[ifp_id]
        if accumulator.first_week_count == 0:
            missing["first-week-mean"].append(ifp_id)
        if not accumulator.latest_by_user:
            missing["final-consensus-median"].append(ifp_id)
            missing["extremized-final-consensus"].append(ifp_id)
        if accumulator.first_week_count == 0 or not accumulator.latest_by_user:
            continue
        if not (
            windows[ifp_id].date_start
            <= accumulator.first_week_min
            <= accumulator.first_week_max
            < windows[ifp_id].effective_cutoff
        ):
            raise ReplayError(f"first-week timestamp bounds fail for {ifp_id}")
        if not (
            windows[ifp_id].date_start
            <= accumulator.eligible_min
            <= accumulator.eligible_max
            < windows[ifp_id].effective_cutoff
        ):
            raise ReplayError(f"final-consensus timestamp bounds fail for {ifp_id}")

        first_raw = accumulator.first_week_sum / accumulator.first_week_count
        first = round_fraction_ties_even(first_raw, denominator)
        latest = sorted(
            accumulator.latest_by_user.values(), key=lambda row: row.user_id
        )
        final_raw = _median([row.value for row in latest])
        final = round_fraction_ties_even(final_raw, denominator)
        denominator_extreme = final * final + (1 - final) * (1 - final)
        extreme_raw = final * final / denominator_extreme
        extreme_clipped = min(max(extreme_raw, Fraction(1, 100)), Fraction(99, 100))
        extreme = round_fraction_ties_even(extreme_clipped, denominator)

        predictions[ifp_id] = {
            "first-week-mean": first,
            "final-consensus-median": final,
            "extremized-final-consensus": extreme,
            "provenance": {
                "effective_cutoff": iso_timestamp(windows[ifp_id].effective_cutoff),
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
                    "latest_rows_sha256": _digest_rows(
                        [_row_digest_payload(row) for row in latest]
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
        "missing_by_model": {key: value for key, value in missing.items()},
        "missing_count_by_model": {key: len(value) for key, value in missing.items()},
    }


def _expected_split_counts(protocol: dict[str, Any]) -> dict[str, int]:
    return {
        name: int(protocol["chronological_split"][name]["expected_count"])
        for name in ("train", "calibration", "monitor")
    }


def assemble_stream(
    protocol: dict[str, Any],
    protocol_commit: str,
    implementation_commit: str,
    implementation_tree: str,
    protocol_sha256: str,
    windows: dict[str, QuestionWindow],
    outcomes: dict[str, int],
    crowd: dict[str, dict[str, Any]],
    question_audit: dict[str, Any],
    forecast_audit: dict[str, Any],
    missingness: dict[str, Any],
) -> tuple[dict[str, Any], list[list[Fraction]]]:
    denominator = int(protocol["quantization"]["denominator"])
    included = sorted(crowd, key=lambda key: (windows[key].date_closed, key))
    split_counts = Counter(windows[key].split for key in included)
    expected = _expected_split_counts(protocol)
    if dict(split_counts) != expected:
        raise ReplayError(
            f"complete-case split counts {dict(split_counts)!r} do not match protocol {expected!r}"
        )
    eligibility = protocol["eligibility_after_temporal_amendment"]
    if len(windows) != eligibility["candidate_count"]:
        raise ReplayError("candidate question count disagrees with the temporal amendment")
    if len(included) != eligibility["included_count"]:
        raise ReplayError("complete-case count disagrees with the temporal amendment")
    if sorted(set(windows) - set(included)) != eligibility["excluded_ifp_ids"]:
        raise ReplayError("complete-case exclusions disagree with the temporal amendment")
    if expected != eligibility["split_counts"]:
        raise ReplayError("split declarations disagree with the temporal amendment")
    train = [key for key in included if windows[key].split == "train"]
    if not train:
        raise ReplayError("the complete-case train split is empty")
    train_base_rate_raw = Fraction(sum(outcomes[key] for key in train), len(train))
    train_base_rate = round_fraction_ties_even(train_base_rate_raw, denominator)

    rows: list[dict[str, Any]] = []
    numeric_predictions: list[list[Fraction]] = []
    for index, ifp_id in enumerate(included):
        window = windows[ifp_id]
        crowd_row = crowd[ifp_id]
        model_values = [
            train_base_rate,
            crowd_row["first-week-mean"],
            crowd_row["final-consensus-median"],
            crowd_row["extremized-final-consensus"],
        ]
        numeric_predictions.append(model_values)
        rows.append(
            {
                "date_closed": iso_timestamp(window.date_closed),
                "date_start": iso_timestamp(window.date_start),
                "date_suspend": iso_timestamp(window.date_suspend),
                "effective_cutoff": iso_timestamp(window.effective_cutoff),
                "ifp_id": ifp_id,
                "index": index,
                "outcome": outcomes[ifp_id],
                "predictions": {
                    model: rational_text(value)
                    for model, value in zip(MODEL_IDS, model_values, strict=True)
                },
                "provenance": crowd_row["provenance"],
                "source_date_closed": window.source_date_closed,
                "source_date_start": window.source_date_start,
                "source_date_suspend": window.source_date_suspend,
                "split": window.split,
            }
        )
    excluded = sorted(set(windows) - set(included))
    exclusion_rows = [
        {
            "ifp_id": key,
            "missing_models": sorted(
                model
                for model, identifiers in missingness["missing_by_model"].items()
                if key in identifiers
            ),
            "split": windows[key].split,
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
        "quantization": {
            "denominator": denominator,
            "tie_rule": "ties to even",
        },
        "schema_version": STREAM_SCHEMA,
        "train_base_rate": {
            "raw": rational_text(train_base_rate_raw),
            "quantized": rational_text(train_base_rate),
            "training_questions": len(train),
        },
    }
    return stream, numeric_predictions


def rationalized_posterior(
    models: list[str],
    prior: list[Fraction],
    calibration_loss_sums: list[Fraction],
    grid_denominator: int,
) -> tuple[list[Fraction], dict[str, Any]]:
    if len(models) != len(prior) or len(models) != len(calibration_loss_sums):
        raise ReplayError("posterior input dimensions disagree")
    with localcontext() as context:
        context.prec = POSTERIOR_DECIMAL_PRECISION
        context.rounding = ROUND_HALF_EVEN
        scores: list[Decimal] = []
        for pi, loss in zip(prior, calibration_loss_sums, strict=True):
            pi_decimal = Decimal(pi.numerator) / Decimal(pi.denominator)
            loss_decimal = Decimal(loss.numerator) / Decimal(loss.denominator)
            scores.append(pi_decimal * context.exp(-loss_decimal))
        total = sum(scores, Decimal(0))
        ideal = [score / total for score in scores]
        # Normalize once more under the pinned context so apportionment starts
        # from a vector whose Decimal sum is as close to one as the context permits.
        ideal_total = sum(ideal, Decimal(0))
        ideal = [weight / ideal_total for weight in ideal]
        scaled = [weight * grid_denominator for weight in ideal]
        floors = [int(value.to_integral_value(rounding=ROUND_FLOOR)) for value in scaled]
        remainder_units = grid_denominator - sum(floors)
        if not 0 <= remainder_units <= len(models):
            raise ReplayError(
                f"posterior apportionment remainder {remainder_units} is outside [0,{len(models)}]"
            )
        order = sorted(
            range(len(models)), key=lambda index: (-(scaled[index] - floors[index]), models[index])
        )
        units = floors[:]
        for index in order[:remainder_units]:
            units[index] += 1
        posterior = [Fraction(unit, grid_denominator) for unit in units]
        if sum(posterior, Fraction(0)) != 1:
            raise ReplayError("rationalized posterior is not a probability mass function")
        diagnostic = {
            "decimal_precision": POSTERIOR_DECIMAL_PRECISION,
            "decimal_rounding": "ROUND_HALF_EVEN",
            "ideal_weight_diagnostics": [format(weight, "f") for weight in ideal],
            "method": (
                "Decimal exp softmax followed by largest-remainder simplex quantization; "
                "ties use ascending model id"
            ),
            "simplex_grid_denominator": grid_denominator,
            "simplex_units": units,
        }
        return posterior, diagnostic


def _log_unit_interval(value: Fraction) -> tuple[Fraction, Fraction]:
    if not 1 <= value <= 2:
        raise AssertionError("unit logarithm reduction failed")
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
        raise ReplayError("log input must be positive")
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
    two_low, two_high = _log_unit_interval(Fraction(2))
    reduced_low, reduced_high = _log_unit_interval(reduced)
    return exponent * two_low + reduced_low, exponent * two_high + reduced_high


def kl_interval(
    posterior: list[Fraction], prior: list[Fraction]
) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(0)
    for rho, pi in zip(posterior, prior, strict=True):
        if rho:
            term_low, term_high = log_interval(rho / pi)
            low += rho * term_low
            high += rho * term_high
    return low, high


def psi_interval(tilt: Fraction) -> tuple[Fraction, Fraction]:
    low, high = log_interval(1 - tilt)
    return -high - tilt, -low - tilt


def _round_down(value: Fraction, denominator: int) -> Fraction:
    scaled = value * denominator
    return Fraction(scaled.numerator // scaled.denominator, denominator)


def _round_up(value: Fraction, denominator: int) -> Fraction:
    return -_round_down(-value, denominator)


def _interval_record(
    interval: tuple[Fraction, Fraction], denominator: int
) -> dict[str, str]:
    return {
        "lower": rational_text(_round_down(interval[0], denominator)),
        "upper": rational_text(_round_up(interval[1], denominator)),
    }


def max_geometric_atom(suffix_length: int) -> int:
    logarithm = 0
    threshold = 4
    while threshold <= suffix_length:
        logarithm += 1
        threshold *= 4
    return max(logarithm - 1, 0) + 2


def _expected_model_prediction_vectors(
    observations: list[dict[str, Any]],
    crowd: dict[str, dict[str, Any]],
    train_base_rate: Fraction,
) -> dict[str, list[Fraction]]:
    """Rebuild each model vector from its declared construction inputs.

    The three crowd vectors come from the outcome-inaccessible forecast
    reduction.  The constant vector uses only the frozen train-split base
    rate.  No caller-supplied provenance label participates in this check.
    """

    identifiers = [str(row["ifp_id"]) for row in observations]
    missing = [ifp_id for ifp_id in identifiers if ifp_id not in crowd]
    if missing:
        raise ReplayError(
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


def _loss_matrix(
    observations: list[dict[str, Any]],
    numeric_predictions: list[list[Fraction]],
    expected_predictions: dict[str, list[Fraction]],
) -> list[list[Fraction]]:
    if len(observations) != len(numeric_predictions):
        raise ReplayError("observation and prediction row counts disagree")
    if any(len(row) != len(MODEL_IDS) for row in numeric_predictions):
        raise ReplayError("prediction row does not match the declared model catalog")
    matrix: list[list[Fraction]] = []
    for model_index, model_id in enumerate(MODEL_IDS):
        predictions = _ingest_model_predictions(
            model_id,
            [row[model_index] for row in numeric_predictions],
            expected_predictions.get(model_id),
        )
        matrix.append(
            [
                _score_brier_prediction(
                    prediction, Fraction(observation["outcome"])
                )
                for observation, prediction in zip(
                    observations, predictions, strict=True
                )
            ]
        )
    return matrix


def _ingest_model_predictions(
    model_id: str,
    predictions: list[Fraction],
    expected_predictions: list[Fraction] | None,
) -> list[Fraction]:
    """Admit only a vector rebuilt from the model's declared safe inputs."""

    if model_id not in MODEL_IDS:
        raise ReplayError(f"model refused at ingestion: undeclared model id {model_id!r}")
    normalized = [Fraction(value) for value in predictions]
    if expected_predictions is None:
        raise ReplayError(
            f"model {model_id!r} has no independently rebuilt prediction vector"
        )
    expected = [Fraction(value) for value in expected_predictions]
    if len(normalized) != len(expected):
        raise ReplayError(f"model {model_id!r} prediction length disagrees with its rebuild")
    if any(not 0 <= value <= 1 for value in normalized):
        raise ReplayError(f"model {model_id!r} emitted a prediction outside [0,1]")
    if normalized != expected:
        raise ReplayError(
            f"model {model_id!r} predictions differ from the independently rebuilt "
            "outcome-inaccessible construction"
        )
    return normalized


def _score_brier_prediction(
    prediction: Fraction, outcome: Fraction
) -> Fraction:
    """Score a prediction vector only after the shared ingestion gate."""

    if not 0 <= prediction <= 1 or outcome not in {0, 1}:
        raise ReplayError("Brier scorer received an invalid prediction or outcome")
    return (prediction - outcome) ** 2


def _deliberately_leaked_tripwire(
    observations: list[dict[str, Any]],
    expected_predictions: dict[str, list[Fraction]],
    reducer: Any = reduce_forecasts,
    ingestor: Any = _ingest_model_predictions,
) -> dict[str, Any]:
    outcomes = [int(row["outcome"]) for row in observations]
    reducer_signature = inspect.signature(reducer)
    reducer_parameters = list(reducer_signature.parameters)
    if "outcomes" in reducer_parameters or any(
        parameter.kind is inspect.Parameter.VAR_KEYWORD
        for parameter in reducer_signature.parameters.values()
    ):
        raise ReplayError("forecast reducer exposes an outcome argument")
    try:
        reducer({}, [], set(), outcomes=outcomes)
    except TypeError:
        pass
    else:
        raise ReplayError("forecast reducer accepted an attempted outcome injection")

    oracle_predictions = [
        Fraction(99, 100) if outcome == 1 else Fraction(1, 100)
        for outcome in outcomes
    ]
    safe_reference = expected_predictions.get("first-week-mean")
    if safe_reference is None:
        raise ReplayError("tripwire lacks the rebuilt first-week reference vector")
    if oracle_predictions == [Fraction(value) for value in safe_reference]:
        raise ReplayError("tripwire is nondiscriminating on this observation sequence")

    try:
        ingestor(
            "oracle-leak",
            oracle_predictions,
            safe_reference,
        )
    except ReplayError:
        pass
    else:
        raise ReplayError("the outcome-derived oracle model passed the shared ingestion gate")

    try:
        ingestor("first-week-mean", oracle_predictions, safe_reference)
    except ReplayError:
        pass
    else:
        raise ReplayError(
            "the relabeled outcome-derived oracle passed the shared ingestion gate"
        )

    return {
        "attempted_dependency": "outcomes",
        "attempted_model_id": "oracle-leak",
        "caller_source_labels_accepted_as_provenance": False,
        "declared_model_relabel_attempt": "first-week-mean",
        "definition": "p=99/100 if outcome=a else 1/100",
        "ingestion_callable": "shared exact-vector model ingestion gate",
        "oracle_prediction_count": len(oracle_predictions),
        "oracle_predictions_sha256": sha256_bytes(
            canonical_json_bytes(
                [rational_text(value) for value in oracle_predictions]
            )
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


def _timestamp_assertion(observations: list[dict[str, Any]]) -> dict[str, Any]:
    audited_reducers = 0
    for row in observations:
        start = datetime.fromisoformat(row["date_start"])
        cutoff = datetime.fromisoformat(row["effective_cutoff"])
        provenance = row["provenance"]
        first = provenance["first_week"]
        final = provenance["final_consensus"]
        first_min = datetime.fromisoformat(first["min_consumed_timestamp"])
        first_max = datetime.fromisoformat(first["max_consumed_timestamp"])
        final_min = datetime.fromisoformat(final["min_consumed_timestamp"])
        final_max = datetime.fromisoformat(final["max_consumed_timestamp"])
        first_cutoff = min(start + timedelta(days=7), cutoff)
        if not start <= first_min <= first_max < first_cutoff:
            raise ReplayError(f"first-week receipt timestamps fail for {row['ifp_id']}")
        if not start <= final_min <= final_max < cutoff:
            raise ReplayError(f"final-consensus receipt timestamps fail for {row['ifp_id']}")
        audited_reducers += 2
    return {
        "audited_observations": len(observations),
        "audited_reducers": audited_reducers,
        "rule": "date_start <= every consumed timestamp < the reducer cutoff",
        "status": "PASS",
    }


def _future_feature_ablation(
    protocol: dict[str, Any],
    windows: dict[str, QuestionWindow],
    accumulators: dict[str, ForecastAccumulator],
    crowd: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    configured = next(
        row for row in protocol["leakage_tests"] if row["id"] == "future_feature_ablation"
    )["windows_days"]
    if configured != list(ABLATION_DAYS):
        raise ReplayError(
            f"future-feature ablation windows must be {list(ABLATION_DAYS)!r}"
        )
    denominator = int(protocol["quantization"]["denominator"])
    rows: list[dict[str, Any]] = []
    primary_match = True
    nested_counts_pass = True
    preceding_counts = {ifp_id: 0 for ifp_id in windows}
    for days in ABLATION_DAYS:
        counts: Counter[str] = Counter()
        missing: Counter[str] = Counter()
        consumed_rows = 0
        global_minimum: datetime | None = None
        global_maximum: datetime | None = None
        observation_rows: list[dict[str, Any]] = []
        missing_ids: list[str] = []
        for ifp_id, window in windows.items():
            accumulator = accumulators[ifp_id].window_accumulators[days]
            split = window.split
            if accumulator.count < preceding_counts[ifp_id]:
                nested_counts_pass = False
            preceding_counts[ifp_id] = accumulator.count
            if accumulator.count == 0:
                missing[split] += 1
                missing_ids.append(ifp_id)
                continue
            window_cutoff = min(
                window.date_start + timedelta(days=days), window.effective_cutoff
            )
            if not (
                window.date_start
                <= accumulator.minimum
                <= accumulator.maximum
                < window_cutoff
            ):
                raise ReplayError(
                    f"{days}-day ablation consumed a future row for {ifp_id}"
                )
            prediction = round_fraction_ties_even(
                accumulator.total / accumulator.count, denominator
            )
            counts[split] += 1
            consumed_rows += accumulator.count
            if global_minimum is None or accumulator.minimum < global_minimum:
                global_minimum = accumulator.minimum
            if global_maximum is None or accumulator.maximum > global_maximum:
                global_maximum = accumulator.maximum
            if days == 7 and ifp_id in crowd:
                primary = crowd[ifp_id]
                primary_provenance = primary["provenance"]["first_week"]
                primary_match = primary_match and all(
                    (
                        prediction == primary["first-week-mean"],
                        accumulator.count == primary_provenance["consumed_rows"],
                        accumulator.hasher.hexdigest()
                        == primary_provenance["consumed_rows_sha256"],
                        iso_timestamp(accumulator.minimum)
                        == primary_provenance["min_consumed_timestamp"],
                        iso_timestamp(accumulator.maximum)
                        == primary_provenance["max_consumed_timestamp"],
                    )
                )
            observation_rows.append(
                {
                    "consumed_rows": accumulator.count,
                    "consumed_rows_sha256": accumulator.hasher.hexdigest(),
                    "effective_window_end": iso_timestamp(window_cutoff),
                    "ifp_id": ifp_id,
                    "max_consumed_timestamp": iso_timestamp(accumulator.maximum),
                    "min_consumed_timestamp": iso_timestamp(accumulator.minimum),
                    "quantized_prediction": rational_text(prediction),
                    "raw_mean": rational_text(
                        accumulator.total / accumulator.count
                    ),
                    "split": split,
                }
            )
        rows.append(
            {
                "consumed_rows": consumed_rows,
                "defined_questions_by_split": dict(sorted(counts.items())),
                "max_consumed_timestamp": (
                    iso_timestamp(global_maximum) if global_maximum is not None else None
                ),
                "min_consumed_timestamp": (
                    iso_timestamp(global_minimum) if global_minimum is not None else None
                ),
                "missing_ifp_ids": sorted(missing_ids),
                "missing_questions_by_split": {
                    split: missing[split]
                    for split in ("train", "calibration", "monitor")
                },
                "observations": sorted(
                    observation_rows, key=lambda row: (row["split"], row["ifp_id"])
                ),
                "prediction_rows_sha256": sha256_bytes(
                    canonical_json_bytes(
                        sorted(observation_rows, key=lambda row: row["ifp_id"])
                    )
                ),
                "window_days": days,
            }
        )
    if not primary_match:
        raise ReplayError("the 7-day ablation differs from the primary first-week model")
    if not nested_counts_pass:
        raise ReplayError("ablation row counts are not nested across increasing windows")
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
        "windows": rows,
    }


def _posthoc_shuffled_time_sensitivity(
    monitor_ids: list[str], monitor_losses: list[list[Fraction]], posterior: list[Fraction]
) -> dict[str, Any]:
    permutations = 200
    horizon = len(monitor_ids)
    if not horizon or any(len(row) != horizon for row in monitor_losses):
        raise ReplayError("shuffled-time control received inconsistent monitor data")
    weighted_losses = [
        sum(
            (posterior[index] * model_losses[time_index]
             for index, model_losses in enumerate(monitor_losses)),
            Fraction(0),
        )
        for time_index in range(horizon)
    ]
    reference_loss_prefix, reference_quadratic_prefix = _posterior_prefix_statistics(
        monitor_losses, posterior
    )
    reference = reference_loss_prefix[-1] / horizon
    if reference != sum(weighted_losses, Fraction(0)) / horizon:
        raise ReplayError("shuffled-time reference risk reconstruction disagrees")
    reference_quadratic = reference_quadratic_prefix[-1]
    order_digest = hashlib.sha256()
    seen_orders: set[tuple[int, ...]] = set()
    quadratic_values: list[Fraction] = []
    for replicate in range(permutations):
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
        if order in seen_orders:
            raise ReplayError("post-hoc shuffled-time control produced a duplicate permutation")
        seen_orders.add(order)
        for index in order:
            order_digest.update(index.to_bytes(4, "big"))
        permuted_losses = [
            [model_losses[index] for index in order]
            for model_losses in monitor_losses
        ]
        permuted_prefix, permuted_quadratic = _posterior_prefix_statistics(
            permuted_losses, posterior
        )
        if permuted_prefix[-1] / horizon != reference:
            raise ReplayError("exact empirical risk changed under a time permutation")
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
        "distinct_permutations": len(seen_orders),
        "every_order_is_bijection": True,
        "order_matrix_sha256": order_digest.hexdigest(),
        "permutations": permutations,
        "quadratic_variation_changed_in_observed_sample": (
            len(set(quadratic_values + [reference_quadratic])) > 1
        ),
        "quadratic_variation_distribution": {
            "maximum": rational_text(ordered_quadratics[-1]),
            "median": rational_text(_median(ordered_quadratics)),
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


def _posterior_prefix_statistics(
    losses: list[list[Fraction]], posterior: list[Fraction]
) -> tuple[list[Fraction], list[Fraction]]:
    horizon = len(losses[0])
    if any(len(values) != horizon for values in losses):
        raise ReplayError("loss matrix rows have unequal lengths")
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


def _suffix_statistics(
    loss_prefix: list[Fraction],
    quadratic_prefix: list[Fraction],
    wake: int,
    horizon: int,
) -> tuple[Fraction, Fraction]:
    if not (0 <= wake < horizon < len(loss_prefix)):
        raise ReplayError(f"invalid suffix [{wake},{horizon})")
    suffix_length = horizon - wake
    empirical = (loss_prefix[horizon] - loss_prefix[wake]) / suffix_length
    quadratic = quadratic_prefix[horizon] - quadratic_prefix[wake]
    return empirical, quadratic


def _boundary_candidates(
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
        raise ReplayError("a boundary suffix must contain at least four observations")
    empirical, quadratic = _suffix_statistics(
        loss_prefix, quadratic_prefix, wake, horizon
    )
    result: list[tuple[Fraction, Fraction, Fraction, dict[str, Any]]] = []
    for atom in range(max_geometric_atom(suffix_length) + 1):
        tilt = Fraction(1, 2 ** (atom + 1))
        cache_key = effective_delta, atom
        if cache_key not in interval_cache:
            confidence_ratio = Fraction((atom + 1) * (atom + 2), 1) / effective_delta
            interval_cache[cache_key] = log_interval(confidence_ratio), psi_interval(tilt)
        confidence, psi = interval_cache[cache_key]
        denominator = suffix_length * tilt
        excess = (
            (entropy[0] + confidence[0] + psi[0] * quadratic) / denominator,
            (entropy[1] + confidence[1] + psi[1] * quadratic) / denominator,
        )
        boundary = empirical + excess[0], empirical + excess[1]
        row = {
            "boundary_interval": _interval_record(boundary, output_denominator),
            "confidence_log_interval": _interval_record(confidence, output_denominator),
            "effective_delta": rational_text(effective_delta),
            "excess_interval": _interval_record(excess, output_denominator),
            "horizon": horizon,
            "kl_interval": _interval_record(entropy, output_denominator),
            "posterior_empirical_brier_risk": rational_text(empirical),
            "psi_interval": _interval_record(psi, output_denominator),
            "suffix_length": suffix_length,
            "suffix_predictor_quadratic_variation": rational_text(quadratic),
            "tilt": rational_text(tilt),
            "tilt_atom": atom,
            "wake": wake,
        }
        reported_lower = parse_fraction(row["boundary_interval"]["lower"], "boundary lower")
        reported_upper = parse_fraction(row["boundary_interval"]["upper"], "boundary upper")
        result.append((reported_upper, reported_lower, boundary[1], row))
    return result


def _select_candidate(
    candidates: list[tuple[Fraction, Fraction, Fraction, dict[str, Any]]]
) -> dict[str, Any]:
    if not candidates:
        raise ReplayError("cannot select from an empty boundary catalog")
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


def _crossing(selected_rows: list[dict[str, Any]], threshold: Fraction) -> int | None:
    for row in selected_rows:
        if parse_fraction(row["boundary_interval"]["upper"], "boundary upper") < threshold:
            return int(row["horizon"])
    return None


class SplitMix64:
    """Pinned unsigned SplitMix64 stream used only by the null diagnostic."""

    MASK = (1 << 64) - 1

    def __init__(self, seed: int):
        if not 0 <= seed <= self.MASK:
            raise ReplayError("SplitMix64 seed is outside the unsigned 64-bit range")
        self.state = seed
        self.words = 0

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & self.MASK
        value = self.state
        value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & self.MASK
        value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & self.MASK
        value ^= value >> 31
        self.words += 1
        return value & self.MASK


def _bernoulli_exact(
    generator: SplitMix64, probability: Fraction
) -> tuple[int, int]:
    probability = Fraction(probability)
    if not 0 <= probability <= 1:
        raise ReplayError("Bernoulli probability is outside [0,1]")
    limit = ((1 << 64) // probability.denominator) * probability.denominator
    rejected = 0
    while True:
        word = generator.next_u64()
        if word < limit:
            return int(word % probability.denominator < probability.numerator), rejected
        rejected += 1


def _reported_endpoint(
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
        empirical, quadratic = _suffix_statistics(
            loss_prefix, quadratic_prefix, wake, horizon
        )
        suffix_length = horizon - wake
        for atom in range(max_geometric_atom(suffix_length) + 1):
            tilt = Fraction(1, 2 ** (atom + 1))
            cache_key = effective_delta, atom
            if cache_key not in interval_cache:
                ratio = Fraction((atom + 1) * (atom + 2), 1) / effective_delta
                interval_cache[cache_key] = log_interval(ratio), psi_interval(tilt)
            confidence, psi = interval_cache[cache_key]
            excess_upper = (
                entropy[1] + confidence[1] + psi[1] * quadratic
            ) / (suffix_length * tilt)
            endpoint = empirical + excess_upper
            candidate = endpoint, excess_upper, wake, atom
            if best is None or (endpoint, wake, atom) < (best[0], best[2], best[3]):
                best = candidate
    if best is None:
        raise ReplayError("no admissible endpoint")
    return (
        _round_up(best[0], output_denominator),
        _round_up(best[1], output_denominator),
        best[2],
        best[3],
    )


def _null_replay(
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
    entropy = kl_interval(posterior, prior)
    seed = int(baseline["null_generator"]["seed_u64_hex"], 16)
    generator = SplitMix64(seed)
    outcome_digest = hashlib.sha256()
    rejected_words = 0
    declaration_counts = {"B1": 0, "B2": 0, "B3": 0}
    crossing_histograms: dict[str, Counter[int]] = {"B2": Counter(), "B3": Counter()}
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ] = {}
    for _replicate in range(replicates):
        outcomes: list[int] = []
        for _index in range(horizon):
            outcome, rejected = _bernoulli_exact(generator, base_rate)
            outcomes.append(outcome)
            rejected_words += rejected
        outcome_digest.update(bytes(outcomes))
        losses = [[] for _ in MODEL_IDS]
        for outcome, predictions in zip(outcomes, monitor_predictions, strict=True):
            for model_index, prediction in enumerate(predictions):
                losses[model_index].append((prediction - outcome) ** 2)
        loss_prefix, quadratic_prefix = _posterior_prefix_statistics(losses, posterior)
        b2_crossing: int | None = None
        b3_crossing: int | None = None
        b1_endpoint: Fraction | None = None
        for report_time in range(4, horizon + 1):
            if b2_crossing is None or report_time == horizon:
                b1_candidate = _reported_endpoint(
                    loss_prefix,
                    quadratic_prefix,
                    entropy,
                    [(0, delta)],
                    report_time,
                    output_denominator,
                    interval_cache,
                )
                if report_time == horizon:
                    b1_endpoint = b1_candidate[0]
                if b2_crossing is None and b1_candidate[0] < threshold:
                    b2_crossing = report_time
            if b3_crossing is None:
                admitted = [
                    (wake, delta / ((wake + 1) * (wake + 2)))
                    for wake in wakes
                    if wake <= report_time - 4
                ]
                b3_candidate = _reported_endpoint(
                    loss_prefix,
                    quadratic_prefix,
                    entropy,
                    admitted,
                    report_time,
                    output_denominator,
                    interval_cache,
                )
                if b3_candidate[0] < threshold:
                    b3_crossing = report_time
        if b1_endpoint is None:
            raise AssertionError("final B1 endpoint was not evaluated")
        if b1_endpoint < threshold:
            declaration_counts["B1"] += 1
        if b2_crossing is not None:
            declaration_counts["B2"] += 1
            crossing_histograms["B2"][b2_crossing] += 1
        if b3_crossing is not None:
            declaration_counts["B3"] += 1
            crossing_histograms["B3"][b3_crossing] += 1
    ceiling = (replicates * delta).numerator // (replicates * delta).denominator
    checks = {
        "B1_count_at_most_nominal_ceiling": declaration_counts["B1"] <= ceiling,
        "B2_count_at_least_25": declaration_counts["B2"] >= 25,
        "B3_count_at_most_nominal_ceiling": declaration_counts["B3"] <= ceiling,
        "B3_final_width_at_most_twice_B1": observed_width_ratio <= 2,
    }
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
        "nominal_count_ceiling": ceiling,
        "procedures": {
            name: {
                "declaration_count": count,
                "declaration_fraction": rational_text(Fraction(count, replicates)),
                **(
                    {
                        "first_crossing_histogram": {
                            str(time): value
                            for time, value in sorted(crossing_histograms[name].items())
                        }
                    }
                    if name in crossing_histograms
                    else {}
                ),
            }
            for name, count in declaration_counts.items()
        },
        "replicates": replicates,
        "win_condition_checks": checks,
        "win_condition_passed": all(checks.values()),
    }


def _overall_preregistered_verdict(
    null_replay: dict[str, Any], leakage_tests: dict[str, Any]
) -> dict[str, Any]:
    checks = null_replay["win_condition_checks"]
    failed_checks = sorted(name for name, passed in checks.items() if not passed)
    incomplete_controls = sorted(
        name
        for name, result in leakage_tests.items()
        if str(result["status"]).startswith("UNDERSPECIFIED")
    )
    win_passed = bool(null_replay["win_condition_passed"])
    overall_passed = win_passed and not incomplete_controls
    status = "PASS" if overall_passed else ("INCOMPLETE" if win_passed else "FAIL")
    return {
        "control_completion": "INCOMPLETE" if incomplete_controls else "COMPLETE",
        "failed_win_condition_checks": failed_checks,
        "incomplete_controls": incomplete_controls,
        "null_win_condition_passed": win_passed,
        "overall_preregistered_passed": overall_passed,
        "status": status,
    }


def compute_receipt(
    protocol: dict[str, Any],
    stream: dict[str, Any],
    numeric_predictions: list[list[Fraction]],
    windows: dict[str, QuestionWindow],
    accumulators: dict[str, ForecastAccumulator],
    crowd: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    observations = stream["observations"]
    base_rate = parse_fraction(stream["train_base_rate"]["quantized"], "train base rate")
    expected_predictions = _expected_model_prediction_vectors(
        observations, crowd, base_rate
    )
    losses = _loss_matrix(observations, numeric_predictions, expected_predictions)
    split_indices = {
        name: [index for index, row in enumerate(observations) if row["split"] == name]
        for name in ("train", "calibration", "monitor")
    }
    calibration = split_indices["calibration"]
    monitor = split_indices["monitor"]
    if not calibration or not monitor:
        raise ReplayError("calibration and monitor splits must both be nonempty")
    calibration_sums = [
        sum((values[index] for index in calibration), Fraction(0)) for values in losses
    ]
    calibration_means = [value / len(calibration) for value in calibration_sums]
    prior = [parse_fraction(value, f"prior[{index}]") for index, value in enumerate(
        protocol["model_catalog"]["prior"]
    )]
    grid_denominator = int(protocol["quantization"]["output_grid_denominator"])
    posterior, posterior_audit = rationalized_posterior(
        MODEL_IDS, prior, calibration_sums, grid_denominator
    )
    monitor_predictions = [numeric_predictions[index] for index in monitor]
    monitor_losses = [[values[index] for index in monitor] for values in losses]
    delta = parse_fraction(protocol["confidence_contract"]["delta"], "delta")
    wakes = list(protocol["confidence_contract"]["wake_grid"])
    output_denominator = grid_denominator
    entropy = kl_interval(posterior, prior)
    horizon = len(monitor)
    loss_prefix, quadratic_prefix = _posterior_prefix_statistics(
        monitor_losses, posterior
    )
    interval_cache: dict[
        tuple[Fraction, int],
        tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]],
    ] = {}

    b1_candidates = _boundary_candidates(
        loss_prefix,
        quadratic_prefix,
        entropy,
        delta,
        0,
        horizon,
        output_denominator,
        interval_cache,
    )
    b1_selected = _select_candidate(b1_candidates)
    b2_atom_rows: list[dict[str, Any]] = []
    b2_selected_by_time: list[dict[str, Any]] = []
    b3_atom_rows: list[dict[str, Any]] = []
    b3_selected_by_time: list[dict[str, Any]] = []
    for report_time in range(4, horizon + 1):
        fixed_candidates = _boundary_candidates(
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
        b2_selected_by_time.append(_select_candidate(fixed_candidates))

        anytime_candidates: list[
            tuple[Fraction, Fraction, Fraction, dict[str, Any]]
        ] = []
        for wake in wakes:
            if wake > report_time - 4:
                continue
            effective_delta = delta / ((wake + 1) * (wake + 2))
            anytime_candidates.extend(
                _boundary_candidates(
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
        b3_selected_by_time.append(_select_candidate(anytime_candidates))

    threshold = base_rate * (1 - base_rate)
    b2_crossing = _crossing(b2_selected_by_time, threshold)
    b3_crossing = _crossing(b3_selected_by_time, threshold)
    b3_selected = b3_selected_by_time[-1]
    b1_upper = parse_fraction(b1_selected["boundary_interval"]["upper"], "B1 upper")
    b3_upper = parse_fraction(b3_selected["boundary_interval"]["upper"], "B3 upper")
    b1_width = parse_fraction(b1_selected["excess_interval"]["upper"], "B1 width")
    b3_width = parse_fraction(b3_selected["excess_interval"]["upper"], "B3 width")
    width_ratio = b3_width / b1_width
    null_replay = _null_replay(
        protocol,
        monitor_predictions,
        posterior,
        prior,
        base_rate,
        threshold,
        width_ratio,
    )
    timestamp_control = _timestamp_assertion(observations)
    tripwire = _deliberately_leaked_tripwire(observations, expected_predictions)
    ablation = _future_feature_ablation(
        protocol, windows, accumulators, crowd
    )
    monitor_ids = [observations[index]["ifp_id"] for index in monitor]
    shuffled_sensitivity = _posthoc_shuffled_time_sensitivity(
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
    overall_verdict = _overall_preregistered_verdict(null_replay, leakage_tests)
    constant_monitor_mean = sum(monitor_losses[0], Fraction(0)) / horizon
    model_monitor_means = [sum(values, Fraction(0)) / horizon for values in monitor_losses]
    return {
        "artifact_status": ARTIFACT_STATUS,
        "anytime_boundary_rows": b3_atom_rows,
        "baselines": {
            "B1_fixed_time": {
                "atom_rows": [candidate[3] for candidate in b1_candidates],
                "declares_below_train_base_rate_brier": b1_upper < threshold,
                "selected": b1_selected,
            },
            "B2_naive_repeated_look": {
                "atom_rows": b2_atom_rows,
                "first_crossing": b2_crossing,
                "selected_by_time": b2_selected_by_time,
                "statistical_status": "invalid under repeated inspection; diagnostic only",
            },
            "B3_anytime_valid": {
                "first_crossing": b3_crossing,
                "selected_by_time": b3_selected_by_time,
            },
            "declaration_threshold": rational_text(threshold),
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
        "log_enclosure": {
            "method": "range-reduced atanh series with exact rational remainder bound",
            "output_denominator": output_denominator,
            "terms": LOG_TERMS,
        },
        "leakage_tests": leakage_tests,
        "models": MODEL_IDS,
        "monitor": {
            "model_empirical_brier": {
                model: rational_text(value)
                for model, value in zip(MODEL_IDS, model_monitor_means, strict=True)
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
            "constant_model_monitor_empirical_brier": rational_text(constant_monitor_mean),
            "informative_against_train_base_rate_brier": b3_upper < threshold,
            "nonvacuous_against_brier_loss_ceiling": b3_upper < 1,
            "train_base_rate_brier_threshold": rational_text(threshold),
        },
        "stream_sha256": sha256_bytes(canonical_json_bytes(stream)),
    }


def load_protocol(path: Path) -> tuple[dict[str, Any], bytes]:
    protocol_checker.validate(path)
    raw = path.read_bytes()
    protocol = parse_json(raw, "protocol")
    if raw != canonical_json_bytes(protocol):
        raise ReplayError("protocol must use canonical JSON bytes")
    catalog_ids = [row["id"] for row in protocol["model_catalog"]["models"]]
    if catalog_ids != MODEL_IDS:
        raise ReplayError(f"model catalog must be exactly {MODEL_IDS!r}")
    return protocol, raw


def verify_inputs(protocol: dict[str, Any], input_dir: Path) -> tuple[dict[str, Path], list[dict[str, Any]]]:
    files: dict[str, Path] = {}
    records: list[dict[str, Any]] = []
    for entry in protocol["dataset"]["files"]:
        path = input_dir / entry["filename"]
        if not path.is_file():
            raise ReplayError(f"missing pinned raw input: {path}")
        actual_md5 = file_digest(path, "md5")
        if actual_md5 != entry["md5"]:
            raise ReplayError(
                f"MD5 mismatch for {path.name}: expected {entry['md5']}, got {actual_md5}"
            )
        size = path.stat().st_size
        expected_size = entry["original_bytes_confirmed"]
        if expected_size is not None and size != expected_size:
            raise ReplayError(
                f"byte count mismatch for {path.name}: expected {expected_size}, got {size}"
            )
        files[entry["filename"]] = path
        records.append(
            {
                "bytes": size,
                "dataverse_id": entry["dataverse_id"],
                "filename": entry["filename"],
                "md5": actual_md5,
                "sha256": file_digest(path, "sha256"),
            }
        )
    return files, records


def _external_output_dir(path: Path) -> Path:
    result = path.resolve()
    try:
        result.relative_to(ROOT.resolve())
    except ValueError:
        return result
    raise ReplayError(f"output directory must be outside the repository: {result}")


def _protocol_commit(protocol_path: Path, protocol_raw: bytes) -> str:
    try:
        relative = protocol_path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as error:
        raise ReplayError("protocol must be a tracked repository file") from error
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%H", "--", relative],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReplayError("cannot resolve the committed protocol revision") from error
    commit = result.stdout.strip()
    if len(commit) != 40:
        raise ReplayError("protocol has no committed revision")
    try:
        frozen = subprocess.run(
            ["git", "show", f"{commit}:{relative}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReplayError("cannot read the committed protocol bytes") from error
    if frozen != protocol_raw:
        raise ReplayError("working protocol bytes differ from their latest committed revision")
    return commit


def _implementation_commit(paths: list[Path], protocol_commit: str) -> str:
    try:
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD^{commit}"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReplayError("cannot resolve the implementation commit") from error
    if len(commit) != 40 or any(character not in "0123456789abcdef" for character in commit):
        raise ReplayError("implementation commit is not lowercase 40-hex")
    try:
        dirty = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReplayError("cannot audit implementation checkout cleanliness") from error
    if dirty:
        raise ReplayError("implementation checkout must be clean before artifact generation")
    try:
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", protocol_commit, commit],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReplayError(
            "implementation commit does not descend from the protocol freeze"
        ) from error
    for path in paths:
        try:
            relative = path.resolve().relative_to(ROOT.resolve()).as_posix()
        except ValueError as error:
            raise ReplayError(f"implementation file is outside the repository: {path}") from error
        if not path.is_file():
            raise ReplayError(f"implementation file is absent: {path}")
        try:
            frozen = subprocess.run(
                ["git", "show", f"{commit}:{relative}"],
                cwd=ROOT,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            ).stdout
        except (OSError, subprocess.CalledProcessError) as error:
            raise ReplayError(
                f"implementation file is absent from commit {commit}: {relative}"
            ) from error
        if frozen != path.read_bytes():
            raise ReplayError(
                f"working implementation bytes differ from {commit}: {relative}"
            )
    return commit


def _commit_tree(commit: str) -> str:
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
        raise ReplayError(f"cannot resolve tree for commit {commit}") from error
    if len(tree) != 40 or any(character not in "0123456789abcdef" for character in tree):
        raise ReplayError("implementation tree is not lowercase 40-hex")
    return tree


def _manifest_file(role: str, name: str, raw: bytes) -> dict[str, Any]:
    return {"bytes": len(raw), "name": name, "role": role, "sha256": sha256_bytes(raw)}


def expected_artifacts(
    protocol_path: Path, input_dir: Path
) -> tuple[bytes, bytes, bytes]:
    protocol, protocol_raw = load_protocol(protocol_path)
    protocol_commit = _protocol_commit(protocol_path, protocol_raw)
    builder_path = Path(__file__).resolve()
    implementation_paths = [
        protocol_path,
        DEFAULT_PROTOCOL_MD,
        DEFAULT_PROTOCOL_CHECKER,
        DEFAULT_FETCHER,
        builder_path,
        DEFAULT_VERIFIER,
        DEFAULT_PROTOCOL_TEST,
        DEFAULT_TEST,
    ]
    implementation_commit = _implementation_commit(
        implementation_paths, protocol_commit
    )
    implementation_tree = _commit_tree(implementation_commit)
    raw_files, raw_records = verify_inputs(protocol, input_dir)
    windows, outcomes, question_audit = load_questions(protocol, raw_files["ifps.csv"])
    forecast_paths = [
        raw_files[entry["filename"]]
        for entry in protocol["dataset"]["files"]
        if entry["role"] == "individual_forecasts"
    ]
    allowed_event_types = set(
        protocol["prediction_before_outcome"]["survey_forecast_event_types"]["allowed"]
    )
    accumulators, forecast_audit = reduce_forecasts(
        windows, forecast_paths, allowed_event_types
    )
    denominator = int(protocol["quantization"]["denominator"])
    crowd, missingness = crowd_predictions(windows, accumulators, denominator)
    stream, numeric_predictions = assemble_stream(
        protocol,
        protocol_commit,
        implementation_commit,
        implementation_tree,
        sha256_bytes(protocol_raw),
        windows,
        outcomes,
        crowd,
        question_audit,
        forecast_audit,
        missingness,
    )
    stream_raw = canonical_json_bytes(stream)
    receipt = compute_receipt(
        protocol,
        stream,
        numeric_predictions,
        windows,
        accumulators,
        crowd,
    )
    receipt_raw = canonical_json_bytes(receipt)
    if not DEFAULT_VERIFIER.is_file():
        raise ReplayError(f"independent verifier is absent: {DEFAULT_VERIFIER}")
    manifest = {
        "artifact_status": ARTIFACT_STATUS,
        "dataset": {
            "license": protocol["dataset"]["license"],
            "persistent_id": protocol["dataset"]["persistent_id"],
            "raw_files": raw_records,
            "version": protocol["dataset"]["version"],
        },
        "files": [
            _manifest_file("protocol", protocol_path.name, protocol_raw),
            _manifest_file("builder", builder_path.name, builder_path.read_bytes()),
            _manifest_file(
                "independent_verifier", DEFAULT_VERIFIER.name, DEFAULT_VERIFIER.read_bytes()
            ),
            _manifest_file(
                "implementation_test", DEFAULT_TEST.name, DEFAULT_TEST.read_bytes()
            ),
            _manifest_file(
                "protocol_companion", DEFAULT_PROTOCOL_MD.name, DEFAULT_PROTOCOL_MD.read_bytes()
            ),
            _manifest_file(
                "protocol_checker", DEFAULT_PROTOCOL_CHECKER.name, DEFAULT_PROTOCOL_CHECKER.read_bytes()
            ),
            _manifest_file(
                "input_fetcher", DEFAULT_FETCHER.name, DEFAULT_FETCHER.read_bytes()
            ),
            _manifest_file(
                "protocol_test", DEFAULT_PROTOCOL_TEST.name, DEFAULT_PROTOCOL_TEST.read_bytes()
            ),
            _manifest_file("stream", STREAM_NAME, stream_raw),
            _manifest_file("receipt", RECEIPT_NAME, receipt_raw),
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


def _atomic_write(path: Path, raw: bytes) -> None:
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


def _check(path: Path, expected: bytes) -> None:
    if not path.is_file():
        raise ReplayError(f"expected artifact is absent: {path}")
    if path.read_bytes() != expected:
        raise ReplayError(f"artifact is stale or mutated: {path}")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        output = _external_output_dir(args.out)
        stream_raw, receipt_raw, manifest_raw = expected_artifacts(
            args.protocol.resolve(), args.inputs.resolve()
        )
        artifacts = {
            STREAM_NAME: stream_raw,
            RECEIPT_NAME: receipt_raw,
            MANIFEST_NAME: manifest_raw,
        }
        if args.check:
            for name, raw in artifacts.items():
                _check(output / name, raw)
        else:
            for name, raw in artifacts.items():
                _atomic_write(output / name, raw)
    except (OSError, KeyError, ReplayError, protocol_checker.ProtocolError) as error:
        print(f"ERROR: GJP Brier replay refused: {error}", file=sys.stderr)
        return 1
    action = "verified" if args.check else "wrote"
    print(f"{action} deterministic GJP Brier replay in {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
