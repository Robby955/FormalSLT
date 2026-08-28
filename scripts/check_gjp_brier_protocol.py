#!/usr/bin/env python3
"""Fail-closed checker for the prospective real-data Brier monitor protocol.

This checker validates a protocol document only.  It must not download the
dataset, build a stream, compute a risk, or write any artifact.  Validation
fails if any path reserved for a prospective output already exists, so a
commit that carries the protocol cannot also carry its result.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROTOCOL = (
    ROOT / "applications" / "brier_monitor" / "realdata" / "gjp-brier-protocol-v1.json"
)

ARTIFACT_STATUS = "PROSPECTIVE PROTOCOL ONLY - NO STREAM, RECEIPT, OR RESULT"
PROTOCOL_VERSION = "gjp-brier-monitor-protocol-v1.1"
SCHEMA_VERSION = "formalslt.brier-monitor.realdata-preregistration.v1"
PERSISTENT_ID = "doi:10.7910/DVN/BPCDH5"
SAFETY_AMENDMENT_IDS = [
    "gjp-temporal-window-amendment-2026-08-28",
    "gjp-rational-posterior-amendment-2026-08-28",
]
MD5_PATTERN = re.compile(r"\A[0-9a-f]{32}\Z")

EXPECTED_ROUNDING = {
    "confidence_log": "up",
    "denominator_suffix_length_times_tilt": "exact",
    "empirical_suffix_risk": "exact",
    "kl_divergence": "up",
    "psi": "up",
    "suffix_quadratic_variation": "exact",
}

EXPECTED_LEAKAGE_TESTS = {
    "deliberately_leaked_tripwire",
    "future_feature_ablation",
    "outcome_shuffle_null",
    "shuffled_time_control",
    "timestamp_assertion",
}


class ProtocolError(ValueError):
    """Raised when the protocol document violates the contract."""


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


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise ProtocolError(f"{where} must be {expected!r}, got {actual!r}")


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ProtocolError(f"{where} must be an object")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ProtocolError(f"{where} must be an array")
    return value


def _fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise ProtocolError(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ProtocolError(f"invalid rational at {where}: {value!r}") from error
    text = (
        str(result.numerator)
        if result.denominator == 1
        else f"{result.numerator}/{result.denominator}"
    )
    if text != value:
        raise ProtocolError(f"noncanonical rational at {where}: {value!r}")
    return result


def _power_of_ten(value: Any, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ProtocolError(f"{where} must be a positive integer")
    probe = value
    while probe % 10 == 0:
        probe //= 10
    if probe != 1:
        raise ProtocolError(f"{where} must be a power of ten, got {value}")
    return value


def max_geometric_atom(suffix_length: int) -> int:
    """Mirror finiteTrajectorySleepingSuffixVarianceMaxIndex in plain arithmetic.

    Lean reads ``(Nat.log 4 (n - w)).pred + 2``.  Nothing here compiles Lean;
    this is an arithmetic restatement used only to check the declared grid is
    admissible.
    """

    log_four = 0
    threshold = 4
    while threshold <= suffix_length:
        log_four += 1
        threshold *= 4
    return max(log_four - 1, 0) + 2


def check_dataset(protocol: dict[str, Any]) -> None:
    dataset = _object(protocol["dataset"], "dataset")
    _exact(dataset["persistent_id"], PERSISTENT_ID, "dataset.persistent_id")
    _exact(dataset["version"], "1.0", "dataset.version")
    _exact(dataset["version_state"], "RELEASED", "dataset.version_state")
    _exact(dataset["license"], "CC0-1.0", "dataset.license")
    if "format=original" not in dataset["access_route"]:
        raise ProtocolError("dataset.access_route must request the original file bytes")
    files = _array(dataset["files"], "dataset.files")
    if len(files) != 6:
        raise ProtocolError("dataset.files must pin exactly six files")
    seen_ids: set[int] = set()
    seen_names: set[str] = set()
    for index, entry in enumerate(files):
        row = _object(entry, f"dataset.files[{index}]")
        identifier = row["dataverse_id"]
        if isinstance(identifier, bool) or not isinstance(identifier, int) or identifier <= 0:
            raise ProtocolError(f"dataset.files[{index}].dataverse_id must be a positive integer")
        if identifier in seen_ids:
            raise ProtocolError(f"duplicate dataverse_id {identifier}")
        seen_ids.add(identifier)
        name = row["filename"]
        if not isinstance(name, str) or not name or name in seen_names:
            raise ProtocolError(f"dataset.files[{index}].filename is empty or duplicated")
        seen_names.add(name)
        if not MD5_PATTERN.match(str(row["md5"])):
            raise ProtocolError(f"dataset.files[{index}].md5 must be 32 lowercase hex characters")
    if not any(row["role"] == "questions_and_outcomes" for row in files):
        raise ProtocolError("dataset.files must pin the questions and outcomes file")
    if sum(1 for row in files if row["role"] == "individual_forecasts") != 4:
        raise ProtocolError("dataset.files must pin four individual-forecast files")
    if sum(1 for row in files if row["role"] == "survey_forecast_codebook") != 1:
        raise ProtocolError("dataset.files must pin the survey forecast codebook")


def check_split(protocol: dict[str, Any]) -> int:
    disclosure = _object(protocol["preregistration_disclosure"], "preregistration_disclosure")
    aggregates = _object(
        disclosure["ifps_aggregates_inspected"], "preregistration_disclosure.ifps_aggregates_inspected"
    )
    total = aggregates["binary_resolved_count"]
    marginal = _object(aggregates["outcome_marginal"], "outcome_marginal")
    if marginal["a"] + marginal["b"] != total:
        raise ProtocolError("disclosed outcome marginal does not sum to the disclosed question count")
    if disclosure["no_forecast_value_joined_to_any_outcome"] is not True:
        raise ProtocolError("the disclosure must assert no forecast value was joined to an outcome")
    if disclosure["no_per_question_outcome_read"] is not True:
        raise ProtocolError("the disclosure must assert no per-question outcome was read")

    split = _object(protocol["chronological_split"], "chronological_split")
    if set(split) != {"train", "calibration", "monitor"}:
        raise ProtocolError("chronological_split must declare train, calibration, and monitor")
    eligibility = _object(
        protocol["eligibility_after_temporal_amendment"],
        "eligibility_after_temporal_amendment",
    )
    if eligibility["candidate_count"] != total:
        raise ProtocolError("eligibility candidate count must match the disclosed question count")
    excluded = _array(eligibility["excluded_ifp_ids"], "excluded_ifp_ids")
    if len(excluded) != eligibility["excluded_no_eligible_forecast_count"]:
        raise ProtocolError("excluded IFP ids must match the no-eligible-forecast count")
    if eligibility["included_count"] + len(excluded) != total:
        raise ProtocolError("included and excluded question counts must partition the candidates")
    counted = sum(_object(split[name], name)["expected_count"] for name in split)
    if counted != eligibility["included_count"]:
        raise ProtocolError(
            f"split expected counts sum to {counted}, not the eligible "
            f"{eligibility['included_count']} questions"
        )
    if eligibility["split_counts"] != {
        name: split[name]["expected_count"] for name in ("calibration", "monitor", "train")
    }:
        raise ProtocolError("eligibility split counts must match the chronological split")
    if split["train"]["date_closed_through"] >= split["calibration"]["date_closed_from"]:
        raise ProtocolError("train and calibration windows overlap")
    if split["calibration"]["date_closed_through"] >= split["monitor"]["date_closed_from"]:
        raise ProtocolError("calibration and monitor windows overlap")
    if split["monitor"]["date_closed_through"] is not None:
        raise ProtocolError("the monitor window must stay open-ended")
    return int(split["monitor"]["expected_count"])


def check_catalog(protocol: dict[str, Any]) -> None:
    catalog = _object(protocol["model_catalog"], "model_catalog")
    models = _array(catalog["models"], "model_catalog.models")
    identifiers = [_object(m, "model")["id"] for m in models]
    if len(set(identifiers)) != len(identifiers):
        raise ProtocolError("model identifiers must be unique")
    prior = [_fraction(v, f"prior[{i}]") for i, v in enumerate(_array(catalog["prior"], "prior"))]
    if len(prior) != len(models):
        raise ProtocolError("prior length must match the model catalog")
    if any(weight <= 0 for weight in prior) or sum(prior, Fraction(0)) != 1:
        raise ProtocolError("prior must be a full-support probability mass function")
    if catalog["extremization_exponent_is_tuned"] is not False:
        raise ProtocolError("the extremization exponent must be declared untuned")

    posterior = _object(protocol["posterior_rule"], "posterior_rule")
    if posterior["frozen_before_monitor_split"] is not True:
        raise ProtocolError("the posterior must be frozen before the monitor split")
    _exact(posterior["computed_on"], "calibration split only", "posterior_rule.computed_on")
    _fraction(posterior["learning_rate_eta"], "posterior_rule.learning_rate_eta")
    _exact(posterior["decimal_precision"], 80, "posterior_rule.decimal_precision")
    _exact(
        posterior["decimal_rounding"],
        "ROUND_HALF_EVEN",
        "posterior_rule.decimal_rounding",
    )
    _exact(
        posterior["quantization_denominator"],
        10**15,
        "posterior_rule.quantization_denominator",
    )
    if "largest-remainder" not in posterior["quantization_rule"]:
        raise ProtocolError("the posterior must use the pinned largest-remainder quantization")


def check_quantization(protocol: dict[str, Any]) -> None:
    quant = _object(protocol["quantization"], "quantization")
    denominator = _power_of_ten(quant["denominator"], "quantization.denominator")
    loss = _power_of_ten(quant["loss_denominator"], "quantization.loss_denominator")
    _power_of_ten(quant["output_grid_denominator"], "quantization.output_grid_denominator")
    if loss != denominator * denominator:
        raise ProtocolError("the loss denominator must be the square of the forecast denominator")
    if quant["monitored_forecaster_is_the_quantized_forecaster"] is not True:
        raise ProtocolError(
            "the monitored forecaster must be the quantized forecaster; otherwise a quantization "
            "residual has to be carried into the bound and is not declared here"
        )
    rounding = _object(quant["rounding_directions"], "quantization.rounding_directions")
    if rounding != EXPECTED_ROUNDING:
        raise ProtocolError(
            "rounding directions must be exactly "
            f"{EXPECTED_ROUNDING!r}; every inexact quantity entering the numerator rounds up"
        )


def check_confidence(protocol: dict[str, Any], monitor_count: int) -> list[tuple[int, int]]:
    contract = _object(protocol["confidence_contract"], "confidence_contract")
    delta = _fraction(contract["delta"], "confidence_contract.delta")
    if not 0 < delta <= 1:
        raise ProtocolError("delta must lie in (0,1]")
    wakes = _array(contract["wake_grid"], "confidence_contract.wake_grid")
    if not wakes or wakes != sorted(set(wakes)):
        raise ProtocolError("the wake grid must be nonempty and strictly increasing")
    if contract["wake_shopping_outside_grid_voids_the_allocation"] is not True:
        raise ProtocolError("the contract must void allocations for wakes outside the grid")
    grid: list[tuple[int, int]] = []
    for wake in wakes:
        if isinstance(wake, bool) or not isinstance(wake, int) or wake < 0:
            raise ProtocolError("every wake must be a nonnegative integer")
        suffix = monitor_count - wake
        if suffix < 4:
            raise ProtocolError(
                f"wake {wake} leaves a suffix of {suffix} observations, below the admitted four"
            )
        grid.append((wake, max_geometric_atom(suffix) + 1))
    return grid


def check_lean_binding(protocol: dict[str, Any]) -> None:
    binding = _object(protocol["lean_binding"], "lean_binding")
    example = ROOT / str(binding["required_example_path"])
    if binding["certified"] is not False:
        raise ProtocolError("the protocol may not declare itself certified")
    if example.exists():
        raise ProtocolError(
            f"{binding['required_example_path']} already exists; a prospective protocol commit "
            "may not carry the instantiation it is preregistering"
        )
    if not str(binding["open_obligation"]).strip():
        raise ProtocolError("the open Lean obligation must be stated")


def check_fresh_outputs(protocol: dict[str, Any]) -> None:
    for relative in _array(protocol["fresh_output_paths"], "fresh_output_paths"):
        candidate = (ROOT / str(relative)).resolve()
        try:
            candidate.relative_to(ROOT.resolve())
        except ValueError as error:
            raise ProtocolError(f"{relative} escapes the repository root") from error
        if candidate.exists():
            raise ProtocolError(
                f"reserved prospective output already exists: {relative}"
            )


def check_leakage_tests(protocol: dict[str, Any]) -> None:
    tests = _array(protocol["leakage_tests"], "leakage_tests")
    identifiers = {_object(test, "leakage test")["id"] for test in tests}
    if identifiers != EXPECTED_LEAKAGE_TESTS:
        raise ProtocolError(
            f"leakage tests must be exactly {sorted(EXPECTED_LEAKAGE_TESTS)}, got {sorted(identifiers)}"
        )
    for test in tests:
        if not str(test["fails_when"]).strip():
            raise ProtocolError(f"leakage test {test['id']} must state its failure condition")
    timestamp_test = next(test for test in tests if test["id"] == "timestamp_assertion")
    if "effective_cutoff" not in timestamp_test["fails_when"]:
        raise ProtocolError("the timestamp assertion must enforce the amended effective cutoff")


def check_prediction_cutoff(protocol: dict[str, Any]) -> None:
    before = _object(protocol["prediction_before_outcome"], "prediction_before_outcome")
    _exact(
        before["effective_cutoff_formula"],
        "min(date_suspend, start-of-date_closed)",
        "prediction_before_outcome.effective_cutoff_formula",
    )
    _exact(
        before["forecast_window_fields"],
        ["date_start", "date_suspend", "date_closed"],
        "prediction_before_outcome.forecast_window_fields",
    )
    if before["receipt_records_source_window"] is not True:
        raise ProtocolError("the receipt must record date_start, date_suspend, and date_closed")
    if before["reduction_function_accepts_outcome_argument"] is not False:
        raise ProtocolError("the reduction function must not accept an outcome argument")
    if before["receipt_records_per_observation_max_consumed_timestamp"] is not True:
        raise ProtocolError("the receipt must record the maximum consumed timestamp per observation")
    if before["receipt_records_per_observation_min_consumed_timestamp"] is not True:
        raise ProtocolError("the receipt must record the minimum consumed timestamp per observation")
    _exact(
        before["rule"],
        "every consumed forecast timestamp satisfies date_start <= timestamp < effective_cutoff",
        "prediction_before_outcome.rule",
    )
    event_types = _object(
        before["survey_forecast_event_types"],
        "prediction_before_outcome.survey_forecast_event_types",
    )
    _exact(event_types["allowed"], [0, 1, 2, 4], "survey_forecast_event_types.allowed")
    if "fail closed" not in event_types["policy"]:
        raise ProtocolError("unknown survey forecast event types must fail closed")
    _exact(
        before["same_user_last_event_tie_break"],
        ["timestamp", "numeric forecast_id", "source year", "source line"],
        "prediction_before_outcome.same_user_last_event_tie_break",
    )

    amendments = _array(protocol["protocol_amendments"], "protocol_amendments")
    if len(amendments) != len(SAFETY_AMENDMENT_IDS):
        raise ProtocolError("the protocol must carry both prospective safety amendments")
    for index, expected_id in enumerate(SAFETY_AMENDMENT_IDS):
        amendment = _object(amendments[index], f"protocol_amendments[{index}]")
        _exact(amendment["id"], expected_id, f"protocol_amendments[{index}].id")
        if amendment["result_existed_before_amendment"] is not False:
            raise ProtocolError("every safety amendment must precede every numerical result")
    _exact(
        amendments[0]["replacement_rule"],
        "date_start <= forecast timestamp < min(date_suspend, start-of-date_closed)",
        "protocol_amendments[0].replacement_rule",
    )
    if "10^15 simplex" not in amendments[1]["replacement_rule"]:
        raise ProtocolError("the posterior amendment must pin the rational simplex rule")


def validate(path: Path) -> list[tuple[int, int]]:
    raw = path.read_bytes()
    protocol = _object(
        json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        ),
        "protocol",
    )
    if raw != canonical_json_bytes(protocol):
        raise ProtocolError("the protocol must use canonical JSON bytes")
    _exact(protocol["artifact_status"], ARTIFACT_STATUS, "artifact_status")
    _exact(protocol["protocol_version"], PROTOCOL_VERSION, "protocol_version")
    _exact(protocol["schema_version"], SCHEMA_VERSION, "schema_version")
    if not _array(protocol["nonclaims"], "nonclaims"):
        raise ProtocolError("the protocol must carry its nonclaims")
    if not _array(protocol["rejected_datasets"], "rejected_datasets"):
        raise ProtocolError("the protocol must record the datasets it rejected and why")
    if not _array(protocol["failure_cases"], "failure_cases"):
        raise ProtocolError("the protocol must record when it produces a misleading result")

    check_dataset(protocol)
    monitor_count = check_split(protocol)
    check_catalog(protocol)
    check_quantization(protocol)
    grid = check_confidence(protocol, monitor_count)
    check_lean_binding(protocol)
    check_fresh_outputs(protocol)
    check_leakage_tests(protocol)
    check_prediction_cutoff(protocol)
    return grid


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        grid = validate(args.protocol)
    except (OSError, KeyError, ProtocolError) as error:
        print(f"ERROR: GJP Brier protocol refused: {error}", file=sys.stderr)
        return 1
    described = ", ".join(f"wake {wake}: {atoms} atoms" for wake, atoms in grid)
    print(f"prospective GJP Brier protocol validated ({described})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
