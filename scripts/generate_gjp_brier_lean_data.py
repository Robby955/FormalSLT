#!/usr/bin/env python3
"""Generate compact Lean certificate inputs for the verified GJP replay.

The source stream and receipt stay outside the repository.  This script checks
their binding, recomputes the selected posterior statistics using exact
rationals from all 175 monitor observations, and emits the exact per-model and
posterior summaries needed by Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_gjp_brier_replay import (  # noqa: E402
    MODEL_IDS,
    parse_fraction,
    parse_json,
)


DEFAULT_OUT = (
    ROOT
    / "FormalSLT"
    / "Applications"
    / "GJPBrierMonitorReplayData.lean"
)

MODEL_DECLARATIONS = {
    "constant-train-baserate": ("constantTrainBaseRate", "false, false"),
    "first-week-mean": ("firstWeekMean", "false, true"),
    "final-consensus-median": ("finalConsensusMedian", "true, false"),
    "extremized-final-consensus": ("extremizedFinalConsensus", "true, true"),
}


class LeanDataError(ValueError):
    """Raised when replay artifacts cannot support the generated Lean data."""


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _rat(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator} : Rat)"
    return f"(({value.numerator} : Rat) / {value.denominator})"


def _bool(value: bool) -> str:
    return "true" if value else "false"


def _require_mapping(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise LeanDataError(f"{where} must be an object")
    return value


def _monitor_rows(stream: dict[str, Any]) -> list[dict[str, Any]]:
    observations = stream.get("observations")
    if not isinstance(observations, list):
        raise LeanDataError("stream observations must be an array")
    rows = [
        _require_mapping(row, f"observations[{index}]")
        for index, row in enumerate(observations)
        if isinstance(row, dict) and row.get("split") == "monitor"
    ]
    if len(rows) != 175:
        raise LeanDataError(f"expected 175 monitor rows, found {len(rows)}")
    return rows


def _prefix_sums(values: list[Fraction]) -> list[Fraction]:
    result = [Fraction(0)]
    for value in values:
        result.append(result[-1] + value)
    return result


def _quadratic_prefix_sums(
    losses: list[Fraction], prefixes: list[Fraction]
) -> list[Fraction]:
    result = [Fraction(0)]
    for index, loss in enumerate(losses):
        predictor = Fraction(1, 2) if index == 0 else prefixes[index] / index
        result.append(result[-1] + (loss - predictor) ** 2)
    return result


def _extract(
    stream_raw: bytes, receipt_raw: bytes
) -> tuple[dict[str, Any], dict[str, Any]]:
    stream = _require_mapping(parse_json(stream_raw, "stream"), "stream")
    receipt = _require_mapping(parse_json(receipt_raw, "receipt"), "receipt")
    if receipt.get("stream_sha256") != _sha256(stream_raw):
        raise LeanDataError("receipt stream_sha256 does not bind the supplied stream")
    if receipt.get("artifact_status") != (
        "REAL-DATA REPLAY; ARITHMETIC NOT YET LEAN-INSTANTIATED"
    ):
        raise LeanDataError("unexpected source artifact status")

    rows = _monitor_rows(stream)
    outcomes: list[bool] = []
    predictions: dict[str, list[Fraction]] = {model: [] for model in MODEL_IDS}
    losses: dict[str, list[Fraction]] = {model: [] for model in MODEL_IDS}
    for index, row in enumerate(rows):
        outcome = row.get("outcome")
        if outcome not in (0, 1):
            raise LeanDataError(f"monitor row {index} has a nonbinary outcome")
        outcomes.append(bool(outcome))
        row_predictions = _require_mapping(
            row.get("predictions"), f"monitor row {index} predictions"
        )
        for model in MODEL_IDS:
            prediction = parse_fraction(
                row_predictions.get(model), f"monitor row {index} {model}"
            )
            if not 0 <= prediction <= 1:
                raise LeanDataError(f"monitor row {index} {model} is outside [0,1]")
            predictions[model].append(prediction)
            losses[model].append((prediction - outcome) ** 2)

    calibration = _require_mapping(receipt.get("calibration"), "calibration")
    posterior_record = _require_mapping(calibration.get("posterior"), "posterior")
    posterior_raw = _require_mapping(
        posterior_record.get("exact_rational_weights"), "posterior weights"
    )
    posterior = {
        model: parse_fraction(posterior_raw.get(model), f"posterior {model}")
        for model in MODEL_IDS
    }
    if sum(posterior.values(), Fraction(0)) != 1:
        raise LeanDataError("posterior weights do not sum to one")

    prefixes = {model: _prefix_sums(losses[model]) for model in MODEL_IDS}
    quadratic_prefixes = {
        model: _quadratic_prefix_sums(losses[model], prefixes[model])
        for model in MODEL_IDS
    }
    quadratics = {
        model: quadratic_prefixes[model][-1] for model in MODEL_IDS
    }
    horizon = len(rows)
    empirical = sum(
        posterior[model] * prefixes[model][-1] / horizon for model in MODEL_IDS
    )
    quadratic = sum(
        posterior[model] * quadratics[model] for model in MODEL_IDS
    )
    witness = _require_mapping(receipt.get("selected_witness"), "selected witness")
    if empirical != parse_fraction(
        witness.get("posterior_empirical_brier_risk"), "tracked empirical risk"
    ):
        raise LeanDataError("recomputed empirical risk does not match the receipt")
    if quadratic != parse_fraction(
        witness.get("suffix_predictor_quadratic_variation"),
        "tracked quadratic variation",
    ):
        raise LeanDataError("recomputed quadratic variation does not match the receipt")

    return (
        {
            "outcomes": outcomes,
            "predictions": predictions,
            "losses": losses,
            "prefixes": prefixes,
            "quadratic_prefixes": quadratic_prefixes,
            "quadratics": quadratics,
            "posterior": posterior,
            "empirical": empirical,
            "quadratic": quadratic,
        },
        receipt,
    )


def render(stream_raw: bytes, receipt_raw: bytes) -> str:
    data, receipt = _extract(stream_raw, receipt_raw)
    witness = _require_mapping(receipt["selected_witness"], "selected witness")
    verdict = _require_mapping(
        receipt["overall_preregistered_verdict"], "preregistered verdict"
    )
    lines = [
        "/-",
        "Copyright (c) 2026 Robby Sneiderman. All rights reserved.",
        "Released under MIT license as described in the file LICENSE.",
        "Authors: Robby Sneiderman",
        "-/",
        "",
        "import Mathlib.Data.Rat.Defs",
        "",
        "/-!",
        "# Generated GJP Brier-monitor replay data",
        "",
        "This module contains exact rational certificate inputs extracted from",
        "the externally replayed, hash-bound GJP artifacts. The generator",
        "recomputes these summaries from all 175 monitor observations before",
        "emitting this compact module. The accompanying receipt checks posterior",
        "aggregation and the real-valued endpoint arithmetic. The preregistered",
        "study verdict remains `FAIL` because one null win condition failed and",
        "the shuffled-time control is incomplete.",
        "-/",
        "",
        "namespace FormalSLT.Applications.GJPBrierMonitorReplayData",
        "",
        "abbrev Model := Bool × Bool",
        "",
        "abbrev constantTrainBaseRate : Model := (false, false)",
        "abbrev firstWeekMean : Model := (false, true)",
        "abbrev finalConsensusMedian : Model := (true, false)",
        "abbrev extremizedFinalConsensus : Model := (true, true)",
        "",
        f'abbrev streamSha256 : String := "{receipt["stream_sha256"]}"',
        f'abbrev receiptSha256 : String := "{_sha256(receipt_raw)}"',
        f'abbrev protocolSha256 : String := "{receipt["protocol_sha256"]}"',
        f'abbrev implementationCommit : String := "{receipt["implementation_commit"]}"',
        f'abbrev implementationTree : String := "{receipt["implementation_tree"]}"',
        "abbrev horizon : Nat := 175",
        "abbrev selectedWake : Nat := 0",
        "abbrev selectedTiltAtom : Nat := 0",
        "abbrev selectedTilt : Rat := ((1 : Rat) / 2)",
        f'abbrev preregisteredStatus : String := "{verdict["status"]}"',
        "",
        "abbrev priorQ (_model : Model) : Rat := 1 / 4",
        "",
        "/-- Monitor outcome at zero-based replay index. Values outside the",
        "hash-bound 175-observation prefix default to `false`. -/",
        "abbrev monitorOutcomes : Array Bool := #[",
    ]
    for outcome in data["outcomes"]:
        lines.append(f"  {_bool(outcome)},")
    lines.extend(
        [
            "]",
            "",
            "abbrev monitorOutcome (n : Nat) : Bool :=",
            "  monitorOutcomes.getD n false",
            "",
            "/-- Quantized forecast at zero-based replay index. Values outside",
            "the hash-bound monitor prefix default to zero. -/",
        ]
    )
    for model in MODEL_IDS:
        lean_name, _pattern = MODEL_DECLARATIONS[model]
        lines.append(f"abbrev {lean_name}PredictionsQ : Array Rat := #[")
        for prediction in data["predictions"][model]:
            lines.append(f"  {_rat(prediction)},")
        lines.extend(["]", ""])
    lines.extend(
        [
            "abbrev monitorPredictionArrayQ : Model → Array Rat",
        ]
    )
    for model in MODEL_IDS:
        lean_name, pattern = MODEL_DECLARATIONS[model]
        lines.append(f"  | ({pattern}) => {lean_name}PredictionsQ")
    lines.extend(
        [
            "",
            "abbrev monitorPredictionQ (model : Model) (n : Nat) : Rat :=",
            "  (monitorPredictionArrayQ model).getD n 0",
            "",
            "/-- Exact Brier loss at zero-based replay index. -/",
        ]
    )
    for model in MODEL_IDS:
        lean_name, _pattern = MODEL_DECLARATIONS[model]
        lines.append(f"abbrev {lean_name}BrierLossesQ : Array Rat := #[")
        for loss in data["losses"][model]:
            lines.append(f"  {_rat(loss)},")
        lines.extend(["]", ""])
    lines.extend(
        [
            "abbrev monitorBrierLossArrayQ : Model → Array Rat",
        ]
    )
    for model in MODEL_IDS:
        lean_name, pattern = MODEL_DECLARATIONS[model]
        lines.append(f"  | ({pattern}) => {lean_name}BrierLossesQ")
    lines.extend(
        [
            "",
            "abbrev monitorBrierLossQ (model : Model) (n : Nat) : Rat :=",
            "  (monitorBrierLossArrayQ model).getD n 0",
            "",
            "/-- Trajectory encoding used by the theorem instance: coordinate",
            "zero is the initial state and coordinate `k + 1` is monitor outcome `k`. -/",
            "abbrev replayPath : Nat → Bool",
            "  | 0 => false",
            "  | k + 1 => monitorOutcome k",
            "",
            "abbrev posteriorQ : Model → Rat",
        ]
    )
    for model in MODEL_IDS:
        _lean_name, pattern = MODEL_DECLARATIONS[model]
        lines.append(f"  | ({pattern}) => {_rat(data['posterior'][model])}")

    lines.extend(["", "abbrev monitorEmpiricalBrierQ : Model → Rat"])
    for model in MODEL_IDS:
        _lean_name, pattern = MODEL_DECLARATIONS[model]
        empirical = data["prefixes"][model][-1] / len(data["outcomes"])
        lines.append(f"  | ({pattern}) => {_rat(empirical)}")

    lines.extend(["", "abbrev monitorQuadraticVariationQ : Model → Rat"])
    for model in MODEL_IDS:
        _lean_name, pattern = MODEL_DECLARATIONS[model]
        lines.append(f"  | ({pattern}) => {_rat(data['quadratics'][model])}")

    lines.extend(
        [
            "",
            "abbrev posteriorEmpiricalBrierRisk : Rat :=",
            f"  {_rat(data['empirical'])}",
            "abbrev suffixPredictorQuadraticVariation : Rat :=",
            f"  {_rat(data['quadratic'])}",
            "abbrev selectedBoundaryLower : Rat :=",
            f"  {_rat(parse_fraction(witness['boundary_interval']['lower'], 'boundary lower'))}",
            "abbrev selectedBoundaryUpper : Rat :=",
            f"  {_rat(parse_fraction(witness['boundary_interval']['upper'], 'boundary upper'))}",
            "abbrev constantModelMonitorEmpiricalBrier : Rat :=",
            f"  {_rat(parse_fraction(witness['constant_model_monitor_empirical_brier'], 'constant model risk'))}",
            "abbrev trainBaseRateBrierThreshold : Rat :=",
            f"  {_rat(parse_fraction(witness['train_base_rate_brier_threshold'], 'base-rate threshold'))}",
            "abbrev reportedSelectionMarginLower : Rat :=",
            f"  {_rat(parse_fraction(witness['reported_selection_margin_lower'], 'selection margin'))}",
            "",
            "end FormalSLT.Applications.GJPBrierMonitorReplayData",
            "",
        ]
    )
    return "\n".join(lines)


def _self_test() -> None:
    if _rat(Fraction(-3, 7)) != "((-3 : Rat) / 7)":
        raise LeanDataError("negative rational rendering failed")
    if _rat(Fraction(5, 1)) != "(5 : Rat)":
        raise LeanDataError("integral rational rendering failed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stream", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        _self_test()
        print("GJP Lean-data generator self-test passed")
        return 0
    if args.stream is None or args.receipt is None:
        parser.error("--stream and --receipt are required unless --self-test is used")

    expected = render(args.stream.read_bytes(), args.receipt.read_bytes())
    if args.check:
        if not args.out.exists() or args.out.read_text() != expected:
            raise LeanDataError(f"generated Lean data differs from {args.out}")
        print(f"verified generated GJP Lean data at {args.out}")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(expected)
    print(f"wrote generated GJP Lean data to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
