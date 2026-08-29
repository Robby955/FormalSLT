#!/usr/bin/env python3
"""Generate split, kernel-checkable GJP pathwise Brier calculations."""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_gjp_brier_replay import MODEL_IDS  # noqa: E402
from scripts.generate_gjp_brier_lean_data import (  # noqa: E402
    MODEL_DECLARATIONS,
    LeanDataError,
    _extract,
    _rat,
)


DEFAULT_OUT_DIR = ROOT / "FormalSLT" / "Applications"
ROOT_MODULE = "GJPBrierMonitorReplayPathData"
BASE_MODULE = f"{ROOT_MODULE}Base"


def _camel(name: str) -> str:
    return name[0].upper() + name[1:]


def _loss_name(model_name: str, index: int) -> str:
    return f"observed{_camel(model_name)}Loss{index}"


def _prefix_name(model_name: str, length: int) -> str:
    return f"observed{_camel(model_name)}LossPrefix{length}"


def _predictor_name(model_name: str, index: int) -> str:
    return f"observed{_camel(model_name)}Predictor{index}"


def _quadratic_name(model_name: str, length: int) -> str:
    return f"observed{_camel(model_name)}QuadraticPrefix{length}"


def _header(import_name: str, title: str) -> list[str]:
    return [
        "/-",
        "Copyright (c) 2026 Robby Sneiderman. All rights reserved.",
        "Released under MIT license as described in the file LICENSE.",
        "Authors: Robby Sneiderman",
        "-/",
        "",
        f"import FormalSLT.Applications.{import_name}",
        "import Mathlib.Tactic",
        "",
        "/-!",
        f"# {title}",
        "",
        "Generated from the hash-bound GJP stream and receipt. Small prefix",
        "recurrences keep kernel checking bounded in memory.",
        "-/",
        "",
        "open Finset",
        "open FormalSLT.AnytimeValid",
        "open FormalSLT.PACBayesKL",
        "open scoped BigOperators",
        "",
        f"namespace FormalSLT.Applications.{ROOT_MODULE}",
        "",
        "open FormalSLT.StochasticDynamics",
        "open GJPBrierMonitorReplayData",
        "",
        "noncomputable section",
        "",
        "set_option maxRecDepth 100000",
        "",
    ]


def render_base() -> str:
    lines = _header(
        "GJPBrierMonitorReplayReceipt", "Generated GJP pathwise Brier score"
    )
    lines.extend(
        [
            "abbrev Model := GJPBrierMonitorReplayData.Model",
            "",
            "def ratToReal (q : Rat) : Real := Rat.cast q",
            "",
            "def boolValue : Bool → Real",
            "  | false => 0",
            "  | true => 1",
            "",
            "def monitorPrediction (model : Model) (n : Nat) : Real :=",
            "  max 0 (min 1 (ratToReal (monitorPredictionQ model n)))",
            "",
            "theorem monitorPrediction_mem_Icc (model : Model) (n : Nat) :",
            "    monitorPrediction model n ∈ Set.Icc (0 : Real) 1 := by",
            "  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩",
            "",
            "def monitorBrierScore (model : Model) : TrajectoryScore Bool :=",
            "  fun n _prefix outcome =>",
            "    (monitorPrediction model n - boolValue outcome) ^ 2",
            "",
            "theorem monitorBrierScore_mem_Icc :",
            "    ∀ model n u outcome,",
            "      monitorBrierScore model n u outcome ∈ Set.Icc (0 : Real) 1 := by",
            "  intro model n u outcome",
            "  rcases monitorPrediction_mem_Icc model n with ⟨hp0, hp1⟩",
            "  cases outcome <;> simp only [monitorBrierScore, boolValue] <;>",
            "    constructor",
            "  · positivity",
            "  · nlinarith",
            "  · positivity",
            "  · nlinarith",
            "",
            "end",
            "",
            f"end FormalSLT.Applications.{ROOT_MODULE}",
            "",
        ]
    )
    return "\n".join(lines)


def render_model(data: dict[str, object], model: str) -> str:
    model_name, _pattern = MODEL_DECLARATIONS[model]
    losses = data["losses"][model]
    prefixes = data["prefixes"][model]
    quadratic_prefixes = data["quadratic_prefixes"][model]
    lines = _header(BASE_MODULE, f"Generated GJP path calculation: {model}")

    for index, loss in enumerate(losses):
        lines.extend(
            [
                f"theorem {_loss_name(model_name, index)} :",
                "    observedTrajectoryScore",
                f"        (monitorBrierScore {model_name}) {index} replayPath =",
                f"      ratToReal {_rat(loss)} := by",
                "  norm_num [observedTrajectoryScore, monitorBrierScore,",
                "    monitorPrediction, monitorPredictionQ, monitorPredictionArrayQ,",
                "    replayPath, monitorOutcome, monitorOutcomes, boolValue, ratToReal,",
                f"    {model_name}PredictionsQ]",
                "",
            ]
        )

    lines.extend(
        [
            f"theorem {_prefix_name(model_name, 0)} :",
            "    (∑ i ∈ Finset.range 0, observedTrajectoryScore",
            f"        (monitorBrierScore {model_name}) i replayPath) = ratToReal 0 := by",
            "  norm_num [ratToReal]",
            "",
        ]
    )
    for length in range(1, len(losses) + 1):
        index = length - 1
        lines.extend(
            [
                f"theorem {_prefix_name(model_name, length)} :",
                f"    (∑ i ∈ Finset.range {length}, observedTrajectoryScore",
                f"        (monitorBrierScore {model_name}) i replayPath) =",
                f"      ratToReal {_rat(prefixes[length])} := by",
                "  rw [Finset.sum_range_succ,",
                f"    {_prefix_name(model_name, length - 1)},",
                f"    {_loss_name(model_name, index)}]",
                "  norm_num [ratToReal]",
                "",
            ]
        )

    for index in range(len(losses)):
        predictor = Fraction(1, 2) if index == 0 else prefixes[index] / index
        lines.extend(
            [
                f"theorem {_predictor_name(model_name, index)} :",
                "    forwardPredictorProcess",
                "        (observedTrajectoryScore",
                f"          (monitorBrierScore {model_name})) {index} replayPath =",
                f"      ratToReal {_rat(predictor)} := by",
            ]
        )
        if index == 0:
            lines.extend(
                [
                    "  norm_num [forwardPredictorProcess, forwardPredictor, ratToReal]",
                    "",
                ]
            )
        else:
            lines.extend(
                [
                    "  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean",
                    "  rw [if_neg (by norm_num),",
                    f"    {_prefix_name(model_name, index)}]",
                    "  norm_num [ratToReal]",
                    "",
                ]
            )

    lines.extend(
        [
            f"theorem {_quadratic_name(model_name, 0)} :",
            "    (∑ i ∈ Finset.range 0,",
            "      (observedTrajectoryScore",
            f"          (monitorBrierScore {model_name}) i replayPath -",
            "        forwardPredictorProcess",
            "          (observedTrajectoryScore",
            f"            (monitorBrierScore {model_name})) i replayPath) ^ 2) =",
            "      ratToReal 0 := by",
            "  norm_num [ratToReal]",
            "",
        ]
    )
    for length in range(1, len(losses) + 1):
        index = length - 1
        lines.extend(
            [
                f"theorem {_quadratic_name(model_name, length)} :",
                f"    (∑ i ∈ Finset.range {length},",
                "      (observedTrajectoryScore",
                f"          (monitorBrierScore {model_name}) i replayPath -",
                "        forwardPredictorProcess",
                "          (observedTrajectoryScore",
                f"            (monitorBrierScore {model_name})) i replayPath) ^ 2) =",
                f"      ratToReal {_rat(quadratic_prefixes[length])} := by",
                "  rw [Finset.sum_range_succ,",
                f"    {_quadratic_name(model_name, length - 1)},",
                f"    {_loss_name(model_name, index)},",
                f"    {_predictor_name(model_name, index)}]",
                "  norm_num [ratToReal]",
                "",
            ]
        )

    lines.extend(
        [
            "end",
            "",
            f"end FormalSLT.Applications.{ROOT_MODULE}",
            "",
        ]
    )
    return "\n".join(lines)


def render_root() -> str:
    imports = [
        f"import FormalSLT.Applications.{ROOT_MODULE}{_camel(MODEL_DECLARATIONS[m][0])}"
        for m in MODEL_IDS
    ]
    return "\n".join(imports + [""])


def outputs(stream_raw: bytes, receipt_raw: bytes, out_dir: Path) -> dict[Path, str]:
    data, _receipt = _extract(stream_raw, receipt_raw)
    result = {
        out_dir / f"{BASE_MODULE}.lean": render_base(),
        out_dir / f"{ROOT_MODULE}.lean": render_root(),
    }
    for model in MODEL_IDS:
        name = MODEL_DECLARATIONS[model][0]
        result[out_dir / f"{ROOT_MODULE}{_camel(name)}.lean"] = render_model(
            data, model
        )
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stream", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = outputs(
        args.stream.read_bytes(), args.receipt.read_bytes(), args.out_dir
    )
    if args.check:
        for path, content in expected.items():
            if not path.exists() or path.read_text() != content:
                raise LeanDataError(f"generated Lean path data differs from {path}")
        print(f"verified {len(expected)} generated GJP Lean path modules")
        return 0
    for path, content in expected.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    print(f"wrote {len(expected)} generated GJP Lean path modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
