from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from typing import Any

import pytest

from scripts import build_gjp_brier_replay as replay
from scripts import generate_gjp_brier_lean_data as generator
from scripts import generate_gjp_brier_lean_path as path_generator


def _rational(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fixture() -> tuple[bytes, bytes]:
    predictions = {
        "constant-train-baserate": Fraction(0),
        "first-week-mean": Fraction(1, 2),
        "final-consensus-median": Fraction(3, 4),
        "extremized-final-consensus": Fraction(1),
    }
    stream: dict[str, Any] = {
        "observations": [
            {
                "split": "monitor",
                "outcome": 1,
                "predictions": {
                    model: _rational(value)
                    for model, value in predictions.items()
                },
            }
            for _ in range(175)
        ]
    }
    stream_raw = (json.dumps(stream, sort_keys=True) + "\n").encode()
    posterior = {model: Fraction(1, 4) for model in replay.MODEL_IDS}
    losses = {model: (value - 1) ** 2 for model, value in predictions.items()}
    empirical = sum(
        posterior[model] * losses[model] for model in replay.MODEL_IDS
    )
    quadratic = sum(
        posterior[model] * (losses[model] - Fraction(1, 2)) ** 2
        for model in replay.MODEL_IDS
    )
    receipt = {
        "artifact_status": "REAL-DATA REPLAY; ARITHMETIC NOT YET LEAN-INSTANTIATED",
        "stream_sha256": hashlib.sha256(stream_raw).hexdigest(),
        "protocol_sha256": "a" * 64,
        "implementation_commit": "b" * 40,
        "implementation_tree": "c" * 40,
        "calibration": {
            "posterior": {
                "exact_rational_weights": {
                    model: _rational(value) for model, value in posterior.items()
                }
            }
        },
        "overall_preregistered_verdict": {"status": "FAIL"},
        "selected_witness": {
            "posterior_empirical_brier_risk": _rational(empirical),
            "suffix_predictor_quadratic_variation": _rational(quadratic),
            "boundary_interval": {"lower": "1/3", "upper": "2/5"},
            "constant_model_monitor_empirical_brier": "1",
            "train_base_rate_brier_threshold": "1/2",
            "reported_selection_margin_lower": "1/10",
        },
    }
    receipt_raw = (json.dumps(receipt, sort_keys=True) + "\n").encode()
    return stream_raw, receipt_raw


def test_compact_generator_recomputes_all_monitor_summaries() -> None:
    stream_raw, receipt_raw = _fixture()
    rendered = generator.render(stream_raw, receipt_raw)

    assert "abbrev horizon : Nat := 175" in rendered
    assert "abbrev monitorEmpiricalBrierQ : Model → Rat" in rendered
    assert "abbrev monitorQuadraticVariationQ : Model → Rat" in rendered
    assert "abbrev posteriorEmpiricalBrierRisk : Rat :=\n  ((21 : Rat) / 64)" in rendered
    assert (
        "abbrev suffixPredictorQuadraticVariation : Rat :=\n"
        "  ((193 : Rat) / 1024)"
    ) in rendered
    assert "abbrev monitorOutcomes : Array Bool" in rendered
    assert "abbrev monitorPredictionArrayQ : Model → Array Rat" in rendered
    assert "abbrev monitorBrierLossArrayQ : Model → Array Rat" in rendered
    assert len(rendered.splitlines()) < 1800


def test_path_generator_splits_kernel_calculations_by_model(tmp_path) -> None:
    stream_raw, receipt_raw = _fixture()
    rendered = path_generator.outputs(stream_raw, receipt_raw, tmp_path)

    assert len(rendered) == 6
    root = rendered[tmp_path / "GJPBrierMonitorReplayPathData.lean"]
    constant = rendered[
        tmp_path / "GJPBrierMonitorReplayPathDataConstantTrainBaseRate.lean"
    ]
    assert "GJPBrierMonitorReplayPathDataConstantTrainBaseRate" in root
    assert "observedConstantTrainBaseRateLossPrefix175" in constant
    assert "observedConstantTrainBaseRateQuadraticPrefix175" in constant
    assert "native_decide" not in constant


def test_generator_refuses_unbound_receipt() -> None:
    stream_raw, receipt_raw = _fixture()
    receipt = json.loads(receipt_raw)
    receipt["stream_sha256"] = "0" * 64
    tampered = (json.dumps(receipt, sort_keys=True) + "\n").encode()

    with pytest.raises(generator.LeanDataError, match="does not bind"):
        generator.render(stream_raw, tampered)
