from __future__ import annotations

import json
import sys
from copy import deepcopy
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
import formalslt_brier_streaming as streaming  # noqa: E402
import formalslt_brier_tabular as tabular  # noqa: E402


UCI_PROTOCOL = ROOT / "applications/brier_monitor/uci357-certificate-protocol-v1.json"
UCI_PREDICTIONS = (
    ROOT / "applications/brier_monitor/generated/uci357-monitor-predictions-v1.csv"
)
UCI_CERTIFICATE = (
    ROOT / "applications/brier_monitor/generated/uci357-certificate-v1/certificate.json"
)


def protocol(models: int = 2) -> dict[str, object]:
    model_ids = [f"model-{index}" for index in range(models)]
    return {
        "analysis": "brier_monitor",
        "claim": {"quantity": tabular.CLAIM_QUANTITY},
        "data": {
            "input_format": "csv",
            "outcome_column": "outcome",
            "prediction_encoding": "scaled_integer",
            "prediction_scale": 100,
            "require_strict_time_order": True,
            "time_column": "time",
        },
        "models": [
            {"column": f"prediction_{index}", "id": model_id}
            for index, model_id in enumerate(model_ids)
        ],
        "protocol_id": "streaming-unit-test",
        "provenance": {
            "evidence_sha256": None,
            "prediction_timing": "PRE_OUTCOME",
            "tier": "DECLARED",
        },
        "schema_version": tabular.PROTOCOL_SCHEMA,
        "statistics": {
            "delta": "1/20",
            "posterior": {
                model_id: str(int(index == 0))
                for index, model_id in enumerate(model_ids)
            },
            "prior": {model_id: f"1/{models}" for model_id in model_ids},
            "tilt": "1/2",
            "wake": 0,
        },
    }


def write_protocol(tmp_path: Path, value: dict[str, object]) -> Path:
    path = tmp_path / "protocol.json"
    path.write_bytes(tabular.canonical_json_bytes(value))
    return path


def test_incremental_selection_switch_and_snapshot_scope(tmp_path: Path) -> None:
    monitor = streaming.StreamingBrierMonitor.from_protocol_path(
        write_protocol(tmp_path, protocol())
    )
    rows = [
        (1, 1, {"model-0": 0, "model-1": 100}),
        (2, 0, {"model-0": 0, "model-1": 100}),
        (3, 0, {"model-0": 0, "model-1": 100}),
        (4, 0, {"model-0": 0, "model-1": 100}),
    ]
    for time, outcome, predictions in rows:
        monitor.update(time=time, outcome=outcome, predictions=predictions)

    snapshot = monitor.snapshot()
    assert snapshot["artifact_status"] == streaming.STATUS
    assert snapshot["claim"]["status"] == "NOT_CERTIFIED"
    assert snapshot["selected"]["model_id"] == "model-0"
    assert snapshot["selection_switches"] == 1
    assert snapshot["selected"]["boundary_upper"] is not None
    assert snapshot["models"]["model-0"]["empirical_brier_risk"] == "1/4"
    assert snapshot["models"]["model-1"]["empirical_brier_risk"] == "3/4"


def test_invalid_update_is_transactional(tmp_path: Path) -> None:
    monitor = streaming.StreamingBrierMonitor.from_protocol_path(
        write_protocol(tmp_path, protocol())
    )
    monitor.update(
        time=1,
        outcome=0,
        predictions={"model-0": 10, "model-1": 20},
    )
    before = deepcopy(monitor.snapshot())

    with pytest.raises(streaming.StreamingMonitorError, match="must lie"):
        monitor.update(
            time=2,
            outcome=1,
            predictions={"model-0": 30, "model-1": 101},
        )

    assert monitor.snapshot() == before


def test_hundred_model_state_is_exact_and_compact(tmp_path: Path) -> None:
    monitor = streaming.StreamingBrierMonitor.from_protocol_path(
        write_protocol(tmp_path, protocol(models=100))
    )
    predictions = {model_id: index for index, model_id in enumerate(monitor.model_ids)}
    for time, outcome in enumerate((0, 1, 0, 1), start=1):
        monitor.update(time=time, outcome=outcome, predictions=predictions)

    snapshot = monitor.snapshot()
    assert len(snapshot["models"]) == 100
    assert snapshot["observations"] == 4
    assert snapshot["selected"]["boundary_upper"] is not None


def test_uci_streaming_preview_matches_checked_certificate() -> None:
    trace = streaming.replay(UCI_PROTOCOL, UCI_PREDICTIONS, every=512)
    certificate = json.loads(UCI_CERTIFICATE.read_bytes())
    selected = trace["final"]["selected"]
    protocol_posterior = trace["final"]["protocol_posterior"]

    assert trace["data"]["observations"] == 8_224
    assert len(trace["points"]) == 17
    assert selected["model_id"] == "logistic_all_sensor"
    assert selected["empirical_brier_risk"] == (
        certificate["statistics"]["posterior_empirical_brier_risk"]
    )
    assert selected["quadratic_variation_upper"] == (
        certificate["statistics"][
            "posterior_suffix_predictor_quadratic_variation_upper"
        ]
    )
    assert selected["boundary_upper"] == certificate["claim"]["upper_bound"]
    assert protocol_posterior == {
        "boundary_upper": certificate["claim"]["upper_bound"],
        "confidence_log_upper": certificate["statistics"][
            "confidence_log_upper"
        ],
        "empirical_brier_risk": certificate["statistics"][
            "posterior_empirical_brier_risk"
        ],
        "kl_upper": certificate["statistics"]["kl_upper"],
        "quadratic_variation_upper": certificate["statistics"][
            "posterior_suffix_predictor_quadratic_variation_upper"
        ],
    }
