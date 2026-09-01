from __future__ import annotations

import sys
from pathlib import Path
from typing import NoReturn

import pytest
from fastapi.testclient import TestClient


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
import formalslt_brier_tabular as tabular  # noqa: E402
import formalslt_monitor_service as service  # noqa: E402


def protocol(input_format: str = "parquet") -> dict[str, object]:
    return {
        "analysis": "brier_monitor",
        "claim": {"quantity": tabular.CLAIM_QUANTITY},
        "data": {
            "input_format": input_format,
            "outcome_column": "outcome",
            "prediction_encoding": "scaled_integer",
            "prediction_scale": 100,
            "require_strict_time_order": True,
            "time_column": "time",
        },
        "models": [
            {"column": "prediction_0", "id": "model-0"},
            {"column": "prediction_1", "id": "model-1"},
        ],
        "protocol_id": "service-unit-test",
        "provenance": {
            "evidence_sha256": None,
            "prediction_timing": "PRE_OUTCOME",
            "tier": "DECLARED",
        },
        "schema_version": tabular.PROTOCOL_SCHEMA,
        "statistics": {
            "delta": "1/20",
            "posterior": {"model-0": "1", "model-1": "0"},
            "prior": {"model-0": "1/2", "model-1": "1/2"},
            "tilt": "1/2",
            "wake": 0,
        },
    }


def create_monitor(client: TestClient) -> str:
    response = client.post("/v1/monitors", json={"protocol": protocol()})
    assert response.status_code == 201, response.text
    return str(response.json()["monitor_id"])


def test_service_updates_are_transactional(tmp_path: Path) -> None:
    client = TestClient(service.create_app(tmp_path / "artifacts"))
    monitor_id = create_monitor(client)
    valid = {
        "time": 1,
        "outcome": 0,
        "predictions": {"model-0": 10, "model-1": 20},
    }
    assert (
        client.post(f"/v1/monitors/{monitor_id}/observations", json=valid).status_code
        == 200
    )
    invalid = {
        "time": 2,
        "outcome": 1,
        "predictions": {"model-0": 30, "model-1": 101},
    }
    response = client.post(f"/v1/monitors/{monitor_id}/observations", json=invalid)
    assert response.status_code == 422
    current = client.get(f"/v1/monitors/{monitor_id}").json()
    assert current["observations"] == 1
    assert current["snapshot"]["last_time"] == 1


def test_service_freezes_live_winner_and_issues_lean_certificate(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    client = TestClient(service.create_app(tmp_path / "artifacts"))
    monitor_id = create_monitor(client)
    for time, outcome in enumerate((1, 0, 0, 0), start=1):
        response = client.post(
            f"/v1/monitors/{monitor_id}/observations",
            json={
                "time": time,
                "outcome": outcome,
                "predictions": {"model-0": 0, "model-1": 100},
            },
        )
        assert response.status_code == 200, response.text

    frozen_response = client.post(f"/v1/monitors/{monitor_id}/freeze")
    assert frozen_response.status_code == 200, frozen_response.text
    frozen = frozen_response.json()
    assert frozen["selection"]["selected_model"] == "model-0"
    assert frozen["frozen_protocol"]["data"]["input_format"] == "csv"
    assert frozen["frozen_protocol"]["statistics"]["posterior"] == {
        "model-0": "1",
        "model-1": "0",
    }

    certificate_response = client.post(f"/v1/monitors/{monitor_id}/certify")
    assert certificate_response.status_code == 200, certificate_response.text
    issued = certificate_response.json()
    certificate = issued["certificate"]
    assert certificate["artifact_status"] == "CERTIFIED"
    assert certificate["kernel"]["result"] == "PASS"
    assert certificate["replay"]["independent_replay"] == "PASS"
    assert (
        certificate["protocol"]["sha256"]
        == issued["selection"]["selected_protocol_sha256"]
    )
    assert (
        certificate["data"]["normalized_stream_sha256"]
        == issued["selection"]["normalized_stream_sha256"]
    )

    def redundant_checker(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("cached certificate must not rerun issuance or Lean")

    monkeypatch.setattr(service.certificate_engine, "issue", redundant_checker)
    monkeypatch.setattr(service.certificate_engine, "verify", redundant_checker)
    repeated = client.post(f"/v1/monitors/{monitor_id}/certify")
    assert repeated.status_code == 200, repeated.text
    assert repeated.json() == issued

    retrieved = client.get(f"/v1/monitors/{monitor_id}/certificates/4")
    assert retrieved.status_code == 200, retrieved.text
    assert retrieved.json()["certificate_id"] == f"{monitor_id}:4"
