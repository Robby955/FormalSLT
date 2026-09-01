from __future__ import annotations

import csv
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
import build_brier_monitor_uci357_certificate as builder  # noqa: E402


def test_hard_selection_is_deterministic_and_tie_broken() -> None:
    assert builder.choose_winner(
        {
            "constant_train_prevalence": 10,
            "logistic_all_sensor": 5,
        }
    ) == "logistic_all_sensor"
    assert builder.choose_winner(
        {
            "constant_train_prevalence": 5,
            "logistic_all_sensor": 5,
        }
    ) == "constant_train_prevalence"


def test_tracked_protocol_binds_evidence_and_stream() -> None:
    evidence_raw = builder.EVIDENCE.read_bytes()
    evidence = json.loads(evidence_raw)
    protocol = json.loads(builder.PROTOCOL.read_bytes())
    prediction_raw = builder.PREDICTIONS.read_bytes()

    assert evidence_raw == builder.canonical_json_bytes(evidence)
    assert builder.PROTOCOL.read_bytes() == builder.canonical_json_bytes(protocol)
    assert protocol["provenance"] == {
        "evidence_sha256": hashlib.sha256(evidence_raw).hexdigest(),
        "prediction_timing": "PRE_OUTCOME",
        "tier": "AUDITED",
    }
    assert evidence["data"]["prediction_stream_sha256"] == hashlib.sha256(
        prediction_raw
    ).hexdigest()
    assert evidence["artifact_status"] == "AUDITED RETROSPECTIVE DEMONSTRATION"
    assert evidence["selection"]["timing"] == "POST_DATA"
    assert evidence["selection"]["winner"] == "logistic_all_sensor"
    assert protocol["statistics"]["posterior"] == {
        "constant_train_prevalence": "0",
        "logistic_all_sensor": "1",
    }


def test_prediction_stream_replays_selection_totals() -> None:
    totals = {model_id: 0 for model_id in builder.MODEL_ORDER}
    previous_index = 0
    row_count = 0
    with builder.PREDICTIONS.open(newline="", encoding="ascii") as handle:
        reader = csv.DictReader(handle)
        assert reader.fieldnames == [
            "sequence_index",
            "outcome",
            "constant_train_prevalence_q",
            "logistic_all_sensor_q",
        ]
        for row_count, row in enumerate(reader, start=1):
            sequence_index = int(row["sequence_index"])
            outcome = int(row["outcome"])
            assert sequence_index == previous_index + 1
            assert outcome in (0, 1)
            previous_index = sequence_index
            for model_id in builder.MODEL_ORDER:
                prediction = int(row[builder.PREDICTION_COLUMNS[model_id]])
                assert 0 <= prediction <= 65_535
                totals[model_id] += (prediction - 65_535 * outcome) ** 2

    evidence = json.loads(builder.EVIDENCE.read_bytes())
    assert row_count == 8_224
    assert totals == evidence["selection"]["loss_numerator_sums"]
    assert builder.choose_winner(totals) == evidence["selection"]["winner"]


def test_source_bindings_are_current() -> None:
    evidence = json.loads(builder.EVIDENCE.read_bytes())
    for binding in evidence["source_bindings"].values():
        path = ROOT / binding["path"]
        assert path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == binding["sha256"]


def test_tracked_compact_certificate_is_bound_and_informative() -> None:
    certificate = json.loads(builder.CERTIFICATE.read_bytes())
    directory = builder.CERTIFICATE.parent

    assert certificate["formal_slt"]["commit"] == (
        "6c6101012f38b902d30582a963a911a20518bfc3"
    )
    assert certificate["data"]["observations"] == 8_224
    assert certificate["data"]["provenance"]["tier"] == "AUDITED"
    assert certificate["replay"]["independent_replay"] == "PASS"
    assert certificate["kernel"]["result"] == "PASS"
    assert certificate["statistics"]["posterior_empirical_brier_risk"] == (
        "2161547227007/35320733114400"
    )
    assert certificate["claim"] == {
        "confidence": "19/20",
        "quantity": "posterior-averaged encountered conditional prefix Brier risk",
        "upper_bound": "18317/250000",
    }
    assert Fraction(certificate["claim"]["upper_bound"]) < Fraction(3, 40)
    assert len(
        certificate["statistics"][
            "posterior_suffix_predictor_quadratic_variation_upper"
        ]
    ) < 40

    assert hashlib.sha256(
        (directory / certificate["kernel"]["checker"]).read_bytes()
    ).hexdigest() == certificate["kernel"]["checker_sha256"]
    assert hashlib.sha256(
        (directory / certificate["replay"]["preparation"]).read_bytes()
    ).hexdigest() == certificate["replay"]["preparation_sha256"]
    assert (directory / certificate["protocol"]["file"]).read_bytes() == (
        builder.PROTOCOL.read_bytes()
    )
