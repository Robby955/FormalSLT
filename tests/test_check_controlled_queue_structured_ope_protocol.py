from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts import check_controlled_queue_structured_ope_protocol as checker


def _spec() -> dict[str, object]:
    return json.loads(checker.DEFAULT_INPUT.read_bytes())


def _write(tmp_path: Path, raw: bytes) -> Path:
    path = tmp_path / "structured-ope-protocol-v1.json"
    path.write_bytes(raw)
    return path


def _write_spec(tmp_path: Path, spec: dict[str, object]) -> Path:
    return _write(tmp_path, checker.canonical_json_bytes(spec))


def test_accepts_frozen_protocol_and_default_cli() -> None:
    assert checker.validate_protocol_file() == _spec()
    assert checker.main([]) == 0


def test_optional_input_accepts_byte_identical_copy(tmp_path: Path) -> None:
    path = _write(tmp_path, checker.DEFAULT_INPUT.read_bytes())
    assert checker.main(["--input", str(path)]) == 0


def test_rejects_duplicate_key(tmp_path: Path) -> None:
    raw = checker.DEFAULT_INPUT.read_bytes()
    line = (
        b'  "artifact_status": '
        b'"PROSPECTIVE PROTOCOL ONLY - NO TRACE OR RESULT",\n'
    )
    assert raw.count(line) == 1
    path = _write(tmp_path, raw.replace(line, line + line, 1))
    with pytest.raises(checker.ProtocolError, match="duplicate JSON key"):
        checker.validate_protocol_file(path)


def test_rejects_noncanonical_whitespace(tmp_path: Path) -> None:
    path = _write(tmp_path, checker.DEFAULT_INPUT.read_bytes() + b"\n")
    with pytest.raises(checker.ProtocolError, match="canonical JSON bytes"):
        checker.validate_protocol_file(path)


@pytest.mark.parametrize("value", [200000.0, float("nan"), float("inf")])
def test_rejects_float_and_nonfinite_numbers(tmp_path: Path, value: float) -> None:
    spec = _spec()
    spec["data_generation"]["horizon"] = value  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="floating-point|non-finite"):
        checker.validate_protocol_file(path)


def test_rejects_boolean_in_integer_field(tmp_path: Path) -> None:
    spec = _spec()
    spec["data_generation"]["horizon"] = True  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="data_generation.horizon"):
        checker.validate_protocol_file(path)


def test_rejects_noncanonical_rational(tmp_path: Path) -> None:
    spec = _spec()
    spec["data_generation"]["true_gamma"] = "298/400"  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="noncanonical rational"):
        checker.validate_protocol_file(path)


def test_rejects_binding_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["bindings"]["model_input"]["sha256"] = "0" * 64  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="bindings.model_input"):
        checker.validate_protocol_file(path)


def test_rejects_true_gamma_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["data_generation"]["true_gamma"] = "147/200"  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="frozen true gamma"):
        checker.validate_protocol_file(path)


def test_rejects_primary_tilt_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["confidence_contract"]["persistence_tilt"] = "1/32"  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="persistence_tilt"):
        checker.validate_protocol_file(path)


def test_rejects_prng_test_seed_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["data_generation"]["prng_contract"]["test_seed_hex"] = "0" * 64  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="test_seed_hex"):
        checker.validate_protocol_file(path)


def test_rejects_primary_threshold_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["primary_endpoint"]["decision_threshold"] = "1/9"  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="decision_threshold"):
        checker.validate_protocol_file(path)


def test_rejects_reporting_rule_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["chronology_contract"][
        "publish_raw_trace_counts_receipts_and_all_baselines_regardless_of_result"
    ] = False  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="publish_raw_trace"):
        checker.validate_protocol_file(path)


def test_rejects_osf_timestamp_contract_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["registration"]["timestamp_contract"][  # type: ignore[index]
        "integer_conversion"
    ] = "floor of the UTC instant to Unix seconds"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="timestamp_contract.integer_conversion"):
        checker.validate_protocol_file(path)


def test_rejects_beacon_round_fallback(tmp_path: Path) -> None:
    spec = _spec()
    spec["data_generation"]["prng_contract"][  # type: ignore[index]
        "beacon_round_on_fetch_or_verification_failure"
    ] = "use the next available verified round"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="beacon_round_on_fetch"):
        checker.validate_protocol_file(path)


def test_rejects_unconditional_threshold_prepromise(tmp_path: Path) -> None:
    spec = _spec()
    spec["primary_endpoint"][  # type: ignore[index]
        "threshold_corollary_contract"
    ] = "always prove endpoint < 1/10"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="threshold_corollary_contract"):
        checker.validate_protocol_file(path)


def test_rejects_post_beacon_histogram_theorem_design(tmp_path: Path) -> None:
    spec = _spec()
    spec["primary_endpoint"]["histogram_evaluation_contract"][  # type: ignore[index]
        "implementation_deadline"
    ] = "design the theorem after reading the trace"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="implementation_deadline"):
        checker.validate_protocol_file(path)


def test_rejects_baseline_confidence_allocation_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["matched_baselines"][1]["confidence_allocation"][  # type: ignore[index]
        "delta_risk"
    ] = "1/20"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="confidence_allocation.delta_risk"):
        checker.validate_protocol_file(path)


def test_rejects_baseline_formula_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["matched_baselines"][3][  # type: ignore[index]
        "eta_formula"
    ] = "replace the frozen formula after seeing the trace"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="eta_formula"):
        checker.validate_protocol_file(path)


def test_rejects_unchecked_baseline_confidence_claim(tmp_path: Path) -> None:
    spec = _spec()
    spec["matched_baselines"][3][  # type: ignore[index]
        "confidence_claim_until_theorem_exists"
    ] = "CHECKED_CONFIDENCE_CERTIFICATE"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="confidence_claim_until_theorem_exists"):
        checker.validate_protocol_file(path)


def test_rejects_hybrid_branch_selection_after_data(tmp_path: Path) -> None:
    spec = _spec()
    spec["receipt_arithmetic_contract"][  # type: ignore[index]
        "hybrid_bessel_upper"
    ] = "select the smaller affine or harmonic branch after reading the trace"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="hybrid_bessel_upper"):
        checker.validate_protocol_file(path)


def test_rejects_log_cost_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["receipt_arithmetic_contract"]["log_cost_upper"][  # type: ignore[index]
        "adaptive"
    ]["risk"] = "15"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="adaptive.risk"):
        checker.validate_protocol_file(path)


def test_rejects_causal_predictor_post_update_scoring(tmp_path: Path) -> None:
    spec = _spec()
    spec["reporting_contract"]["causal_predictor_contract"][  # type: ignore[index]
        "evaluation"
    ] = "update first and score the same transition afterward"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="causal_predictor_contract.evaluation"):
        checker.validate_protocol_file(path)


def test_rejects_oracle_potential_centering_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["matched_baselines"][0]["potential_contract"][  # type: ignore[index]
        "centering_reference"
    ] = "stationary_reference_selected_after_data"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="centering_reference"):
        checker.validate_protocol_file(path)


def test_rejects_oracle_drift_oscillation_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["matched_baselines"][0]["potential_contract"][  # type: ignore[index]
        "drift_oscillation"
    ]["formula"] = "maximum absolute drift selected after data"
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="drift_oscillation.formula"):
        checker.validate_protocol_file(path)


def test_rejects_reporting_row_reordering(tmp_path: Path) -> None:
    spec = _spec()
    rows = spec["reporting_contract"]["row_order"]  # type: ignore[index]
    rows[0], rows[1] = rows[1], rows[0]  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="reporting_contract.row_order"):
        checker.validate_protocol_file(path)


def test_rejects_support_and_allocation_drift(tmp_path: Path) -> None:
    spec = _spec()
    spec["adaptive_secondary"]["candidate_support"] = [  # type: ignore[index]
        "nominal",
        "low",
        "high",
    ]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="candidate_support"):
        checker.validate_protocol_file(path)


def test_rejects_appearance_of_declared_fresh_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source_root = checker.ROOT
    isolated_root = tmp_path / "repo"
    for binding in checker.EXPECTED_BINDINGS.values():
        relative = Path(binding["path"])
        destination = isolated_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((source_root / relative).read_bytes())

    monkeypatch.setattr(checker, "ROOT", isolated_root)
    protocol = _write(tmp_path, checker.DEFAULT_INPUT.read_bytes())
    checker.validate_protocol_file(protocol)

    appeared = isolated_root / checker.FRESH_OUTPUT_PATHS[0]
    appeared.parent.mkdir(parents=True, exist_ok=True)
    appeared.write_bytes(b"must fail closed")
    with pytest.raises(checker.ProtocolError, match="prospective output already exists"):
        checker.validate_protocol_file(protocol)


def test_rejects_broken_symlink_at_declared_fresh_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source_root = checker.ROOT
    isolated_root = tmp_path / "repo"
    for binding in checker.EXPECTED_BINDINGS.values():
        relative = Path(binding["path"])
        destination = isolated_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((source_root / relative).read_bytes())

    monkeypatch.setattr(checker, "ROOT", isolated_root)
    protocol = _write(tmp_path, checker.DEFAULT_INPUT.read_bytes())
    checker.validate_protocol_file(protocol)

    appeared = isolated_root / checker.FRESH_OUTPUT_PATHS[0]
    appeared.parent.mkdir(parents=True, exist_ok=True)
    appeared.symlink_to(isolated_root / "missing-prospective-output")
    with pytest.raises(checker.ProtocolError, match="prospective output already exists"):
        checker.validate_protocol_file(protocol)


def test_rejects_unknown_nested_field(tmp_path: Path) -> None:
    spec = _spec()
    spec["success_criteria"]["unexpected"] = "must fail closed"  # type: ignore[index]
    path = _write_spec(tmp_path, spec)
    with pytest.raises(checker.ProtocolError, match="keys mismatch"):
        checker.validate_protocol_file(path)
