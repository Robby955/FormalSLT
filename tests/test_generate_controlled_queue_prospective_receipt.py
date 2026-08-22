from __future__ import annotations

import inspect
import json
import struct
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
from typing import Any

import pytest

from scripts import generate_controlled_queue_prospective_receipt as generator


def _binary(states: list[int], actions: list[int]) -> bytes:
    horizon = len(states) - 1
    return (
        generator.BINARY_HEADER.pack(
            generator.BINARY_MAGIC, horizon, len(states), len(actions)
        )
        + bytes(states)
        + bytes(actions)
    )


def _model_and_deterministic() -> tuple[dict[str, Any], dict[str, Any]]:
    model = generator.parse_model_tables(generator.DEFAULT_MODEL_TABLES.read_bytes())
    return model, generator.compute_deterministic_tables(model)


def _synthetic_histogram() -> list[list[list[int]]]:
    histogram = [
        [[0] * generator.STATE_COUNT for _ in range(generator.ACTION_COUNT)]
        for _ in range(generator.STATE_COUNT)
    ]
    histogram[0][0][generator.queue_step(0, 0)] = generator.HORIZON
    return histogram


def _minimal_render_receipt(
    total: Fraction | None = None,
    histogram: list[list[list[int]]] | None = None,
) -> dict[str, Any]:
    model, deterministic = _model_and_deterministic()
    if histogram is None:
        histogram = _synthetic_histogram()
    selected = deterministic["selected"]
    score = generator.score_summary_with_count(
        histogram,
        model["target_policies"][1],
        model["losses"][2],
        selected["potential"],
        generator.PRIMARY_B,
    )
    risk = generator.empirical_bernstein_correction(
        score, log_upper=9, tilt=Fraction(1, 16)
    )
    persistence_hits = sum(
        histogram[state][action][generator.queue_step(state, action)]
        for state in range(generator.STATE_COUNT)
        for action in range(generator.ACTION_COUNT)
    )
    persistence = generator.structured_eta(
        generator.CANDIDATE_HITS[1],
        persistence_hits,
        generator.HORIZON,
        tilt=Fraction(1, 64),
        log_upper=7,
    )
    residual = (
        generator.PRIMARY_DRIFT
        + generator.PRIMARY_SENSITIVITY * persistence["eta"]
    )
    coherent_total = score["empirical_corrected_score"] + risk + residual
    if total is None:
        total = coherent_total
    public_score = generator._public_score_summary(score)
    rows = []
    for endpoint in generator.ROW_ORDER:
        rows.append(
            {
                "endpoint_id": endpoint,
                "total_certified_rhs": generator.number(total),
                "empirical_corrected_score": generator.number(Fraction(0)),
                "risk_statistical_correction": generator.number(Fraction(0)),
                "persistence_or_transition_radius": generator.number(Fraction(0)),
                "candidate_or_truncation_residual": generator.number(Fraction(0)),
            }
        )
    rows[0].update(
        {
            "empirical_corrected_score": generator.number(
                score["empirical_corrected_score"]
            ),
            "risk_statistical_correction": generator.number(risk),
            "persistence_or_transition_radius": generator.number(
                persistence["eta"]
            ),
            "candidate_or_truncation_residual": generator.number(residual),
            "total_certified_rhs": generator.number(total),
        }
    )
    return {
        "protocol_binding": {"sha256": generator.PROTOCOL_SHA256},
        "trace_manifest_binding": {"sha256": "1" * 64},
        "trace_summary": {
            "trace_sha256": "2" * 64,
            "horizon": generator.HORIZON,
            "initial_state": 0,
            "dummy_initial_action": 0,
        },
        "code_freeze": {"commit": "3" * 40, "tree": "4" * 40},
        "registration": {"id": "abc12"},
        "beacon": {"round": 123},
        "sufficient_statistics": {
            "physical_transition_histogram": histogram,
            "augmented_source_visits": [1] * generator.AUGMENTED_COUNT,
            "persistence_hit_count": persistence_hits,
            "primary_score": public_score,
            "adaptive_selected_indices": [0, 0, 0, 0, 0],
        },
        "reporting_rows": rows,
    }


def test_strict_json_rejects_duplicates_floats_and_boolean_integers() -> None:
    with pytest.raises(generator.ProspectiveReceiptError, match="duplicate JSON key"):
        generator.parse_json_bytes(b'{"x":1,"x":2}', "duplicate")
    with pytest.raises(generator.ProspectiveReceiptError, match="floating-point"):
        generator.parse_json_bytes(b'{"x":1.0}', "float")
    with pytest.raises(generator.ProspectiveReceiptError, match="JSON boolean"):
        generator._integer(True, "integer")


def test_half_even_decimal_is_exact_and_normalizes_negative_zero() -> None:
    assert generator.decimal_text(Fraction(1, 2_000_000_000_000_000)) == "0.000000000000000"
    assert generator.decimal_text(Fraction(3, 2_000_000_000_000_000)) == "0.000000000000002"
    assert generator.decimal_text(Fraction(-1, 2_000_000_000_000_000)) == "0.000000000000000"
    assert generator.decimal_text(Fraction(-3, 2_000_000_000_000_000)) == "-0.000000000000002"
    assert generator.decimal_text(Fraction(-1, 10**30)) == "0.000000000000000"


def test_balanced_fraction_accumulation_is_exact() -> None:
    values = [Fraction((-1) ** index, index + 1) for index in range(257)]
    partials: list[Fraction | None] = []
    for value in values:
        generator._balanced_fraction_add(partials, value)
    assert generator._balanced_fraction_total(partials) == sum(values, Fraction(0))
    assert generator._vacuity(Fraction(1, 10), primary=True)["status"] == "PRIMARY_THRESHOLD_NOT_MET"
    assert generator._vacuity(Fraction(1, 10) - Fraction(1, 10**30), primary=True)["status"] == "PRIMARY_SUCCESS"


def test_binary_and_physical_indexing_use_next_action_and_terminal_edge() -> None:
    raw = _binary([0, 1, 5], [0, 1, 0])
    states, actions = generator.decode_trace(raw, expected_horizon=2)
    counts = generator.physical_counts(states, actions)
    assert counts["edge_counts"][0][1][1] == 1
    assert counts["edge_counts"][1][0][5] == 1
    assert counts["edge_counts"][0][0][1] == 0
    assert sum(sum(sum(row) for row in actions_) for actions_ in counts["edge_counts"]) == 2


def test_augmented_indexing_uses_dummy_only_at_x0() -> None:
    states = [0, 1, 5]
    actions = [0, 1, 0]
    edges, visits = generator.augmented_counts(states, actions)
    assert edges[0][3] == 1  # (eco,S0) -> (boost,S1)
    assert edges[3][10] == 1  # (boost,S1) -> (eco,S5)
    assert visits[0] == 1 and visits[3] == 1


def test_predecode_tables_reconstruct_exact_frozen_drift_and_sensitivity() -> None:
    _model, deterministic = _model_and_deterministic()
    selected = deterministic["selected"]
    assert selected["actual_span"] == generator.PRIMARY_B
    assert selected["drift_oscillation"] == generator.PRIMARY_DRIFT
    assert selected["refresh_sensitivity_oscillation"] == generator.PRIMARY_SENSITIVITY


def test_oracle_builder_runs_before_trace_decoder() -> None:
    order: list[str] = []

    def deterministic(_model: dict[str, Any]) -> dict[str, Any]:
        order.append("oracle")
        return {"oracle": True}

    def decode(_raw: bytes) -> tuple[list[int], list[int]]:
        order.append("trace")
        return [0, 0], [0, 0]

    value, _states, _actions = generator.load_deterministic_then_decode(
        {}, b"trace", deterministic_builder=deterministic, decoder=decode
    )
    assert value == {"oracle": True}
    assert order == ["oracle", "trace"]


def test_affine_hybrid_branch_and_frozen_psi_log_are_not_data_selected() -> None:
    summary = generator.indicator_bessel_summary(1, 4)
    assert summary["bessel_q"] == Fraction(3, 4)
    assert summary["hybrid_affine_upper"] == Fraction(13, 8)
    radius = generator.persistence_radius(1, 4, tilt=Fraction(1, 64), log_upper=7)
    expected = (Fraction(7) + Fraction(1, 8064) * Fraction(13, 8)) / (4 * Fraction(1, 64))
    assert radius["direct_boundary"] == expected
    assert radius["complement_boundary"] == expected


def test_adaptive_selector_has_no_true_gamma_input_and_certifies_exact_minimum() -> None:
    assert "true_gamma" not in inspect.signature(generator.select_adaptive_endpoint).parameters
    base = {
        "sum": Fraction(0),
        "sum_squares": Fraction(0),
        "row_sums": [[Fraction(0)] * 2 for _ in range(24)],
        "row_sum_squares": [[Fraction(0)] * 2 for _ in range(24)],
        "bessel_q": Fraction(0),
        "hybrid_affine_upper": Fraction(1, 2),
        "scale": Fraction(3, 2),
        "span_bound": Fraction(0),
        "empirical_corrected_score": Fraction(0),
        "count": Fraction(20),
    }
    catalog = [
        {
            "candidate_index": candidate,
            "depth_index": depth,
            "posterior_index": posterior,
            "summary": dict(base),
        }
        for candidate in range(3)
        for depth in range(7)
        for posterior in range(12)
    ]
    result = generator.select_adaptive_endpoint(catalog, 15, 20)
    candidates = result["catalog_minimum_certificate"]
    assert len(candidates) == 4032
    exact_min = min((row["total_certified_rhs"], *row["indices"]) for row in candidates)
    assert (result["selected"]["total_certified_rhs"], *result["selected"]["indices"]) == exact_min


def test_unstructured_uses_2304_coordinates_4608_orientations_half_and_n_over_v() -> None:
    model, _deterministic = _model_and_deterministic()
    n = 48
    edges = [[0] * 48 for _ in range(48)]
    visits = [1] * 48
    for source in range(48):
        edges[source][source] = 1
    result = generator.unstructured_transition_summary(
        edges, visits, model["candidate_kernels"][1], n
    )
    assert result["coordinate_count"] == 2304
    assert result["oriented_coordinate_count"] == 4608
    assert result["all_augmented_source_rows_visited"] is True
    first = result["source_rows"][0]
    assert first["coordinate_radius_sum_half"] == Fraction(1, 2) * sum(
        first["coordinate_radii"], Fraction(0)
    )
    observed = edges[0][0]
    direct = generator.indicator_bessel_summary(observed, n)
    raw = (Fraction(18) + Fraction(1, 8064) * direct["hybrid_affine_upper"]) / (
        n * Fraction(1, 64)
    )
    assert first["coordinate_radii"][0] == Fraction(n, visits[0]) * raw


def test_unstructured_zero_visit_is_totalized_but_fails_premise() -> None:
    model, _deterministic = _model_and_deterministic()
    edges = [[0] * 48 for _ in range(48)]
    visits = [0] * 48
    result = generator.unstructured_transition_summary(
        edges, visits, model["candidate_kernels"][1], 48
    )
    assert result["all_augmented_source_rows_visited"] is False
    assert result["source_rows"][0]["premise_visited"] is False
    assert result["source_rows"][0]["row_eta"] == 0


def test_causal_predictors_score_preupdate_and_use_next_action() -> None:
    result = generator.causal_beta_summaries([0, 18, 0], [0, 1, 0])
    global_row, band_row = result["predictors"]
    assert Fraction(global_row["cumulative_brier_loss"]["rational"]) == Fraction(25, 36)
    assert global_row["final_alpha"] == 2 and global_row["final_beta"] == 2
    assert Fraction(band_row["cumulative_brier_loss"]["rational"]) == Fraction(1, 2)
    assert band_row["final_cells_alpha_beta"][0][1] == [2, 1]
    assert band_row["final_cells_alpha_beta"][2][0] == [1, 2]


def test_fixed_range_remains_planned_not_checked() -> None:
    status = generator._vacuity(Fraction(1, 100), planned=True)
    assert status["status"] == "PLANNED_NOT_CHECKED"
    assert generator.fixed_range_eta(Fraction(73, 96), 15, 20)["eta"] > 0


def test_oracle_remains_planned_not_checked() -> None:
    status = generator._vacuity(Fraction(1, 100), planned=True)
    assert status["status"] == "PLANNED_NOT_CHECKED"
    assert any("oracle true-kernel" in claim for claim in generator.NONCLAIMS)
    rows: list[dict[str, Any]] = [{} for _ in generator.ROW_ORDER]
    for index, event_label in (
        (2, "oracle_true_kernel_planned_arithmetic"),
        (5, "fixed_range_planned_arithmetic"),
    ):
        rows[index] = generator._report_row(
            endpoint_id=generator.ROW_ORDER[index],
            theorem_or_event=generator._event(
                event_label,
                None,
                "PLANNED_ARITHMETIC_ONLY",
                checked_outer_mass=None,
                planned_allocation=Fraction(1, 20),
            ),
            certification_status="PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
            empirical=Fraction(0),
            risk=Fraction(0),
            radius=Fraction(0),
            residual=Fraction(0),
            total=Fraction(0),
            confidence={},
            settings={},
            vacuity=generator._vacuity(Fraction(0), planned=True),
        )
    generator._validate_planned_reporting_rows(rows)
    relabeled = deepcopy(rows)
    relabeled[2]["theorem_or_event"]["lean_theorem"] = (
        "exists_controlledQueueKnownKernelOPE_event"
    )
    with pytest.raises(generator.ProspectiveReceiptError, match="oracle theorem or event"):
        generator._validate_planned_reporting_rows(relabeled)


def test_renderer_freezes_bounded_conditional_proof_and_threshold_gate() -> None:
    below = generator.render_lean(_minimal_render_receipt(Fraction(1, 20)))
    above = generator.render_lean(_minimal_render_receipt(Fraction(1, 5)))
    text = below.decode()
    assert text.count("private theorem prospectiveCertificate_") == 48
    assert "sharpStructuredReceiptBoundary_evaluation_of_histogram" in text
    assert "prospectiveHistogramUpper_eq" in text
    assert "def oracleTrueKernelCertificationStatus : String :=" in text
    assert "def fixedRangeCertificationStatus : String :=" in text
    assert text.count("PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE") >= 2
    assert "(hhist : HasPhysicalTransitionHistogram" in text
    assert "prospectiveSharpStructuredEndpoint_lt_one_tenth" in text
    assert "lt_of_le_of_lt (prospectiveSharpStructuredEndpoint_le path hhist)" in text
    assert "prospectiveSharpStructuredEndpoint_lt_one_tenth" not in above.decode()
    assert "#print axioms FormalSLT.Applications.ControlledQueueProspectiveStructuredOPEData.prospectiveSharpStructuredEndpoint_le" in text
    assert "sorry" not in text and "axiom " not in text
    assert below == generator.render_lean(_minimal_render_receipt(Fraction(1, 20)))


def test_coherent_synthetic_renderer_uses_exact_primary_formula() -> None:
    receipt = _minimal_render_receipt()
    primary = receipt["reporting_rows"][0]
    total = sum(
        (
            Fraction(primary[key]["rational"])
            for key in (
                "empirical_corrected_score",
                "risk_statistical_correction",
                "candidate_or_truncation_residual",
            )
        ),
        Fraction(0),
    )
    assert Fraction(primary["total_certified_rhs"]["rational"]) == total
    rendered = generator.render_lean(receipt).decode()
    assert f"def prospectivePrimaryUpper : ℚ :=\n  {generator._lean_rat(str(total))}" in rendered


def test_manifest_last_writer_order_and_exclusive_overwrite(tmp_path: Path) -> None:
    calls: list[str] = []

    def writer(path: Path, raw: bytes) -> None:
        calls.append(path.name)

    generator.write_artifacts_manifest_last(
        tmp_path / "receipt.json",
        b"r",
        tmp_path / "data.lean",
        b"l",
        tmp_path / "manifest.json",
        b"m",
        writer=writer,
    )
    assert calls == ["receipt.json", "data.lean", "manifest.json"]
    target = tmp_path / "exclusive"
    generator._exclusive_atomic_write(target, b"first")
    with pytest.raises(generator.ProspectiveReceiptError, match="refusing to overwrite"):
        generator._exclusive_atomic_write(target, b"second")
    assert target.read_bytes() == b"first"


def test_path_alias_and_one_byte_protocol_mutation_fail_closed(tmp_path: Path) -> None:
    shared = tmp_path / "shared"
    shared.write_bytes(b"x")
    with pytest.raises(generator.ProspectiveReceiptError, match="aliases protected input"):
        generator.validate_artifact_paths({"input": shared}, {"output": shared})
    raw = bytearray(generator.DEFAULT_PROTOCOL.read_bytes())
    raw[-2] ^= 1
    with pytest.raises(generator.ProspectiveReceiptError, match="protocol SHA-256"):
        generator.validate_protocol(bytes(raw))


def test_canonical_number_objects_never_use_json_floats() -> None:
    value = generator.number(Fraction(1, 3))
    assert value == {"rational": "1/3", "decimal": "0.333333333333333"}
    raw = generator.canonical_json_bytes({"value": value})
    assert json.loads(raw)["value"]["rational"] == "1/3"
    assert b"0.333333333333333" in raw
