from __future__ import annotations

import inspect
import json
from fractions import Fraction
from pathlib import Path

import pytest

from scripts import verify_controlled_queue_prospective_receipt as verifier


@pytest.fixture(scope="session")
def parsed_model() -> dict[str, object]:
    return verifier.parse_model_tables(verifier.DEFAULT_MODEL_TABLES.read_bytes())


@pytest.fixture(scope="session")
def deterministic(parsed_model: dict[str, object]) -> dict[str, object]:
    return verifier.compute_deterministic_tables(parsed_model)


def _flat_score_catalog(value: Fraction = Fraction(0)) -> list[dict[str, object]]:
    summary = {
        "count": Fraction(200_000),
        "sum": Fraction(0),
        "sum_squares": Fraction(0),
        "bessel_q": Fraction(0),
        "hybrid_affine_upper": Fraction(1, 2),
        "scale": Fraction(3, 2),
        "span_bound": Fraction(0),
        "empirical_corrected_score": value,
    }
    return [
        {
            "candidate_index": candidate,
            "depth_index": depth,
            "posterior_index": posterior,
            "summary": dict(summary),
        }
        for candidate in range(3)
        for depth in range(7)
        for posterior in range(12)
    ]


def test_verifier_is_independent_of_both_generators() -> None:
    source = Path(verifier.__file__).read_text()
    assert "from scripts import generate_controlled_queue" not in source
    assert "import generate_controlled_queue" not in source


def test_protocol_and_model_golden_constants(
    parsed_model: dict[str, object], deterministic: dict[str, object]
) -> None:
    protocol = verifier.validate_protocol(verifier.DEFAULT_PROTOCOL.read_bytes())
    assert protocol["protocol_version"] == verifier.PROTOCOL_VERSION
    selected = deterministic["selected"]
    assert selected["actual_span"] == verifier.PRIMARY_B
    assert selected["drift_oscillation"] == verifier.PRIMARY_DRIFT
    assert (
        selected["refresh_sensitivity_oscillation"]
        == verifier.PRIMARY_SENSITIVITY
    )
    assert parsed_model["candidate_kernels"][1] == verifier.refresh_kernel(
        Fraction(3, 4)
    )


def test_action_indexing_uses_a_k_plus_one_and_terminal_transition() -> None:
    states = [0, 4, 8]
    actions = [0, 1, 0]
    physical = verifier.physical_counts(states, actions)
    assert physical["edge_counts"][0][1][4] == 1
    assert physical["edge_counts"][4][0][8] == 1
    assert physical["edge_counts"][0][0][4] == 0
    augmented, visits = verifier.augmented_counts(states, actions)
    assert augmented[0][2 * 4 + 1] == 1
    assert augmented[2 * 4 + 1][2 * 8] == 1
    assert visits[0] == 1
    assert visits[2 * 4 + 1] == 1


def test_binary_decoder_rejects_terminal_or_header_truncation() -> None:
    header = verifier.BINARY_HEADER.pack(verifier.BINARY_MAGIC, 2, 3, 3)
    raw = header + bytes([0, 1, 2]) + bytes([0, 1, 0])
    states, actions = verifier.decode_trace(raw, expected_horizon=2)
    assert states == [0, 1, 2]
    assert actions == [0, 1, 0]
    with pytest.raises(verifier.VerificationError, match="byte length"):
        verifier.decode_trace(raw[:-1], expected_horizon=2)


def test_trace_counts_rejects_prng_audit_and_metadata_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(verifier, "HORIZON", 2)
    states = [0, 0, 0]
    actions = [0, 0, 0]
    trace_raw = b"synthetic trace"
    value = {
        "artifact_status": verifier.TRACE_ARTIFACT_STATUS,
        "counts": verifier.physical_counts(states, actions),
        "final_action": 0,
        "final_state": 0,
        "generator_revision": verifier.TRACE_GENERATOR_REVISION,
        "horizon": 2,
        "initial_action": 0,
        "initial_state": 0,
        "nonclaims": verifier.TRACE_NONCLAIMS,
        "prng_audit": {
            "bytes_consumed": 32,
            "digest_blocks_generated": 1,
            "rejections_by_modulus": {},
            "version": verifier.PRNG_VERSION,
            "words_consumed": 4,
        },
        "schema_version": verifier.TRACE_COUNTS_SCHEMA,
        "trace_sha256": verifier.sha256(trace_raw),
        "trace_version": verifier.TRACE_VERSION,
    }
    verifier.validate_trace_counts(
        verifier.canonical_json(value), trace_raw, states, actions
    )
    value["prng_audit"]["words_consumed"] = 5
    value["prng_audit"]["bytes_consumed"] = 40
    value["prng_audit"]["digest_blocks_generated"] = 2
    with pytest.raises(verifier.VerificationError, match="accepted draws"):
        verifier.validate_trace_counts(
            verifier.canonical_json(value), trace_raw, states, actions
        )


def test_oracle_is_built_before_trace_decode() -> None:
    order: list[str] = []

    def build(_model: object) -> dict[str, bool]:
        order.append("deterministic")
        return {"ready": True}

    def decode(_raw: bytes) -> tuple[list[int], list[int]]:
        order.append("decode")
        return [0, 0], [0, 0]

    result, _, _ = verifier.deterministic_then_decode(
        {}, b"trace", deterministic_builder=build, decoder=decode
    )
    assert result == {"ready": True}
    assert order == ["deterministic", "decode"]


def test_selector_has_no_true_gamma_argument_and_ignores_true_gamma(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert "true_gamma" not in inspect.signature(
        verifier.select_adaptive_endpoint
    ).parameters
    catalog = _flat_score_catalog()
    first = verifier.select_adaptive_endpoint(catalog, 151_250, 200_000)
    monkeypatch.setattr(verifier, "TRUE_GAMMA", Fraction(1, 99))
    second = verifier.select_adaptive_endpoint(catalog, 151_250, 200_000)
    assert first == second


def test_selector_uses_frozen_lexicographic_tie_break(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        verifier,
        "CANDIDATE_GAMMAS",
        (Fraction(1), Fraction(1), Fraction(1)),
    )
    monkeypatch.setattr(
        verifier,
        "CANDIDATE_HITS",
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    monkeypatch.setattr(
        verifier,
        "empirical_bernstein_correction",
        lambda _summary, *, log_upper, tilt: Fraction(0),
    )
    monkeypatch.setattr(
        verifier,
        "structured_eta",
        lambda *_args, **_kwargs: {"eta": Fraction(0)},
    )
    selected = verifier.select_adaptive_endpoint(
        _flat_score_catalog(), 0, 200_000
    )["selected"]
    assert selected["indices"] == [0, 0, 0, 0, 0]


def test_empirical_bernstein_uses_fixed_affine_psi_and_log() -> None:
    summary = {
        "scale": Fraction(9, 2),
        "hybrid_affine_upper": Fraction(17, 3),
        "count": Fraction(200_000),
    }
    actual = verifier.empirical_bernstein_correction(
        summary, log_upper=9, tilt=Fraction(1, 16)
    )
    expected = Fraction(9, 2) * (
        9 + Fraction(1, 480) * Fraction(17, 3)
    ) / (200_000 * Fraction(1, 16))
    assert actual == expected
    harmonic_like = Fraction(9, 2) * (
        9 + Fraction(1, 112) * Fraction(17, 3)
    ) / (200_000 * Fraction(1, 16))
    assert actual != harmonic_like


def test_persistence_tracks_direct_and_complement_orientations() -> None:
    result = verifier.persistence_radius(
        37, 100, tilt=Fraction(1, 64), log_upper=7
    )
    assert result["direct_sum"] == 37
    assert result["complement_sum"] == 63
    assert result["radius"] == max(
        result["direct_boundary"], result["complement_boundary"]
    )
    assert result["direct_hybrid_affine_upper"] == Fraction(1, 2) + Fraction(
        3, 2
    ) * (Fraction(37) - Fraction(37 * 37, 100))


def test_unstructured_counts_2304_coordinates_4608_orientations_and_half_nv(
    parsed_model: dict[str, object],
) -> None:
    edges = [[0] * 48 for _ in range(48)]
    visits = [1] * 48
    for source in range(48):
        edges[source][source] = 1
    result = verifier.unstructured_transition_summary(
        edges, visits, parsed_model["candidate_kernels"][1], 48
    )
    assert result["coordinate_count"] == 2304
    assert result["oriented_coordinate_count"] == 4608
    first = result["source_rows"][0]
    assert first["coordinate_radius_sum_half"] == Fraction(1, 2) * sum(
        first["coordinate_radii"], Fraction(0)
    )
    direct = verifier.indicator_summary(1, 48)
    complement = verifier.indicator_summary(47, 48)
    base = max(
        (18 + Fraction(1, 8064) * direct["hybrid_affine_upper"])
        / (48 * Fraction(1, 64)),
        (18 + Fraction(1, 8064) * complement["hybrid_affine_upper"])
        / (48 * Fraction(1, 64)),
    )
    assert first["coordinate_radii"][0] == 48 * base


def test_unstructured_zero_visit_is_totalized_but_premise_fails(
    parsed_model: dict[str, object],
) -> None:
    edges = [[0] * 48 for _ in range(48)]
    visits = [0] * 48
    result = verifier.unstructured_transition_summary(
        edges, visits, parsed_model["candidate_kernels"][1], 200_000
    )
    assert result["all_augmented_source_rows_visited"] is False
    assert result["eta_augmented"] == 0
    assert all(row["premise_visited"] is False for row in result["source_rows"])


def test_causal_beta_scores_preupdate_and_preserves_predictor_order() -> None:
    states = [0, 18, 0]
    actions = [0, 1, 0]
    result = verifier.causal_beta_summaries(states, actions)
    assert [row["id"] for row in result["predictors"]] == [
        "global_beta",
        "queue_band_action_beta",
    ]
    # Global Beta(1,1) predicts 1/2 before the first update, then 2/3.
    assert result["predictors"][0]["cumulative_brier_loss"]["rational"] == "25/36"
    assert result["predictors"][0]["mean_brier_loss"]["rational"] == "25/72"
    assert result["predictors"][0]["final_alpha"] == 2
    assert result["predictors"][0]["final_beta"] == 2


def test_balanced_fraction_sum_preserves_exact_order_independent_value() -> None:
    terms = [Fraction(1, denominator * denominator) for denominator in range(2, 41)]
    assert verifier.balanced_fraction_sum(terms) == sum(terms, Fraction(0))
    assert verifier.balanced_fraction_sum(list(reversed(terms))) == sum(
        terms, Fraction(0)
    )


def test_fixed_range_arithmetic_is_distinct_and_must_remain_noncertificate() -> None:
    eta = verifier.fixed_range_eta(Fraction(73, 96), 151_000, 200_000)
    structured = verifier.structured_eta(
        Fraction(73, 96),
        151_000,
        200_000,
        tilt=Fraction(1, 64),
        log_upper=7,
    )
    assert eta["eta"] != structured["eta"]
    row = verifier._report_row(
        endpoint_id=verifier.ROW_ORDER[5],
        theorem_or_event=verifier._event(
            "fixed_range_planned_arithmetic",
            None,
            "PLANNED_ARITHMETIC_ONLY",
            checked_outer_mass=None,
            planned_allocation=Fraction(1, 20),
        ),
        certification_status="PLANNED_NOT_CHECKED - NOT_A_CONFIDENCE_CERTIFICATE",
        empirical=Fraction(0),
        risk=Fraction(0),
        radius=eta["eta"],
        residual=Fraction(0),
        total=eta["eta"],
        confidence={"confidence_claim": "NOT_A_CONFIDENCE_CERTIFICATE"},
        settings={"fixed_range_arithmetic_only": True},
        vacuity=verifier._vacuity(eta["eta"], planned=True),
    )
    assert row["certification_status"].startswith("PLANNED_NOT_CHECKED")
    assert row["vacuity_and_threshold_status"]["status"] == "PLANNED_NOT_CHECKED"


def test_strict_rational_threshold_and_decimal_half_even() -> None:
    assert verifier._vacuity(Fraction(1, 10) - Fraction(1, 10**30), primary=True)[
        "status"
    ] == "PRIMARY_SUCCESS"
    assert verifier._vacuity(Fraction(1, 10), primary=True)["status"] == (
        "PRIMARY_THRESHOLD_NOT_MET"
    )
    assert verifier.decimal_text(Fraction(1, 2 * 10**15)) == "0.000000000000000"
    assert verifier.decimal_text(Fraction(3, 2 * 10**15)) == "0.000000000000002"
    assert verifier.decimal_text(Fraction(-3, 2 * 10**15)) == "-0.000000000000002"
    assert verifier.decimal_text(Fraction(-1, 10**30)) == "0.000000000000000"


def test_json_rejects_floats_duplicate_keys_and_decimal_mutation() -> None:
    with pytest.raises(verifier.VerificationError, match="floating-point"):
        verifier.parse_json(b'{"x":0.1}', "fixture")
    with pytest.raises(verifier.VerificationError, match="duplicate"):
        verifier.parse_json(b'{"x":1,"x":2}', "fixture")
    with pytest.raises(verifier.VerificationError, match="decimal"):
        verifier._number(
            {"rational": "1/10", "decimal": "0.100000000000001"}, "number"
        )


def test_provenance_path_and_one_byte_mutations_are_rejected(tmp_path: Path) -> None:
    target = tmp_path / "evidence.json"
    target.write_bytes(b"{}\n")
    row = verifier._file_row("evidence", target, target.read_bytes())
    role, path, raw, checked = verifier._read_manifest_row(row, "fixture row")
    assert (role, path, raw, checked) == ("evidence", target, b"{}\n", row)
    target.write_bytes(b"{ }\n")
    with pytest.raises(verifier.VerificationError, match="bytes|sha256"):
        verifier._read_manifest_row(row, "fixture row")
    with pytest.raises(verifier.VerificationError, match="canonical POSIX"):
        verifier._resolve_manifest_path("evidence/../binding.json", "fixture path")
    with pytest.raises(verifier.VerificationError, match="canonical POSIX"):
        verifier._resolve_manifest_path("evidence//binding.json", "fixture path")
    supplied = dict(verifier.EXPECTED_SUPPLIED_PATHS)
    supplied["receipt"] = tmp_path / "relabeled-receipt.json"
    with pytest.raises(verifier.VerificationError, match="frozen supplied path"):
        verifier._validate_supplied_paths(supplied)


def test_canonical_receipt_byte_mutation_is_detectable() -> None:
    value = {"schema_version": verifier.RECEIPT_SCHEMA, "x": 1}
    raw = verifier.canonical_json(value)
    parsed = verifier.parse_canonical_object(raw, "receipt fixture")
    assert parsed == value
    mutated = raw.replace(b'"x": 1', b'"x": 2')
    assert verifier.sha256(mutated) != verifier.sha256(raw)
    assert verifier.parse_canonical_object(mutated, "mutated fixture")["x"] == 2


def test_model_input_and_manifest_cross_binding() -> None:
    model_raw = verifier.DEFAULT_MODEL_INPUT.read_bytes()
    tables_raw = verifier.DEFAULT_MODEL_TABLES.read_bytes()
    model = verifier.validate_model_input(model_raw)
    manifest = verifier.validate_model_manifest(
        verifier.DEFAULT_MODEL_MANIFEST.read_bytes(),
        verifier.DEFAULT_MODEL_INPUT,
        model_raw,
        verifier.DEFAULT_MODEL_TABLES,
        tables_raw,
    )
    assert model["model_version"] == "controlled-queue-v1"
    assert manifest["model_version"] == "controlled-queue-v1"


def test_number_json_has_only_authoritative_rational_and_display() -> None:
    value = verifier.number(Fraction(7, 3))
    assert value == {"rational": "7/3", "decimal": "2.333333333333333"}
    assert verifier._number(value, "fixture number") == Fraction(7, 3)
    encoded = json.loads(verifier.canonical_json(value))
    assert set(encoded) == {"rational", "decimal"}


def _lean_fixture_receipt(primary: Fraction = Fraction(1, 5)) -> dict[str, object]:
    zero = verifier.number(0)
    score = {
        "count": verifier.number(200_000),
        "sum": zero,
        "sum_squares": zero,
        "row_sums": [[zero for _ in range(2)] for _ in range(24)],
        "row_sum_squares": [[zero for _ in range(2)] for _ in range(24)],
        "bessel_q": zero,
        "hybrid_affine_upper": verifier.number(Fraction(1, 2)),
        "scale": verifier.number(Fraction(3, 2)),
        "span_bound": zero,
        "empirical_corrected_score": zero,
    }
    reporting_rows = []
    for endpoint in verifier.ROW_ORDER:
        reporting_rows.append(
            {
                "endpoint_id": endpoint,
                "total_certified_rhs": verifier.number(primary),
                "empirical_corrected_score": zero,
                "risk_statistical_correction": zero,
                "persistence_or_transition_radius": zero,
                "candidate_or_truncation_residual": verifier.number(primary),
            }
        )
    return {
        "protocol_binding": {"sha256": "1" * 64},
        "trace_manifest_binding": {"sha256": "2" * 64},
        "trace_summary": {
            "trace_sha256": "3" * 64,
            "horizon": 200_000,
            "initial_state": 0,
            "dummy_initial_action": 0,
        },
        "registration": {"id": "abc12"},
        "beacon": {"round": 42},
        "code_freeze": {"commit": "4" * 40, "tree": "5" * 40},
        "sufficient_statistics": {
            "physical_transition_histogram": [
                [[0 for _ in range(24)] for _ in range(2)] for _ in range(24)
            ],
            "augmented_source_visits": [0 for _ in range(48)],
            "persistence_hit_count": 0,
            "primary_score": score,
            "adaptive_selected_indices": [0, 0, 0, 0, 0],
        },
        "reporting_rows": reporting_rows,
    }


def test_expected_lean_is_conditional_and_has_bounded_row_certificates() -> None:
    raw = verifier.render_expected_lean(_lean_fixture_receipt())
    assert raw.count(b"private theorem prospectiveCertificate_") == 48
    assert raw.count(b"private theorem prospectiveStateCertificate_") == 24
    assert b"private noncomputable def prospectiveActualScoreRow" in raw
    assert b"private structure ProspectiveStateSubtotalCertificate" in raw
    assert b"HasPhysicalTransitionHistogram" in raw
    assert b"sharpStructuredReceiptBoundary_evaluation_of_histogram" in raw
    assert b"prospectiveHistogramUpper_eq" in raw
    assert b"theorem prospectiveSharpStructuredEndpoint_le" in raw
    assert b"prospectiveSharpStructuredEndpoint_lt_one_tenth" not in raw


def test_definitions_only_or_histogram_only_lean_is_rejected() -> None:
    with pytest.raises(verifier.VerificationError, match="conditional histogram"):
        verifier._validate_lean_contract(
            b"def prospectivePhysicalTransitionHistogram := 0\n"
        )
    full = verifier.render_expected_lean(_lean_fixture_receipt())
    missing_premise = full.replace(b"HasPhysicalTransitionHistogram", b"MissingPremise")
    with pytest.raises(verifier.VerificationError, match="conditional histogram"):
        verifier._validate_lean_contract(missing_premise)
    stale_pre_fix = full.replace(
        b"prospectiveStateCertificate_23", b"staleProspectiveStateCertificate_23"
    )
    with pytest.raises(verifier.VerificationError, match="conditional histogram"):
        verifier._validate_lean_contract(stale_pre_fix)


def test_threshold_corollary_is_rendered_only_for_exact_strict_success() -> None:
    below = verifier.render_expected_lean(
        _lean_fixture_receipt(Fraction(1, 10) - Fraction(1, 10**30))
    )
    equal = verifier.render_expected_lean(_lean_fixture_receipt(Fraction(1, 10)))
    assert b"prospectiveSharpStructuredEndpoint_lt_one_tenth" in below
    assert b"prospectiveSharpStructuredEndpoint_lt_one_tenth" not in equal


def test_no_canonical_prospective_outputs_exist_during_code_freeze() -> None:
    assert not verifier.DEFAULT_TRACE.exists()
    assert not verifier.DEFAULT_COUNTS.exists()
    assert not verifier.DEFAULT_TRACE_MANIFEST.exists()
    assert not verifier.DEFAULT_RECEIPT.exists()
    assert not verifier.DEFAULT_RECEIPT_MANIFEST.exists()
    assert not verifier.DEFAULT_LEAN.exists()


def _write_json(path: Path, value: object) -> bytes:
    raw = verifier.canonical_json(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return raw


def _write_external_json(path: Path, value: object) -> bytes:
    raw = (json.dumps(value, separators=(",", ":"), sort_keys=False) + "\n").encode()
    assert raw != verifier.canonical_json(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return raw


@pytest.fixture(scope="session")
def full_receipt_fixture(tmp_path_factory: pytest.TempPathFactory) -> dict[str, object]:
    directory = tmp_path_factory.mktemp("prospective-receipt-verifier")
    evidence = directory / "evidence"
    generated = directory / "generated"
    evidence.mkdir()
    generated.mkdir()

    paths: dict[str, Path] = {
        "protocol": verifier.DEFAULT_PROTOCOL,
        "trace": generated / "structured-ope-trace-v1.bin",
        "counts": generated / "structured-ope-trace-v1-counts.json",
        "trace_manifest": generated / "structured-ope-trace-v1-manifest.json",
        "model_input": verifier.DEFAULT_MODEL_INPUT,
        "model_manifest": verifier.DEFAULT_MODEL_MANIFEST,
        "model_tables": verifier.DEFAULT_MODEL_TABLES,
        "selected_data": verifier.DEFAULT_SELECTED_DATA,
        "known_kernel_source": verifier.DEFAULT_KNOWN_KERNEL_SOURCE,
        "persistence_source": verifier.DEFAULT_PERSISTENCE_SOURCE,
        "structured_source": verifier.DEFAULT_STRUCTURED_SOURCE,
        "sharp_structured_source": verifier.DEFAULT_SHARP_STRUCTURED_SOURCE,
        "sharp_receipt_core_source": verifier.DEFAULT_SHARP_RECEIPT_CORE_SOURCE,
        "receipt": generated / "structured-ope-receipt-v1.json",
        "receipt_manifest": generated / "structured-ope-receipt-v1-manifest.json",
        "lean": generated / "ControlledQueueProspectiveStructuredOPEData.lean",
        "osf_registration": evidence / "osf-registration-v1.json",
        "osf_binding": evidence / "code-freeze-binding-v1.json",
        "osf_binding_file": evidence / "osf-code-freeze-binding-file-v1.json",
        "quicknet_chain": evidence / "quicknet-chain-info-v1.json",
        "quicknet_round": evidence / "quicknet-round-v1.json",
    }
    protocol_raw = paths["protocol"].read_bytes()
    model_input_raw = paths["model_input"].read_bytes()
    model_manifest_raw = paths["model_manifest"].read_bytes()
    model_tables_raw = paths["model_tables"].read_bytes()

    n = verifier.HORIZON
    trace_raw = (
        verifier.BINARY_HEADER.pack(verifier.BINARY_MAGIC, n, n + 1, n + 1)
        + bytes(n + 1)
        + bytes(n + 1)
    )
    paths["trace"].write_bytes(trace_raw)
    states = [0] * (n + 1)
    actions = [0] * (n + 1)
    physical = verifier.physical_counts(states, actions)
    counts_value = {
        "artifact_status": verifier.TRACE_ARTIFACT_STATUS,
        "counts": physical,
        "final_action": 0,
        "final_state": 0,
        "generator_revision": verifier.TRACE_GENERATOR_REVISION,
        "horizon": n,
        "initial_action": 0,
        "initial_state": 0,
        "nonclaims": verifier.TRACE_NONCLAIMS,
        "prng_audit": {
            "bytes_consumed": 16 * n,
            "digest_blocks_generated": n // 2,
            "rejections_by_modulus": {},
            "version": verifier.PRNG_VERSION,
            "words_consumed": 2 * n,
        },
        "schema_version": verifier.TRACE_COUNTS_SCHEMA,
        "trace_sha256": verifier.sha256(trace_raw),
        "trace_version": verifier.TRACE_VERSION,
    }
    counts_raw = _write_json(paths["counts"], counts_value)

    registration_id = "abc12"
    date_registered = "2026-08-21T20:00:00.125Z"
    registration_second = verifier._registration_second(date_registered)[1]
    round_number, round_time = verifier._formula_round(registration_second)
    signature = bytes(range(48))
    registration_raw = _write_external_json(
        paths["osf_registration"],
        {
            "data": {
                "id": registration_id,
                "type": "registrations",
                "attributes": {
                    "public": True,
                    "registration": True,
                    "withdrawn": False,
                    "date_registered": date_registered,
                },
            }
        },
    )
    freeze_commit = "1" * 40
    freeze_tree = "2" * 40
    code_rows = [
        verifier._file_row(role, path, path.read_bytes())
        for role, _path_text, path in verifier.CODE_FILES
    ]
    binding_value = {
        "artifact_status": verifier.BINDING_STATUS,
        "schema_version": verifier.BINDING_SCHEMA,
        "protocol": {
            "path": verifier.PROTOCOL_PATH,
            "bytes": len(protocol_raw),
            "sha256": verifier.PROTOCOL_SHA256,
            "commit": verifier.PROTOCOL_COMMIT,
            "tree": verifier.PROTOCOL_TREE,
        },
        "code_freeze": {"commit": freeze_commit, "tree": freeze_tree},
        "code_files": code_rows,
    }
    binding_raw = _write_json(paths["osf_binding"], binding_value)
    binding_file_raw = _write_external_json(
        paths["osf_binding_file"],
        {
            "data": {
                "id": "binding-file-1",
                "type": "files",
                "attributes": {
                    "name": "code-freeze-binding-v1.json",
                    "kind": "file",
                    "current_version": 1,
                    "materialized_path": "/Archive of OSF Storage/code-freeze-binding-v1.json",
                    "size": len(binding_raw),
                    "extra": {"hashes": {"sha256": verifier.sha256(binding_raw)}},
                },
                "relationships": {
                    "target": {
                        "data": {"id": registration_id, "type": "registrations"},
                        "links": {
                            "related": {
                                "href": f"https://api.osf.io/v2/registrations/{registration_id}/"
                            }
                        },
                    }
                },
            }
        },
    )
    chain_raw = _write_external_json(
        paths["quicknet_chain"],
        {
            "beacon_id": verifier.BEACON_ID,
            "chain_hash": verifier.CHAIN_HASH,
            "genesis_seed": verifier.GROUP_HASH,
            "public_key": verifier.PUBLIC_KEY,
            "scheme": verifier.SCHEME_ID,
            "period": verifier.PERIOD_SECONDS,
            "genesis_time": verifier.GENESIS_SECONDS,
        },
    )
    round_raw = _write_external_json(
        paths["quicknet_round"],
        {
            "round": round_number,
            "signature": signature.hex(),
            "randomness": verifier.sha256(signature),
        },
    )
    seed = __import__("hashlib").sha256(
        b"FormalSLT/controlled-queue/prospective-structured-ope-v1\0"
        + bytes.fromhex(verifier.CHAIN_HASH)
        + round_number.to_bytes(8, "big")
        + signature
    ).digest()
    input_files = (
        ("protocol", paths["protocol"], protocol_raw),
        ("osf_registration_response", paths["osf_registration"], registration_raw),
        ("osf_registration_binding", paths["osf_binding"], binding_raw),
        ("osf_registration_binding_file", paths["osf_binding_file"], binding_file_raw),
        ("quicknet_chain_info", paths["quicknet_chain"], chain_raw),
        ("quicknet_round", paths["quicknet_round"], round_raw),
        ("model_input", paths["model_input"], model_input_raw),
        ("model_manifest", paths["model_manifest"], model_manifest_raw),
        ("model_tables", paths["model_tables"], model_tables_raw),
    )
    trace_manifest = {
        "artifact_status": verifier.TRACE_ARTIFACT_STATUS,
        "schema_version": verifier.TRACE_MANIFEST_SCHEMA,
        "trace_version": verifier.TRACE_VERSION,
        "generator": {
            **{key: code_rows[0][key] for key in ("bytes", "path", "sha256")},
            "revision": verifier.TRACE_GENERATOR_REVISION,
        },
        "independent_verifier": {
            key: code_rows[1][key] for key in ("bytes", "path", "sha256")
        },
        "code_freeze": {
            "commit": freeze_commit,
            "tree": freeze_tree,
            "code_files": code_rows,
        },
        "registration": {
            "api_response_sha256": verifier.sha256(registration_raw),
            "binding_file_api_response_sha256": verifier.sha256(binding_file_raw),
            "binding_sha256": verifier.sha256(binding_raw),
            "date_registered": date_registered,
            "id": registration_id,
            "protocol_commit": verifier.PROTOCOL_COMMIT,
            "protocol_tree": verifier.PROTOCOL_TREE,
            "unix_seconds_ceiling": registration_second,
        },
        "beacon": {
            "chain_hash": verifier.CHAIN_HASH,
            "group_hash": verifier.GROUP_HASH,
            "scheme_id": verifier.SCHEME_ID,
            "round": round_number,
            "round_time_unix_seconds": round_time,
            "randomness": verifier.sha256(signature),
            "signature_sha256": verifier.sha256(signature),
            "derived_seed_sha256": verifier.sha256(seed),
            "signature_verified": True,
            "signature_verifier": {
                "implementation": verifier.BLS_IMPLEMENTATION,
                "dependency": "py-ecc",
                "version": verifier.PY_ECC_VERSION,
                "dst": verifier.BLS_DST,
            },
        },
        "parameters": {
            "action_count": 2,
            "behavior_policy": "behavior_uniform",
            "binary_expected_bytes": verifier.BINARY_BYTES,
            "binary_magic_hex": verifier.BINARY_MAGIC.hex(),
            "binary_version": verifier.BINARY_VERSION,
            "family": "refreshEnvironment",
            "horizon": n,
            "initial_action": 0,
            "initial_state": 0,
            "prng_version": verifier.PRNG_VERSION,
            "sampling_version": verifier.SAMPLING_VERSION,
            "state_count": 24,
            "true_gamma": "149/200",
        },
        "inputs": [verifier._file_row(role, path, raw) for role, path, raw in input_files],
        "outputs": [
            verifier._file_row("trace_binary", paths["trace"], trace_raw),
            verifier._file_row("trace_counts", paths["counts"], counts_raw),
        ],
        "manifest_note": "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "nonclaims": verifier.TRACE_NONCLAIMS,
    }
    trace_manifest_raw = _write_json(paths["trace_manifest"], trace_manifest)

    model = verifier.parse_model_tables(model_tables_raw)
    deterministic = verifier.compute_deterministic_tables(model)
    source_raw = {
        name: paths[name].read_bytes()
        for name in (
            "selected_data",
            "known_kernel_source",
            "persistence_source",
            "structured_source",
            "sharp_structured_source",
            "sharp_receipt_core_source",
        )
    }
    receipt = verifier.build_expected_receipt(
        protocol_path=paths["protocol"],
        protocol_raw=protocol_raw,
        trace_path=paths["trace"],
        trace_raw=trace_raw,
        counts_path=paths["counts"],
        counts_raw=counts_raw,
        trace_manifest_path=paths["trace_manifest"],
        trace_manifest_raw=trace_manifest_raw,
        trace_manifest=trace_manifest,
        model_input_path=paths["model_input"],
        model_input_raw=model_input_raw,
        model_manifest_path=paths["model_manifest"],
        model_manifest_raw=model_manifest_raw,
        model_tables_path=paths["model_tables"],
        model_tables_raw=model_tables_raw,
        selected_data_path=paths["selected_data"],
        selected_data_raw=source_raw["selected_data"],
        known_kernel_source_path=paths["known_kernel_source"],
        known_kernel_source_raw=source_raw["known_kernel_source"],
        persistence_source_path=paths["persistence_source"],
        persistence_source_raw=source_raw["persistence_source"],
        structured_source_path=paths["structured_source"],
        structured_source_raw=source_raw["structured_source"],
        sharp_structured_source_path=paths["sharp_structured_source"],
        sharp_structured_source_raw=source_raw["sharp_structured_source"],
        sharp_receipt_core_source_path=paths["sharp_receipt_core_source"],
        sharp_receipt_core_source_raw=source_raw["sharp_receipt_core_source"],
        deterministic=deterministic,
        states=states,
        actions=actions,
        physical=physical,
        model=model,
    )
    receipt_raw = _write_json(paths["receipt"], receipt)
    lean_raw = verifier.render_expected_lean(receipt)
    paths["lean"].write_bytes(lean_raw)
    receipt_manifest = verifier.build_expected_manifest(
        receipt=receipt,
        receipt_path=paths["receipt"],
        receipt_raw=receipt_raw,
        lean_path=paths["lean"],
        lean_raw=lean_raw,
    )
    _write_json(paths["receipt_manifest"], receipt_manifest)

    git_files = {
        verifier.PROTOCOL_PATH: protocol_raw,
        **{path_text: path.read_bytes() for _role, path_text, path in verifier.CODE_FILES},
        verifier.SHARP_STRUCTURED_SOURCE_PATH: source_raw["sharp_structured_source"],
        verifier.SHARP_RECEIPT_CORE_SOURCE_PATH: source_raw["sharp_receipt_core_source"],
    }

    def fake_git(*arguments: str) -> bytes:
        if arguments[:2] == ("cat-file", "-t"):
            return b"commit\n"
        if arguments[:2] == ("rev-parse", "--verify"):
            ref = arguments[2]
            return ((verifier.PROTOCOL_TREE if ref.startswith(verifier.PROTOCOL_COMMIT) else freeze_tree) + "\n").encode()
        if arguments[:2] == ("merge-base", "--is-ancestor"):
            return b""
        if arguments[0] == "show":
            _commit, path_text = arguments[1].split(":", 1)
            return git_files[path_text]
        raise AssertionError(f"unexpected fake Git call: {arguments!r}")

    return {"paths": paths, "fake_git": fake_git}


def _verify_full_fixture(
    full_receipt_fixture: dict[str, object], monkeypatch: pytest.MonkeyPatch
) -> dict[str, object]:
    paths = full_receipt_fixture["paths"]
    monkeypatch.setattr(verifier, "_git", full_receipt_fixture["fake_git"])
    monkeypatch.setattr(
        verifier,
        "TRACE_EVIDENCE_PATHS",
        {
            "osf_registration_response": paths["osf_registration"],
            "osf_registration_binding": paths["osf_binding"],
            "osf_registration_binding_file": paths["osf_binding_file"],
            "quicknet_chain_info": paths["quicknet_chain"],
            "quicknet_round": paths["quicknet_round"],
        },
    )
    monkeypatch.setattr(
        verifier,
        "EXPECTED_SUPPLIED_PATHS",
        {
            role: paths[role]
            for role in (
                "protocol",
                "trace",
                "counts",
                "trace_manifest",
                "model_input",
                "model_manifest",
                "model_tables",
                "selected_data",
                "known_kernel_source",
                "persistence_source",
                "structured_source",
                "sharp_structured_source",
                "sharp_receipt_core_source",
                "receipt",
                "receipt_manifest",
                "lean",
            )
        },
    )
    return verifier.verify_paths(
        protocol_path=paths["protocol"],
        trace_path=paths["trace"],
        counts_path=paths["counts"],
        trace_manifest_path=paths["trace_manifest"],
        model_input_path=paths["model_input"],
        model_manifest_path=paths["model_manifest"],
        model_tables_path=paths["model_tables"],
        selected_data_path=paths["selected_data"],
        known_kernel_source_path=paths["known_kernel_source"],
        persistence_source_path=paths["persistence_source"],
        structured_source_path=paths["structured_source"],
        sharp_structured_source_path=paths["sharp_structured_source"],
        sharp_receipt_core_source_path=paths["sharp_receipt_core_source"],
        receipt_path=paths["receipt"],
        receipt_manifest_path=paths["receipt_manifest"],
        lean_path=paths["lean"],
    )


def test_full_independent_fixture_verifies(
    full_receipt_fixture: dict[str, object], monkeypatch: pytest.MonkeyPatch
) -> None:
    result = _verify_full_fixture(full_receipt_fixture, monkeypatch)
    assert len(result["receipt_sha256"]) == 64
    assert Fraction(result["primary_upper"]) > 0


def test_receipt_verifier_rejects_registration_id_inside_immutable_binding(
    full_receipt_fixture: dict[str, object],
) -> None:
    paths = full_receipt_fixture["paths"]
    binding = json.loads(paths["osf_binding"].read_bytes())
    binding["registration_id"] = "abc12"
    with pytest.raises(verifier.VerificationError, match="keys mismatch"):
        verifier._validate_code_freeze_binding(
            binding,
            paths["protocol"].read_bytes(),
        )


def test_receipt_verifier_cross_binds_registration_response_and_file_target(
    full_receipt_fixture: dict[str, object],
) -> None:
    paths = full_receipt_fixture["paths"]
    metadata = json.loads(paths["osf_binding_file"].read_bytes())
    binding_raw = paths["osf_binding"].read_bytes()
    with pytest.raises(verifier.VerificationError, match="binding target data"):
        verifier._verify_osf_binding_file(metadata, "other", binding_raw)
