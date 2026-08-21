from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from fractions import Fraction
from pathlib import Path

from scripts import generate_controlled_queue_model as generator


def load_spec_and_tables() -> tuple[dict, dict]:
    spec = generator.parse_input_bytes(generator.DEFAULT_INPUT.read_bytes())
    return spec, generator.build_tables(spec)


def test_candidate_kernels_and_policies_are_exactly_normalized() -> None:
    _spec, tables = load_spec_and_tables()

    assert tables["dimensions"] == {
        "physical_state_count": 24,
        "action_count": 2,
        "augmented_behavior_state_count": 48,
        "candidate_count": 3,
        "target_policy_count": 4,
        "fixed_predictor_count": 3,
        "causal_predictor_count": 2,
    }
    assert tables["augmented_behavior_states"] == [
        {
            "id": 2 * state + action,
            "state": state,
            "action": ("eco", "boost")[action],
            "action_index": action,
        }
        for state in range(24)
        for action in range(2)
    ]
    for candidate in tables["candidate_kernels"]:
        assert len(candidate["rows"]) == 48
        for row in candidate["rows"]:
            probabilities = [Fraction(value) for value in row["probabilities"]]
            assert len(probabilities) == 24
            assert all(value > 0 for value in probabilities)
            assert sum(probabilities) == 1

    for policy in tables["policies"]:
        assert len(policy["rows"]) == 24
        for row in policy["rows"]:
            probabilities = [Fraction(value) for value in row["probabilities"]]
            assert len(probabilities) == 2
            assert all(value > 0 for value in probabilities)
            assert sum(probabilities) == 1


def test_target_policy_overlap_cap_is_exactly_three_halves() -> None:
    _spec, tables = load_spec_and_tables()
    behavior = tables["policies"][0]
    ratios: list[Fraction] = []

    for target in tables["policies"][1:]:
        for state in range(24):
            behavior_row = behavior["rows"][state]["probabilities"]
            target_row = target["rows"][state]["probabilities"]
            for action in range(2):
                ratio = Fraction(target_row[action]) / Fraction(behavior_row[action])
                ratios.append(ratio)
                assert ratio <= Fraction(3, 2)

    assert max(ratios) == Fraction(3, 2)


def test_queue_step_and_refresh_formula_match_the_frozen_specification() -> None:
    spec, tables = load_spec_and_tables()
    generator.validate_candidate_kernel_compaction(tables)
    step_by_row = {
        (row["state"], row["action"]): row["next_state"]
        for row in tables["queue_step"]
    }

    for row in tables["queue_step"]:
        queue, regime = divmod(row["state"], 3)
        action_index = ("eco", "boost").index(row["action"])
        service = spec["actions"][action_index]["service_capacity"]
        arrival = spec["state_space"]["arrival_by_regime"][regime]
        next_queue = min(7, max(0, queue - service) + arrival)
        next_regime = (regime + 1) % 3
        assert row["next_state"] == 3 * next_queue + next_regime

    for candidate in tables["candidate_kernels"]:
        gamma = Fraction(candidate["gamma"])
        base = (1 - gamma) / 24
        for row in candidate["rows"]:
            step = step_by_row[(row["state"], row["action"])]
            assert [Fraction(value) for value in row["probabilities"]] == [
                base + (gamma if destination == step else 0)
                for destination in range(24)
            ]


def test_lean_render_fails_closed_on_candidate_kernel_compaction_drift() -> None:
    _spec, tables = load_spec_and_tables()

    wrong_candidate_order = deepcopy(tables)
    wrong_candidate_order["candidate_kernels"][0:2] = reversed(
        wrong_candidate_order["candidate_kernels"][0:2]
    )

    wrong_row_order = deepcopy(tables)
    wrong_row_order["candidate_kernels"][0]["rows"][0:2] = reversed(
        wrong_row_order["candidate_kernels"][0]["rows"][0:2]
    )

    wrong_exact_fraction = deepcopy(tables)
    wrong_exact_fraction["candidate_kernels"][0]["rows"][0]["probabilities"][0] = (
        "1/32"
    )

    noncanonical_exact_fraction = deepcopy(tables)
    noncanonical_exact_fraction["candidate_kernels"][0]["rows"][0][
        "probabilities"
    ][0] = "2/128"

    wrong_destination_order = deepcopy(tables)
    probabilities = wrong_destination_order["candidate_kernels"][0]["rows"][0][
        "probabilities"
    ]
    probabilities[0], probabilities[1] = probabilities[1], probabilities[0]

    for drifted in (
        wrong_candidate_order,
        wrong_row_order,
        wrong_exact_fraction,
        noncanonical_exact_fraction,
        wrong_destination_order,
    ):
        try:
            generator.render_lean(drifted)
        except generator.SchemaError:
            pass
        else:  # pragma: no cover
            raise AssertionError("candidate-kernel compaction drift was accepted")


def test_control_cost_and_overload_outcome_use_exact_frozen_formulas() -> None:
    spec, tables = load_spec_and_tables()
    outcomes = spec["outcomes"]

    expected_cost = []
    for action in spec["actions"]:
        boost_indicator = int(action["id"] == "boost")
        for destination in range(24):
            next_queue = destination // 3
            value = Fraction(
                outcomes["control_cost_queue_weight"] * next_queue
                + outcomes["control_cost_boost_weight"] * boost_indicator,
                outcomes["control_cost_denominator"],
            )
            expected_cost.append(
                {
                    "action": action["id"],
                    "next_state": destination,
                    "value": generator.rational_text(value),
                }
            )
    assert tables["control_cost"] == expected_cost

    expected_outcome = [
        {
            "next_state": destination,
            "value": int(destination // 3 >= outcomes["overload_queue_minimum"]),
        }
        for destination in range(24)
    ]
    assert tables["overload_outcome"] == expected_outcome


def test_all_predictor_formulas_and_causal_declarations_are_exact() -> None:
    spec, tables = load_spec_and_tables()
    step_by_row = {
        (row["state"], row["action"]): row["next_state"]
        for row in tables["queue_step"]
    }
    overload_minimum = spec["outcomes"]["overload_queue_minimum"]
    nominal_gamma = Fraction(
        next(
            candidate["gamma"]
            for candidate in spec["candidates"]
            if candidate["id"] == spec["nominal_candidate"]
        )
    )
    overload_state_count = sum(
        destination // 3 >= overload_minimum for destination in range(24)
    )
    uniform_overload_probability = Fraction(overload_state_count, 24)

    predictors = {predictor["id"]: predictor for predictor in tables["fixed_predictors"]}
    assert set(predictors) == {
        "global_climatology",
        "queue_action_threshold",
        "nominal_model_overload",
    }
    for predictor_id, predictor in predictors.items():
        assert len(predictor["rows"]) == 48
        for row in predictor["rows"]:
            step_overloads = (
                step_by_row[(row["state"], row["action"])] // 3 >= overload_minimum
            )
            if predictor_id == "global_climatology":
                expected = Fraction(1, 4)
            elif predictor_id == "queue_action_threshold":
                expected = Fraction(3, 4) if step_overloads else Fraction(1, 4)
            else:
                expected = (1 - nominal_gamma) * uniform_overload_probability
                if step_overloads:
                    expected += nominal_gamma
            assert Fraction(row["overload_probability"]) == expected

    assert tables["causal_predictors"] == spec["causal_predictors"]
    assert [predictor["id"] for predictor in tables["causal_predictors"]] == [
        "global_beta",
        "queue_band_action_beta",
    ]


def test_every_fixed_predictor_brier_entry_uses_the_exact_square_loss() -> None:
    _spec, tables = load_spec_and_tables()
    probability_by_row = {
        (predictor["id"], row["state"], row["action"]): Fraction(
            row["overload_probability"]
        )
        for predictor in tables["fixed_predictors"]
        for row in predictor["rows"]
    }
    outcomes = [Fraction(row["value"]) for row in tables["overload_outcome"]]

    assert [entry["id"] for entry in tables["fixed_brier_loss"]] == [
        "global_climatology",
        "queue_action_threshold",
        "nominal_model_overload",
    ]
    for predictor in tables["fixed_brier_loss"]:
        assert len(predictor["rows"]) == 48
        for row in predictor["rows"]:
            probability = probability_by_row[
                (predictor["id"], row["state"], row["action"])
            ]
            actual = [Fraction(value) for value in row["losses"]]
            expected = [(probability - outcome) ** 2 for outcome in outcomes]
            assert actual == expected
            assert all(Fraction(0) <= value <= Fraction(1) for value in actual)


def test_generation_is_byte_deterministic_and_manifest_hashes_outputs() -> None:
    first = generator.expected_artifacts(
        generator.DEFAULT_INPUT, generator.DEFAULT_TABLES, generator.DEFAULT_LEAN
    )
    second = generator.expected_artifacts(
        generator.DEFAULT_INPUT, generator.DEFAULT_TABLES, generator.DEFAULT_LEAN
    )
    assert first == second

    tables_bytes, lean_bytes, manifest_bytes = first
    manifest = json.loads(manifest_bytes)
    files = {entry["path"]: entry for entry in manifest["files"]}
    assert files["applications/controlled_queue/generated/model-v1-tables.json"][
        "sha256"
    ] == hashlib.sha256(tables_bytes).hexdigest()
    assert files["FormalSLT/Applications/ControlledQueueData.lean"][
        "sha256"
    ] == hashlib.sha256(lean_bytes).hexdigest()
    assert manifest["artifact_status"] == "MODEL/PREPROCESSING ONLY"
    assert "not a theorem-produced good path" in manifest["nonclaims"]


def test_next_trace_contract_is_recorded_without_generating_a_trace() -> None:
    spec, tables = load_spec_and_tables()
    expected = spec["generation"]["next_trace_slice_contract"]

    assert expected == {
        "status": "OPEN",
        "prng_sampling_requirement": (
            "language-independent, versioned, byte-reproducible"
        ),
        "required_fields": [
            "initial_state",
            "prng_contract",
            "sampling_contract",
        ],
        "required_exact_weight_tables": [
            "prior_weights",
            "posterior_weights",
            "candidate_weights",
            "coordinate_weights",
            "tilt_weights",
        ],
    }
    assert tables["generation_parameters"]["next_trace_slice_contract"] == expected
    _tables_bytes, _lean_bytes, manifest_bytes = generator.expected_artifacts(
        generator.DEFAULT_INPUT, generator.DEFAULT_TABLES, generator.DEFAULT_LEAN
    )
    assert json.loads(manifest_bytes)["parameters"]["next_trace_slice_contract"] == expected
    assert "trace" not in tables


def test_check_mode_fails_closed_on_stale_input_table_lean_or_manifest_bytes(
    tmp_path: Path,
) -> None:
    for stale_role in ("input", "tables", "lean", "manifest"):
        case = tmp_path / stale_role
        case.mkdir()
        paths = {
            "input": case / "model-v1.json",
            "tables": case / "model-v1-tables.json",
            "lean": case / "ControlledQueueData.lean",
            "manifest": case / "model-v1-manifest.json",
        }
        paths["input"].write_bytes(generator.DEFAULT_INPUT.read_bytes())
        arguments = [
            "--input",
            str(paths["input"]),
            "--tables-output",
            str(paths["tables"]),
            "--lean-output",
            str(paths["lean"]),
            "--manifest-output",
            str(paths["manifest"]),
        ]

        assert generator.main(arguments) == 0
        assert generator.main([*arguments, "--check"]) == 0
        paths[stale_role].write_bytes(paths[stale_role].read_bytes() + b" ")
        assert generator.main([*arguments, "--check"]) == 1


def test_schema_rejects_floats_and_noncanonical_rationals() -> None:
    raw = generator.DEFAULT_INPUT.read_text()
    with_float = raw.replace('"random_seed": 20260820', '"random_seed": 20260820.0')
    try:
        generator.parse_input_bytes(with_float.encode())
    except generator.SchemaError as error:
        assert "floating-point" in str(error)
    else:  # pragma: no cover
        raise AssertionError("float-valued input was accepted")

    noncanonical = raw.replace('"gamma": "5/8"', '"gamma": "10/16"')
    try:
        generator.parse_input_bytes(noncanonical.encode())
    except generator.SchemaError as error:
        assert "canonical" in str(error)
    else:  # pragma: no cover
        raise AssertionError("noncanonical rational was accepted")


def test_schema_rejects_drift_in_a_named_policy_table() -> None:
    spec = generator.parse_input_bytes(generator.DEFAULT_INPUT.read_bytes())
    drifted = deepcopy(spec)
    drifted["target_policies"][0]["boost_probability_by_state"][0] = "3/4"
    try:
        generator.validate_spec(drifted)
    except generator.SchemaError as error:
        assert "frozen v1 policy rules" in str(error)
    else:  # pragma: no cover
        raise AssertionError("semantic drift in the conservative policy was accepted")
