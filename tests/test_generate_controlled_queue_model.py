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


def test_control_cost_and_fixed_brier_losses_are_bounded() -> None:
    _spec, tables = load_spec_and_tables()

    control_costs = [Fraction(row["value"]) for row in tables["control_cost"]]
    assert min(control_costs) == 0
    assert max(control_costs) == 1
    assert all(Fraction(0) <= value <= Fraction(1) for value in control_costs)

    brier_losses = [
        Fraction(value)
        for predictor in tables["fixed_brier_loss"]
        for row in predictor["rows"]
        for value in row["losses"]
    ]
    assert brier_losses
    assert all(Fraction(0) <= value <= Fraction(1) for value in brier_losses)


def test_nominal_predictor_is_compiled_from_the_nominal_kernel() -> None:
    _spec, tables = load_spec_and_tables()
    nominal_kernel = next(
        candidate for candidate in tables["candidate_kernels"] if candidate["id"] == "nominal"
    )
    nominal_predictor = next(
        predictor
        for predictor in tables["fixed_predictors"]
        if predictor["id"] == "nominal_model_overload"
    )
    overload_states = {
        row["next_state"]
        for row in tables["overload_outcome"]
        if row["value"] == 1
    }

    for kernel_row, predictor_row in zip(
        nominal_kernel["rows"], nominal_predictor["rows"], strict=True
    ):
        kernel_probability = sum(
            Fraction(probability)
            for destination, probability in enumerate(kernel_row["probabilities"])
            if destination in overload_states
        )
        assert kernel_probability == Fraction(predictor_row["overload_probability"])


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


def test_check_mode_fails_closed_on_stale_manifest(tmp_path: Path) -> None:
    input_path = tmp_path / "model-v1.json"
    tables_path = tmp_path / "model-v1-tables.json"
    lean_path = tmp_path / "ControlledQueueData.lean"
    manifest_path = tmp_path / "model-v1-manifest.json"
    input_path.write_bytes(generator.DEFAULT_INPUT.read_bytes())
    arguments = [
        "--input",
        str(input_path),
        "--tables-output",
        str(tables_path),
        "--lean-output",
        str(lean_path),
        "--manifest-output",
        str(manifest_path),
    ]

    assert generator.main(arguments) == 0
    assert generator.main([*arguments, "--check"]) == 0
    manifest_path.write_bytes(manifest_path.read_bytes() + b" ")
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
