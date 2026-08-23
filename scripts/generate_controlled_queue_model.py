#!/usr/bin/env python3
"""Compile the frozen controlled-queue model into exact deterministic tables.

This generator is deliberately dependency-free and fail-closed.  It validates
the exact v1 benchmark schema, rejects floating-point and duplicate-key JSON,
and emits byte-stable JSON, Lean data, and a SHA-256 manifest.

The generated artifacts are MODEL/PREPROCESSING ONLY.  They are not a
statistical certificate, do not produce a trajectory, and do not establish
membership of any path in a theorem-produced event.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "applications" / "controlled_queue" / "model-v1.json"
DEFAULT_TABLES = (
    ROOT / "applications" / "controlled_queue" / "generated" / "model-v1-tables.json"
)
DEFAULT_LEAN = ROOT / "FormalSLT" / "Applications" / "ControlledQueueData.lean"
DEFAULT_MANIFEST = (
    ROOT / "applications" / "controlled_queue" / "generated" / "model-v1-manifest.json"
)

SCHEMA_VERSION = "controlled-queue-input-v1"
MODEL_VERSION = "controlled-queue-v1"
GENERATOR_REVISION = "controlled-queue-preprocess-v1"
ARTIFACT_STATUS = "MODEL/PREPROCESSING ONLY"

STATE_COUNT = 24
ACTION_IDS = ("eco", "boost")
CANDIDATE_IDS = ("low", "nominal", "high")
TARGET_POLICY_IDS = (
    "conservative",
    "queue_threshold",
    "regime_aware",
    "aggressive",
)
FIXED_PREDICTOR_IDS = (
    "global_climatology",
    "queue_action_threshold",
    "nominal_model_overload",
)
CAUSAL_PREDICTOR_IDS = (
    "global_beta",
    "queue_band_action_beta",
)
NEXT_TRACE_REQUIRED_FIELDS = (
    "initial_state",
    "prng_contract",
    "sampling_contract",
)
NEXT_TRACE_REQUIRED_WEIGHT_TABLES = (
    "prior_weights",
    "posterior_weights",
    "candidate_weights",
    "coordinate_weights",
    "tilt_weights",
)


class SchemaError(ValueError):
    """Raised when the frozen input does not match the exact benchmark schema."""


def _reject_float(value: str) -> None:
    raise SchemaError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise SchemaError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SchemaError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_input_bytes(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SchemaError(f"invalid UTF-8 JSON: {error}") from error
    if not isinstance(value, dict):
        raise SchemaError("top-level JSON value must be an object")
    validate_spec(value)
    return value


def _expect_object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise SchemaError(f"{where} must be an object")
    return value


def _expect_list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise SchemaError(f"{where} must be an array")
    return value


def _expect_string(value: Any, where: str) -> str:
    if not isinstance(value, str):
        raise SchemaError(f"{where} must be a string")
    return value


def _expect_int(value: Any, where: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise SchemaError(f"{where} must be an integer")
    if minimum is not None and value < minimum:
        raise SchemaError(f"{where} must be at least {minimum}")
    return value


def _expect_keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise SchemaError(f"{where} keys mismatch; missing={missing}, extra={extra}")


def _expect_exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise SchemaError(f"{where} must be {expected!r}, got {actual!r}")


def parse_rational(value: Any, where: str) -> Fraction:
    text = _expect_string(value, where)
    try:
        result = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise SchemaError(f"{where} is not a rational string: {text!r}") from error
    if rational_text(result) != text:
        raise SchemaError(
            f"{where} must be canonical; expected {rational_text(result)!r}, got {text!r}"
        )
    return result


def rational_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _validate_probability(value: Any, where: str, *, positive: bool = False) -> Fraction:
    result = parse_rational(value, where)
    lower_ok = result > 0 if positive else result >= 0
    if not lower_ok or result > 1:
        qualifier = "(0, 1]" if positive else "[0, 1]"
        raise SchemaError(f"{where} must lie in {qualifier}, got {result}")
    return result


def _validate_policy(policy: Any, where: str, expected_id: str) -> None:
    obj = _expect_object(policy, where)
    _expect_keys(obj, {"id", "boost_probability_by_state"}, where)
    _expect_exact(obj["id"], expected_id, f"{where}.id")
    probabilities = _expect_list(
        obj["boost_probability_by_state"], f"{where}.boost_probability_by_state"
    )
    if len(probabilities) != STATE_COUNT:
        raise SchemaError(
            f"{where}.boost_probability_by_state must have {STATE_COUNT} entries"
        )
    for state, probability in enumerate(probabilities):
        _validate_probability(
            probability, f"{where}.boost_probability_by_state[{state}]", positive=True
        )


def validate_spec(spec: dict[str, Any]) -> None:
    _expect_keys(
        spec,
        {
            "schema_version",
            "model_version",
            "artifact_status",
            "state_space",
            "actions",
            "candidates",
            "nominal_candidate",
            "kernel",
            "behavior_policy",
            "target_policies",
            "fixed_predictors",
            "causal_predictors",
            "outcomes",
            "generation",
        },
        "input",
    )
    _expect_exact(spec["schema_version"], SCHEMA_VERSION, "schema_version")
    _expect_exact(spec["model_version"], MODEL_VERSION, "model_version")
    _expect_exact(spec["artifact_status"], ARTIFACT_STATUS, "artifact_status")

    state_space = _expect_object(spec["state_space"], "state_space")
    _expect_keys(
        state_space,
        {
            "queue_capacity",
            "regime_count",
            "encoding",
            "augmented_encoding",
            "update_order",
            "arrival_by_regime",
            "regime_transition",
        },
        "state_space",
    )
    _expect_exact(state_space["queue_capacity"], 7, "state_space.queue_capacity")
    _expect_exact(state_space["regime_count"], 3, "state_space.regime_count")
    _expect_exact(
        state_space["encoding"],
        "state_id = 3 * queue + regime",
        "state_space.encoding",
    )
    _expect_exact(
        state_space["augmented_encoding"],
        "augmented_state_id = 2 * state_id + action_index",
        "state_space.augmented_encoding",
    )
    _expect_exact(
        state_space["update_order"],
        ["service", "arrival", "regime_transition"],
        "state_space.update_order",
    )
    _expect_exact(
        state_space["arrival_by_regime"], [0, 1, 2], "state_space.arrival_by_regime"
    )
    _expect_exact(
        state_space["regime_transition"],
        "next_regime = (regime + 1) mod 3",
        "state_space.regime_transition",
    )

    actions = _expect_list(spec["actions"], "actions")
    if len(actions) != len(ACTION_IDS):
        raise SchemaError("actions must contain exactly eco and boost")
    for index, (action, expected_id, expected_capacity) in enumerate(
        zip(actions, ACTION_IDS, (1, 2), strict=True)
    ):
        where = f"actions[{index}]"
        obj = _expect_object(action, where)
        _expect_keys(obj, {"id", "service_capacity"}, where)
        _expect_exact(obj["id"], expected_id, f"{where}.id")
        _expect_exact(obj["service_capacity"], expected_capacity, f"{where}.service_capacity")

    candidates = _expect_list(spec["candidates"], "candidates")
    expected_gammas = (Fraction(5, 8), Fraction(3, 4), Fraction(7, 8))
    if len(candidates) != len(CANDIDATE_IDS):
        raise SchemaError("candidates must contain exactly low, nominal, and high")
    for index, (candidate, expected_id, expected_gamma) in enumerate(
        zip(candidates, CANDIDATE_IDS, expected_gammas, strict=True)
    ):
        where = f"candidates[{index}]"
        obj = _expect_object(candidate, where)
        _expect_keys(obj, {"id", "gamma"}, where)
        _expect_exact(obj["id"], expected_id, f"{where}.id")
        gamma = _validate_probability(obj["gamma"], f"{where}.gamma", positive=True)
        if gamma != expected_gamma:
            raise SchemaError(f"{where}.gamma must be {expected_gamma}")
    _expect_exact(spec["nominal_candidate"], "nominal", "nominal_candidate")

    kernel = _expect_object(spec["kernel"], "kernel")
    _expect_keys(kernel, {"form", "uniform_state_count"}, "kernel")
    _expect_exact(
        kernel["form"],
        "gamma * delta(queue_step) + (1 - gamma) * uniform",
        "kernel.form",
    )
    _expect_exact(kernel["uniform_state_count"], STATE_COUNT, "kernel.uniform_state_count")

    _validate_policy(spec["behavior_policy"], "behavior_policy", "behavior_uniform")
    behavior = spec["behavior_policy"]["boost_probability_by_state"]
    if any(parse_rational(value, "behavior probability") != Fraction(1, 2) for value in behavior):
        raise SchemaError("behavior policy must be exactly uniform at every state")

    target_policies = _expect_list(spec["target_policies"], "target_policies")
    if len(target_policies) != len(TARGET_POLICY_IDS):
        raise SchemaError("target_policies must contain exactly four declared policies")
    for index, (policy, expected_id) in enumerate(
        zip(target_policies, TARGET_POLICY_IDS, strict=True)
    ):
        _validate_policy(policy, f"target_policies[{index}]", expected_id)
        for state, value in enumerate(policy["boost_probability_by_state"]):
            probability = parse_rational(value, f"target_policies[{index}][{state}]")
            if probability not in {Fraction(1, 4), Fraction(3, 4)}:
                raise SchemaError(
                    f"target_policies[{index}] state {state} must use 1/4 or 3/4"
                )
    policy_probabilities = {
        policy["id"]: [
            parse_rational(value, f"policy {policy['id']} state {state}")
            for state, value in enumerate(policy["boost_probability_by_state"])
        ]
        for policy in target_policies
    }
    frozen_policy_rules = {
        "conservative": [Fraction(1, 4) for _state in range(STATE_COUNT)],
        "queue_threshold": [
            Fraction(3, 4) if state // 3 >= 4 else Fraction(1, 4)
            for state in range(STATE_COUNT)
        ],
        "regime_aware": [
            Fraction(3, 4)
            if state % 3 == 2 or state // 3 >= 6
            else Fraction(1, 4)
            for state in range(STATE_COUNT)
        ],
        "aggressive": [Fraction(3, 4) for _state in range(STATE_COUNT)],
    }
    if policy_probabilities != frozen_policy_rules:
        raise SchemaError("target policy tables do not match the frozen v1 policy rules")

    fixed_predictors = _expect_list(spec["fixed_predictors"], "fixed_predictors")
    if len(fixed_predictors) != len(FIXED_PREDICTOR_IDS):
        raise SchemaError("fixed_predictors must contain exactly the three declared predictors")
    fixed_expected = (
        {
            "id": "global_climatology",
            "kind": "constant",
            "probability": "1/4",
        },
        {
            "id": "queue_action_threshold",
            "kind": "deterministic_overload_threshold",
            "low_probability": "1/4",
            "high_probability": "3/4",
        },
        {
            "id": "nominal_model_overload",
            "kind": "candidate_overload_probability",
            "candidate": "nominal",
        },
    )
    for index, (actual, expected) in enumerate(
        zip(fixed_predictors, fixed_expected, strict=True)
    ):
        where = f"fixed_predictors[{index}]"
        obj = _expect_object(actual, where)
        _expect_keys(obj, set(expected), where)
        _expect_exact(obj, expected, where)
        for key in ("probability", "low_probability", "high_probability"):
            if key in obj:
                _validate_probability(obj[key], f"{where}.{key}")

    causal_predictors = _expect_list(spec["causal_predictors"], "causal_predictors")
    if len(causal_predictors) != len(CAUSAL_PREDICTOR_IDS):
        raise SchemaError("causal_predictors must contain exactly the two declared predictors")
    causal_expected = (
        {
            "id": "global_beta",
            "kind": "beta_global",
            "prior_alpha": 1,
            "prior_beta": 1,
            "history_contract": "transition indices strictly below t",
        },
        {
            "id": "queue_band_action_beta",
            "kind": "beta_queue_band_action",
            "prior_alpha": 1,
            "prior_beta": 1,
            "queue_bands": [[0, 3], [4, 5], [6, 7]],
            "history_contract": "transition indices strictly below t",
        },
    )
    for index, (actual, expected) in enumerate(
        zip(causal_predictors, causal_expected, strict=True)
    ):
        where = f"causal_predictors[{index}]"
        obj = _expect_object(actual, where)
        _expect_keys(obj, set(expected), where)
        _expect_exact(obj, expected, where)

    outcomes = _expect_object(spec["outcomes"], "outcomes")
    _expect_keys(
        outcomes,
        {
            "overload_queue_minimum",
            "control_cost_queue_weight",
            "control_cost_boost_weight",
            "control_cost_denominator",
        },
        "outcomes",
    )
    _expect_exact(outcomes["overload_queue_minimum"], 6, "outcomes.overload_queue_minimum")
    _expect_exact(outcomes["control_cost_queue_weight"], 8, "outcomes.control_cost_queue_weight")
    _expect_exact(outcomes["control_cost_boost_weight"], 7, "outcomes.control_cost_boost_weight")
    _expect_exact(outcomes["control_cost_denominator"], 63, "outcomes.control_cost_denominator")

    generation = _expect_object(spec["generation"], "generation")
    _expect_keys(
        generation,
        {
            "horizon",
            "random_seed",
            "confidence_allocation",
            "posterior_catalog",
            "depth_grid",
            "tilt_grid",
            "next_trace_slice_contract",
        },
        "generation",
    )
    _expect_int(generation["horizon"], "generation.horizon", minimum=1)
    _expect_int(generation["random_seed"], "generation.random_seed", minimum=0)
    allocation = _expect_object(
        generation["confidence_allocation"], "generation.confidence_allocation"
    )
    _expect_keys(allocation, {"total", "trajectory", "transition"}, "confidence_allocation")
    total = _validate_probability(allocation["total"], "confidence_allocation.total", positive=True)
    trajectory = _validate_probability(
        allocation["trajectory"], "confidence_allocation.trajectory", positive=True
    )
    transition = _validate_probability(
        allocation["transition"], "confidence_allocation.transition", positive=True
    )
    if trajectory + transition != total:
        raise SchemaError("trajectory and transition allocations must sum to total")
    _expect_exact(
        generation["posterior_catalog"],
        list(FIXED_PREDICTOR_IDS + CAUSAL_PREDICTOR_IDS),
        "generation.posterior_catalog",
    )
    depth_grid = _expect_list(generation["depth_grid"], "generation.depth_grid")
    depths = [
        _expect_int(value, f"generation.depth_grid[{index}]", minimum=0)
        for index, value in enumerate(depth_grid)
    ]
    if depths != sorted(set(depths)) or not depths:
        raise SchemaError("generation.depth_grid must be nonempty, sorted, and unique")
    tilt_grid = _expect_list(generation["tilt_grid"], "generation.tilt_grid")
    tilts = [
        parse_rational(value, f"generation.tilt_grid[{index}]")
        for index, value in enumerate(tilt_grid)
    ]
    if not tilts or any(value <= 0 for value in tilts) or tilts != sorted(set(tilts)):
        raise SchemaError("generation.tilt_grid must be positive, nonempty, sorted, and unique")
    next_trace = _expect_object(
        generation["next_trace_slice_contract"],
        "generation.next_trace_slice_contract",
    )
    _expect_keys(
        next_trace,
        {
            "status",
            "prng_sampling_requirement",
            "required_fields",
            "required_exact_weight_tables",
        },
        "generation.next_trace_slice_contract",
    )
    _expect_exact(
        next_trace["status"], "OPEN", "generation.next_trace_slice_contract.status"
    )
    _expect_exact(
        next_trace["prng_sampling_requirement"],
        "language-independent, versioned, byte-reproducible",
        "generation.next_trace_slice_contract.prng_sampling_requirement",
    )
    _expect_exact(
        next_trace["required_fields"],
        list(NEXT_TRACE_REQUIRED_FIELDS),
        "generation.next_trace_slice_contract.required_fields",
    )
    _expect_exact(
        next_trace["required_exact_weight_tables"],
        list(NEXT_TRACE_REQUIRED_WEIGHT_TABLES),
        "generation.next_trace_slice_contract.required_exact_weight_tables",
    )


def state_id(queue: int, regime: int) -> int:
    return 3 * queue + regime


def queue_step(spec: dict[str, Any], source: int, action_index: int) -> int:
    regime_count = spec["state_space"]["regime_count"]
    queue_capacity = spec["state_space"]["queue_capacity"]
    queue, regime = divmod(source, regime_count)
    service = spec["actions"][action_index]["service_capacity"]
    arrival = spec["state_space"]["arrival_by_regime"][regime]
    next_queue = min(queue_capacity, max(0, queue - service) + arrival)
    next_regime = (regime + 1) % regime_count
    return state_id(next_queue, next_regime)


def _policy_table(policy: dict[str, Any]) -> dict[str, Any]:
    rows = []
    for source, boost_text in enumerate(policy["boost_probability_by_state"]):
        boost = parse_rational(boost_text, f"policy {policy['id']} state {source}")
        rows.append(
            {
                "state": source,
                "probabilities": [rational_text(1 - boost), rational_text(boost)],
            }
        )
    return {"id": policy["id"], "rows": rows}


def build_tables(spec: dict[str, Any]) -> dict[str, Any]:
    states = [
        {"id": source, "queue": source // 3, "regime": source % 3}
        for source in range(STATE_COUNT)
    ]
    actions = [
        {
            "id": action["id"],
            "index": index,
            "service_capacity": action["service_capacity"],
        }
        for index, action in enumerate(spec["actions"])
    ]
    augmented_behavior_states = [
        {
            "id": len(ACTION_IDS) * source + action_index,
            "state": source,
            "action": action_id,
            "action_index": action_index,
        }
        for source in range(STATE_COUNT)
        for action_index, action_id in enumerate(ACTION_IDS)
    ]
    steps = [
        {
            "state": source,
            "action": ACTION_IDS[action_index],
            "next_state": queue_step(spec, source, action_index),
        }
        for source in range(STATE_COUNT)
        for action_index in range(len(ACTION_IDS))
    ]

    candidate_tables = []
    candidate_gamma: dict[str, Fraction] = {}
    for candidate in spec["candidates"]:
        gamma = parse_rational(candidate["gamma"], f"candidate {candidate['id']} gamma")
        candidate_gamma[candidate["id"]] = gamma
        base = (1 - gamma) / STATE_COUNT
        rows = []
        for source in range(STATE_COUNT):
            for action_index, action_id in enumerate(ACTION_IDS):
                step = queue_step(spec, source, action_index)
                probabilities = [
                    rational_text(base + (gamma if destination == step else 0))
                    for destination in range(STATE_COUNT)
                ]
                rows.append(
                    {
                        "state": source,
                        "action": action_id,
                        "probabilities": probabilities,
                    }
                )
        candidate_tables.append(
            {
                "id": candidate["id"],
                "gamma": rational_text(gamma),
                "uniform_mass_per_state": rational_text(base),
                "rows": rows,
            }
        )

    policies = [_policy_table(spec["behavior_policy"])] + [
        _policy_table(policy) for policy in spec["target_policies"]
    ]

    fixed_predictors = []
    nominal_gamma = candidate_gamma[spec["nominal_candidate"]]
    overload_minimum = spec["outcomes"]["overload_queue_minimum"]
    overload_state_count = (
        spec["state_space"]["queue_capacity"] - overload_minimum + 1
    ) * spec["state_space"]["regime_count"]
    uniform_overload_probability = Fraction(overload_state_count, STATE_COUNT)
    for predictor in spec["fixed_predictors"]:
        rows = []
        for source in range(STATE_COUNT):
            for action_index, action_id in enumerate(ACTION_IDS):
                step_overloads = (
                    queue_step(spec, source, action_index) // 3 >= overload_minimum
                )
                if predictor["kind"] == "constant":
                    probability = parse_rational(
                        predictor["probability"], f"predictor {predictor['id']}"
                    )
                elif predictor["kind"] == "deterministic_overload_threshold":
                    probability = parse_rational(
                        predictor[
                            "high_probability" if step_overloads else "low_probability"
                        ],
                        f"predictor {predictor['id']}",
                    )
                elif predictor["kind"] == "candidate_overload_probability":
                    probability = (
                        (1 - nominal_gamma) * uniform_overload_probability
                        + (nominal_gamma if step_overloads else 0)
                    )
                else:  # pragma: no cover - validation makes this unreachable
                    raise AssertionError(f"unsupported predictor kind: {predictor['kind']}")
                rows.append(
                    {
                        "state": source,
                        "action": action_id,
                        "overload_probability": rational_text(probability),
                    }
                )
        fixed_predictors.append(
            {"id": predictor["id"], "kind": predictor["kind"], "rows": rows}
        )

    control_cost = []
    queue_weight = spec["outcomes"]["control_cost_queue_weight"]
    boost_weight = spec["outcomes"]["control_cost_boost_weight"]
    cost_denominator = spec["outcomes"]["control_cost_denominator"]
    for action_index, action_id in enumerate(ACTION_IDS):
        boost_indicator = 1 if action_id == "boost" else 0
        for destination in range(STATE_COUNT):
            next_queue = destination // 3
            value = Fraction(
                queue_weight * next_queue + boost_weight * boost_indicator,
                cost_denominator,
            )
            control_cost.append(
                {
                    "action": action_id,
                    "next_state": destination,
                    "value": rational_text(value),
                }
            )

    overload_outcome = [
        {
            "next_state": destination,
            "value": 1 if destination // 3 >= overload_minimum else 0,
        }
        for destination in range(STATE_COUNT)
    ]

    fixed_brier_loss = []
    for predictor in fixed_predictors:
        rows = []
        for predictor_row in predictor["rows"]:
            probability = Fraction(predictor_row["overload_probability"])
            losses = []
            for destination in range(STATE_COUNT):
                outcome = Fraction(1 if destination // 3 >= overload_minimum else 0)
                losses.append(rational_text((probability - outcome) ** 2))
            rows.append(
                {
                    "state": predictor_row["state"],
                    "action": predictor_row["action"],
                    "losses": losses,
                }
            )
        fixed_brier_loss.append({"id": predictor["id"], "rows": rows})

    generation = spec["generation"]
    return {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": SCHEMA_VERSION,
        "model_version": MODEL_VERSION,
        "generator_revision": GENERATOR_REVISION,
        "nonclaims": [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not an unknown-kernel target-policy OPE result",
        ],
        "dimensions": {
            "physical_state_count": STATE_COUNT,
            "action_count": len(ACTION_IDS),
            "augmented_behavior_state_count": STATE_COUNT * len(ACTION_IDS),
            "candidate_count": len(CANDIDATE_IDS),
            "target_policy_count": len(TARGET_POLICY_IDS),
            "fixed_predictor_count": len(FIXED_PREDICTOR_IDS),
            "causal_predictor_count": len(CAUSAL_PREDICTOR_IDS),
        },
        "states": states,
        "actions": actions,
        "augmented_behavior_states": augmented_behavior_states,
        "queue_step": steps,
        "candidate_kernels": candidate_tables,
        "policies": policies,
        "fixed_predictors": fixed_predictors,
        "causal_predictors": spec["causal_predictors"],
        "control_cost": control_cost,
        "overload_outcome": overload_outcome,
        "fixed_brier_loss": fixed_brier_loss,
        "generation_parameters": {
            "horizon": generation["horizon"],
            "random_seed": generation["random_seed"],
            "confidence_allocation": generation["confidence_allocation"],
            "posterior_catalog": generation["posterior_catalog"],
            "depth_grid": generation["depth_grid"],
            "tilt_grid": generation["tilt_grid"],
            "next_trace_slice_contract": generation["next_trace_slice_contract"],
        },
    }


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _lean_rat(value: str | int) -> str:
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return f"({fraction.numerator} : ℚ)"
    return f"(({fraction.numerator} : ℚ) / {fraction.denominator})"


def _render_list(values: Sequence[str], *, indent: int = 2) -> str:
    if not values:
        return "[]"
    prefix = " " * indent
    continuation = ",\n" + prefix
    return "[\n" + prefix + continuation.join(values) + "\n" + " " * (indent - 2) + "]"


def _render_nested_rational_table(table: Any, depth: int = 0) -> str:
    if isinstance(table, list):
        rendered = [_render_nested_rational_table(value, depth + 1) for value in table]
        return _render_list(rendered, indent=2 * (depth + 1))
    return _lean_rat(table)


def _render_nested_nat_table(table: Any, depth: int = 0) -> str:
    if isinstance(table, list):
        rendered = [_render_nested_nat_table(value, depth + 1) for value in table]
        return _render_list(rendered, indent=2 * (depth + 1))
    if isinstance(table, bool) or not isinstance(table, int) or table < 0:
        raise AssertionError(f"expected a natural-number table entry, got {table!r}")
    return str(table)


def validate_candidate_kernel_compaction(tables: dict[str, Any]) -> None:
    """Fail unless materialized kernel cells equal the compact Lean formula.

    The JSON artifact retains all candidate-kernel cells, while the Lean
    artifact reconstructs them from candidate gamma values and one deterministic
    destination per state-action row.  Validate both positional contracts and
    every exact rational before allowing that compact representation to render.
    """

    expected_rows = [
        (source, action_id)
        for source in range(STATE_COUNT)
        for action_id in ACTION_IDS
    ]
    queue_rows = _expect_list(tables.get("queue_step"), "generated.queue_step")
    if len(queue_rows) != len(expected_rows):
        raise SchemaError(
            "generated.queue_step must contain exactly "
            f"{len(expected_rows)} state-action rows"
        )

    compact_steps: list[int] = []
    for row_index, (row, (expected_state, expected_action)) in enumerate(
        zip(queue_rows, expected_rows, strict=True)
    ):
        where = f"generated.queue_step[{row_index}]"
        row_object = _expect_object(row, where)
        _expect_keys(row_object, {"state", "action", "next_state"}, where)
        _expect_exact(row_object["state"], expected_state, f"{where}.state")
        _expect_exact(row_object["action"], expected_action, f"{where}.action")
        next_state = _expect_int(
            row_object["next_state"], f"{where}.next_state", minimum=0
        )
        if next_state >= STATE_COUNT:
            raise SchemaError(
                f"{where}.next_state must be below {STATE_COUNT}, got {next_state}"
            )
        compact_steps.append(next_state)

    candidates = _expect_list(
        tables.get("candidate_kernels"), "generated.candidate_kernels"
    )
    if len(candidates) != len(CANDIDATE_IDS):
        raise SchemaError(
            "generated.candidate_kernels must contain exactly "
            f"{len(CANDIDATE_IDS)} candidates"
        )

    for candidate_index, (candidate, expected_id) in enumerate(
        zip(candidates, CANDIDATE_IDS, strict=True)
    ):
        where = f"generated.candidate_kernels[{candidate_index}]"
        candidate_object = _expect_object(candidate, where)
        _expect_keys(
            candidate_object,
            {"id", "gamma", "uniform_mass_per_state", "rows"},
            where,
        )
        _expect_exact(candidate_object["id"], expected_id, f"{where}.id")
        gamma = parse_rational(candidate_object["gamma"], f"{where}.gamma")
        base = (1 - gamma) / STATE_COUNT
        uniform_mass = parse_rational(
            candidate_object["uniform_mass_per_state"],
            f"{where}.uniform_mass_per_state",
        )
        if uniform_mass != base:
            raise SchemaError(
                f"{where}.uniform_mass_per_state must be {rational_text(base)!r}, "
                f"got {candidate_object['uniform_mass_per_state']!r}"
            )

        rows = _expect_list(candidate_object["rows"], f"{where}.rows")
        if len(rows) != len(expected_rows):
            raise SchemaError(
                f"{where}.rows must contain exactly {len(expected_rows)} rows"
            )
        for row_index, (row, (expected_state, expected_action), step) in enumerate(
            zip(rows, expected_rows, compact_steps, strict=True)
        ):
            row_where = f"{where}.rows[{row_index}]"
            row_object = _expect_object(row, row_where)
            _expect_keys(
                row_object, {"state", "action", "probabilities"}, row_where
            )
            _expect_exact(
                row_object["state"], expected_state, f"{row_where}.state"
            )
            _expect_exact(
                row_object["action"], expected_action, f"{row_where}.action"
            )
            probabilities = _expect_list(
                row_object["probabilities"], f"{row_where}.probabilities"
            )
            if len(probabilities) != STATE_COUNT:
                raise SchemaError(
                    f"{row_where}.probabilities must contain exactly "
                    f"{STATE_COUNT} destinations"
                )
            for destination, probability in enumerate(probabilities):
                cell_where = f"{row_where}.probabilities[{destination}]"
                actual = parse_rational(probability, cell_where)
                expected = base + (gamma if destination == step else 0)
                if actual != expected:
                    raise SchemaError(
                        f"{cell_where} must be {rational_text(expected)!r} from "
                        "candidate gamma and candidateKernelStep, "
                        f"got {probability!r}"
                    )


def render_lean(tables: dict[str, Any]) -> bytes:
    validate_candidate_kernel_compaction(tables)
    coordinates = [f"({row['queue']}, {row['regime']})" for row in tables["states"]]
    action_names = [_lean_string(row["id"]) for row in tables["actions"]]
    services = [str(row["service_capacity"]) for row in tables["actions"]]
    augmented_behavior_states = [
        f"({row['state']}, {row['action_index']})"
        for row in tables["augmented_behavior_states"]
    ]
    queue_steps = []
    for source in range(STATE_COUNT):
        source_rows = [
            row["next_state"] for row in tables["queue_step"] if row["state"] == source
        ]
        queue_steps.append(source_rows)
    candidate_kernel_steps = [
        f"({row['next_state']} : Fin 24)" for row in tables["queue_step"]
    ]
    candidate_names = [_lean_string(row["id"]) for row in tables["candidate_kernels"]]
    candidate_gammas = [row["gamma"] for row in tables["candidate_kernels"]]
    policy_names = [_lean_string(policy["id"]) for policy in tables["policies"]]
    policy_table = [
        [row["probabilities"] for row in policy["rows"]]
        for policy in tables["policies"]
    ]
    predictor_names = [
        _lean_string(predictor["id"]) for predictor in tables["fixed_predictors"]
    ]
    predictor_table = [
        [row["overload_probability"] for row in predictor["rows"]]
        for predictor in tables["fixed_predictors"]
    ]
    causal_names = [
        _lean_string(predictor["id"]) for predictor in tables["causal_predictors"]
    ]
    control_cost_table = []
    for action_id in ACTION_IDS:
        control_cost_table.append(
            [
                row["value"]
                for row in tables["control_cost"]
                if row["action"] == action_id
            ]
        )
    outcome_table = [row["value"] for row in tables["overload_outcome"]]
    brier_table = [
        [row["losses"] for row in predictor["rows"]]
        for predictor in tables["fixed_brier_loss"]
    ]
    allocation = tables["generation_parameters"]["confidence_allocation"]
    allocation_table = _render_nested_rational_table(
        [allocation["total"], allocation["trajectory"], allocation["transition"]]
    )

    content = f'''/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Mathlib.Data.Rat.Defs

/-!
# Generated controlled-queue benchmark data

Status: **MODEL/PREPROCESSING ONLY**.

This file is generated by `scripts/generate_controlled_queue_model.py` from the
frozen `applications/controlled_queue/model-v1.json` input.  It contains exact
rational definitions and tables only.  It is not a statistical certificate,
does not define a theorem-produced good path, and does not prove any
unknown-kernel target-policy OPE statement.

Table order is fixed: physical states use `3 * queue + regime`; actions are
`eco`, then `boost`; kernel and predictor rows use state-major/action-minor
order; kernel columns use physical-state order.
-/

namespace FormalSLT.Applications.ControlledQueueData

/-- Frozen input-schema identifier. -/
def schemaVersion : String := {_lean_string(SCHEMA_VERSION)}

/-- Frozen model identifier. -/
def modelVersion : String := {_lean_string(MODEL_VERSION)}

/-- Generator contract identifier. -/
def generatorRevision : String := {_lean_string(GENERATOR_REVISION)}

/-- This module's claim boundary. -/
def artifactStatus : String := {_lean_string(ARTIFACT_STATUS)}

/-- The 24 physical states.  No stochastic semantics are attached here. -/
abbrev PhysicalState := Fin 24

/-- The two action indices.  No policy semantics are attached here. -/
abbrev Action := Fin 2

/-- `(queue, regime)` coordinates in physical-state order. -/
def stateCoordinates : List (Nat × Nat) := {_render_list(coordinates)}

/-- Action names in action-index order. -/
def actionNames : List String := {_render_list(action_names)}

/-- Service capacities in action-index order. -/
def serviceCapacities : List Nat := {_render_list(services)}

/-- `(physical state, action)` pairs in 48-state augmented order. -/
def augmentedBehaviorStateTable : List (Nat × Nat) :=
  {_render_list(augmented_behavior_states)}

/-- Deterministic queue-step target state, indexed by state then action. -/
def queueStepTable : List (List Nat) := {_render_nested_nat_table(queue_steps)}

/-- Candidate identifiers in kernel-table order. -/
def candidateNames : List String := {_render_list(candidate_names)}

/-- Candidate persistence parameters. -/
def candidateGammaTable : List ℚ := {_render_nested_rational_table(candidate_gammas)}

/-- Deterministic persistence destination in state-action row order. -/
def candidateKernelStepByRow : List (Fin 24) :=
  {_render_list(candidate_kernel_steps)}

/-- One refresh-mixture row with persistence mass at `nextState`. -/
def candidateKernelRow (gamma : ℚ) (nextState : Fin 24) : List ℚ :=
  List.ofFn fun destination : Fin 24 ↦
    (1 - gamma) / 24 + if destination = nextState then gamma else 0

/-- Exact candidate kernels, indexed by candidate, state-action row, and next
state.  The Lean representation uses the frozen refresh-mixture formula; the
companion JSON artifact retains every materialized rational cell. -/
def candidateKernelTable : List (List (List ℚ)) :=
  candidateGammaTable.map fun gamma ↦
    candidateKernelStepByRow.map fun nextState ↦
      candidateKernelRow gamma nextState

/-- Behavior policy followed by the four target-policy identifiers. -/
def policyNames : List String := {_render_list(policy_names)}

/-- Exact action probabilities, indexed by policy, physical state, and action. -/
def policyTable : List (List (List ℚ)) :=
  {_render_nested_rational_table(policy_table)}

/-- Fixed predictor identifiers in prediction-table order. -/
def fixedPredictorNames : List String := {_render_list(predictor_names)}

/-- Exact overload forecasts, indexed by predictor and state-action row. -/
def fixedPredictorTable : List (List ℚ) :=
  {_render_nested_rational_table(predictor_table)}

/-- Declared causal predictor identifiers.  Their histories are not generated here. -/
def causalPredictorNames : List String := {_render_list(causal_names)}

/-- Exact control cost, indexed by action and next state. -/
def controlCostTable : List (List ℚ) :=
  {_render_nested_rational_table(control_cost_table)}

/-- Binary overload outcome in next-state order. -/
def overloadOutcomeTable : List ℚ :=
  {_render_nested_rational_table(outcome_table)}

/-- Fixed-predictor Brier losses, indexed by predictor, state-action row, and next state. -/
def fixedBrierLossTable : List (List (List ℚ)) :=
  {_render_nested_rational_table(brier_table)}

/-- Reserved future trace horizon.  No trace is generated in this slice. -/
def horizon : Nat := {tables['generation_parameters']['horizon']}

/-- Reserved future deterministic trace seed.  No trace is generated in this slice. -/
def randomSeed : Nat := {tables['generation_parameters']['random_seed']}

/-- Declared total, trajectory, and transition failure budgets. -/
def confidenceAllocation : List ℚ :=
  {allocation_table}

/-- Predeclared finite depth grid. -/
def depthGrid : List Nat :=
  {_render_list([str(value) for value in tables['generation_parameters']['depth_grid']])}

/-- Predeclared finite tilt grid. -/
def tiltGrid : List ℚ :=
  {_render_nested_rational_table(tables['generation_parameters']['tilt_grid'])}

end FormalSLT.Applications.ControlledQueueData
'''
    return content.encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _display_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.name


def build_manifest(
    spec: dict[str, Any],
    input_path: Path,
    input_bytes: bytes,
    tables_path: Path,
    tables_bytes: bytes,
    lean_path: Path,
    lean_bytes: bytes,
) -> dict[str, Any]:
    generator_path = Path(__file__).resolve()
    generation = spec["generation"]
    return {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": SCHEMA_VERSION,
        "model_version": MODEL_VERSION,
        "generator": {
            "path": _display_path(generator_path),
            "revision": GENERATOR_REVISION,
            "sha256": sha256_bytes(generator_path.read_bytes()),
        },
        "parameters": {
            "physical_state_count": STATE_COUNT,
            "action_count": len(ACTION_IDS),
            "augmented_behavior_state_count": STATE_COUNT * len(ACTION_IDS),
            "candidate_gammas": [candidate["gamma"] for candidate in spec["candidates"]],
            "nominal_candidate": spec["nominal_candidate"],
            "horizon": generation["horizon"],
            "random_seed": generation["random_seed"],
            "confidence_allocation": generation["confidence_allocation"],
            "posterior_catalog": generation["posterior_catalog"],
            "depth_grid": generation["depth_grid"],
            "tilt_grid": generation["tilt_grid"],
            "next_trace_slice_contract": generation["next_trace_slice_contract"],
        },
        "files": [
            {
                "role": "input",
                "path": _display_path(input_path),
                "sha256": sha256_bytes(input_bytes),
            },
            {
                "role": "output",
                "path": _display_path(tables_path),
                "sha256": sha256_bytes(tables_bytes),
            },
            {
                "role": "output",
                "path": _display_path(lean_path),
                "sha256": sha256_bytes(lean_bytes),
            },
        ],
        "nonclaims": [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not a proof bridge",
        ],
    }


def expected_artifacts(
    input_path: Path, tables_path: Path, lean_path: Path
) -> tuple[bytes, bytes, bytes]:
    input_bytes = input_path.read_bytes()
    spec = parse_input_bytes(input_bytes)
    tables = build_tables(spec)
    tables_bytes = canonical_json_bytes(tables)
    lean_bytes = render_lean(tables)
    manifest = build_manifest(
        spec,
        input_path,
        input_bytes,
        tables_path,
        tables_bytes,
        lean_path,
        lean_bytes,
    )
    return tables_bytes, lean_bytes, canonical_json_bytes(manifest)


def _write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _check_exact(path: Path, expected: bytes) -> bool:
    try:
        actual = path.read_bytes()
    except FileNotFoundError:
        print(f"missing generated artifact: {path}", file=sys.stderr)
        return False
    if actual != expected:
        print(f"stale generated artifact: {path}", file=sys.stderr)
        return False
    return True


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--tables-output", type=Path, default=DEFAULT_TABLES)
    parser.add_argument("--lean-output", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--manifest-output", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless all generated artifacts are byte-identical to fresh output",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        tables_bytes, lean_bytes, manifest_bytes = expected_artifacts(
            args.input, args.tables_output, args.lean_output
        )
    except (OSError, SchemaError) as error:
        print(f"controlled-queue generation failed: {error}", file=sys.stderr)
        return 2

    artifacts = (
        (args.tables_output, tables_bytes),
        (args.lean_output, lean_bytes),
        (args.manifest_output, manifest_bytes),
    )
    if args.check:
        return 0 if all(_check_exact(path, data) for path, data in artifacts) else 1

    for path, data in artifacts:
        _write_atomic(path, data)
        print(f"wrote {path} ({len(data)} bytes, sha256={sha256_bytes(data)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
