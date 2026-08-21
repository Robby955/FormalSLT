#!/usr/bin/env python3
"""Fail-closed checker for the prospective structured queue OPE protocol.

This checker validates a protocol document only.  It must not generate a
trajectory, inspect prospective counts, choose an analysis, or write any
receipt.  In particular, validation fails if any path reserved for a
prospective output already exists.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, NoReturn, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = (
    ROOT
    / "applications"
    / "controlled_queue"
    / "structured-ope-protocol-v1.json"
)

SCHEMA_VERSION = "controlled-queue-structured-ope-preregistration-v1"
PROTOCOL_VERSION = "controlled-queue-structured-ope-protocol-v1"
ARTIFACT_STATUS = "PROSPECTIVE PROTOCOL ONLY - NO TRACE OR RESULT"
HORIZON = 200_000

TRUE_GAMMA = Fraction(149, 200)
TRUE_HIT_PROBABILITY = Fraction(1209, 1600)
NOMINAL_GAMMA = Fraction(3, 4)
NOMINAL_HIT_PROBABILITY = Fraction(73, 96)
NOMINAL_ROW_TV = Fraction(23, 4800)

PRNG_DOMAIN = "FormalSLT/controlled-queue/prospective-structured-ope-v1"
PRNG_TEST_SEED_HEX = (
    "ac40e6b078e9298f9b271e6d7ed690b8911fa1e3f7005deff855ca43d94d5fcf"
)
PRNG_TEST_COUNTER_ZERO_DIGEST_HEX = (
    "02be0e953603f95244eea43f8a16795185b337e881a64248d260219cfb7721ca"
)
EXPECTED_PROTOCOL_SHA256 = (
    "e62fa5d4896c50c04c50a709bf5b380fa037e40898197f7bb269c77d95799742"
)

CANDIDATE_SUPPORT = ("low", "nominal", "high")
CANDIDATE_GAMMAS = ("5/8", "3/4", "7/8")
DEPTH_SUPPORT = (0, 1, 2, 3, 5, 8, 12)
ADMISSIBLE_TILT_SUPPORT = ("1/16", "1/8", "1/4", "1/2")
TARGET_POLICY_SUPPORT = (
    "conservative",
    "queue_threshold",
    "regime_aware",
    "aggressive",
)
FIXED_PREDICTOR_SUPPORT = (
    "global_climatology",
    "queue_action_threshold",
    "nominal_model_overload",
)
HYPOTHESIS_SUPPORT = tuple(
    f"{policy}/{predictor}"
    for policy in TARGET_POLICY_SUPPORT
    for predictor in FIXED_PREDICTOR_SUPPORT
)

EXPECTED_BINDINGS = {
    "lake_manifest": {
        "path": "lake-manifest.json",
        "sha256": "52d60d1a48be7143c261c93c4f375c92a814a2499e2c320325b5f4e5855a8a66",
    },
    "lean_toolchain": {
        "path": "lean-toolchain",
        "sha256": "2bdc48adfa58d0017e538a0ad117c5d73d35deec879978f909406a80c8037273",
    },
    "model_input": {
        "path": "applications/controlled_queue/model-v1.json",
        "sha256": "4e92a71ddf07e04e202c901d8c7a682cdf306754a69a0e219fca8ef75abee5a0",
    },
    "model_manifest": {
        "path": "applications/controlled_queue/generated/model-v1-manifest.json",
        "sha256": "25c4a3ae364023b68a1de77ceff30d9e812f2e7173e36a3142ad0deec3d4a289",
    },
    "model_tables": {
        "path": "applications/controlled_queue/generated/model-v1-tables.json",
        "sha256": "7d8cf4d970f6e41413ccdf7d62b13bc77418076836505d06ebb4a606493ab724",
    },
    "persistence_confidence_source": {
        "path": "FormalSLT/Applications/ControlledQueuePersistenceConfidence.lean",
        "sha256": "5e0d9ce372505b50ad5fbae6f9fb07b9b5e37fef5a6658afe0e46ee2c652bd43",
    },
    "structured_ope_source": {
        "path": "FormalSLT/Applications/ControlledQueueStructuredOPE.lean",
        "sha256": "d7b2669b70774d82bdca2dd338495988a543c94f283e558f278b610198a8d7b4",
    },
    "known_kernel_receipt_source": {
        "path": "FormalSLT/Applications/ControlledQueueKnownKernelReceipt.lean",
        "sha256": "a92e58c2789161d6836ba934f5204b670dda11e0040687bc8ea05fe5645e5b0e",
    },
    "pilot_selected_potential_data": {
        "path": "FormalSLT/Applications/ControlledQueueKnownKernelReceiptData.lean",
        "sha256": "f1e47658b26a5bdd6064fc8ae5fc9abebc6710520793fd0f63369566d392d1a2",
    },
}

SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")


class ProtocolError(ValueError):
    """Raised when the prospective protocol violates its frozen contract."""


def _fail(message: str) -> NoReturn:
    raise ProtocolError(message)


def _reject_float(value: str) -> NoReturn:
    _fail(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> NoReturn:
    _fail(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json_bytes(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError(f"invalid UTF-8 JSON in {where}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def rational_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        _fail(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ProtocolError(f"invalid rational at {where}: {value!r}") from error
    if rational_text(result) != value:
        _fail(f"noncanonical rational at {where}: {value!r}")
    return result


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        _fail(f"{where} must be an object")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        _fail(f"{where} must be an array")
    return value


def _keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    if actual != expected:
        _fail(
            f"{where} keys mismatch; missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def _exact(actual: Any, expected: Any, where: str) -> None:
    # ``bool`` is an ``int`` subclass in Python.  Type-sensitive equality is
    # necessary for fail-closed JSON validation of integer fields.
    if type(actual) is not type(expected) or actual != expected:
        _fail(f"{where} must be {expected!r}, got {actual!r}")


def _exact_tree(actual: Any, expected: Any, where: str) -> None:
    """Recursively compare values while reporting exact nested key sets."""

    if isinstance(expected, dict):
        row = _object(actual, where)
        _keys(row, set(expected), where)
        for key, expected_value in expected.items():
            _exact_tree(row[key], expected_value, f"{where}.{key}")
        return
    if isinstance(expected, list):
        entries = _array(actual, where)
        if len(entries) != len(expected):
            _fail(f"{where} must contain {len(expected)} entries")
        for index, (entry, expected_value) in enumerate(zip(entries, expected)):
            _exact_tree(entry, expected_value, f"{where}[{index}]")
        return
    _exact(actual, expected, where)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _resolve_repository_path(path_text: Any, where: str) -> Path:
    if not isinstance(path_text, str):
        _fail(f"{where} must be a string")
    if not path_text or Path(path_text).is_absolute():
        _fail(f"{where} must be a nonempty repository-relative path")
    path = (ROOT / path_text).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise ProtocolError(f"{where} escapes the repository root") from error
    return path


def _validate_bindings(value: Any) -> None:
    bindings = _object(value, "bindings")
    _keys(bindings, set(EXPECTED_BINDINGS), "bindings")
    for role, expected in EXPECTED_BINDINGS.items():
        row = _object(bindings[role], f"bindings.{role}")
        _keys(row, {"path", "sha256"}, f"bindings.{role}")
        _exact(row, expected, f"bindings.{role}")
        digest = row["sha256"]
        if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
            _fail(f"bindings.{role}.sha256 must be a lowercase SHA-256 digest")
        path = _resolve_repository_path(row["path"], f"bindings.{role}.path")
        if not path.is_file():
            _fail(f"bindings.{role}.path is not a file: {row['path']}")
        _exact(_sha256(path.read_bytes()), digest, f"bindings.{role}.sha256")


def _validate_registration(value: Any) -> None:
    expected = {
        "base_commit": "299bb0a45398dcf055701ed7a5786ccf2ca41b6c",
        "base_tree": "3f983a3ba7c1bc1572defa814929f8f3a16f9d3a",
        "fresh_trace_generated": False,
        "pilot_disclosure": [
            "the refresh-family source law and true gamma, horizon, selected nominal depth-twelve potential, confidence allocations, tilts, and one-tenth success threshold were chosen after inspecting a separate retrospective trace and power analysis",
            "the confirmatory trace uses a new fixed initial observation, a future public randomness beacon, and a full-horizon indexing contract",
        ],
        "pilot_informed": True,
        "public_timestamp_required_before_generation": True,
        "registration_mode": "public OSF registration binding both preregistration and code-freeze Git objects before any beacon round is selected or trace is generated",
        "timestamp_contract": {
            "api_url_template": "https://api.osf.io/v2/registrations/{registration_id}/",
            "binding_requirement": "the immutable registration files contain the canonical protocol SHA-256, preregistration commit and tree, code-freeze commit and tree, and every code-freeze generator and verifier SHA-256",
            "field": "data.attributes.date_registered",
            "field_format": "RFC3339 UTC ending in Z; fractional seconds allowed",
            "integer_conversion": "ceiling of the exact UTC instant to Unix seconds",
            "provider": "Open Science Framework Registrations",
        },
    }
    _exact_tree(value, expected, "registration")
    for key in ("base_commit", "base_tree"):
        digest = value[key]
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{40}", digest) is None:
            _fail(f"registration.{key} must be a lowercase 40-digit Git object id")


def _validate_data_generation(value: Any) -> None:
    generation = _object(value, "data_generation")
    _keys(
        generation,
        {
            "action_encoding",
            "behavior_policy_id",
            "binary_contract",
            "family",
            "horizon",
            "initial_observation",
            "nearest_candidate",
            "path_contract",
            "prng_contract",
            "sampling_contract",
            "state_encoding",
            "true_gamma",
            "true_gamma_role",
            "true_hit_probability",
        },
        "data_generation",
    )
    _exact(generation["family"], "refreshEnvironment", "data_generation.family")
    _exact(
        generation["true_gamma_role"],
        "fixed source-law parameter for generation and independent replay; forbidden to primary endpoint selection",
        "data_generation.true_gamma_role",
    )
    _exact(generation["horizon"], HORIZON, "data_generation.horizon")
    _exact(
        generation["behavior_policy_id"],
        "behavior_uniform",
        "data_generation.behavior_policy_id",
    )
    _exact(
        generation["state_encoding"],
        "state_id = 3 * queue + regime",
        "data_generation.state_encoding",
    )
    _exact(generation["action_encoding"], ["eco", "boost"], "action_encoding")

    true_gamma = _fraction(generation["true_gamma"], "data_generation.true_gamma")
    true_hit = _fraction(
        generation["true_hit_probability"],
        "data_generation.true_hit_probability",
    )
    _exact(true_gamma, TRUE_GAMMA, "frozen true gamma")
    _exact(true_hit, TRUE_HIT_PROBABILITY, "frozen true hit probability")
    _exact((1 + 23 * true_gamma) / 24, true_hit, "true hit-probability identity")
    if generation["true_gamma"] in CANDIDATE_GAMMAS:
        _fail("data_generation.true_gamma must be outside the candidate support")

    nearest = _object(generation["nearest_candidate"], "nearest_candidate")
    nearest_expected = {
        "candidate_id": "nominal",
        "candidate_index": 1,
        "exact_row_total_variation_gap": "23/4800",
        "gamma": "3/4",
        "hit_probability": "73/96",
    }
    _exact_tree(nearest, nearest_expected, "data_generation.nearest_candidate")
    nominal_gamma = _fraction(nearest["gamma"], "nearest_candidate.gamma")
    nominal_hit = _fraction(
        nearest["hit_probability"], "nearest_candidate.hit_probability"
    )
    row_tv = _fraction(
        nearest["exact_row_total_variation_gap"],
        "nearest_candidate.exact_row_total_variation_gap",
    )
    _exact(nominal_gamma, NOMINAL_GAMMA, "nominal gamma")
    _exact(nominal_hit, NOMINAL_HIT_PROBABILITY, "nominal hit probability")
    _exact((1 + 23 * nominal_gamma) / 24, nominal_hit, "nominal hit identity")
    _exact(abs(true_hit - nominal_hit), row_tv, "hit-gap identity")
    _exact(abs(true_gamma - nominal_gamma) * Fraction(23, 24), row_tv, "row-TV identity")
    _exact(row_tv, NOMINAL_ROW_TV, "frozen nominal row TV")

    initial_expected = {
        "action_id": "eco",
        "action_index": 0,
        "lean_order": "(action,state)",
        "physical_state_index": 0,
        "queue": 0,
        "regime": 0,
    }
    _exact_tree(
        generation["initial_observation"],
        initial_expected,
        "data_generation.initial_observation",
    )

    path_expected = {
        "action_array_length": HORIZON + 1,
        "dummy_previous_action_used_only_at_x0": True,
        "observation": "x_0 = (eco,S_0); x_(k+1) = (A_(k+1),S_(k+1))",
        "sampling": "sample A_(k+1) from behaviorPolicy at S_k, then sample S_(k+1) from refreshEnvironment(true_gamma) at (S_k,A_(k+1))",
        "score": "score k uses the controlled transition x_k to x_(k+1)",
        "score_count": HORIZON,
        "state_array_length": HORIZON + 1,
        "transition_range": "k = 0,...,199999",
    }
    _exact_tree(generation["path_contract"], path_expected, "data_generation.path_contract")

    prng_expected = {
        "beacon_api": "https://api.drand.sh/v2/chains/{chain_hash}/rounds/{round}",
        "beacon_chain_hash": "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971",
        "beacon_chain_info_api": "https://api.drand.sh/v2/chains/{chain_hash}/info",
        "beacon_chain_info_exact_match_required": True,
        "beacon_genesis_unix_seconds": 1692803367,
        "beacon_group_hash": "f477d5c89f21a17c863a7f937c6a6d15859414d2be09cd448d4279af331c5d3e",
        "beacon_period_seconds": 3,
        "beacon_public_key": "83cf0f2896adee7eb8b5f01fcad3912212c437e0073e911fb90022d3e760183c8c4b450b6a0a6c3ac6a5776a2d1064510d1fec758c921cc22b0e17e63aaf4bcb5ed66304de9cf809bd274ca73bab4af5a6e9c76a4bc09e76eae8991ef5ece45a",
        "beacon_round_formula": "1 + ceil((osf_registration_unix_seconds + 3600 - beacon_genesis_unix_seconds) / beacon_period_seconds)",
        "beacon_round_on_fetch_or_verification_failure": "abort, publish the failure, and do not use a later round or another seed",
        "beacon_round_time_formula": "beacon_genesis_unix_seconds + (round - 1) * beacon_period_seconds",
        "beacon_scheme_id": "bls-unchained-g1-rfc9380",
        "beacon_signature_encoding": "hex-decoded signature bytes",
        "beacon_signature_verification_required": True,
        "beacon_signature_verifier_contract": "the pinned code-freeze verifier checks the formula-selected round signature under the frozen public key and bls-unchained-g1-rfc9380 scheme before deriving the seed",
        "block_input": "domain_utf8 || 0x00 || seed_bytes || counter_u64_be",
        "block_output": "32 digest bytes consumed left-to-right",
        "counter_encoding": "unsigned 64-bit big-endian",
        "counter_start": 0,
        "domain_utf8": PRNG_DOMAIN,
        "hash": "SHA-256",
        "seed_derivation": "SHA256(domain_utf8 || 0x00 || beacon_chain_hash_bytes || beacon_round_u64_be || beacon_signature_bytes)",
        "seed_source": "the single quicknet round computed by beacon_round_formula from the public OSF date_registered field; no search and no fallback",
        "separator_hex": "00",
        "test_counter_zero_digest_hex": PRNG_TEST_COUNTER_ZERO_DIGEST_HEX,
        "test_seed_derivation": "SHA256(domain_utf8 || UTF8(/test-seed))",
        "test_seed_hex": PRNG_TEST_SEED_HEX,
        "version": "sha256-counter-stream-v1",
        "word_encoding": "eight consecutive stream bytes as unsigned 64-bit big-endian",
    }
    _exact_tree(generation["prng_contract"], prng_expected, "data_generation.prng_contract")
    prng = generation["prng_contract"]
    genesis = prng["beacon_genesis_unix_seconds"]
    period = prng["beacon_period_seconds"]
    if isinstance(genesis, bool) or not isinstance(genesis, int):
        _fail("data_generation.prng_contract.beacon_genesis_unix_seconds must be an integer")
    if isinstance(period, bool) or not isinstance(period, int) or period <= 0:
        _fail("data_generation.prng_contract.beacon_period_seconds must be a positive integer")
    for key, expected_bytes in (
        ("beacon_chain_hash", 32),
        ("beacon_group_hash", 32),
        ("beacon_public_key", 96),
    ):
        encoded = prng[key]
        if (
            not isinstance(encoded, str)
            or re.fullmatch(r"[0-9a-f]+", encoded) is None
            or len(bytes.fromhex(encoded)) != expected_bytes
        ):
            _fail(f"data_generation.prng_contract.{key} has invalid lowercase hex encoding")

    def formula_round(registration_second: int) -> int:
        numerator = registration_second + 3600 - genesis
        return 1 + (-(-numerator // period))

    # Check all residue classes of the frozen period.  The formula-selected
    # round is the unique first round at or after registration + 3600 seconds.
    for residue in range(period):
        registration_second = genesis + 1_000_000 + residue
        round_number = formula_round(registration_second)
        round_time = genesis + (round_number - 1) * period
        target_time = registration_second + 3600
        if round_time < target_time or round_time - period >= target_time:
            _fail("beacon round/time formulas do not select the first eligible round")
    test_seed = hashlib.sha256(PRNG_DOMAIN.encode("utf-8") + b"/test-seed").digest()
    _exact(test_seed.hex(), PRNG_TEST_SEED_HEX, "PRNG test-seed derivation")
    test_vector = hashlib.sha256(
        PRNG_DOMAIN.encode("utf-8")
        + b"\0"
        + test_seed
        + (0).to_bytes(8, "big")
    ).hexdigest()
    _exact(
        test_vector,
        PRNG_TEST_COUNTER_ZERO_DIGEST_HEX,
        "PRNG test counter-zero vector",
    )

    sampling_expected = {
        "categorical": "reduce rational probabilities to integer weights over their least common denominator; draw uniformly below the total weight; use left-closed cumulative intervals in listed order",
        "draw_order": "one categorical action draw followed by one categorical next-state draw per transition; rejection draws consume additional words immediately",
        "uniform_integer": "for modulus m, set limit = 2^64 - (2^64 mod m); reject words x >= limit; return x mod m",
        "version": "exact-categorical-u64-rejection-v1",
    }
    _exact_tree(
        generation["sampling_contract"],
        sampling_expected,
        "data_generation.sampling_contract",
    )

    binary_expected = {
        "action_count_encoding": "unsigned 64-bit big-endian",
        "action_values": "200001 unsigned bytes in dummy_eco,A_1,...,A_200000 order",
        "byte_order": "big-endian",
        "causal_predictor_streams_replayed_from_path_not_stored": True,
        "expected_byte_length": 400036,
        "horizon_encoding": "unsigned 64-bit big-endian",
        "layout": "magic || horizon_u64 || state_count_u64 || action_count_u64 || state_bytes || action_bytes",
        "magic_ascii": "FSLTCQSP1\n",
        "magic_hex": "46534c5443515350310a",
        "no_endpoint_values": True,
        "state_count_encoding": "unsigned 64-bit big-endian",
        "state_values": "200001 unsigned bytes in S_0,...,S_200000 order",
        "version": "controlled-queue-prospective-trace-binary-v1",
    }
    _exact_tree(generation["binary_contract"], binary_expected, "data_generation.binary_contract")
    magic = bytes.fromhex(binary_expected["magic_hex"])
    _exact(magic.decode("ascii"), binary_expected["magic_ascii"], "binary magic identity")
    expected_length = len(magic) + 3 * 8 + 2 * (HORIZON + 1)
    _exact(expected_length, binary_expected["expected_byte_length"], "binary length identity")


def _validate_analysis_estimand(value: Any) -> None:
    expected = {
        "analysis_time": HORIZON,
        "hypothesis_prior": "uniform over the 12 policy-predictor atoms",
        "hypothesis_prior_mass": "1/12",
        "importance_ratio_cap": "3/2",
        "optional_stopping_for_primary": False,
        "posterior": "Dirac(queue_threshold,nominal_model_overload)",
        "posterior_fixed_before_data": True,
        "predictor_id": "nominal_model_overload",
        "predictor_index": 2,
        "quantity": "stationary Brier risk under the true refresh-family environment",
        "target_policy_id": "queue_threshold",
        "target_policy_index": 1,
    }
    _exact_tree(value, expected, "analysis_estimand")
    _exact(
        len(HYPOTHESIS_SUPPORT)
        * _fraction(value["hypothesis_prior_mass"], "hypothesis_prior_mass"),
        Fraction(1),
        "hypothesis prior normalization",
    )
    _fraction(value["importance_ratio_cap"], "importance_ratio_cap")


def _validate_confidence_contract(value: Any) -> None:
    expected = {
        "delta_persistence": "1/40",
        "delta_risk": "1/40",
        "delta_total": "1/20",
        "event_accounting": "intersect the risk and persistence outer-mass events; use the union bound; no independence or sample split",
        "persistence_eta": "abs(73/96 - persistence_hit_count/n) + max(direct_empirical_Bernstein_boundary,complement_empirical_Bernstein_boundary)",
        "persistence_orientation_prior": {"complement": "1/2", "direct": "1/2"},
        "persistence_psi_upper_bound": "1/8064",
        "persistence_tilt": "1/64",
        "persistence_tilt_weight": "1",
        "psi_bound_formula": "forwardEmpiricalBernsteinPsi(lambda) <= lambda^2 / (2 * (1 - lambda)) for 0 <= lambda < 1",
        "risk_psi_upper_bound": "1/480",
        "risk_tilt": "1/16",
        "risk_tilt_weight": "1",
    }
    _exact_tree(value, expected, "confidence_contract")
    risk_delta = _fraction(value["delta_risk"], "confidence_contract.delta_risk")
    persistence_delta = _fraction(
        value["delta_persistence"], "confidence_contract.delta_persistence"
    )
    total_delta = _fraction(value["delta_total"], "confidence_contract.delta_total")
    _exact(risk_delta + persistence_delta, total_delta, "confidence union allocation")
    for key in ("risk_tilt", "risk_tilt_weight", "persistence_tilt", "persistence_tilt_weight"):
        _fraction(value[key], f"confidence_contract.{key}")
    risk_tilt = _fraction(value["risk_tilt"], "confidence_contract.risk_tilt")
    persistence_tilt = _fraction(
        value["persistence_tilt"], "confidence_contract.persistence_tilt"
    )
    risk_psi = _fraction(
        value["risk_psi_upper_bound"], "confidence_contract.risk_psi_upper_bound"
    )
    persistence_psi = _fraction(
        value["persistence_psi_upper_bound"],
        "confidence_contract.persistence_psi_upper_bound",
    )
    _exact(
        risk_tilt**2 / (2 * (1 - risk_tilt)),
        risk_psi,
        "risk psi upper-bound identity",
    )
    _exact(
        persistence_tilt**2 / (2 * (1 - persistence_tilt)),
        persistence_psi,
        "persistence psi upper-bound identity",
    )
    orientation = value["persistence_orientation_prior"]
    orientation_total = sum(
        (_fraction(weight, f"persistence_orientation_prior.{key}") for key, weight in orientation.items()),
        Fraction(0),
    )
    _exact(orientation_total, Fraction(1), "persistence orientation prior normalization")


def _validate_primary_endpoint(value: Any) -> None:
    expected = {
        "candidate_drift_oscillation": "58989951/9007199254740992",
        "candidate_gamma": "3/4",
        "candidate_id": "nominal",
        "candidate_index": 1,
        "decision_threshold": "1/10",
        "endpoint_formula": "risk_boundary + candidate_drift_oscillation + refresh_drift_sensitivity_oscillation * persistence_eta",
        "endpoint_id": "selected_h12_sharp_structured_eb",
        "potential_depth": 12,
        "potential_shift": "h_shift(z) = h_raw(z) - h_raw(0)",
        "potential_source": "selectedPotentialTable in the bound pilot-selected potential data",
        "potential_span": "390176269054599/2251799813685248",
        "refresh_drift_sensitivity_oscillation": "831542406207231/3236962232172544",
        "required_checked_results": [
            "targetPolicyPoissonDrift_refresh_sub_candidate_eq",
            "abs_approximateTargetPolicyPoissonResidual_le_refreshSensitivity",
            "exists_controlledQueueSharpStructuredReceipt_event",
            "forwardEmpiricalBernsteinPsi_le_quadratic",
            "sharpStructuredReceiptBoundary_evaluation_of_histogram",
        ],
        "residual_formula": "candidate_drift_oscillation + refresh_drift_sensitivity_oscillation * persistence_eta",
        "risk_boundary": "stationaryTargetPolicyOPEBoundary with the fixed selected potential, span, ratio cap, Dirac posterior, risk tilt, and risk delta",
        "selection": "fixed before data; no candidate, depth, tilt, policy, predictor, posterior, or time selection",
        "status": "FROZEN PROSPECTIVE PRIMARY - REQUIRED SHARP THEOREM AND RECEIPT NOT YET IMPLEMENTED",
        "threshold_corollary_contract": "prove endpoint < 1/10 only if the frozen exact receipt arithmetic supports it; otherwise publish the exact endpoint without that corollary",
    }
    _exact_tree(value, expected, "primary_endpoint")
    for key in (
        "candidate_gamma",
        "candidate_drift_oscillation",
        "potential_span",
        "refresh_drift_sensitivity_oscillation",
        "decision_threshold",
    ):
        parsed = _fraction(value[key], f"primary_endpoint.{key}")
        if parsed < 0:
            _fail(f"primary_endpoint.{key} must be nonnegative")


def _validate_adaptive_secondary(value: Any) -> None:
    expected = {
        "analysis_time": HORIZON,
        "candidate_support": list(CANDIDATE_SUPPORT),
        "catalog_weight": "1/21",
        "decision_threshold": "1",
        "depth_support": list(DEPTH_SUPPORT),
        "endpoint_id": "adaptive_d1_21_atom_eb",
        "event_relation_to_primary": "separate valid event and confidence allocation; no simultaneous-primary claim without an additional union construction",
        "persistence_tilt_support": list(ADMISSIBLE_TILT_SUPPORT),
        "persistence_tilt_weight": "1/4",
        "posterior_support": "12 Dirac policy-predictor atoms in policy-major then predictor-major order",
        "risk_tilt_support": list(ADMISSIBLE_TILT_SUPPORT),
        "risk_tilt_weight": "1/4",
        "selection_rule": "minimize the exact certified RHS and break ties lexicographically by candidate_index,depth_index,risk_tilt_index,persistence_tilt_index,posterior_index",
        "status": "SECONDARY - CURRENT CHECKED D=1 FINITE-CATALOG EVENT",
    }
    _exact_tree(value, expected, "adaptive_secondary")
    catalog_weight = _fraction(value["catalog_weight"], "adaptive_secondary.catalog_weight")
    _exact(
        len(CANDIDATE_SUPPORT) * len(DEPTH_SUPPORT) * catalog_weight,
        Fraction(1),
        "adaptive candidate-depth allocation",
    )
    for prefix in ("risk", "persistence"):
        support = value[f"{prefix}_tilt_support"]
        for index, tilt in enumerate(support):
            parsed = _fraction(tilt, f"adaptive_secondary.{prefix}_tilt_support[{index}]")
            if not 0 < parsed < 1:
                _fail(f"adaptive_secondary.{prefix}_tilt_support[{index}] must lie in (0,1)")
        weight = _fraction(value[f"{prefix}_tilt_weight"], f"{prefix}_tilt_weight")
        _exact(len(support) * weight, Fraction(1), f"adaptive {prefix}-tilt allocation")
    _fraction(value["decision_threshold"], "adaptive_secondary.decision_threshold")


def _validate_matched_baselines(value: Any) -> None:
    expected = [
        {
            "analysis_time": HORIZON,
            "baseline_id": "oracle_true_kernel_selected_h12_eb",
            "confidence_allocation": {
                "delta_persistence": "0",
                "delta_risk": "1/20",
                "delta_total": "1/20",
                "persistence_tilt": "not applicable",
                "persistence_tilt_weight": "not applicable",
                "risk_tilt": "1/16",
                "risk_tilt_weight": "1",
            },
            "difference_from_primary": "replace empirical persistence uncertainty by the exact true refresh parameter and use a true-kernel depth-twelve potential",
            "endpoint_formula": "stationaryTargetPolicyOPEBoundary for refreshEnvironment(149/200), the deterministic true-kernel depth-twelve potential, fixed Dirac posterior, C=3/2, risk tilt 1/16, and risk delta 1/20, plus its exact depth-twelve drift oscillation",
            "posterior": "Dirac(queue_threshold,nominal_model_overload)",
            "potential_contract": "finiteDepthPoissonPotential at depth 12 for refreshEnvironment(149/200), computed from the model before reading the trace; no depth or potential selection",
            "predictor_id": "nominal_model_overload",
            "same_path_and_estimand": True,
            "selection_rule": "fixed before data",
            "status": "PLANNED ORACLE BASELINE",
            "target_policy_id": "queue_threshold",
        },
        {
            "analysis_time": HORIZON,
            "baseline_id": "generic_d1_m12_structured_eb",
            "candidate_id": "nominal",
            "candidate_index": 1,
            "confidence_allocation": {
                "delta_persistence": "1/40",
                "delta_risk": "1/40",
                "delta_total": "1/20",
                "persistence_tilt": "1/64",
                "persistence_tilt_weight": "1",
                "risk_tilt": "1/16",
                "risk_tilt_weight": "1",
            },
            "difference_from_primary": "use the generic D=1 depth-twelve potential with span 16245775/4194304 and candidate truncation 531441/16777216",
            "endpoint_formula": "stationaryTargetPolicyOPEBoundary with the generic D=1 nominal depth-twelve potential and B=16245775/4194304, plus 531441/16777216 + 2*(1+B)*persistence_eta",
            "posterior": "Dirac(queue_threshold,nominal_model_overload)",
            "potential_depth": 12,
            "predictor_id": "nominal_model_overload",
            "same_path_and_estimand": True,
            "selection_rule": "fixed before data",
            "status": "CHECKED THEOREM FAMILY; NUMERICAL RECEIPT PENDING",
            "target_policy_id": "queue_threshold",
        },
        {
            "analysis_time": HORIZON,
            "baseline_id": "generic_d1_m5_structured_eb",
            "candidate_id": "nominal",
            "candidate_index": 1,
            "confidence_allocation": {
                "delta_persistence": "1/40",
                "delta_risk": "1/40",
                "delta_total": "1/20",
                "persistence_tilt": "1/64",
                "persistence_tilt_weight": "1",
                "risk_tilt": "1/16",
                "risk_tilt_weight": "1",
            },
            "difference_from_primary": "fix depth five with generic D=1 span 781/256 and candidate truncation 243/1024",
            "endpoint_formula": "stationaryTargetPolicyOPEBoundary with the generic D=1 nominal depth-five potential and B=781/256, plus 243/1024 + 2*(1+B)*persistence_eta",
            "posterior": "Dirac(queue_threshold,nominal_model_overload)",
            "potential_depth": 5,
            "predictor_id": "nominal_model_overload",
            "same_path_and_estimand": True,
            "selection_rule": "fixed before data",
            "status": "CHECKED THEOREM FAMILY; NUMERICAL RECEIPT PENDING",
            "target_policy_id": "queue_threshold",
        },
        {
            "analysis_time": HORIZON,
            "baseline_id": "selected_h12_nonvariance_fixed_range",
            "candidate_id": "nominal",
            "candidate_index": 1,
            "confidence_allocation": {
                "delta_persistence": "1/40",
                "delta_risk": "1/40",
                "delta_total": "1/20",
                "persistence_tilt": "1/64",
                "persistence_tilt_weight": "1",
                "risk_tilt": "1/16",
                "risk_tilt_weight": "1",
            },
            "difference_from_primary": "replace both empirical-Bernstein variance terms by their fixed-range sub-gamma corrections at the same fixed tilts",
            "endpoint_formula": "fixed-range target-policy boundary with risk correction lambda_r/(8*(1-lambda_r/3)) + (KL+log(1/delta_r))/(n*lambda_r), plus candidate_drift_oscillation + refresh_drift_sensitivity_oscillation*eta_fixed_range",
            "eta_formula": "abs(73/96 - persistence_hit_count/n) + lambda_p/(8*(1-lambda_p/3)) + log(2/delta_p)/(n*lambda_p)",
            "posterior": "Dirac(queue_threshold,nominal_model_overload)",
            "potential_depth": 12,
            "potential_source": "the same fixed selectedPotentialTable used by the primary",
            "predictor_id": "nominal_model_overload",
            "same_path_and_estimand": True,
            "selection_rule": "fixed before data",
            "status": "PLANNED THEOREM AND RECEIPT",
            "target_policy_id": "queue_threshold",
        },
        {
            "all_augmented_source_rows_must_be_visited": True,
            "analysis_time": HORIZON,
            "baseline_id": "unstructured_4608_coordinate_eb",
            "candidate_id": "nominal",
            "candidate_index": 1,
            "confidence_allocation": {
                "delta_risk": "1/40",
                "delta_total": "1/20",
                "delta_transition": "1/40",
                "risk_tilt": "1/16",
                "risk_tilt_weight": "1",
                "transition_tilt": "1/64",
                "transition_tilt_weight": "1",
            },
            "difference_from_primary": "replace both the sharp selected-potential transfer and scalar refresh-family confidence radius by the generic D=1 depth-twelve potential and full augmented transition-coordinate construction",
            "endpoint_formula": "stationaryTargetPolicyOPEBoundary with the generic D=1 nominal depth-twelve potential and B=16245775/4194304, plus 531441/16777216 + 4*(1+B)*eta_augmented",
            "posterior": "Dirac(queue_threshold,nominal_model_overload)",
            "potential_depth": 12,
            "predictor_id": "nominal_model_overload",
            "same_path_and_estimand": True,
            "selection_rule": "fixed before data",
            "status": "CHECKED THEOREM FAMILY; NUMERICAL RECEIPT PENDING",
            "target_policy_id": "queue_threshold",
            "transition_coordinate_prior_mass": "1/4608",
        },
    ]
    _exact_tree(value, expected, "matched_baselines")

    rows = _array(value, "matched_baselines")
    for index, row in enumerate(rows):
        allocation = _object(
            row["confidence_allocation"],
            f"matched_baselines[{index}].confidence_allocation",
        )
        delta_risk = _fraction(
            allocation["delta_risk"],
            f"matched_baselines[{index}].confidence_allocation.delta_risk",
        )
        delta_total = _fraction(
            allocation["delta_total"],
            f"matched_baselines[{index}].confidence_allocation.delta_total",
        )
        if "delta_persistence" in allocation:
            second_delta = _fraction(
                allocation["delta_persistence"],
                f"matched_baselines[{index}].confidence_allocation.delta_persistence",
            )
        else:
            second_delta = _fraction(
                allocation["delta_transition"],
                f"matched_baselines[{index}].confidence_allocation.delta_transition",
            )
        _exact(
            delta_risk + second_delta,
            delta_total,
            f"matched_baselines[{index}] confidence allocation",
        )
        _fraction(
            allocation["risk_tilt"],
            f"matched_baselines[{index}].confidence_allocation.risk_tilt",
        )
        _exact(
            _fraction(
                allocation["risk_tilt_weight"],
                f"matched_baselines[{index}].confidence_allocation.risk_tilt_weight",
            ),
            Fraction(1),
            f"matched_baselines[{index}] risk tilt weight",
        )
        if index != 0:
            second_tilt_name = (
                "transition_tilt" if "transition_tilt" in allocation else "persistence_tilt"
            )
            _fraction(
                allocation[second_tilt_name],
                f"matched_baselines[{index}].confidence_allocation.{second_tilt_name}",
            )
            _exact(
                _fraction(
                    allocation[f"{second_tilt_name}_weight"],
                    f"matched_baselines[{index}].confidence_allocation.{second_tilt_name}_weight",
                ),
                Fraction(1),
                f"matched_baselines[{index}] second tilt weight",
            )

    gamma = Fraction(3, 4)
    for depth, span_text, truncation_text in (
        (12, "16245775/4194304", "531441/16777216"),
        (5, "781/256", "243/1024"),
    ):
        _exact(
            (1 - gamma**depth) / (1 - gamma),
            _fraction(span_text, f"generic depth-{depth} span"),
            f"generic depth-{depth} span identity",
        )
        _exact(
            gamma**depth,
            _fraction(truncation_text, f"generic depth-{depth} truncation"),
            f"generic depth-{depth} truncation identity",
        )
    _exact(
        4608
        * _fraction(
            rows[4]["transition_coordinate_prior_mass"],
            "matched_baselines[4].transition_coordinate_prior_mass",
        ),
        Fraction(1),
        "unstructured transition-coordinate allocation",
    )


def _validate_success_criteria(value: Any) -> None:
    expected = {
        "adaptive_secondary_cannot_replace_failed_primary": True,
        "primary_success": "selected_h12_sharp_structured_eb endpoint < 1/10",
        "primary_useful_fallback": "selected_h12_sharp_structured_eb endpoint < 1",
        "report_failure_unchanged": True,
    }
    _exact_tree(value, expected, "success_criteria")


FRESH_OUTPUT_PATHS = [
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1.bin",
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-counts.json",
    "applications/controlled_queue/prospective/generated/structured-ope-trace-v1-manifest.json",
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1.json",
    "applications/controlled_queue/prospective/generated/structured-ope-receipt-v1-manifest.json",
    "FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean",
]


def _validate_artifact_contract(value: Any) -> None:
    expected = {
        "fresh_output_paths": FRESH_OUTPUT_PATHS,
        "independent_verifiers_must_not_import_generators": True,
        "lean_hash_boundary": "Lean proves table-to-endpoint arithmetic; manifests and independent verifiers bind raw bytes and hashes",
        "receipt_generator_path": "scripts/generate_controlled_queue_prospective_receipt.py",
        "receipt_verifier_path": "scripts/verify_controlled_queue_prospective_receipt.py",
        "trace_generator_must_not_compute_endpoints": True,
        "trace_generator_path": "scripts/generate_controlled_queue_prospective_trace.py",
        "trace_manifest_must_bind": "OSF registration id, date_registered value and API-response SHA-256; protocol and code-freeze Git objects; quicknet chain, formula-selected round and verified signature; every generator, verifier, input and output SHA-256",
        "trace_verifier_path": "scripts/verify_controlled_queue_prospective_trace.py",
    }
    _exact_tree(value, expected, "artifact_contract")
    seen: set[Path] = set()
    for index, path_text in enumerate(value["fresh_output_paths"]):
        path = _resolve_repository_path(path_text, f"artifact_contract.fresh_output_paths[{index}]")
        if path in seen:
            _fail("artifact_contract.fresh_output_paths must not contain duplicates")
        seen.add(path)
        if path.exists():
            _fail(f"prospective output already exists: {path_text}")


def _validate_chronology_contract(value: Any) -> None:
    expected = {
        "analytic_change_requires_new_protocol_and_never_inspected_beacon_round": True,
        "beacon_round_selected_only_after_osf_registration_plus_seconds": 3600,
        "code_freeze_required_before_generation": True,
        "no_seed_horizon_gamma_endpoint_selector_delta_or_threshold_change_after_beacon": True,
        "nonanalytic_typo_correction_requires_logged_amendment": True,
        "preregistration_commit_contains_fresh_output": False,
        "public_osf_registration_binding_both_commits_required_before_generation": True,
        "publish_raw_trace_counts_receipts_and_all_baselines_regardless_of_result": True,
        "single_generation_run": True,
    }
    _exact_tree(value, expected, "chronology_contract")


def _validate_reporting_contract(value: Any) -> None:
    expected = {
        "causal_predictors_reported_separately_as_dynamic_encountered_risk": True,
        "exact_rational_and_decimal_required": True,
        "failure_and_vacuous_rows_published_unchanged": True,
        "no_suppression_or_reordering_based_on_result": True,
        "required_fields_per_row": [
            "endpoint_id",
            "theorem_or_event",
            "empirical_corrected_score",
            "risk_statistical_correction",
            "persistence_or_transition_radius",
            "candidate_or_truncation_residual",
            "total_certified_rhs",
            "confidence_allocation",
            "selected_indices_or_fixed_settings",
            "vacuity_and_threshold_status",
        ],
        "row_order": [
            "selected_h12_sharp_structured_eb",
            "adaptive_d1_21_atom_eb",
            "oracle_true_kernel_selected_h12_eb",
            "generic_d1_m12_structured_eb",
            "generic_d1_m5_structured_eb",
            "selected_h12_nonvariance_fixed_range",
            "unstructured_4608_coordinate_eb",
        ],
        "separate_event_label_required": True,
    }
    _exact_tree(value, expected, "reporting_contract")
    report = _object(value, "reporting_contract")
    fields = _array(report["required_fields_per_row"], "reporting required fields")
    rows = _array(report["row_order"], "reporting row order")
    if len(fields) != 10 or len(set(fields)) != len(fields):
        _fail("reporting_contract must freeze ten distinct required fields per row")
    if len(rows) != 7 or len(set(rows)) != len(rows):
        _fail("reporting_contract must freeze seven distinct rows")


def _validate_nonclaims(value: Any) -> None:
    expected = [
        "not a generated trace, numerical result, confidence receipt, or theorem",
        "not evidence that the one-tenth primary threshold will be met",
        "not a general unknown-kernel result outside the one-parameter refresh family",
        "not a test that the true environment belongs to the refresh family",
        "not adaptive candidate or depth selection for the primary endpoint",
        "not a simultaneous confidence statement for the primary, secondary, and baseline rows",
        "not stationary target-policy certification for the two causal Beta predictors",
        "not proof that any eventual named path belongs to a theorem-produced good event",
        "not Lean verification of raw bytes, SHA-256, a drand signature, or a public timestamp",
        "not a cumulative-value, control-regret, or policy-optimization guarantee",
    ]
    _exact_tree(value, expected, "nonclaims")


def validate_protocol(spec: dict[str, Any]) -> None:
    """Validate the in-memory protocol and all of its bound dependencies."""

    _keys(
        spec,
        {
            "adaptive_secondary",
            "analysis_estimand",
            "artifact_contract",
            "artifact_status",
            "bindings",
            "chronology_contract",
            "confidence_contract",
            "data_generation",
            "matched_baselines",
            "nonclaims",
            "primary_endpoint",
            "protocol_version",
            "registration",
            "reporting_contract",
            "schema_version",
            "success_criteria",
        },
        "protocol",
    )
    _exact(spec["schema_version"], SCHEMA_VERSION, "schema_version")
    _exact(spec["protocol_version"], PROTOCOL_VERSION, "protocol_version")
    _exact(spec["artifact_status"], ARTIFACT_STATUS, "artifact_status")
    _validate_registration(spec["registration"])
    _validate_bindings(spec["bindings"])
    _validate_data_generation(spec["data_generation"])
    _validate_analysis_estimand(spec["analysis_estimand"])
    _validate_confidence_contract(spec["confidence_contract"])
    _validate_primary_endpoint(spec["primary_endpoint"])
    _validate_adaptive_secondary(spec["adaptive_secondary"])
    _validate_matched_baselines(spec["matched_baselines"])
    _validate_success_criteria(spec["success_criteria"])
    _validate_artifact_contract(spec["artifact_contract"])
    _validate_chronology_contract(spec["chronology_contract"])
    _validate_reporting_contract(spec["reporting_contract"])
    _validate_nonclaims(spec["nonclaims"])


def validate_protocol_file(path: Path = DEFAULT_INPUT) -> dict[str, Any]:
    raw = path.read_bytes()
    value = parse_json_bytes(raw, str(path))
    spec = _object(value, "protocol")
    if raw != canonical_json_bytes(spec):
        _fail("protocol must use canonical JSON bytes")
    validate_protocol(spec)
    _exact(_sha256(raw), EXPECTED_PROTOCOL_SHA256, "frozen protocol SHA-256")
    return spec


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        default=DEFAULT_INPUT,
        help="protocol JSON to validate",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    try:
        validate_protocol_file(arguments.input)
    except (OSError, ProtocolError) as error:
        print(f"controlled-queue structured OPE protocol: FAIL: {error}", file=sys.stderr)
        return 1
    print("controlled-queue structured OPE protocol: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
