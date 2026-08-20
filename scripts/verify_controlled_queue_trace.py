#!/usr/bin/env python3
"""Independently verify the controlled-queue trace preprocessing artifacts.

This verifier intentionally does not import either generator.  It checks all
SHA-256 bindings, independently replays the documented counter-stream and
sampling contracts, reconstructs every count, and checks that each stored Beta
prediction uses only outcomes at indices strictly below the current index.
Passing this verifier is a data-integrity result, not a Lean theorem or a
statistical certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import struct
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TRACE_INPUT = ROOT / "applications" / "controlled_queue" / "trace-v1.json"
DEFAULT_MODEL_INPUT = ROOT / "applications" / "controlled_queue" / "model-v1.json"
DEFAULT_TRACE = ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1.bin"
DEFAULT_COUNTS = (
    ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1-counts.json"
)
DEFAULT_MANIFEST = (
    ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1-manifest.json"
)
TRACE_GENERATOR = ROOT / "scripts" / "generate_controlled_queue_trace.py"
MODEL_GENERATOR = ROOT / "scripts" / "generate_controlled_queue_model.py"

SCHEMA_VERSION = "controlled-queue-trace-input-v1"
TRACE_VERSION = "controlled-queue-trace-v1"
GENERATOR_REVISION = "controlled-queue-trace-generator-v1"
ARTIFACT_STATUS = "TRACE/PREPROCESSING ONLY"
PRNG_VERSION = "sha256-counter-stream-v1"
SAMPLING_VERSION = "exact-categorical-u64-rejection-v1"
BINARY_VERSION = "controlled-queue-trace-binary-v1"
BINARY_MAGIC = bytes.fromhex("4351545256310000")
BINARY_HEADER = struct.Struct(">8sQ")
UINT64_SPACE = 1 << 64
STATE_COUNT = 24
ACTION_IDS = ("eco", "boost")
PREDICTOR_SUPPORT = (
    "global_climatology",
    "queue_action_threshold",
    "nominal_model_overload",
    "global_beta",
    "queue_band_action_beta",
)
POSTERIOR_IDS = tuple(f"delta_{name}" for name in PREDICTOR_SUPPORT) + (
    "uniform_predictor_posterior",
)
DOMAIN = "FormalSLT/controlled-queue/trace-v1"
SEED_HEX = "00000000000000000000000000000000000000000000000000000000013527d4"
COUNTER_ZERO_DIGEST_HEX = (
    "4937262570967d5d0f4abeb19ec4c872ba9868308e594c0ae9acc077a6349896"
)


class VerificationError(ValueError):
    """Raised when a trace input, binding, or replay check fails."""


def _reject_float(value: str) -> None:
    raise VerificationError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise VerificationError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise VerificationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json(raw: bytes, where: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_unique_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"invalid UTF-8 JSON in {where}: {error}") from error


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"{where} must be an object")
    return value


def _list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise VerificationError(f"{where} must be an array")
    return value


def _exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise VerificationError(f"{where} mismatch: expected {expected!r}, got {actual!r}")


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.name


def _rational(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise VerificationError(f"{where} is not a rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError(f"invalid rational at {where}: {value!r}") from error
    canonical = (
        str(result.numerator)
        if result.denominator == 1
        else f"{result.numerator}/{result.denominator}"
    )
    if value != canonical:
        raise VerificationError(f"noncanonical rational at {where}: {value!r}")
    return result


def _normalized(values: Any, expected_length: int, where: str) -> list[Fraction]:
    raw = _list(values, where)
    if len(raw) != expected_length:
        raise VerificationError(f"{where} must contain {expected_length} entries")
    parsed = [_rational(value, f"{where}[{i}]") for i, value in enumerate(raw)]
    if any(value < 0 for value in parsed) or sum(parsed) != 1:
        raise VerificationError(f"{where} is not a normalized nonnegative distribution")
    return parsed


class IndependentCounterStream:
    def __init__(self, domain: str, seed_hex: str, start: int) -> None:
        self.prefix = domain.encode("utf-8") + b"\0" + bytes.fromhex(seed_hex)
        self.counter = start
        self.buffer = b""
        self.words = 0
        self.blocks = 0
        self.rejections: dict[int, int] = {}

    def next_u64(self) -> int:
        if len(self.buffer) < 8:
            if self.counter >= UINT64_SPACE:
                raise VerificationError("PRNG counter exhausted")
            self.buffer += hashlib.sha256(
                self.prefix + self.counter.to_bytes(8, "big")
            ).digest()
            self.counter += 1
            self.blocks += 1
        word = int.from_bytes(self.buffer[:8], "big")
        self.buffer = self.buffer[8:]
        self.words += 1
        return word

    def below(self, modulus: int) -> int:
        if not 1 <= modulus <= UINT64_SPACE:
            raise VerificationError("invalid rejection-sampling modulus")
        limit = UINT64_SPACE - UINT64_SPACE % modulus
        rejected = 0
        while True:
            word = self.next_u64()
            if word < limit:
                if rejected:
                    self.rejections[modulus] = self.rejections.get(modulus, 0) + rejected
                return word % modulus
            rejected += 1


def _weights(probabilities: Sequence[Fraction]) -> list[int]:
    if not probabilities or any(value < 0 for value in probabilities):
        raise VerificationError("invalid categorical probability vector")
    if sum(probabilities) != 1:
        raise VerificationError("categorical probabilities do not sum to one")
    denominator = math.lcm(*(value.denominator for value in probabilities))
    result = [value.numerator * (denominator // value.denominator) for value in probabilities]
    divisor = math.gcd(*result)
    return [value // divisor for value in result]


def _sample(weights: Sequence[int], stream: IndependentCounterStream) -> int:
    total = sum(weights)
    draw = stream.below(total)
    cumulative = 0
    for index, weight in enumerate(weights):
        cumulative += weight
        if draw < cumulative:
            return index
    raise VerificationError("categorical replay escaped cumulative intervals")


def _queue_step(model: dict[str, Any], state: int, action: int) -> int:
    queue, regime = divmod(state, 3)
    service = model["actions"][action]["service_capacity"]
    arrival = model["state_space"]["arrival_by_regime"][regime]
    return 3 * min(7, max(0, queue - service) + arrival) + (regime + 1) % 3


def _band(queue: int, bands: Sequence[Sequence[int]]) -> int:
    for index, pair in enumerate(bands):
        if pair[0] <= queue <= pair[1]:
            return index
    raise VerificationError(f"queue {queue} is outside the frozen band partition")


def _verify_trace_contract(trace: dict[str, Any], model: dict[str, Any], model_raw: bytes) -> None:
    _exact(trace.get("schema_version"), SCHEMA_VERSION, "trace schema")
    _exact(trace.get("trace_version"), TRACE_VERSION, "trace version")
    _exact(trace.get("artifact_status"), ARTIFACT_STATUS, "trace status")
    binding = _object(trace.get("model_binding"), "model_binding")
    _exact(
        binding.get("path"),
        "applications/controlled_queue/model-v1.json",
        "model binding path",
    )
    _exact(binding.get("sha256"), _sha(model_raw), "model input binding")
    _exact(binding.get("schema_version"), model.get("schema_version"), "model schema binding")
    _exact(binding.get("model_version"), model.get("model_version"), "model version binding")

    parameters = _object(trace.get("trace_parameters"), "trace_parameters")
    _exact(parameters.get("horizon"), 200000, "trace horizon")
    _exact(parameters.get("horizon"), model["generation"]["horizon"], "model horizon")
    _exact(parameters.get("initial_state"), 0, "initial state")
    _exact(parameters.get("source_candidate"), "nominal", "source candidate")
    _exact(parameters.get("behavior_policy"), "behavior_uniform", "behavior policy")
    _exact(
        _list(parameters.get("transition_order"), "transition order"),
        [
            "sample action from behavior policy at current state",
            "record causal predictions from transitions with index strictly below t",
            "sample next state from source candidate",
            "record outcome and update causal sufficient statistics",
        ],
        "transition order",
    )

    prng = _object(trace.get("prng_contract"), "prng_contract")
    _exact(prng.get("version"), PRNG_VERSION, "PRNG version")
    _exact(prng.get("hash"), "SHA-256", "PRNG hash")
    _exact(prng.get("domain_utf8"), DOMAIN, "PRNG domain")
    _exact(prng.get("separator_hex"), "00", "PRNG separator")
    _exact(prng.get("seed_hex"), SEED_HEX, "PRNG seed")
    _exact(prng.get("counter_start"), 0, "PRNG counter start")
    digest = hashlib.sha256(
        prng["domain_utf8"].encode()
        + b"\0"
        + bytes.fromhex(prng["seed_hex"])
        + (0).to_bytes(8, "big")
    ).hexdigest()
    _exact(digest, COUNTER_ZERO_DIGEST_HEX, "independent PRNG test vector")
    _exact(prng.get("counter_zero_digest_hex"), digest, "PRNG test vector")
    sampling = _object(trace.get("sampling_contract"), "sampling_contract")
    _exact(sampling.get("version"), SAMPLING_VERSION, "sampling version")
    _exact(
        sampling.get("uniform_integer"),
        "for modulus m, set limit = 2^64 - (2^64 mod m); reject words x >= limit; return x mod m",
        "uniform-integer contract",
    )
    _exact(
        sampling.get("categorical"),
        "reduce rational probabilities to integer weights over their least common denominator; draw uniformly below the total weight; use left-closed cumulative intervals in listed order",
        "categorical contract",
    )
    _exact(
        sampling.get("draw_order"),
        "one categorical action draw followed by one categorical next-state draw per transition; rejection draws consume additional words immediately",
        "sampling draw order",
    )

    tables = _object(trace.get("weight_tables"), "weight_tables")
    prior = _object(tables.get("prior_weights"), "prior_weights")
    _exact(prior.get("support"), list(PREDICTOR_SUPPORT), "prior support")
    _exact(
        _normalized(prior.get("weights"), 5, "prior weights"),
        [Fraction(1, 5)] * 5,
        "prior weights",
    )
    posteriors = _list(tables.get("posterior_weights"), "posterior_weights")
    _exact(len(posteriors), 6, "posterior count")
    for index, row in enumerate(posteriors):
        item = _object(row, f"posterior {index}")
        _exact(item.get("id"), POSTERIOR_IDS[index], f"posterior {index} id")
        actual = _normalized(item.get("weights"), 5, f"posterior {index}")
        expected = [Fraction(1 if j == index else 0) for j in range(5)]
        if index == 5:
            expected = [Fraction(1, 5)] * 5
        _exact(actual, expected, f"posterior {index} weights")
    candidates = _object(tables.get("candidate_weights"), "candidate_weights")
    _exact(candidates.get("support"), ["low", "nominal", "high"], "candidate support")
    _exact(
        _normalized(candidates.get("weights"), 3, "candidate weights"),
        [Fraction(1, 3)] * 3,
        "candidate weights",
    )
    coordinates = _object(tables.get("coordinate_weights"), "coordinate_weights")
    _exact(
        coordinates.get("support_encoding"),
        "augmented_state_id = 2 * state_id + action_index",
        "coordinate support encoding",
    )
    _exact(
        _normalized(coordinates.get("weights"), 48, "coordinate weights"),
        [Fraction(1, 48)] * 48,
        "coordinate weights",
    )
    tilts = _object(tables.get("tilt_weights"), "tilt_weights")
    _exact(tilts.get("support"), model["generation"]["tilt_grid"], "tilt support")
    _exact(
        _normalized(tilts.get("weights"), 5, "tilt weights"),
        [Fraction(1, 5)] * 5,
        "tilt weights",
    )

    binary = _object(trace.get("binary_contract"), "binary_contract")
    _exact(binary.get("version"), BINARY_VERSION, "binary version")
    _exact(binary.get("magic_hex"), BINARY_MAGIC.hex(), "binary magic")
    _exact(
        binary.get("header"),
        "8 magic bytes followed by horizon as unsigned 64-bit big-endian",
        "binary header contract",
    )
    _exact(
        binary.get("payload"),
        [
            "horizon + 1 physical state ids as unsigned bytes",
            "horizon action indices as unsigned bytes",
            "horizon global Beta numerators as unsigned 32-bit big-endian",
            "horizon global Beta denominators as unsigned 32-bit big-endian",
            "horizon queue-band/action Beta numerators as unsigned 32-bit big-endian",
            "horizon queue-band/action Beta denominators as unsigned 32-bit big-endian",
        ],
        "binary payload contract",
    )
    _exact(
        trace.get("nonclaims"),
        [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not Lean-verified trace data",
            "not a direct deterministic-initial ControlledTrajectory horizon alignment",
            "not an unknown-kernel target-policy OPE result",
        ],
        "trace nonclaims",
    )

    _exact(model.get("schema_version"), "controlled-queue-input-v1", "model schema")
    _exact(model.get("model_version"), "controlled-queue-v1", "model version")
    _exact(model["state_space"]["queue_capacity"], 7, "queue capacity")
    _exact(model["state_space"]["regime_count"], 3, "regime count")
    _exact(model["state_space"]["arrival_by_regime"], [0, 1, 2], "arrival table")
    _exact([row["id"] for row in model["actions"]], list(ACTION_IDS), "action order")
    _exact([row["service_capacity"] for row in model["actions"]], [1, 2], "service table")
    _exact(model["nominal_candidate"], "nominal", "nominal candidate")
    nominal = next(row for row in model["candidates"] if row["id"] == "nominal")
    _exact(_rational(nominal["gamma"], "nominal gamma"), Fraction(3, 4), "nominal gamma")
    behavior = model["behavior_policy"]["boost_probability_by_state"]
    if len(behavior) != STATE_COUNT or any(Fraction(value) != Fraction(1, 2) for value in behavior):
        raise VerificationError("behavior policy is not the frozen uniform policy")
    _exact(
        model["causal_predictors"][1]["queue_bands"],
        [[0, 3], [4, 5], [6, 7]],
        "queue bands",
    )


def _verify_manifest(
    manifest: dict[str, Any],
    trace_input: Path,
    trace_input_raw: bytes,
    model_input: Path,
    model_input_raw: bytes,
    trace_path: Path,
    trace_raw: bytes,
    counts_path: Path,
    counts_raw: bytes,
) -> None:
    _exact(manifest.get("artifact_status"), ARTIFACT_STATUS, "manifest status")
    _exact(manifest.get("schema_version"), SCHEMA_VERSION, "manifest schema")
    _exact(manifest.get("trace_version"), TRACE_VERSION, "manifest trace version")
    generator = _object(manifest.get("generator"), "manifest generator")
    _exact(generator.get("path"), _display(TRACE_GENERATOR), "trace generator path")
    _exact(generator.get("revision"), GENERATOR_REVISION, "trace generator revision")
    _exact(generator.get("sha256"), _sha(TRACE_GENERATOR.read_bytes()), "trace generator hash")
    dependencies = _list(manifest.get("generator_dependencies"), "generator dependencies")
    _exact(len(dependencies), 1, "generator dependency count")
    dependency = _object(dependencies[0], "model generator dependency")
    _exact(dependency.get("path"), _display(MODEL_GENERATOR), "model generator path")
    _exact(dependency.get("sha256"), _sha(MODEL_GENERATOR.read_bytes()), "model generator hash")
    verifier = _object(manifest.get("independent_verifier"), "independent verifier")
    verifier_path = Path(__file__).resolve()
    _exact(verifier.get("path"), _display(verifier_path), "verifier path")
    _exact(verifier.get("sha256"), _sha(verifier_path.read_bytes()), "verifier hash")

    expected_files = [
        ("trace_input", trace_input, trace_input_raw),
        ("model_input", model_input, model_input_raw),
        ("raw_trace_output", trace_path, trace_raw),
        ("counts_output", counts_path, counts_raw),
    ]
    files = _list(manifest.get("files"), "manifest files")
    _exact(len(files), len(expected_files), "manifest file count")
    for row, (role, path, raw) in zip(files, expected_files, strict=True):
        item = _object(row, f"manifest file {role}")
        _exact(item.get("role"), role, f"{role} role")
        _exact(item.get("path"), _display(path), f"{role} path")
        _exact(item.get("sha256"), _sha(raw), f"{role} hash")
        if role.endswith("output"):
            _exact(item.get("bytes"), len(raw), f"{role} size")


def _decode_binary(raw: bytes, horizon: int) -> tuple[bytes, bytes, tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    expected_size = BINARY_HEADER.size + (horizon + 1) + horizon + 4 * horizon * 4
    if len(raw) != expected_size:
        raise VerificationError(
            f"binary size mismatch: expected {expected_size}, got {len(raw)}"
        )
    magic, stored_horizon = BINARY_HEADER.unpack_from(raw)
    _exact(magic, BINARY_MAGIC, "binary magic")
    _exact(stored_horizon, horizon, "binary horizon")
    offset = BINARY_HEADER.size
    states = raw[offset : offset + horizon + 1]
    offset += horizon + 1
    actions = raw[offset : offset + horizon]
    offset += horizon
    arrays = []
    for _index in range(4):
        arrays.append(struct.unpack_from(f">{horizon}I", raw, offset))
        offset += 4 * horizon
    return states, actions, arrays[0], arrays[1], arrays[2], arrays[3]


def _replay(
    trace_spec: dict[str, Any], model: dict[str, Any], trace_raw: bytes
) -> dict[str, Any]:
    horizon = trace_spec["trace_parameters"]["horizon"]
    states, actions, global_num, global_den, cell_num, cell_den = _decode_binary(
        trace_raw, horizon
    )
    if any(state >= STATE_COUNT for state in states):
        raise VerificationError("raw trace contains an out-of-range state")
    if any(action >= len(ACTION_IDS) for action in actions):
        raise VerificationError("raw trace contains an out-of-range action")
    _exact(states[0], trace_spec["trace_parameters"]["initial_state"], "raw initial state")

    prng = trace_spec["prng_contract"]
    stream = IndependentCounterStream(
        prng["domain_utf8"], prng["seed_hex"], prng["counter_start"]
    )
    behavior_weights = [
        _weights([1 - Fraction(value), Fraction(value)])
        for value in model["behavior_policy"]["boost_probability_by_state"]
    ]
    gamma = Fraction(
        next(row["gamma"] for row in model["candidates"] if row["id"] == "nominal")
    )
    base = (1 - gamma) / STATE_COUNT
    kernel_weights = []
    for state in range(STATE_COUNT):
        action_rows = []
        for action in range(len(ACTION_IDS)):
            step = _queue_step(model, state, action)
            action_rows.append(
                _weights(
                    [
                        base + (gamma if destination == step else 0)
                        for destination in range(STATE_COUNT)
                    ]
                )
            )
        kernel_weights.append(action_rows)

    bands = model["causal_predictors"][1]["queue_bands"]
    global_alpha = model["causal_predictors"][0]["prior_alpha"]
    global_beta = model["causal_predictors"][0]["prior_beta"]
    cell_alpha = model["causal_predictors"][1]["prior_alpha"]
    cell_beta = model["causal_predictors"][1]["prior_beta"]
    overload_minimum = model["outcomes"]["overload_queue_minimum"]

    source_visits = [0] * STATE_COUNT
    destination_counts = [0] * STATE_COUNT
    action_counts = [0] * len(ACTION_IDS)
    state_action_counts = [[0] * len(ACTION_IDS) for _state in range(STATE_COUNT)]
    edge_counts = [
        [[0] * STATE_COUNT for _action in range(len(ACTION_IDS))]
        for _state in range(STATE_COUNT)
    ]
    global_trials = 0
    global_successes = 0
    cell_trials = [[0] * len(ACTION_IDS) for _band_index in bands]
    cell_successes = [[0] * len(ACTION_IDS) for _band_index in bands]

    for time in range(horizon):
        state = states[time]
        action = _sample(behavior_weights[state], stream)
        _exact(actions[time], action, f"action replay at t={time}")
        band = _band(state // 3, bands)

        _exact(global_num[time], global_alpha + global_successes, f"global numerator at t={time}")
        _exact(
            global_den[time],
            global_alpha + global_beta + global_trials,
            f"global denominator at t={time}",
        )
        _exact(
            cell_num[time],
            cell_alpha + cell_successes[band][action],
            f"cell numerator at t={time}",
        )
        _exact(
            cell_den[time],
            cell_alpha + cell_beta + cell_trials[band][action],
            f"cell denominator at t={time}",
        )

        destination = _sample(kernel_weights[state][action], stream)
        _exact(states[time + 1], destination, f"next-state replay at t={time}")
        outcome = int(destination // 3 >= overload_minimum)

        source_visits[state] += 1
        destination_counts[destination] += 1
        action_counts[action] += 1
        state_action_counts[state][action] += 1
        edge_counts[state][action][destination] += 1
        global_trials += 1
        global_successes += outcome
        cell_trials[band][action] += 1
        cell_successes[band][action] += outcome

    if sum(source_visits) != horizon or sum(destination_counts) != horizon:
        raise VerificationError("state-count conservation failed")
    if sum(action_counts) != horizon:
        raise VerificationError("action-count conservation failed")
    if sum(sum(row) for row in state_action_counts) != horizon:
        raise VerificationError("state-action count conservation failed")
    if sum(sum(sum(row) for row in actions_) for actions_ in edge_counts) != horizon:
        raise VerificationError("edge-count conservation failed")

    cell_rows = []
    for band, pair in enumerate(bands):
        for action, action_id in enumerate(ACTION_IDS):
            trials = cell_trials[band][action]
            successes = cell_successes[band][action]
            cell_rows.append(
                {
                    "queue_band": pair,
                    "action": action_id,
                    "prior_alpha": cell_alpha,
                    "prior_beta": cell_beta,
                    "trials": trials,
                    "successes": successes,
                    "failures": trials - successes,
                    "final_posterior_numerator": cell_alpha + successes,
                    "final_posterior_denominator": cell_alpha + cell_beta + trials,
                }
            )
    return {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": SCHEMA_VERSION,
        "trace_version": TRACE_VERSION,
        "generator_revision": GENERATOR_REVISION,
        "horizon": horizon,
        "initial_state": states[0],
        "final_state": states[-1],
        "trace_sha256": _sha(trace_raw),
        "counts": {
            "source_state_visits": source_visits,
            "destination_state_counts": destination_counts,
            "action_counts": action_counts,
            "state_action_counts": state_action_counts,
            "edge_counts": edge_counts,
            "outcome_counts": {
                "non_overload": horizon - global_successes,
                "overload": global_successes,
            },
        },
        "causal_sufficient_statistics": {
            "global_beta": {
                "prior_alpha": global_alpha,
                "prior_beta": global_beta,
                "trials": global_trials,
                "successes": global_successes,
                "failures": global_trials - global_successes,
                "final_posterior_numerator": global_alpha + global_successes,
                "final_posterior_denominator": global_alpha + global_beta + global_trials,
            },
            "queue_band_action_beta": cell_rows,
        },
        "prng_audit": {
            "version": PRNG_VERSION,
            "words_consumed": stream.words,
            "bytes_consumed": stream.words * 8,
            "digest_blocks_generated": stream.blocks,
            "rejections_by_modulus": {
                str(key): value for key, value in sorted(stream.rejections.items())
            },
        },
        "nonclaims": trace_spec["nonclaims"],
    }


def verify_paths(
    trace_input: Path,
    model_input: Path,
    trace_path: Path,
    counts_path: Path,
    manifest_path: Path,
) -> None:
    trace_input_raw = trace_input.read_bytes()
    model_input_raw = model_input.read_bytes()
    trace_raw = trace_path.read_bytes()
    counts_raw = counts_path.read_bytes()
    manifest_raw = manifest_path.read_bytes()
    trace_spec = _object(parse_json(trace_input_raw, "trace input"), "trace input")
    model = _object(parse_json(model_input_raw, "model input"), "model input")
    counts = _object(parse_json(counts_raw, "counts output"), "counts output")
    manifest = _object(parse_json(manifest_raw, "manifest"), "manifest")
    _exact(counts_raw, _canonical_json(counts), "canonical counts bytes")
    _exact(manifest_raw, _canonical_json(manifest), "canonical manifest bytes")
    _verify_trace_contract(trace_spec, model, model_input_raw)
    _verify_manifest(
        manifest,
        trace_input,
        trace_input_raw,
        model_input,
        model_input_raw,
        trace_path,
        trace_raw,
        counts_path,
        counts_raw,
    )
    replayed = _replay(trace_spec, model, trace_raw)
    _exact(counts, replayed, "independently replayed counts and predictions")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trace-input", type=Path, default=DEFAULT_TRACE_INPUT)
    parser.add_argument("--model-input", type=Path, default=DEFAULT_MODEL_INPUT)
    parser.add_argument("--trace", type=Path, default=DEFAULT_TRACE)
    parser.add_argument("--counts", type=Path, default=DEFAULT_COUNTS)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--check",
        action="store_true",
        help="explicit read-only verification mode (the verifier never writes)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        verify_paths(
            args.trace_input,
            args.model_input,
            args.trace,
            args.counts,
            args.manifest,
        )
    except (OSError, VerificationError, KeyError, StopIteration, ValueError) as error:
        print(f"controlled-queue trace verification failed: {error}", file=sys.stderr)
        return 1
    print(
        "verified controlled-queue trace bytes, hashes, replay, counts, and causal prediction order"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
