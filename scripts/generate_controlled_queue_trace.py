#!/usr/bin/env python3
"""Generate the frozen controlled-queue trace and causal prediction data.

This dependency-free generator implements the versioned SHA-256 counter-stream
and exact categorical sampling contracts in ``trace-v1.json``.  Its outputs
are deterministic data/preprocessing artifacts only.  They are not imported
into Lean and do not establish a certificate or good-event membership.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import struct
import sys
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import generate_controlled_queue_model as model_generator  # noqa: E402


DEFAULT_TRACE_INPUT = ROOT / "applications" / "controlled_queue" / "trace-v1.json"
DEFAULT_MODEL_INPUT = ROOT / "applications" / "controlled_queue" / "model-v1.json"
DEFAULT_TRACE_OUTPUT = (
    ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1.bin"
)
DEFAULT_COUNTS_OUTPUT = (
    ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1-counts.json"
)
DEFAULT_MANIFEST_OUTPUT = (
    ROOT / "applications" / "controlled_queue" / "generated" / "trace-v1-manifest.json"
)
DEFAULT_VERIFIER = ROOT / "scripts" / "verify_controlled_queue_trace.py"

SCHEMA_VERSION = "controlled-queue-trace-input-v1"
TRACE_VERSION = "controlled-queue-trace-v1"
GENERATOR_REVISION = "controlled-queue-trace-generator-v1"
ARTIFACT_STATUS = "TRACE/PREPROCESSING ONLY"
BINARY_VERSION = "controlled-queue-trace-binary-v1"
BINARY_MAGIC = bytes.fromhex("4351545256310000")
BINARY_HEADER = struct.Struct(">8sQ")
UINT64_SPACE = 1 << 64

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
CANDIDATE_SUPPORT = ("low", "nominal", "high")
TILT_SUPPORT = ("1/16", "1/8", "1/4", "1/2", "1")
PRNG_VERSION = "sha256-counter-stream-v1"
SAMPLING_VERSION = "exact-categorical-u64-rejection-v1"
DOMAIN = "FormalSLT/controlled-queue/trace-v1"
SEED_HEX = "00000000000000000000000000000000000000000000000000000000013527d4"
COUNTER_ZERO_DIGEST_HEX = (
    "4937262570967d5d0f4abeb19ec4c872ba9868308e594c0ae9acc077a6349896"
)


class TraceSchemaError(ValueError):
    """Raised when the frozen trace input violates its exact v1 contract."""


def _reject_float(value: str) -> None:
    raise TraceSchemaError(f"floating-point JSON numbers are forbidden: {value}")


def _reject_constant(value: str) -> None:
    raise TraceSchemaError(f"non-finite JSON number is forbidden: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise TraceSchemaError(f"duplicate JSON key: {key}")
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
        raise TraceSchemaError(f"invalid UTF-8 JSON in {where}: {error}") from error


def _expect_object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise TraceSchemaError(f"{where} must be an object")
    return value


def _expect_list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise TraceSchemaError(f"{where} must be an array")
    return value


def _expect_keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    if set(value) != expected:
        raise TraceSchemaError(
            f"{where} keys mismatch; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def _expect_exact(actual: Any, expected: Any, where: str) -> None:
    if actual != expected:
        raise TraceSchemaError(f"{where} must be {expected!r}, got {actual!r}")


def _fraction(value: Any, where: str) -> Fraction:
    if not isinstance(value, str):
        raise TraceSchemaError(f"{where} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise TraceSchemaError(f"invalid rational at {where}: {value!r}") from error
    if model_generator.rational_text(result) != value:
        raise TraceSchemaError(f"noncanonical rational at {where}: {value!r}")
    return result


def _validate_distribution(values: Any, length: int, where: str) -> list[Fraction]:
    entries = _expect_list(values, where)
    if len(entries) != length:
        raise TraceSchemaError(f"{where} must contain {length} entries")
    parsed = [_fraction(value, f"{where}[{index}]") for index, value in enumerate(entries)]
    if any(value < 0 for value in parsed) or sum(parsed) != 1:
        raise TraceSchemaError(f"{where} must be a nonnegative normalized distribution")
    return parsed


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def validate_trace_spec(
    spec: dict[str, Any], model_bytes: bytes, model_spec: dict[str, Any]
) -> None:
    _expect_keys(
        spec,
        {
            "schema_version",
            "trace_version",
            "artifact_status",
            "model_binding",
            "trace_parameters",
            "prng_contract",
            "sampling_contract",
            "weight_tables",
            "binary_contract",
            "nonclaims",
        },
        "trace input",
    )
    _expect_exact(spec["schema_version"], SCHEMA_VERSION, "schema_version")
    _expect_exact(spec["trace_version"], TRACE_VERSION, "trace_version")
    _expect_exact(spec["artifact_status"], ARTIFACT_STATUS, "artifact_status")

    binding = _expect_object(spec["model_binding"], "model_binding")
    _expect_keys(
        binding,
        {"path", "schema_version", "model_version", "sha256"},
        "model_binding",
    )
    _expect_exact(
        binding["path"],
        "applications/controlled_queue/model-v1.json",
        "model_binding.path",
    )
    _expect_exact(binding["schema_version"], model_spec["schema_version"], "model binding")
    _expect_exact(binding["model_version"], model_spec["model_version"], "model binding")
    _expect_exact(binding["sha256"], sha256_bytes(model_bytes), "model_binding.sha256")

    parameters = _expect_object(spec["trace_parameters"], "trace_parameters")
    _expect_keys(
        parameters,
        {
            "horizon",
            "initial_state",
            "source_candidate",
            "behavior_policy",
            "transition_order",
        },
        "trace_parameters",
    )
    _expect_exact(parameters["horizon"], 200000, "trace_parameters.horizon")
    _expect_exact(
        parameters["horizon"], model_spec["generation"]["horizon"], "trace horizon"
    )
    _expect_exact(parameters["initial_state"], 0, "trace_parameters.initial_state")
    _expect_exact(
        parameters["source_candidate"], model_spec["nominal_candidate"], "source candidate"
    )
    _expect_exact(
        parameters["behavior_policy"], model_spec["behavior_policy"]["id"], "behavior policy"
    )
    _expect_exact(
        parameters["transition_order"],
        [
            "sample action from behavior policy at current state",
            "record causal predictions from transitions with index strictly below t",
            "sample next state from source candidate",
            "record outcome and update causal sufficient statistics",
        ],
        "trace_parameters.transition_order",
    )

    prng = _expect_object(spec["prng_contract"], "prng_contract")
    _expect_keys(
        prng,
        {
            "version",
            "hash",
            "domain_utf8",
            "separator_hex",
            "seed_hex",
            "counter_start",
            "counter_encoding",
            "block_input",
            "block_output",
            "word_encoding",
            "counter_zero_digest_hex",
        },
        "prng_contract",
    )
    expected_prng = {
        "version": PRNG_VERSION,
        "hash": "SHA-256",
        "domain_utf8": DOMAIN,
        "separator_hex": "00",
        "seed_hex": SEED_HEX,
        "counter_start": 0,
        "counter_encoding": "unsigned 64-bit big-endian",
        "block_input": "domain_utf8 || 0x00 || seed_bytes || counter_u64_be",
        "block_output": "32 digest bytes consumed left-to-right",
        "word_encoding": "eight consecutive stream bytes as unsigned 64-bit big-endian",
        "counter_zero_digest_hex": COUNTER_ZERO_DIGEST_HEX,
    }
    _expect_exact(prng, expected_prng, "prng_contract")
    computed_vector = hashlib.sha256(
        DOMAIN.encode() + b"\0" + bytes.fromhex(SEED_HEX) + (0).to_bytes(8, "big")
    ).hexdigest()
    _expect_exact(computed_vector, COUNTER_ZERO_DIGEST_HEX, "PRNG test vector")

    sampling = _expect_object(spec["sampling_contract"], "sampling_contract")
    _expect_keys(
        sampling,
        {"version", "uniform_integer", "categorical", "draw_order"},
        "sampling_contract",
    )
    _expect_exact(sampling["version"], SAMPLING_VERSION, "sampling_contract.version")
    _expect_exact(
        sampling["uniform_integer"],
        "for modulus m, set limit = 2^64 - (2^64 mod m); reject words x >= limit; return x mod m",
        "sampling_contract.uniform_integer",
    )
    _expect_exact(
        sampling["categorical"],
        "reduce rational probabilities to integer weights over their least common denominator; draw uniformly below the total weight; use left-closed cumulative intervals in listed order",
        "sampling_contract.categorical",
    )
    _expect_exact(
        sampling["draw_order"],
        "one categorical action draw followed by one categorical next-state draw per transition; rejection draws consume additional words immediately",
        "sampling_contract.draw_order",
    )

    tables = _expect_object(spec["weight_tables"], "weight_tables")
    _expect_keys(
        tables,
        {
            "prior_weights",
            "posterior_weights",
            "candidate_weights",
            "coordinate_weights",
            "tilt_weights",
        },
        "weight_tables",
    )
    prior = _expect_object(tables["prior_weights"], "prior_weights")
    _expect_keys(prior, {"support", "weights"}, "prior_weights")
    _expect_exact(prior["support"], list(PREDICTOR_SUPPORT), "prior_weights.support")
    _expect_exact(
        _validate_distribution(prior["weights"], 5, "prior_weights.weights"),
        [Fraction(1, 5)] * 5,
        "prior weights",
    )

    posteriors = _expect_list(tables["posterior_weights"], "posterior_weights")
    if len(posteriors) != len(POSTERIOR_IDS):
        raise TraceSchemaError("posterior_weights must contain five deltas and one uniform row")
    for index, (row, expected_id) in enumerate(zip(posteriors, POSTERIOR_IDS, strict=True)):
        obj = _expect_object(row, f"posterior_weights[{index}]")
        _expect_keys(obj, {"id", "weights"}, f"posterior_weights[{index}]")
        _expect_exact(obj["id"], expected_id, f"posterior_weights[{index}].id")
        weights = _validate_distribution(obj["weights"], 5, f"posterior_weights[{index}].weights")
        expected = [Fraction(1 if j == index else 0) for j in range(5)]
        if index == 5:
            expected = [Fraction(1, 5)] * 5
        _expect_exact(weights, expected, f"posterior_weights[{index}].weights")

    candidates = _expect_object(tables["candidate_weights"], "candidate_weights")
    _expect_keys(candidates, {"support", "weights"}, "candidate_weights")
    _expect_exact(candidates["support"], list(CANDIDATE_SUPPORT), "candidate support")
    _expect_exact(
        _validate_distribution(candidates["weights"], 3, "candidate_weights.weights"),
        [Fraction(1, 3)] * 3,
        "candidate weights",
    )
    coordinates = _expect_object(tables["coordinate_weights"], "coordinate_weights")
    _expect_keys(coordinates, {"support_encoding", "weights"}, "coordinate_weights")
    _expect_exact(
        coordinates["support_encoding"],
        "augmented_state_id = 2 * state_id + action_index",
        "coordinate_weights.support_encoding",
    )
    _expect_exact(
        _validate_distribution(coordinates["weights"], 48, "coordinate_weights.weights"),
        [Fraction(1, 48)] * 48,
        "coordinate weights",
    )
    tilts = _expect_object(tables["tilt_weights"], "tilt_weights")
    _expect_keys(tilts, {"support", "weights"}, "tilt_weights")
    _expect_exact(tilts["support"], list(TILT_SUPPORT), "tilt support")
    _expect_exact(tilts["support"], model_spec["generation"]["tilt_grid"], "model tilt grid")
    _expect_exact(
        _validate_distribution(tilts["weights"], 5, "tilt_weights.weights"),
        [Fraction(1, 5)] * 5,
        "tilt weights",
    )

    binary = _expect_object(spec["binary_contract"], "binary_contract")
    _expect_keys(binary, {"version", "magic_hex", "header", "payload"}, "binary_contract")
    _expect_exact(binary["version"], BINARY_VERSION, "binary_contract.version")
    _expect_exact(binary["magic_hex"], BINARY_MAGIC.hex(), "binary_contract.magic_hex")
    _expect_exact(
        binary["header"],
        "8 magic bytes followed by horizon as unsigned 64-bit big-endian",
        "binary_contract.header",
    )
    payload = _expect_list(binary["payload"], "binary_contract.payload")
    if len(payload) != 6 or not all(isinstance(item, str) for item in payload):
        raise TraceSchemaError("binary_contract.payload must describe exactly six arrays")

    _expect_exact(
        spec["nonclaims"],
        [
            "not a statistical certificate",
            "not a theorem-produced good path",
            "not Lean-verified trace data",
            "not a direct deterministic-initial ControlledTrajectory horizon alignment",
            "not an unknown-kernel target-policy OPE result",
        ],
        "nonclaims",
    )


def parse_trace_input_bytes(
    raw: bytes, model_bytes: bytes, model_spec: dict[str, Any]
) -> dict[str, Any]:
    value = _expect_object(parse_json_bytes(raw, "trace input"), "trace input")
    validate_trace_spec(value, model_bytes, model_spec)
    return value


class CounterStream:
    """SHA-256 counter stream with the exact frozen v1 byte contract."""

    def __init__(self, domain: str, seed_hex: str, counter_start: int = 0) -> None:
        self._prefix = domain.encode("utf-8") + b"\0" + bytes.fromhex(seed_hex)
        self._counter = counter_start
        self._buffer = b""
        self.words_consumed = 0
        self.digest_blocks_generated = 0
        self.rejections_by_modulus: dict[int, int] = {}

    def _refill(self) -> None:
        if self._counter >= UINT64_SPACE:
            raise OverflowError("SHA-256 counter stream exhausted")
        self._buffer += hashlib.sha256(
            self._prefix + self._counter.to_bytes(8, "big")
        ).digest()
        self._counter += 1
        self.digest_blocks_generated += 1

    def next_u64(self) -> int:
        while len(self._buffer) < 8:
            self._refill()
        word = int.from_bytes(self._buffer[:8], "big")
        self._buffer = self._buffer[8:]
        self.words_consumed += 1
        return word

    def uniform_below(self, modulus: int) -> int:
        value, rejections = rejection_sample_u64(modulus, self.next_u64)
        if rejections:
            self.rejections_by_modulus[modulus] = (
                self.rejections_by_modulus.get(modulus, 0) + rejections
            )
        return value


def rejection_sample_u64(
    modulus: int, draw_word: Callable[[], int]
) -> tuple[int, int]:
    """Return an unbiased integer below ``modulus`` and the rejection count."""

    if not 1 <= modulus <= UINT64_SPACE:
        raise ValueError("modulus must lie in [1, 2^64]")
    limit = UINT64_SPACE - (UINT64_SPACE % modulus)
    rejections = 0
    while True:
        word = draw_word()
        if not 0 <= word < UINT64_SPACE:
            raise ValueError("draw_word returned a value outside unsigned 64-bit range")
        if word < limit:
            return word % modulus, rejections
        rejections += 1


def integer_weights(probabilities: Sequence[Fraction]) -> list[int]:
    if not probabilities or any(value < 0 for value in probabilities):
        raise ValueError("categorical probabilities must be nonempty and nonnegative")
    if sum(probabilities) != 1:
        raise ValueError("categorical probabilities must sum exactly to one")
    denominator = math.lcm(*(value.denominator for value in probabilities))
    weights = [value.numerator * (denominator // value.denominator) for value in probabilities]
    common = math.gcd(*weights)
    return [weight // common for weight in weights]


def sample_from_weights(weights: Sequence[int], stream: CounterStream) -> int:
    if not weights or any(weight < 0 for weight in weights):
        raise ValueError("categorical weights must be nonempty and nonnegative")
    total = sum(weights)
    if total <= 0:
        raise ValueError("categorical weights must have positive total")
    draw = stream.uniform_below(total)
    cumulative = 0
    for index, weight in enumerate(weights):
        cumulative += weight
        if draw < cumulative:
            return index
    raise AssertionError("categorical draw escaped its cumulative intervals")


def _queue_band(queue: int, bands: Sequence[Sequence[int]]) -> int:
    for index, (lower, upper) in enumerate(bands):
        if lower <= queue <= upper:
            return index
    raise AssertionError(f"queue {queue} belongs to no frozen band")


def _pack_u32(values: Sequence[int]) -> bytes:
    if any(not 0 <= value < (1 << 32) for value in values):
        raise OverflowError("prediction numerator or denominator exceeds uint32")
    return struct.pack(f">{len(values)}I", *values)


def _candidate_weights(
    model_spec: dict[str, Any], candidate_id: str
) -> list[list[list[int]]]:
    candidate = next(
        row for row in model_spec["candidates"] if row["id"] == candidate_id
    )
    gamma = Fraction(candidate["gamma"])
    base = (1 - gamma) / model_generator.STATE_COUNT
    rows: list[list[list[int]]] = []
    for state in range(model_generator.STATE_COUNT):
        action_rows = []
        for action in range(len(model_generator.ACTION_IDS)):
            step = model_generator.queue_step(model_spec, state, action)
            probabilities = [
                base + (gamma if destination == step else 0)
                for destination in range(model_generator.STATE_COUNT)
            ]
            action_rows.append(integer_weights(probabilities))
        rows.append(action_rows)
    return rows


def generate_trace(
    trace_spec: dict[str, Any], model_spec: dict[str, Any]
) -> tuple[bytes, dict[str, Any]]:
    parameters = trace_spec["trace_parameters"]
    horizon = parameters["horizon"]
    stream = CounterStream(
        trace_spec["prng_contract"]["domain_utf8"],
        trace_spec["prng_contract"]["seed_hex"],
        trace_spec["prng_contract"]["counter_start"],
    )
    behavior_weights = [
        integer_weights([1 - Fraction(boost), Fraction(boost)])
        for boost in model_spec["behavior_policy"]["boost_probability_by_state"]
    ]
    kernel_weights = _candidate_weights(model_spec, parameters["source_candidate"])
    bands = model_spec["causal_predictors"][1]["queue_bands"]
    global_alpha = model_spec["causal_predictors"][0]["prior_alpha"]
    global_beta = model_spec["causal_predictors"][0]["prior_beta"]
    cell_alpha = model_spec["causal_predictors"][1]["prior_alpha"]
    cell_beta = model_spec["causal_predictors"][1]["prior_beta"]
    overload_minimum = model_spec["outcomes"]["overload_queue_minimum"]

    states = bytearray([parameters["initial_state"]])
    actions = bytearray()
    global_numerators: list[int] = []
    global_denominators: list[int] = []
    cell_numerators: list[int] = []
    cell_denominators: list[int] = []

    source_visits = [0] * 24
    destination_counts = [0] * 24
    action_counts = [0] * 2
    state_action_counts = [[0] * 2 for _state in range(24)]
    edge_counts = [[[0] * 24 for _action in range(2)] for _state in range(24)]
    global_trials = 0
    global_successes = 0
    cell_trials = [[0] * 2 for _band in range(len(bands))]
    cell_successes = [[0] * 2 for _band in range(len(bands))]
    state = parameters["initial_state"]

    for _time in range(horizon):
        action = sample_from_weights(behavior_weights[state], stream)
        band = _queue_band(state // 3, bands)

        global_numerators.append(global_alpha + global_successes)
        global_denominators.append(global_alpha + global_beta + global_trials)
        cell_numerators.append(cell_alpha + cell_successes[band][action])
        cell_denominators.append(
            cell_alpha + cell_beta + cell_trials[band][action]
        )

        destination = sample_from_weights(kernel_weights[state][action], stream)
        outcome = int(destination // 3 >= overload_minimum)

        actions.append(action)
        states.append(destination)
        source_visits[state] += 1
        destination_counts[destination] += 1
        action_counts[action] += 1
        state_action_counts[state][action] += 1
        edge_counts[state][action][destination] += 1

        global_trials += 1
        global_successes += outcome
        cell_trials[band][action] += 1
        cell_successes[band][action] += outcome
        state = destination

    trace_bytes = b"".join(
        (
            BINARY_HEADER.pack(BINARY_MAGIC, horizon),
            bytes(states),
            bytes(actions),
            _pack_u32(global_numerators),
            _pack_u32(global_denominators),
            _pack_u32(cell_numerators),
            _pack_u32(cell_denominators),
        )
    )
    trace_hash = sha256_bytes(trace_bytes)
    cell_rows = []
    for band, (lower, upper) in enumerate(bands):
        for action, action_id in enumerate(model_generator.ACTION_IDS):
            trials = cell_trials[band][action]
            successes = cell_successes[band][action]
            cell_rows.append(
                {
                    "queue_band": [lower, upper],
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
    counts = {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": SCHEMA_VERSION,
        "trace_version": TRACE_VERSION,
        "generator_revision": GENERATOR_REVISION,
        "horizon": horizon,
        "initial_state": parameters["initial_state"],
        "final_state": state,
        "trace_sha256": trace_hash,
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
            "words_consumed": stream.words_consumed,
            "bytes_consumed": stream.words_consumed * 8,
            "digest_blocks_generated": stream.digest_blocks_generated,
            "rejections_by_modulus": {
                str(key): value for key, value in sorted(stream.rejections_by_modulus.items())
            },
        },
        "nonclaims": trace_spec["nonclaims"],
    }
    return trace_bytes, counts


def _display_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.name


def build_manifest(
    trace_spec: dict[str, Any],
    trace_input: Path,
    trace_input_bytes: bytes,
    model_input: Path,
    model_input_bytes: bytes,
    trace_output: Path,
    trace_bytes: bytes,
    counts_output: Path,
    counts_bytes: bytes,
) -> dict[str, Any]:
    generator_path = Path(__file__).resolve()
    model_generator_path = Path(model_generator.__file__).resolve()
    verifier_path = DEFAULT_VERIFIER.resolve()
    if not verifier_path.is_file():
        raise TraceSchemaError(f"independent verifier is missing: {verifier_path}")
    return {
        "artifact_status": ARTIFACT_STATUS,
        "schema_version": SCHEMA_VERSION,
        "trace_version": TRACE_VERSION,
        "generator": {
            "path": _display_path(generator_path),
            "revision": GENERATOR_REVISION,
            "sha256": sha256_bytes(generator_path.read_bytes()),
        },
        "generator_dependencies": [
            {
                "path": _display_path(model_generator_path),
                "sha256": sha256_bytes(model_generator_path.read_bytes()),
            }
        ],
        "independent_verifier": {
            "path": _display_path(verifier_path),
            "sha256": sha256_bytes(verifier_path.read_bytes()),
        },
        "parameters": {
            "horizon": trace_spec["trace_parameters"]["horizon"],
            "initial_state": trace_spec["trace_parameters"]["initial_state"],
            "source_candidate": trace_spec["trace_parameters"]["source_candidate"],
            "behavior_policy": trace_spec["trace_parameters"]["behavior_policy"],
            "prng_version": trace_spec["prng_contract"]["version"],
            "sampling_version": trace_spec["sampling_contract"]["version"],
            "binary_version": trace_spec["binary_contract"]["version"],
            "binary_layout": trace_spec["binary_contract"],
        },
        "files": [
            {
                "role": "trace_input",
                "path": _display_path(trace_input),
                "sha256": sha256_bytes(trace_input_bytes),
            },
            {
                "role": "model_input",
                "path": _display_path(model_input),
                "sha256": sha256_bytes(model_input_bytes),
            },
            {
                "role": "raw_trace_output",
                "path": _display_path(trace_output),
                "bytes": len(trace_bytes),
                "sha256": sha256_bytes(trace_bytes),
            },
            {
                "role": "counts_output",
                "path": _display_path(counts_output),
                "bytes": len(counts_bytes),
                "sha256": sha256_bytes(counts_bytes),
            },
        ],
        "manifest_note": "the manifest is canonical JSON and is not recursively self-hashed",
        "nonclaims": trace_spec["nonclaims"],
    }


def expected_artifacts(
    trace_input: Path,
    model_input: Path,
    trace_output: Path,
    counts_output: Path,
) -> tuple[bytes, bytes, bytes]:
    trace_input_bytes = trace_input.read_bytes()
    model_input_bytes = model_input.read_bytes()
    model_spec = model_generator.parse_input_bytes(model_input_bytes)
    trace_spec = parse_trace_input_bytes(trace_input_bytes, model_input_bytes, model_spec)
    trace_bytes, counts = generate_trace(trace_spec, model_spec)
    counts_bytes = canonical_json_bytes(counts)
    manifest = build_manifest(
        trace_spec,
        trace_input,
        trace_input_bytes,
        model_input,
        model_input_bytes,
        trace_output,
        trace_bytes,
        counts_output,
        counts_bytes,
    )
    return trace_bytes, counts_bytes, canonical_json_bytes(manifest)


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
    parser.add_argument("--trace-input", type=Path, default=DEFAULT_TRACE_INPUT)
    parser.add_argument("--model-input", type=Path, default=DEFAULT_MODEL_INPUT)
    parser.add_argument("--trace-output", type=Path, default=DEFAULT_TRACE_OUTPUT)
    parser.add_argument("--counts-output", type=Path, default=DEFAULT_COUNTS_OUTPUT)
    parser.add_argument("--manifest-output", type=Path, default=DEFAULT_MANIFEST_OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless all generated artifacts are byte-identical to fresh output",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        trace_bytes, counts_bytes, manifest_bytes = expected_artifacts(
            args.trace_input,
            args.model_input,
            args.trace_output,
            args.counts_output,
        )
    except (OSError, TraceSchemaError, model_generator.SchemaError, ValueError) as error:
        print(f"controlled-queue trace generation failed: {error}", file=sys.stderr)
        return 2
    artifacts = (
        (args.trace_output, trace_bytes),
        (args.counts_output, counts_bytes),
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
