from __future__ import annotations

import hashlib
import json
import struct
from fractions import Fraction
from pathlib import Path

from scripts import generate_controlled_queue_model as model_generator
from scripts import generate_controlled_queue_trace as generator
from scripts import verify_controlled_queue_trace as verifier


def _expected() -> tuple[bytes, bytes, bytes]:
    return generator.expected_artifacts(
        generator.DEFAULT_TRACE_INPUT,
        generator.DEFAULT_MODEL_INPUT,
        generator.DEFAULT_TRACE_OUTPUT,
        generator.DEFAULT_COUNTS_OUTPUT,
    )


def _temp_arguments(tmp_path: Path) -> tuple[list[str], dict[str, Path]]:
    paths = {
        "trace_input": tmp_path / "trace-v1.json",
        "model_input": tmp_path / "model-v1.json",
        "trace": tmp_path / "trace-v1.bin",
        "counts": tmp_path / "trace-v1-counts.json",
        "manifest": tmp_path / "trace-v1-manifest.json",
    }
    paths["trace_input"].write_bytes(generator.DEFAULT_TRACE_INPUT.read_bytes())
    paths["model_input"].write_bytes(generator.DEFAULT_MODEL_INPUT.read_bytes())
    arguments = [
        "--trace-input",
        str(paths["trace_input"]),
        "--model-input",
        str(paths["model_input"]),
        "--trace-output",
        str(paths["trace"]),
        "--counts-output",
        str(paths["counts"]),
        "--manifest-output",
        str(paths["manifest"]),
    ]
    return arguments, paths


def _verifier_arguments(paths: dict[str, Path]) -> list[str]:
    return [
        "--trace-input",
        str(paths["trace_input"]),
        "--model-input",
        str(paths["model_input"]),
        "--trace",
        str(paths["trace"]),
        "--counts",
        str(paths["counts"]),
        "--manifest",
        str(paths["manifest"]),
        "--check",
    ]


def _rewrite_manifest_hash(paths: dict[str, Path], role: str, raw: bytes) -> None:
    manifest = json.loads(paths["manifest"].read_bytes())
    item = next(row for row in manifest["files"] if row["role"] == role)
    item["sha256"] = hashlib.sha256(raw).hexdigest()
    if role.endswith("output"):
        item["bytes"] = len(raw)
    paths["manifest"].write_text(
        json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    )


def _decode_prediction_arrays(
    raw: bytes, horizon: int
) -> tuple[bytes, bytes, tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    magic, stored_horizon = generator.BINARY_HEADER.unpack_from(raw)
    assert magic == generator.BINARY_MAGIC
    assert stored_horizon == horizon
    offset = generator.BINARY_HEADER.size
    states = raw[offset : offset + horizon + 1]
    offset += horizon + 1
    actions = raw[offset : offset + horizon]
    offset += horizon
    arrays = []
    for _index in range(4):
        arrays.append(struct.unpack_from(f">{horizon}I", raw, offset))
        offset += 4 * horizon
    assert offset == len(raw)
    return states, actions, arrays[0], arrays[1], arrays[2], arrays[3]


def test_generation_is_byte_deterministic_and_matches_tracked_artifacts() -> None:
    first = _expected()
    second = _expected()
    assert first == second
    assert first[0] == generator.DEFAULT_TRACE_OUTPUT.read_bytes()
    assert first[1] == generator.DEFAULT_COUNTS_OUTPUT.read_bytes()
    assert first[2] == generator.DEFAULT_MANIFEST_OUTPUT.read_bytes()


def test_manifest_binds_every_consumed_input_output_and_generator() -> None:
    trace_bytes, counts_bytes, manifest_bytes = _expected()
    manifest = json.loads(manifest_bytes)
    files = {row["role"]: row for row in manifest["files"]}
    assert set(files) == {
        "trace_input",
        "model_input",
        "raw_trace_output",
        "counts_output",
    }
    assert files["trace_input"]["sha256"] == hashlib.sha256(
        generator.DEFAULT_TRACE_INPUT.read_bytes()
    ).hexdigest()
    assert files["model_input"]["sha256"] == hashlib.sha256(
        generator.DEFAULT_MODEL_INPUT.read_bytes()
    ).hexdigest()
    assert files["raw_trace_output"]["sha256"] == hashlib.sha256(trace_bytes).hexdigest()
    assert files["counts_output"]["sha256"] == hashlib.sha256(counts_bytes).hexdigest()
    assert manifest["generator"]["sha256"] == hashlib.sha256(
        Path(generator.__file__).read_bytes()
    ).hexdigest()
    assert manifest["generator_dependencies"][0]["sha256"] == hashlib.sha256(
        Path(model_generator.__file__).read_bytes()
    ).hexdigest()
    assert manifest["independent_verifier"]["sha256"] == hashlib.sha256(
        Path(verifier.__file__).read_bytes()
    ).hexdigest()


def test_frozen_weight_and_sampling_tables_are_exactly_normalized() -> None:
    model_raw = generator.DEFAULT_MODEL_INPUT.read_bytes()
    model = model_generator.parse_input_bytes(model_raw)
    trace = generator.parse_trace_input_bytes(
        generator.DEFAULT_TRACE_INPUT.read_bytes(), model_raw, model
    )
    tables = trace["weight_tables"]
    distributions = [
        tables["prior_weights"]["weights"],
        tables["candidate_weights"]["weights"],
        tables["coordinate_weights"]["weights"],
        tables["tilt_weights"]["weights"],
        *(row["weights"] for row in tables["posterior_weights"]),
    ]
    for values in distributions:
        parsed = [Fraction(value) for value in values]
        assert all(value >= 0 for value in parsed)
        assert sum(parsed) == 1

    compiled = model_generator.build_tables(model)
    behavior = compiled["policies"][0]
    assert all(sum(Fraction(value) for value in row["probabilities"]) == 1 for row in behavior["rows"])
    nominal = next(row for row in compiled["candidate_kernels"] if row["id"] == "nominal")
    assert all(sum(Fraction(value) for value in row["probabilities"]) == 1 for row in nominal["rows"])


def test_prng_vector_and_unbiased_rejection_behavior_are_frozen() -> None:
    stream = generator.CounterStream(generator.DOMAIN, generator.SEED_HEX)
    assert [stream.next_u64() for _index in range(4)] == [
        5275727430732381533,
        1101902728927692914,
        13445611245270551562,
        16838044726953547926,
    ]
    assert stream.digest_blocks_generated == 1

    draws = iter([(1 << 64) - 1, 7])
    value, rejections = generator.rejection_sample_u64(10, lambda: next(draws))
    assert value == 7
    assert rejections == 1


def test_binary_predictions_are_prequential_without_look_ahead() -> None:
    raw = generator.DEFAULT_TRACE_OUTPUT.read_bytes()
    horizon = 200000
    states, actions, global_num, global_den, cell_num, cell_den = _decode_prediction_arrays(
        raw, horizon
    )
    assert len(states) == horizon + 1
    assert len(actions) == horizon
    assert (global_num[0], global_den[0]) == (1, 2)
    assert (cell_num[0], cell_den[0]) == (1, 2)

    global_trials = 0
    global_successes = 0
    cell_trials = [[0, 0] for _band in range(3)]
    cell_successes = [[0, 0] for _band in range(3)]
    bands = [[0, 3], [4, 5], [6, 7]]
    for time in range(1000):
        queue = states[time] // 3
        band = next(i for i, (low, high) in enumerate(bands) if low <= queue <= high)
        action = actions[time]
        assert (global_num[time], global_den[time]) == (
            1 + global_successes,
            2 + global_trials,
        )
        assert (cell_num[time], cell_den[time]) == (
            1 + cell_successes[band][action],
            2 + cell_trials[band][action],
        )
        outcome = int(states[time + 1] // 3 >= 6)
        global_trials += 1
        global_successes += outcome
        cell_trials[band][action] += 1
        cell_successes[band][action] += outcome


def test_count_tables_conserve_all_transitions_and_match_sufficient_statistics() -> None:
    counts = json.loads(generator.DEFAULT_COUNTS_OUTPUT.read_bytes())
    horizon = counts["horizon"]
    data = counts["counts"]
    assert sum(data["source_state_visits"]) == horizon
    assert sum(data["destination_state_counts"]) == horizon
    assert sum(data["action_counts"]) == horizon
    assert sum(sum(row) for row in data["state_action_counts"]) == horizon
    assert sum(
        sum(sum(destinations) for destinations in action_rows)
        for action_rows in data["edge_counts"]
    ) == horizon
    assert sum(data["outcome_counts"].values()) == horizon
    global_stats = counts["causal_sufficient_statistics"]["global_beta"]
    assert global_stats["trials"] == horizon
    assert global_stats["successes"] == data["outcome_counts"]["overload"]
    cell_rows = counts["causal_sufficient_statistics"]["queue_band_action_beta"]
    assert sum(row["trials"] for row in cell_rows) == horizon
    assert sum(row["successes"] for row in cell_rows) == global_stats["successes"]


def test_independent_verifier_replays_the_tracked_trace() -> None:
    assert verifier.main(["--check"]) == 0
    assert "import generate_controlled_queue_trace" not in Path(verifier.__file__).read_text()


def test_independent_verifier_fails_on_tampered_trace(tmp_path: Path) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    assert verifier.main(_verifier_arguments(paths)) == 0
    raw = bytearray(paths["trace"].read_bytes())
    raw[generator.BINARY_HEADER.size + 17] ^= 1
    paths["trace"].write_bytes(raw)
    assert verifier.main(_verifier_arguments(paths)) == 1


def test_independent_verifier_rejects_manifest_parameter_tamper(tmp_path: Path) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    manifest = json.loads(paths["manifest"].read_bytes())
    manifest["parameters"]["horizon"] -= 1
    paths["manifest"].write_text(
        json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    )
    assert verifier.main(_verifier_arguments(paths)) == 1


def test_independent_replay_rejects_trace_tamper_after_rehash(tmp_path: Path) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    raw = bytearray(paths["trace"].read_bytes())
    raw[generator.BINARY_HEADER.size + 17] ^= 1
    tampered = bytes(raw)
    paths["trace"].write_bytes(tampered)
    _rewrite_manifest_hash(paths, "raw_trace_output", tampered)
    assert verifier.main(_verifier_arguments(paths)) == 1


def test_independent_replay_rejects_prediction_tamper_after_rehash(
    tmp_path: Path,
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    raw = bytearray(paths["trace"].read_bytes())
    horizon = 200000
    global_numerator_offset = generator.BINARY_HEADER.size + (horizon + 1) + horizon
    raw[global_numerator_offset + 3] ^= 1
    tampered = bytes(raw)
    paths["trace"].write_bytes(tampered)
    _rewrite_manifest_hash(paths, "raw_trace_output", tampered)
    assert verifier.main(_verifier_arguments(paths)) == 1


def test_independent_replay_rejects_count_tamper_after_rehash(tmp_path: Path) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    counts = json.loads(paths["counts"].read_bytes())
    counts["counts"]["action_counts"][0] -= 1
    tampered = (
        json.dumps(counts, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode()
    paths["counts"].write_bytes(tampered)
    _rewrite_manifest_hash(paths, "counts_output", tampered)
    assert verifier.main(_verifier_arguments(paths)) == 1


def test_check_mode_fails_closed_on_stale_output_and_input(tmp_path: Path) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    assert generator.main([*arguments, "--check"]) == 0
    paths["counts"].write_bytes(paths["counts"].read_bytes() + b" ")
    assert generator.main([*arguments, "--check"]) == 1

    assert generator.main(arguments) == 0
    paths["trace_input"].write_bytes(paths["trace_input"].read_bytes() + b" ")
    assert generator.main([*arguments, "--check"]) == 1


def test_trace_artifact_remains_outside_lean_sources() -> None:
    tracked_lean = list((generator.ROOT / "FormalSLT").rglob("*.lean"))
    assert all("trace-v1" not in path.read_text() for path in tracked_lean)
    trace = json.loads(generator.DEFAULT_TRACE_INPUT.read_bytes())
    assert "not Lean-verified trace data" in trace["nonclaims"]
    assert (
        "not a direct deterministic-initial ControlledTrajectory horizon alignment"
        in trace["nonclaims"]
    )
