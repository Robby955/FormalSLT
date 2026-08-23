from __future__ import annotations

import hashlib
import json
import struct
from fractions import Fraction
from pathlib import Path

import pytest

from scripts import generate_controlled_queue_known_kernel_receipt as generator
from scripts import verify_controlled_queue_known_kernel_receipt as verifier


def _check_arguments(input_path: Path) -> list[str]:
    return [
        "--input",
        str(input_path),
        "--receipt",
        str(generator.DEFAULT_RECEIPT),
        "--manifest",
        str(generator.DEFAULT_MANIFEST),
        "--lean",
        str(generator.DEFAULT_LEAN),
        "--check",
    ]


def _temp_arguments(tmp_path: Path) -> tuple[list[str], dict[str, Path]]:
    paths = {
        "receipt": tmp_path / "known-kernel-receipt-v1.json",
        "manifest": tmp_path / "known-kernel-receipt-v1-manifest.json",
        "lean": tmp_path / "ControlledQueueKnownKernelReceiptData.lean",
    }
    arguments = [
        "--input",
        str(generator.DEFAULT_INPUT),
        "--receipt",
        str(paths["receipt"]),
        "--manifest",
        str(paths["manifest"]),
        "--lean",
        str(paths["lean"]),
    ]
    return arguments, paths


def _isolated_provenance_arguments(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[list[str], Path, Path]:
    source_root = generator.ROOT
    repo_root = tmp_path / "repo"
    spec = json.loads(generator.DEFAULT_INPUT.read_bytes())
    relative_paths = {
        binding["path"] for binding in spec["bindings"].values()
    } | {
        generator.MODEL_LEAN_PATH,
        generator.MODEL_GENERATOR_PATH,
        generator.TRACE_GENERATOR_PATH,
        generator.TRACE_VERIFIER_PATH,
    }
    for relative_path in sorted(relative_paths):
        source = source_root / relative_path
        destination = repo_root / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())

    input_path = repo_root / "applications/controlled_queue/known-kernel-receipt-v1.json"
    input_path.parent.mkdir(parents=True, exist_ok=True)
    input_path.write_bytes(generator.DEFAULT_INPUT.read_bytes())
    monkeypatch.setattr(generator, "ROOT", repo_root)
    monkeypatch.setattr(verifier, "ROOT", repo_root)

    output_root = tmp_path / "outputs"
    arguments = [
        "--input",
        str(input_path),
        "--receipt",
        str(output_root / "known-kernel-receipt-v1.json"),
        "--manifest",
        str(output_root / "known-kernel-receipt-v1-manifest.json"),
        "--lean",
        str(output_root / "ControlledQueueKnownKernelReceiptData.lean"),
    ]
    return arguments, repo_root, input_path


def _mutated_input(case: str) -> bytes:
    raw = generator.DEFAULT_INPUT.read_bytes()
    if case == "duplicate_key":
        line = (
            b'  "artifact_status": '
            b'"DETERMINISTIC KNOWN-KERNEL RECEIPT INPUT",\n'
        )
        assert raw.count(line) == 1
        return raw.replace(line, line + line, 1)
    if case == "float":
        old = b'"depth": 12'
        assert raw.count(old) == 1
        return raw.replace(old, b'"depth": 12.0', 1)
    if case == "boolean_for_integer":
        spec = json.loads(raw)
        spec["selection"]["target_policy_index"] = True
        return generator.canonical_json_bytes(spec)
    if case == "noncanonical_rational":
        spec = json.loads(raw)
        value = Fraction(spec["expected_receipt"]["score_sum"])
        spec["expected_receipt"]["score_sum"] = (
            f"{2 * value.numerator}/{2 * value.denominator}"
        )
        return generator.canonical_json_bytes(spec)
    if case == "unknown_field":
        spec = json.loads(raw)
        spec["unexpected"] = "must fail closed"
        return generator.canonical_json_bytes(spec)
    if case == "extra_whitespace":
        return raw + b"\n"
    if case == "negative_zero":
        old = b'"anchor_state": 0'
        assert raw.count(old) == 1
        return raw.replace(old, b'"anchor_state": -0', 1)
    if case == "nonclaim_drift":
        spec = json.loads(raw)
        spec["nonclaims"] = ["schema drift must fail closed"]
        return generator.canonical_json_bytes(spec)
    raise AssertionError(f"unknown mutation case: {case}")


def _decode_trace(raw: bytes, horizon: int) -> tuple[bytes, bytes]:
    magic, stored_horizon = generator.TRACE_HEADER.unpack_from(raw)
    assert magic == generator.TRACE_MAGIC
    assert stored_horizon == horizon
    offset = generator.TRACE_HEADER.size
    states = raw[offset : offset + horizon + 1]
    offset += horizon + 1
    actions = raw[offset : offset + horizon]
    assert len(states) == horizon + 1
    assert len(actions) == horizon
    return states, actions


def _histogram(
    states: bytes, actions: bytes, start: int, stop: int
) -> list[list[list[int]]]:
    result = [
        [
            [0 for _destination in range(generator.STATE_COUNT)]
            for _action in range(generator.ACTION_COUNT)
        ]
        for _state in range(generator.STATE_COUNT)
    ]
    for time in range(start, stop):
        result[states[time]][actions[time]][states[time + 1]] += 1
    return result


def _histogram_sha256(histogram: list[list[list[int]]]) -> str:
    encoded = b"".join(
        struct.pack(">Q", histogram[state][action][destination])
        for state in range(generator.STATE_COUNT)
        for action in range(generator.ACTION_COUNT)
        for destination in range(generator.STATE_COUNT)
    )
    return hashlib.sha256(encoded).hexdigest()


def _moments(
    histogram: list[list[list[int]]],
    scores: list[list[list[Fraction]]],
) -> tuple[Fraction, Fraction]:
    score_sum = sum(
        (
            histogram[state][action][destination]
            * scores[state][action][destination]
            for state in range(generator.STATE_COUNT)
            for action in range(generator.ACTION_COUNT)
            for destination in range(generator.STATE_COUNT)
        ),
        Fraction(0),
    )
    square_sum = sum(
        (
            histogram[state][action][destination]
            * scores[state][action][destination] ** 2
            for state in range(generator.STATE_COUNT)
            for action in range(generator.ACTION_COUNT)
            for destination in range(generator.STATE_COUNT)
        ),
        Fraction(0),
    )
    return score_sum, square_sum


def test_generator_check_accepts_canonical_tracked_artifacts() -> None:
    assert generator.main(["--check"]) == 0


def test_independent_verifier_check_accepts_canonical_tracked_artifacts() -> None:
    assert verifier.main(["--check"]) == 0
    assert (
        "import generate_controlled_queue_known_kernel_receipt"
        not in Path(verifier.__file__).read_text()
    )


def test_independent_verifier_accepts_custom_generated_output_paths(
    tmp_path: Path,
) -> None:
    arguments, _paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    assert verifier.main([*arguments, "--check"]) == 0


def test_custom_output_manifest_distinguishes_same_basename_paths(
    tmp_path: Path,
) -> None:
    receipt_path = tmp_path / "receipt" / "artifact"
    manifest_path = tmp_path / "manifest" / "manifest.json"
    lean_path = tmp_path / "lean" / "artifact"
    arguments = [
        "--input",
        str(generator.DEFAULT_INPUT),
        "--receipt",
        str(receipt_path),
        "--manifest",
        str(manifest_path),
        "--lean",
        str(lean_path),
    ]
    assert generator.main(arguments) == 0
    manifest = json.loads(manifest_path.read_bytes())
    output_paths = {row["role"]: row["path"] for row in manifest["outputs"]}
    assert output_paths["receipt"] != output_paths["lean_data"]
    assert output_paths["receipt"] == receipt_path.resolve().as_posix()
    assert output_paths["lean_data"] == lean_path.resolve().as_posix()
    assert verifier.main([*arguments, "--check"]) == 0


@pytest.mark.parametrize(
    ("case", "generator_message", "verifier_message"),
    [
        ("duplicate_key", "duplicate JSON key", "duplicate JSON key"),
        (
            "float",
            "floating-point JSON numbers are forbidden",
            "floating-point JSON numbers are forbidden",
        ),
        (
            "boolean_for_integer",
            "JSON booleans are forbidden",
            "JSON booleans are forbidden",
        ),
        (
            "noncanonical_rational",
            "noncanonical rational",
            "canonical rational",
        ),
        ("unknown_field", "keys mismatch", "keys mismatch"),
        (
            "extra_whitespace",
            "canonical JSON bytes",
            "canonical receipt input",
        ),
        (
            "negative_zero",
            "canonical JSON bytes",
            "canonical receipt input",
        ),
        ("nonclaim_drift", "nonclaims", "nonclaims"),
    ],
)
def test_generator_and_verifier_reject_noncanonical_input(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    case: str,
    generator_message: str,
    verifier_message: str,
) -> None:
    input_path = tmp_path / "known-kernel-receipt-v1.json"
    input_path.write_bytes(_mutated_input(case))
    arguments = _check_arguments(input_path)

    assert generator.main(arguments) == 1
    assert generator_message in capsys.readouterr().err

    assert verifier.main(arguments) == 1
    assert verifier_message in capsys.readouterr().err


def test_generator_and_verifier_reject_source_hash_drift(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    spec = json.loads(generator.DEFAULT_INPUT.read_bytes())
    spec["bindings"]["trace_binary"]["sha256"] = "0" * 64
    input_path = tmp_path / "known-kernel-receipt-v1.json"
    input_path.write_bytes(generator.canonical_json_bytes(spec))
    arguments = _check_arguments(input_path)

    assert generator.main(arguments) == 1
    generator_error = capsys.readouterr().err
    assert "trace_binary" in generator_error
    assert "sha256" in generator_error

    assert verifier.main(arguments) == 1
    verifier_error = capsys.readouterr().err
    assert "trace_binary" in verifier_error
    assert "sha256" in verifier_error


def test_generator_and_verifier_reject_cross_binding_provenance_mutations(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    arguments, repo_root, input_path = _isolated_provenance_arguments(
        tmp_path, monkeypatch
    )
    assert generator.main(arguments) == 0
    capsys.readouterr()

    base_input_raw = input_path.read_bytes()
    trace_manifest_path = repo_root / generator.EXPECTED_BINDING_PATHS["trace_manifest"]
    base_trace_manifest_raw = trace_manifest_path.read_bytes()
    model_tables_path = repo_root / generator.EXPECTED_BINDING_PATHS["model_tables"]
    copied_tables_relative = (
        "applications/controlled_queue/generated/model-v1-tables-copy.json"
    )
    copied_tables_path = repo_root / copied_tables_relative
    copied_tables_path.write_bytes(model_tables_path.read_bytes())

    for case, expected_terms in (
        ("trace_role_swap", ("trace manifest", "raw_trace_output")),
        ("unrelated_model_manifest", ("bindings.model_manifest", "trace-v1-manifest")),
        ("copied_model_tables_binding", ("bindings.model_tables", "model-v1-tables")),
        ("trace_model_dependency", ("trace manifest", "model-generator dependency")),
    ):
        input_path.write_bytes(base_input_raw)
        trace_manifest_path.write_bytes(base_trace_manifest_raw)
        spec = json.loads(base_input_raw)

        if case == "trace_role_swap":
            trace_manifest = json.loads(base_trace_manifest_raw)
            raw_trace_row = next(
                row
                for row in trace_manifest["files"]
                if row["role"] == "raw_trace_output"
            )
            counts_row = next(
                row
                for row in trace_manifest["files"]
                if row["role"] == "counts_output"
            )
            raw_trace_row["role"], counts_row["role"] = (
                counts_row["role"],
                raw_trace_row["role"],
            )
            trace_manifest_raw = generator.canonical_json_bytes(trace_manifest)
            trace_manifest_path.write_bytes(trace_manifest_raw)
            spec["bindings"]["trace_manifest"]["sha256"] = hashlib.sha256(
                trace_manifest_raw
            ).hexdigest()
        elif case == "unrelated_model_manifest":
            spec["bindings"]["model_manifest"] = dict(
                spec["bindings"]["trace_manifest"]
            )
        elif case == "copied_model_tables_binding":
            spec["bindings"]["model_tables"] = {
                "path": copied_tables_relative,
                "sha256": hashlib.sha256(copied_tables_path.read_bytes()).hexdigest(),
            }
        elif case == "trace_model_dependency":
            trace_manifest = json.loads(base_trace_manifest_raw)
            trace_generator = trace_manifest["generator"]
            trace_manifest["generator_dependencies"] = [
                {
                    "path": trace_generator["path"],
                    "sha256": trace_generator["sha256"],
                }
            ]
            trace_manifest_raw = generator.canonical_json_bytes(trace_manifest)
            trace_manifest_path.write_bytes(trace_manifest_raw)
            spec["bindings"]["trace_manifest"]["sha256"] = hashlib.sha256(
                trace_manifest_raw
            ).hexdigest()
        else:
            raise AssertionError(f"unknown provenance mutation: {case}")

        input_path.write_bytes(generator.canonical_json_bytes(spec))
        assert generator.main([*arguments, "--check"]) == 1
        generator_error = capsys.readouterr().err
        assert all(term in generator_error for term in expected_terms)

        assert verifier.main([*arguments, "--check"]) == 1
        verifier_error = capsys.readouterr().err
        assert all(term in verifier_error for term in expected_terms)


def test_independent_verifier_rejects_unknown_receipt_field_with_matching_manifest(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    capsys.readouterr()

    receipt = json.loads(paths["receipt"].read_bytes())
    receipt["unexpected"] = "must fail closed"
    receipt_raw = generator.canonical_json_bytes(receipt)
    paths["receipt"].write_bytes(receipt_raw)

    manifest = json.loads(paths["manifest"].read_bytes())
    receipt_row = next(
        row for row in manifest["outputs"] if row["role"] == "receipt"
    )
    receipt_row["bytes"] = len(receipt_raw)
    receipt_row["sha256"] = hashlib.sha256(receipt_raw).hexdigest()
    paths["manifest"].write_bytes(generator.canonical_json_bytes(manifest))

    assert verifier.main([*arguments, "--check"]) == 1
    assert "receipt keys mismatch" in capsys.readouterr().err


def test_independent_verifier_rejects_boolean_forged_receipt_and_lean(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    capsys.readouterr()

    receipt = json.loads(paths["receipt"].read_bytes())
    receipt["selection"]["target_policy_index"] = True
    receipt_raw = generator.canonical_json_bytes(receipt)
    paths["receipt"].write_bytes(receipt_raw)

    lean_raw = paths["lean"].read_bytes()
    old = b"def selectedTargetIndex : Nat := 1"
    assert lean_raw.count(old) == 1
    lean_raw = lean_raw.replace(old, b"def selectedTargetIndex : Nat := True", 1)
    paths["lean"].write_bytes(lean_raw)

    manifest = json.loads(paths["manifest"].read_bytes())
    by_role = {row["role"]: row for row in manifest["outputs"]}
    by_role["receipt"]["bytes"] = len(receipt_raw)
    by_role["receipt"]["sha256"] = hashlib.sha256(receipt_raw).hexdigest()
    by_role["lean_data"]["bytes"] = len(lean_raw)
    by_role["lean_data"]["sha256"] = hashlib.sha256(lean_raw).hexdigest()
    paths["manifest"].write_bytes(generator.canonical_json_bytes(manifest))

    assert verifier.main([*arguments, "--check"]) == 1
    assert "JSON booleans are forbidden" in capsys.readouterr().err


def test_independent_verifier_rejects_integer_in_boolean_receipt_field(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    capsys.readouterr()

    receipt = json.loads(paths["receipt"].read_bytes())
    receipt["trace_alignment"]["off_by_one_histogram_is_distinct"] = 1
    receipt_raw = generator.canonical_json_bytes(receipt)
    paths["receipt"].write_bytes(receipt_raw)

    manifest = json.loads(paths["manifest"].read_bytes())
    receipt_row = next(
        row for row in manifest["outputs"] if row["role"] == "receipt"
    )
    receipt_row["bytes"] = len(receipt_raw)
    receipt_row["sha256"] = hashlib.sha256(receipt_raw).hexdigest()
    paths["manifest"].write_bytes(generator.canonical_json_bytes(manifest))

    assert verifier.main([*arguments, "--check"]) == 1
    assert "must be a JSON boolean" in capsys.readouterr().err


@pytest.mark.parametrize("artifact", ["receipt", "manifest", "lean"])
def test_generator_check_rejects_stale_generated_bytes(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    artifact: str,
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    assert generator.main(arguments) == 0
    capsys.readouterr()

    paths[artifact].write_bytes(paths[artifact].read_bytes() + b"\n")
    assert generator.main([*arguments, "--check"]) == 1
    assert "stale generated artifact" in capsys.readouterr().err


@pytest.mark.parametrize(
    "alias_pair",
    [("receipt", "manifest"), ("receipt", "lean"), ("manifest", "lean")],
)
def test_generator_rejects_aliased_output_paths_before_writing(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    alias_pair: tuple[str, str],
) -> None:
    arguments, paths = _temp_arguments(tmp_path)
    paths[alias_pair[1]] = paths[alias_pair[0]]
    arguments = [
        "--input",
        str(generator.DEFAULT_INPUT),
        "--receipt",
        str(paths["receipt"]),
        "--manifest",
        str(paths["manifest"]),
        "--lean",
        str(paths["lean"]),
    ]
    assert generator.main(arguments) == 1
    assert "output paths must be distinct" in capsys.readouterr().err
    assert not paths[alias_pair[0]].exists()


def test_generator_rejects_input_output_alias_before_writing(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    input_path = tmp_path / "known-kernel-receipt-v1.json"
    original = generator.DEFAULT_INPUT.read_bytes()
    input_path.write_bytes(original)
    arguments = [
        "--input",
        str(input_path),
        "--receipt",
        str(input_path),
        "--manifest",
        str(tmp_path / "manifest.json"),
        "--lean",
        str(tmp_path / "Data.lean"),
    ]
    assert generator.main(arguments) == 1
    assert "output path aliases protected input" in capsys.readouterr().err
    assert input_path.read_bytes() == original


@pytest.mark.parametrize(
    ("left_name", "right_name"),
    [("Bundle.json", "bundle.json"), ("é.json", "e\u0301.json")],
)
def test_generator_rejects_case_or_unicode_normalized_output_aliases(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    left_name: str,
    right_name: str,
) -> None:
    receipt_path = tmp_path / left_name
    manifest_path = tmp_path / right_name
    arguments = [
        "--input",
        str(generator.DEFAULT_INPUT),
        "--receipt",
        str(receipt_path),
        "--manifest",
        str(manifest_path),
        "--lean",
        str(tmp_path / "Data.lean"),
    ]
    assert generator.main(arguments) == 1
    assert "output paths must be distinct" in capsys.readouterr().err
    assert not receipt_path.exists()
    assert not manifest_path.exists()


def test_suffix_histogram_hash_prevents_equal_moment_off_by_one_substitution() -> None:
    spec = json.loads(generator.DEFAULT_INPUT.read_bytes())
    receipt = json.loads(generator.DEFAULT_RECEIPT.read_bytes())
    trace_path = generator.ROOT / spec["bindings"]["trace_binary"]["path"]
    tables_path = generator.ROOT / spec["bindings"]["model_tables"]["path"]
    tables = json.loads(tables_path.read_bytes())
    horizon = spec["trace_alignment"]["source_horizon"]
    states, actions = _decode_trace(trace_path.read_bytes(), horizon)

    suffix = _histogram(states, actions, 1, horizon)
    wrong_prefix = _histogram(states, actions, 0, horizon - 1)
    assert sum(count for rows in suffix for row in rows for count in row) == 199999
    assert sum(count for rows in wrong_prefix for row in rows for count in row) == 199999

    differences = {
        (state, action, destination): (
            suffix[state][action][destination]
            - wrong_prefix[state][action][destination]
        )
        for state in range(generator.STATE_COUNT)
        for action in range(generator.ACTION_COUNT)
        for destination in range(generator.STATE_COUNT)
        if suffix[state][action][destination]
        != wrong_prefix[state][action][destination]
    }
    assert differences == {(0, 1, 1): -1, (6, 1, 1): 1}

    suffix_hash = _histogram_sha256(suffix)
    wrong_prefix_hash = _histogram_sha256(wrong_prefix)
    assert suffix_hash == "2a484e76850d41fa40e16bdb988bb24131a355800e503e283a26ad22b9d8a874"
    assert wrong_prefix_hash == "1f29382a3b672ea83c66fc9f7bc910c0097c3fb974286a2959395fa041cb65bb"
    assert suffix_hash != wrong_prefix_hash
    assert suffix_hash == spec["edge_histogram_contract"]["sha256"]
    assert suffix_hash == receipt["trace_alignment"]["suffix_edge_histogram_sha256"]
    assert wrong_prefix_hash == receipt["trace_alignment"]["off_by_one_edge_histogram_sha256"]
    assert suffix == receipt["trace_alignment"]["suffix_edge_histogram"]

    policy = next(
        row
        for row in tables["policies"]
        if row["id"] == receipt["selection"]["target_policy_id"]
    )
    brier = next(
        row
        for row in tables["fixed_brier_loss"]
        if row["id"] == receipt["selection"]["predictor_id"]
    )
    potential = [Fraction(value) for value in receipt["potential_receipt"]["values"]]
    span = Fraction(receipt["potential_receipt"]["span"])
    scale = Fraction(receipt["potential_receipt"]["normalized_scale"])
    scores = [
        [
            [
                (
                    Fraction(policy["rows"][state]["probabilities"][action])
                    / Fraction(1, 2)
                )
                * (
                    Fraction(brier["rows"][2 * state + action]["losses"][destination])
                    + potential[destination]
                    - potential[state]
                    + span
                )
                / scale
                for destination in range(generator.STATE_COUNT)
            ]
            for action in range(generator.ACTION_COUNT)
        ]
        for state in range(generator.STATE_COUNT)
    ]
    assert scores[0][1][1] == scores[6][1][1]

    expected_moments = (
        Fraction(receipt["score_receipt"]["sum"]),
        Fraction(receipt["score_receipt"]["sum_squares"]),
    )
    assert _moments(suffix, scores) == expected_moments
    assert _moments(wrong_prefix, scores) == expected_moments
