from __future__ import annotations

import hashlib
import importlib.util
import json
import struct
from copy import deepcopy
from pathlib import Path
from typing import Any, Sequence

import pytest

from scripts import generate_controlled_queue_prospective_trace as generator


ROUND_42_SIGNATURE = (
    "95a9f9f5b231b7714de1553105d8ffdf3dcda24cfdb1e689319bccf79a9c8ce4"
    "30a91b811fbfaf763900bc998b5d686a"
)
ROUND_42_RANDOMNESS = (
    "8ada64bae5c6c0f5540a6a13af56e663240edfbd2c76ac6a8f27671eb7259ce3"
)
ROUND_42_SEED = (
    "5fb136be36676facd9f08dd3b7efc1c12642d14773f6c29bcd8a01e829a1bdf4"
)
ROUND_42_COUNTER_ZERO = (
    "a746f391a82b4fdbcffcdae8e1769f475a663eddbec369976136950619a94017"
)


def _model() -> dict[str, Any]:
    return generator.parse_json_bytes(generator.DEFAULT_MODEL_INPUT.read_bytes(), "model")


def _osf_response(
    *,
    registration_id: str = "abc12",
    date_registered: str = "2026-08-21T12:34:56.000001Z",
) -> dict[str, Any]:
    return {
        "data": {
            "attributes": {
                "date_registered": date_registered,
                "public": True,
                "registration": True,
                "withdrawn": False,
            },
            "id": registration_id,
            "type": "registrations",
        }
    }


def _chain_info() -> dict[str, Any]:
    return {
        "beacon_id": generator.QUICKNET_BEACON_ID,
        "chain_hash": generator.QUICKNET_CHAIN_HASH,
        "genesis_seed": generator.QUICKNET_GROUP_HASH,
        "genesis_time": generator.QUICKNET_GENESIS,
        "period": generator.QUICKNET_PERIOD,
        "public_key": generator.QUICKNET_PUBLIC_KEY,
        "scheme": generator.QUICKNET_SCHEME,
    }


def _round_42() -> dict[str, Any]:
    return {
        "randomness": ROUND_42_RANDOMNESS,
        "round": 42,
        "signature": ROUND_42_SIGNATURE,
    }


def _binding_metadata(
    binding_raw: bytes, *, registration_id: str = "abc12"
) -> dict[str, Any]:
    return {
        "data": {
            "attributes": {
                "current_version": 1,
                "extra": {
                    "hashes": {"sha256": hashlib.sha256(binding_raw).hexdigest()}
                },
                "kind": "file",
                "materialized_path": (
                    "/Archive of OSF Storage/code-freeze-binding-v1.json"
                ),
                "name": "code-freeze-binding-v1.json",
                "size": len(binding_raw),
            },
            "id": "osf-file-id",
            "relationships": {
                "node": {
                    "data": {"id": registration_id, "type": "nodes"},
                },
                "target": {
                    "data": {"id": registration_id, "type": "registrations"},
                    "links": {
                        "related": {
                            "href": f"https://api.osf.io/v2/registrations/{registration_id}/"
                        }
                    },
                },
            },
            "type": "files",
        }
    }


def _fake_code_freeze(
    tmp_path: Path, protocol_raw: bytes
) -> tuple[dict[str, Any], dict[tuple[str, ...], bytes]]:
    protocol_commit = generator.EXPECTED_PROTOCOL_COMMIT
    protocol_tree = generator.EXPECTED_PROTOCOL_TREE
    freeze_commit = "3" * 40
    freeze_tree = "4" * 40
    code_rows = []
    git_results: dict[tuple[str, ...], bytes] = {
        ("cat-file", "-t", protocol_commit): b"commit\n",
        ("show", "-s", "--format=%T", protocol_commit): (
            protocol_tree + "\n"
        ).encode(),
        ("show", f"{protocol_commit}:{generator.PROTOCOL_PATH}"): protocol_raw,
        ("cat-file", "-t", freeze_commit): b"commit\n",
        ("show", "-s", "--format=%T", freeze_commit): (
            freeze_tree + "\n"
        ).encode(),
        ("merge-base", "--is-ancestor", protocol_commit, freeze_commit): b"",
    }
    for index, role in enumerate(generator.CODE_FILE_ROLES):
        path_text = generator.CODE_FILE_PATHS[role]
        raw = f"{role}-frozen-bytes-{index}\n".encode()
        path = tmp_path / path_text
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        code_rows.append(
            {
                "bytes": len(raw),
                "path": path_text,
                "role": role,
                "sha256": hashlib.sha256(raw).hexdigest(),
            }
        )
        git_results[("show", f"{freeze_commit}:{path_text}")] = raw
    binding = {
        "artifact_status": generator.BINDING_STATUS,
        "code_files": code_rows,
        "code_freeze": {"commit": freeze_commit, "tree": freeze_tree},
        "protocol": {
            "bytes": len(protocol_raw),
            "commit": protocol_commit,
            "path": generator.PROTOCOL_PATH,
            "sha256": hashlib.sha256(protocol_raw).hexdigest(),
            "tree": protocol_tree,
        },
        "registration_id": "abc12",
        "schema_version": generator.BINDING_SCHEMA,
    }
    return binding, git_results


def test_protocol_identity_and_declared_paths_are_frozen() -> None:
    assert generator.EXPECTED_PROTOCOL_SHA256
    raw = generator.DEFAULT_PROTOCOL.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == generator.EXPECTED_PROTOCOL_SHA256
    assert generator.EXPECTED_PROTOCOL_COMMIT == (
        "65d8d56245e3862821fce09bcf30b017f03d2baa"
    )
    assert generator.EXPECTED_PROTOCOL_TREE == (
        "8dbe01780fd2cec94b8b954f6ef1c8c210afee53"
    )
    protocol = json.loads(raw)
    assert protocol["schema_version"] == generator.PROTOCOL_SCHEMA
    assert protocol["protocol_version"] == generator.PROTOCOL_VERSION
    assert tuple(protocol["artifact_contract"]["fresh_output_paths"]) == (
        generator.FRESH_OUTPUT_PATHS
    )
    assert protocol["artifact_contract"]["trace_generator_path"] == (
        generator.CODE_FILE_PATHS["trace_generator"]
    )


def test_strict_json_rejects_duplicate_float_nonfinite_and_boolean_integer() -> None:
    with pytest.raises(generator.ProspectiveTraceError, match="duplicate JSON key"):
        generator.parse_json_bytes(b'{"x":1,"x":2}', "duplicate")
    with pytest.raises(generator.ProspectiveTraceError, match="floating-point"):
        generator.parse_json_bytes(b'{"x":1.0}', "float")
    with pytest.raises(generator.ProspectiveTraceError, match="non-finite"):
        generator.parse_json_bytes(b'{"x":NaN}', "nan")
    with pytest.raises(generator.ProspectiveTraceError, match="JSON boolean"):
        generator._integer(True, "integer")


def test_registration_time_ceiling_is_exact_without_float_conversion() -> None:
    assert generator.parse_registration_time("1970-01-01T00:00:00Z")[1] == 0
    assert generator.parse_registration_time("1970-01-01T00:00:00.000Z")[1] == 0
    assert generator.parse_registration_time("1970-01-01T00:00:00.000001Z")[1] == 1
    assert generator.parse_registration_time("1969-12-31T23:59:59.9Z")[1] == 0
    with pytest.raises(generator.ProspectiveTraceError, match="RFC3339"):
        generator.parse_registration_time("2026-08-21T12:34:56+00:00")
    with pytest.raises(generator.ProspectiveTraceError, match="invalid OSF"):
        generator.parse_registration_time("2026-02-30T12:34:56Z")


def test_round_formula_selects_unique_first_eligible_round_for_all_residues() -> None:
    for residue in range(generator.QUICKNET_PERIOD):
        registration_second = generator.QUICKNET_GENESIS + 1_000_000 + residue
        selected = generator.formula_selected_round(registration_second)
        round_time = generator.quicknet_round_time(selected)
        target = registration_second + generator.REGISTRATION_DELAY_SECONDS
        assert round_time >= target
        assert round_time - generator.QUICKNET_PERIOD < target
    with pytest.raises(generator.ProspectiveTraceError, match="JSON boolean"):
        generator.formula_selected_round(True)


def test_prng_and_seed_derivation_vectors_are_frozen() -> None:
    test_seed = hashlib.sha256(generator.PRNG_DOMAIN.encode() + b"/test-seed").digest()
    assert test_seed.hex() == generator.TEST_SEED_HEX
    stream = generator.CounterStream(test_seed)
    assert hashlib.sha256(
        generator.PRNG_DOMAIN.encode()
        + b"\0"
        + test_seed
        + (0).to_bytes(8, "big")
    ).hexdigest() == generator.TEST_COUNTER_ZERO_DIGEST_HEX
    assert [stream.next_u64() for _ in range(4)] == [
        197611467670026578,
        4967088031842859345,
        9634105499622720072,
        15159153303846592970,
    ]

    signature = bytes.fromhex(ROUND_42_SIGNATURE)
    seed = generator.derive_seed(42, signature)
    assert seed.hex() == ROUND_42_SEED
    assert hashlib.sha256(
        generator.PRNG_DOMAIN.encode()
        + b"\0"
        + seed
        + (0).to_bytes(8, "big")
    ).hexdigest() == ROUND_42_COUNTER_ZERO


def test_rejection_sampling_rejects_tail_without_bias() -> None:
    draws = iter([(1 << 64) - 1, 7])
    assert generator.rejection_sample_u64(10, lambda: next(draws)) == (7, 1)
    with pytest.raises(ValueError, match="integer"):
        generator.rejection_sample_u64(True, lambda: 0)
    with pytest.raises(ValueError, match="outside"):
        generator.rejection_sample_u64(2, lambda: True)


def test_short_trace_vector_is_deterministic_and_contains_no_endpoint() -> None:
    seed = bytes.fromhex(generator.TEST_SEED_HEX)
    first_raw, first_counts = generator.generate_trace_bytes_and_counts(
        _model(), seed, horizon=8
    )
    second_raw, second_counts = generator.generate_trace_bytes_and_counts(
        _model(), seed, horizon=8
    )
    assert (first_raw, first_counts) == (second_raw, second_counts)
    assert hashlib.sha256(first_raw).hexdigest() == (
        "acf3d82d7229ae86549566c6d626eecc4846bc8932cca2756024a31865bcdf6b"
    )
    assert hashlib.sha256(generator.canonical_json_bytes(first_counts)).hexdigest() == (
        "c2f2c2e547b0b8a9b2153255b6188a5a0b0ef6bad78f644949621caa9e4d1674"
    )
    magic, horizon, state_count, action_count = generator.BINARY_HEADER.unpack_from(
        first_raw
    )
    assert (magic, horizon, state_count, action_count) == (
        generator.BINARY_MAGIC,
        8,
        9,
        9,
    )
    states = first_raw[generator.BINARY_HEADER.size : generator.BINARY_HEADER.size + 9]
    actions = first_raw[generator.BINARY_HEADER.size + 9 :]
    assert list(states) == [0, 1, 5, 6, 3, 1, 5, 6, 7]
    assert list(actions) == [0, 0, 0, 0, 1, 1, 1, 1, 0]
    assert first_counts["counts"]["persistence_hit_count"] == 6
    assert first_counts["counts"]["persistence_miss_count"] == 2
    assert first_counts["counts"]["transition_action_counts"] == [4, 4]
    serialized = generator.canonical_json_bytes(first_counts).decode()
    for forbidden in (
        "certified_upper_bound",
        "decision_threshold",
        "empirical_corrected_score",
        "posterior",
        "potential",
    ):
        assert forbidden not in serialized


def test_count_tables_conserve_exactly_the_transition_horizon() -> None:
    raw, receipt = generator.generate_trace_bytes_and_counts(
        _model(), bytes.fromhex(generator.TEST_SEED_HEX), horizon=32
    )
    counts = receipt["counts"]
    assert sum(counts["source_state_visits"]) == 32
    assert sum(counts["destination_state_counts"]) == 32
    assert sum(counts["transition_action_counts"]) == 32
    assert sum(map(sum, counts["state_action_counts"])) == 32
    assert sum(
        count
        for state_rows in counts["edge_counts"]
        for action_row in state_rows
        for count in action_row
    ) == 32
    assert counts["persistence_hit_count"] + counts["persistence_miss_count"] == 32
    assert receipt["trace_sha256"] == hashlib.sha256(raw).hexdigest()


def test_osf_registration_requires_public_completed_nonwithdrawn_record() -> None:
    raw = json.dumps(_osf_response(), separators=(",", ":")).encode()
    parsed = generator.parse_osf_registration(raw)
    assert parsed["id"] == "abc12"
    assert parsed["date_registered"] == "2026-08-21T12:34:56.000001Z"

    for field, bad_value, message in (
        ("public", 1, "must be public"),
        ("registration", False, "completed registration"),
        ("withdrawn", True, "must not be withdrawn"),
    ):
        value = _osf_response()
        value["data"]["attributes"][field] = bad_value
        with pytest.raises(generator.ProspectiveTraceError, match=message):
            generator.parse_osf_registration(json.dumps(value).encode())


def test_osf_binding_file_metadata_cross_binds_registration_and_bytes() -> None:
    binding_raw = b'{"binding":"exact bytes"}\n'
    value = _binding_metadata(binding_raw)
    raw = json.dumps(value, separators=(",", ":")).encode()
    parsed = generator.parse_osf_binding_file_metadata(raw, "abc12", binding_raw)
    assert parsed == {
        "current_version": 1,
        "file_id": "osf-file-id",
        "kind": "file",
        "materialized_path": (
            "/Archive of OSF Storage/code-freeze-binding-v1.json"
        ),
        "name": "code-freeze-binding-v1.json",
        "sha256": hashlib.sha256(binding_raw).hexdigest(),
        "size": len(binding_raw),
    }

    tamper_cases = [
        ("data.attributes.size", len(binding_raw) + 1, "attributes.size"),
        ("data.attributes.current_version", True, "JSON boolean"),
        ("data.attributes.kind", "folder", "attributes.kind"),
        (
            "data.attributes.materialized_path",
            "/Archive of OSF Storage/../code-freeze-binding-v1.json",
            "canonical POSIX path",
        ),
        ("data.relationships.node.data.id", "other", "node id"),
        ("data.relationships.target.data.type", "nodes", "target type"),
        (
            "data.relationships.target.links.related.href",
            "https://api.osf.io/v2/registrations/other/",
            "target related href",
        ),
    ]
    for dotted, replacement, message in tamper_cases:
        tampered = deepcopy(value)
        target: Any = tampered
        parts = dotted.split(".")
        for part in parts[:-1]:
            target = target[part]
        target[parts[-1]] = replacement
        with pytest.raises(generator.ProspectiveTraceError, match=message):
            generator.parse_osf_binding_file_metadata(
                json.dumps(tampered).encode(), "abc12", binding_raw
            )


def test_chain_info_and_round_are_exact_and_signature_is_not_trusted() -> None:
    chain_raw = json.dumps(_chain_info(), separators=(",", ":")).encode()
    assert generator.parse_quicknet_chain_info(chain_raw) == _chain_info()
    bad_chain = _chain_info()
    bad_chain["period"] = True
    with pytest.raises(generator.ProspectiveTraceError, match="period"):
        generator.parse_quicknet_chain_info(json.dumps(bad_chain).encode())

    calls: list[tuple[int, bytes, bytes]] = []

    def valid_backend(round_number: int, signature: bytes, public_key: bytes) -> bool:
        calls.append((round_number, signature, public_key))
        return True

    round_raw = json.dumps(_round_42(), separators=(",", ":")).encode()
    value, verification, signature = generator.parse_quicknet_round(
        round_raw, 42, signature_backend=valid_backend
    )
    assert value == _round_42()
    assert signature == bytes.fromhex(ROUND_42_SIGNATURE)
    assert verification["version"] == generator.PY_ECC_VERSION
    assert calls == [
        (42, bytes.fromhex(ROUND_42_SIGNATURE), bytes.fromhex(generator.QUICKNET_PUBLIC_KEY))
    ]

    bad_randomness = _round_42()
    bad_randomness["randomness"] = "0" * 64
    with pytest.raises(generator.ProspectiveTraceError, match="randomness"):
        generator.parse_quicknet_round(
            json.dumps(bad_randomness).encode(),
            42,
            signature_backend=valid_backend,
        )
    with pytest.raises(generator.ProspectiveTraceError, match="BLS signature is invalid"):
        generator.parse_quicknet_round(
            round_raw,
            42,
            signature_backend=lambda _round, _sig, _pk: False,
        )
    with pytest.raises(generator.ProspectiveTraceError, match="JSON boolean"):
        bad_round = _round_42()
        bad_round["round"] = True
        generator.parse_quicknet_round(
            json.dumps(bad_round).encode(),
            42,
            signature_backend=valid_backend,
        )


@pytest.mark.skipif(
    importlib.util.find_spec("py_ecc") is None,
    reason="pinned py-ecc is intentionally optional until execution environment freeze",
)
def test_actual_py_ecc_accepts_official_quicknet_vector_and_rejects_tamper() -> None:
    descriptor = generator.verify_quicknet_signature(
        42, ROUND_42_SIGNATURE, generator.QUICKNET_PUBLIC_KEY
    )
    assert descriptor == {
        "dependency": "py-ecc",
        "dst": "BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_",
        "implementation": "py_ecc_low_level_rfc9380",
        "version": "8.0.0",
    }
    with pytest.raises(generator.ProspectiveTraceError, match="invalid"):
        generator.verify_quicknet_signature(
            43, ROUND_42_SIGNATURE, generator.QUICKNET_PUBLIC_KEY
        )


def test_missing_pinned_bls_dependency_fails_closed() -> None:
    if importlib.util.find_spec("py_ecc") is not None:
        pytest.skip("py-ecc is installed; official-vector test covers the backend")
    with pytest.raises(generator.ProspectiveTraceError, match="py-ecc==8.0.0"):
        generator.verify_quicknet_signature(
            42, ROUND_42_SIGNATURE, generator.QUICKNET_PUBLIC_KEY
        )


def test_canonical_osf_binding_proves_git_objects_and_all_four_code_files(
    tmp_path: Path,
) -> None:
    protocol_raw = b'{"protocol":"frozen"}\n'
    binding, git_results = _fake_code_freeze(tmp_path, protocol_raw)
    raw = generator.canonical_json_bytes(binding)

    def fake_git(arguments: Sequence[str]) -> bytes:
        return git_results[tuple(arguments)]

    parsed, code_files = generator.validate_osf_binding(
        raw,
        "abc12",
        protocol_raw,
        root=tmp_path,
        git_runner=fake_git,
    )
    assert parsed == binding
    assert tuple(code_files) == generator.CODE_FILE_ROLES

    with pytest.raises(generator.ProspectiveTraceError, match="canonical JSON"):
        generator.validate_osf_binding(
            raw + b"\n",
            "abc12",
            protocol_raw,
            root=tmp_path,
            git_runner=fake_git,
        )

    boolean_binding = deepcopy(binding)
    boolean_binding["code_files"][0]["bytes"] = True
    with pytest.raises(generator.ProspectiveTraceError, match="JSON booleans"):
        generator.validate_osf_binding(
            generator.canonical_json_bytes(boolean_binding),
            "abc12",
            protocol_raw,
            root=tmp_path,
            git_runner=fake_git,
        )

    wrong_git = dict(git_results)
    wrong_git[("show", "-s", "--format=%T", "3" * 40)] = ("5" * 40 + "\n").encode()
    with pytest.raises(generator.ProspectiveTraceError, match="code-freeze Git tree"):
        generator.validate_osf_binding(
            raw,
            "abc12",
            protocol_raw,
            root=tmp_path,
            git_runner=lambda args: wrong_git[tuple(args)],
        )

    first_role = generator.CODE_FILE_ROLES[0]
    (tmp_path / generator.CODE_FILE_PATHS[first_role]).write_bytes(b"working tree drift")
    with pytest.raises(generator.ProspectiveTraceError, match=f"{first_role}.bytes"):
        generator.validate_osf_binding(
            raw,
            "abc12",
            protocol_raw,
            root=tmp_path,
            git_runner=fake_git,
        )


@pytest.mark.parametrize(
    ("left_name", "right_name"),
    [("Bundle.json", "bundle.json"), ("é.json", "e\u0301.json")],
)
def test_path_identity_rejects_casefold_and_nfc_aliases(
    tmp_path: Path, left_name: str, right_name: str
) -> None:
    inputs = {"input": tmp_path / "input.json"}
    outputs = {
        "trace": tmp_path / left_name,
        "manifest": tmp_path / right_name,
    }
    with pytest.raises(generator.ProspectiveTraceError, match="output paths must be distinct"):
        generator._validate_artifact_paths(inputs, outputs)


def test_frozen_input_path_rejects_case_variant_even_when_bytes_match(
    tmp_path: Path,
) -> None:
    expected = tmp_path / "Frozen.json"
    variant = tmp_path / "frozen.json"
    expected.write_bytes(b"same")
    variant.write_bytes(b"same")
    with pytest.raises(generator.ProspectiveTraceError, match="frozen repository path"):
        generator._require_exact_path(variant, expected, "input")


@pytest.mark.parametrize("symlink_role", ["input", "output", "protected"])
def test_artifact_paths_reject_symlink_components(
    tmp_path: Path, symlink_role: str
) -> None:
    real = tmp_path / "real"
    real.mkdir()
    linked = tmp_path / "linked"
    linked.symlink_to(real, target_is_directory=True)
    inputs = {
        "input": linked / "input.json"
        if symlink_role == "input"
        else tmp_path / "input.json"
    }
    outputs = {
        "trace": linked / "trace.bin"
        if symlink_role == "output"
        else tmp_path / "trace.bin"
    }
    protected = {
        "generator": linked / "generator.py"
        if symlink_role == "protected"
        else tmp_path / "generator.py"
    }
    with pytest.raises(generator.ProspectiveTraceError, match="symbolic-link component"):
        generator._validate_artifact_paths(inputs, outputs, protected=protected)


def test_artifact_paths_reject_broken_output_symlink(tmp_path: Path) -> None:
    output = tmp_path / "trace.bin"
    output.symlink_to(tmp_path / "missing.bin")
    with pytest.raises(generator.ProspectiveTraceError, match="symbolic-link component"):
        generator._validate_artifact_paths(
            {"input": tmp_path / "input.json"}, {"trace": output}
        )


def test_output_cannot_alias_input_and_writes_are_manifest_last(tmp_path: Path) -> None:
    same = tmp_path / "same.json"
    with pytest.raises(generator.ProspectiveTraceError, match="aliases protected input"):
        generator._validate_artifact_paths(
            {"input": same},
            {"trace": same, "manifest": tmp_path / "manifest.json"},
        )

    writes: list[tuple[Path, bytes]] = []
    paths = [tmp_path / "trace.bin", tmp_path / "counts.json", tmp_path / "manifest.json"]
    generator.write_artifacts_manifest_last(
        paths[0],
        b"trace",
        paths[1],
        b"counts",
        paths[2],
        b"manifest",
        writer=lambda path, raw: writes.append((path, raw)),
    )
    assert writes == list(zip(paths, (b"trace", b"counts", b"manifest"), strict=True))


def test_atomic_writer_is_exclusive_and_preserves_complete_bytes(tmp_path: Path) -> None:
    path = tmp_path / "artifact.bin"
    generator._write_atomic(path, b"new complete bytes")
    assert path.read_bytes() == b"new complete bytes"
    with pytest.raises(generator.ProspectiveTraceError, match="refusing to overwrite"):
        generator._write_atomic(path, b"replacement")
    assert path.read_bytes() == b"new complete bytes"
    assert not list(tmp_path.glob(f".{path.name}.*"))


def test_manifest_schema_binds_every_input_code_file_and_output(tmp_path: Path) -> None:
    input_roles = (
        "protocol",
        "osf_registration_response",
        "osf_registration_binding",
        "osf_registration_binding_file",
        "quicknet_chain_info",
        "quicknet_round",
        "model_input",
        "model_manifest",
        "model_tables",
    )
    input_files = {
        role: (tmp_path / f"{role}.json", f"{role}\n".encode())
        for role in input_roles
    }
    code_files = {
        role: (tmp_path / f"{role}.py", f"{role}\n".encode())
        for role in generator.CODE_FILE_ROLES
    }
    registration = {
        "date_registered": "2026-08-21T12:34:56Z",
        "id": "abc12",
        "unix_seconds_ceiling": 1_755_779_696,
    }
    binding = {
        "code_freeze": {"commit": "3" * 40, "tree": "4" * 40},
        "protocol": {"commit": "1" * 40, "tree": "2" * 40},
    }
    round_value = _round_42()
    manifest = generator.build_manifest(
        registration=registration,
        registration_raw=input_files["osf_registration_response"][1],
        binding=binding,
        binding_raw=input_files["osf_registration_binding"][1],
        binding_file_metadata_raw=input_files["osf_registration_binding_file"][1],
        chain_raw=input_files["quicknet_chain_info"][1],
        round_value=round_value,
        round_raw=input_files["quicknet_round"][1],
        verification={
            "dependency": "py-ecc",
            "dst": generator.QUICKNET_DST.decode(),
            "implementation": generator.PY_ECC_IMPLEMENTATION,
            "version": generator.PY_ECC_VERSION,
        },
        seed=bytes.fromhex(ROUND_42_SEED),
        input_files=input_files,
        code_files=code_files,
        trace_path=tmp_path / "trace.bin",
        trace_raw=b"trace",
        counts_path=tmp_path / "counts.json",
        counts_raw=b"counts",
    )
    assert manifest["schema_version"] == generator.MANIFEST_SCHEMA
    assert [row["role"] for row in manifest["inputs"]] == list(input_roles)
    assert [row["role"] for row in manifest["outputs"]] == [
        "trace_binary",
        "trace_counts",
    ]
    assert [row["role"] for row in manifest["code_freeze"]["code_files"]] == list(
        generator.CODE_FILE_ROLES
    )
    assert manifest["beacon"]["signature_verified"] is True
    assert manifest["registration"]["binding_file_api_response_sha256"] == (
        hashlib.sha256(input_files["osf_registration_binding_file"][1]).hexdigest()
    )


def test_default_check_is_read_only_and_no_prospective_output_exists(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[tuple[Path, bytes]] = []
    monkeypatch.setattr(
        generator,
        "_write_atomic",
        lambda path, raw: calls.append((path, raw)),
    )
    before = {
        path_text: (generator.ROOT / path_text).exists()
        for path_text in generator.FRESH_OUTPUT_PATHS
    }
    assert generator.main(["--check"]) != 0
    after = {
        path_text: (generator.ROOT / path_text).exists()
        for path_text in generator.FRESH_OUTPUT_PATHS
    }
    assert calls == []
    assert before == after
    assert not any(after.values())


def test_generator_has_no_network_client_or_generator_import() -> None:
    source = Path(generator.__file__).read_text()
    for forbidden in (
        "import requests",
        "import urllib",
        "import socket",
        "urlopen(",
        "requests.get(",
        "curl ",
        "generate_controlled_queue_trace as",
    ):
        assert forbidden not in source
