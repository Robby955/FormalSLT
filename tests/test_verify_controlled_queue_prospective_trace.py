from __future__ import annotations

import ast
import calendar
import hashlib
import json
import shutil
import struct
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Any

import pytest

from scripts import verify_controlled_queue_prospective_trace as verifier


TEST_REGISTRATION_ID = "abc12"
TEST_DATE_REGISTERED = "2026-08-21T20:00:00.125Z"
TEST_SIGNATURE = bytes(range(48))
CODE_FREEZE_COMMIT = "1" * 40
CODE_FREEZE_TREE = "2" * 40


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


class FixtureStream:
    """Test-only reconstruction of the frozen stream, with no project imports."""

    def __init__(self, seed: bytes) -> None:
        self.prefix = (
            b"FormalSLT/controlled-queue/prospective-structured-ope-v1\0" + seed
        )
        self.counter = 0
        self.buffer = b""
        self.words = 0
        self.blocks = 0
        self.rejections: dict[int, int] = {}

    def word(self) -> int:
        if len(self.buffer) < 8:
            self.buffer += hashlib.sha256(
                self.prefix + self.counter.to_bytes(8, "big")
            ).digest()
            self.counter += 1
            self.blocks += 1
        result = int.from_bytes(self.buffer[:8], "big")
        self.buffer = self.buffer[8:]
        self.words += 1
        return result

    def below(self, modulus: int) -> int:
        space = 1 << 64
        limit = space - space % modulus
        rejected = 0
        while True:
            value = self.word()
            if value < limit:
                if rejected:
                    self.rejections[modulus] = self.rejections.get(modulus, 0) + rejected
                return value % modulus
            rejected += 1


def _fixture_registration_second() -> int:
    base = calendar.timegm(datetime(2026, 8, 21, 20, 0, 0).timetuple())
    return base + 1


def _fixture_round() -> tuple[int, int]:
    second = _fixture_registration_second()
    numerator = second + 3600 - 1_692_803_367
    number = 1 + (-(-numerator // 3))
    return number, 1_692_803_367 + (number - 1) * 3


def _queue_step(state: int, action: int) -> int:
    queue, regime = divmod(state, 3)
    service = (1, 2)[action]
    arrival = (0, 1, 2)[regime]
    return 3 * min(7, max(0, queue - service) + arrival) + (regime + 1) % 3


def _destination(draw: int, step: int) -> int:
    cumulative = 0
    for destination in range(24):
        cumulative += 1209 if destination == step else 17
        if draw < cumulative:
            return destination
    raise AssertionError("test categorical draw escaped its weights")


def _build_trace(seed: bytes) -> tuple[bytes, dict[str, Any], dict[str, Any], int, int]:
    stream = FixtureStream(seed)
    states = bytearray([0])
    actions = bytearray([0])
    source_visits = [0] * 24
    destination_counts = [0] * 24
    transition_action_counts = [0, 0]
    state_action_counts = [[0, 0] for _ in range(24)]
    edge_counts = [[[0] * 24 for _ in range(2)] for _ in range(24)]
    persistence_hits = 0

    for _time in range(200_000):
        state = states[-1]
        action = stream.below(2)
        step = _queue_step(state, action)
        destination = _destination(stream.below(1600), step)
        actions.append(action)
        states.append(destination)
        source_visits[state] += 1
        destination_counts[destination] += 1
        transition_action_counts[action] += 1
        state_action_counts[state][action] += 1
        edge_counts[state][action][destination] += 1
        persistence_hits += int(destination == step)

    raw = (
        b"FSLTCQSP1\n"
        + struct.pack(">QQQ", 200_000, 200_001, 200_001)
        + bytes(states)
        + bytes(actions)
    )
    assert len(raw) == 400_036
    counts = {
        "source_state_visits": source_visits,
        "destination_state_counts": destination_counts,
        "transition_action_counts": transition_action_counts,
        "state_action_counts": state_action_counts,
        "edge_counts": edge_counts,
        "persistence_hit_count": persistence_hits,
        "persistence_miss_count": 200_000 - persistence_hits,
    }
    audit = {
        "version": "sha256-counter-stream-v1",
        "words_consumed": stream.words,
        "bytes_consumed": stream.words * 8,
        "digest_blocks_generated": stream.blocks,
        "rejections_by_modulus": {
            str(key): value for key, value in sorted(stream.rejections.items())
        },
    }
    return raw, counts, audit, states[-1], actions[-1]


def _row(role: str, path: str, raw: bytes) -> dict[str, Any]:
    return {"role": role, "path": path, "bytes": len(raw), "sha256": _sha(raw)}


def _write(path: Path, value: Any) -> bytes:
    raw = _canonical(value)
    path.write_bytes(raw)
    return raw


def _build_fixture(directory: Path) -> dict[str, Any]:
    directory.mkdir(parents=True, exist_ok=True)
    paths = {
        "protocol": directory / "structured-ope-protocol-v1.json",
        "osf_registration_response": directory / "osf-registration-v1.json",
        "osf_registration_binding": directory / "code-freeze-binding-v1.json",
        "osf_registration_binding_file": directory / "osf-code-freeze-binding-file-v1.json",
        "quicknet_chain_info": directory / "quicknet-chain-info-v1.json",
        "quicknet_round": directory / "quicknet-round-v1.json",
        "model_input": directory / "model-v1.json",
        "model_manifest": directory / "model-v1-manifest.json",
        "model_tables": directory / "model-v1-tables.json",
        "trace": directory / "structured-ope-trace-v1.bin",
        "counts": directory / "structured-ope-trace-v1-counts.json",
        "manifest": directory / "structured-ope-trace-v1-manifest.json",
    }
    paths["protocol"].write_bytes(verifier.DEFAULT_PROTOCOL.read_bytes())
    paths["model_input"].write_bytes(verifier.DEFAULT_MODEL_INPUT.read_bytes())
    paths["model_manifest"].write_bytes(verifier.DEFAULT_MODEL_MANIFEST.read_bytes())
    paths["model_tables"].write_bytes(verifier.DEFAULT_MODEL_TABLES.read_bytes())

    code_paths: dict[str, Path] = {}
    code_rows: list[dict[str, Any]] = []
    for role, frozen_path, _actual in verifier.CODE_FILES:
        path = directory / f"fixture-{role}.py"
        raw = f"# fixture {role}\n".encode()
        path.write_bytes(raw)
        code_paths[role] = path
        code_rows.append(_row(role, frozen_path, raw))

    binding = {
        "artifact_status": "PUBLIC OSF CODE FREEZE BINDING",
        "schema_version": "controlled-queue-prospective-code-freeze-binding-v1",
        "registration_id": TEST_REGISTRATION_ID,
        "protocol": {
            "path": verifier.PROTOCOL_PATH,
            "bytes": len(paths["protocol"].read_bytes()),
            "sha256": verifier.PROTOCOL_SHA256,
            "commit": verifier.PROTOCOL_COMMIT,
            "tree": verifier.PROTOCOL_TREE,
        },
        "code_freeze": {"commit": CODE_FREEZE_COMMIT, "tree": CODE_FREEZE_TREE},
        "code_files": code_rows,
    }
    binding_raw = _write(paths["osf_registration_binding"], binding)
    osf_response = {
        "data": {
            "id": TEST_REGISTRATION_ID,
            "type": "registrations",
            "attributes": {
                "date_registered": TEST_DATE_REGISTERED,
                "public": True,
                "registration": True,
                "withdrawn": False,
            },
            "links": {"self": f"https://api.osf.io/v2/registrations/{TEST_REGISTRATION_ID}/"},
        }
    }
    osf_raw = _write(paths["osf_registration_response"], osf_response)
    binding_file_response = {
        "data": {
            "id": "osf-file-1",
            "type": "files",
            "attributes": {
                "name": "code-freeze-binding-v1.json",
                "kind": "file",
                "materialized_path": (
                    "/Archive of OSF Storage/code-freeze-binding-v1.json"
                ),
                "size": len(binding_raw),
                "current_version": 1,
                "extra": {"hashes": {"sha256": _sha(binding_raw)}},
            },
            "relationships": {
                "target": {
                    "data": {"id": TEST_REGISTRATION_ID, "type": "registrations"},
                    "links": {
                        "related": {
                            "href": f"https://api.osf.io/v2/registrations/{TEST_REGISTRATION_ID}/"
                        }
                    },
                },
            },
        }
    }
    binding_file_raw = _write(
        paths["osf_registration_binding_file"], binding_file_response
    )
    chain_info = {
        "public_key": verifier.PUBLIC_KEY,
        "period": 3,
        "genesis_time": 1_692_803_367,
        "genesis_seed": verifier.GROUP_HASH,
        "chain_hash": verifier.CHAIN_HASH,
        "scheme": verifier.SCHEME_ID,
        "beacon_id": "quicknet",
    }
    chain_raw = _write(paths["quicknet_chain_info"], chain_info)
    round_number, round_time = _fixture_round()
    round_response = {
        "round": round_number,
        "signature": TEST_SIGNATURE.hex(),
        "randomness": _sha(TEST_SIGNATURE),
    }
    round_raw = _write(paths["quicknet_round"], round_response)
    seed = hashlib.sha256(
        b"FormalSLT/controlled-queue/prospective-structured-ope-v1\0"
        + bytes.fromhex(verifier.CHAIN_HASH)
        + round_number.to_bytes(8, "big")
        + TEST_SIGNATURE
    ).digest()
    trace_raw, raw_counts, audit, final_state, final_action = _build_trace(seed)
    paths["trace"].write_bytes(trace_raw)
    counts = {
        "artifact_status": verifier.ARTIFACT_STATUS,
        "schema_version": verifier.COUNTS_SCHEMA,
        "trace_version": verifier.TRACE_VERSION,
        "generator_revision": verifier.GENERATOR_REVISION,
        "horizon": 200_000,
        "initial_state": 0,
        "initial_action": 0,
        "final_state": final_state,
        "final_action": final_action,
        "trace_sha256": _sha(trace_raw),
        "counts": raw_counts,
        "prng_audit": audit,
        "nonclaims": verifier.NONCLAIMS,
    }
    counts_raw = _write(paths["counts"], counts)

    raws = {
        "protocol": paths["protocol"].read_bytes(),
        "osf_registration_response": osf_raw,
        "osf_registration_binding": binding_raw,
        "osf_registration_binding_file": binding_file_raw,
        "quicknet_chain_info": chain_raw,
        "quicknet_round": round_raw,
        "model_input": paths["model_input"].read_bytes(),
        "model_manifest": paths["model_manifest"].read_bytes(),
        "model_tables": paths["model_tables"].read_bytes(),
        "trace": trace_raw,
        "counts": counts_raw,
    }
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
    inputs = [
        _row(role, paths[role].resolve().as_posix(), raws[role])
        for role in input_roles
    ]
    outputs = [
        _row("trace_binary", paths["trace"].resolve().as_posix(), trace_raw),
        _row("trace_counts", paths["counts"].resolve().as_posix(), counts_raw),
    ]
    registration_second = _fixture_registration_second()
    manifest = {
        "artifact_status": verifier.ARTIFACT_STATUS,
        "schema_version": verifier.MANIFEST_SCHEMA,
        "trace_version": verifier.TRACE_VERSION,
        "generator": {
            "path": code_rows[0]["path"],
            "revision": verifier.GENERATOR_REVISION,
            "bytes": code_rows[0]["bytes"],
            "sha256": code_rows[0]["sha256"],
        },
        "independent_verifier": {
            key: code_rows[1][key] for key in ("path", "bytes", "sha256")
        },
        "code_freeze": {
            "commit": CODE_FREEZE_COMMIT,
            "tree": CODE_FREEZE_TREE,
            "code_files": code_rows,
        },
        "registration": {
            "id": TEST_REGISTRATION_ID,
            "date_registered": TEST_DATE_REGISTERED,
            "unix_seconds_ceiling": registration_second,
            "api_response_sha256": _sha(osf_raw),
            "binding_sha256": _sha(binding_raw),
            "binding_file_api_response_sha256": _sha(binding_file_raw),
            "protocol_commit": verifier.PROTOCOL_COMMIT,
            "protocol_tree": verifier.PROTOCOL_TREE,
        },
        "beacon": {
            "chain_hash": verifier.CHAIN_HASH,
            "group_hash": verifier.GROUP_HASH,
            "scheme_id": verifier.SCHEME_ID,
            "round": round_number,
            "round_time_unix_seconds": round_time,
            "randomness": _sha(TEST_SIGNATURE),
            "signature_sha256": _sha(TEST_SIGNATURE),
            "derived_seed_sha256": _sha(seed),
            "signature_verified": True,
            "signature_verifier": {
                "implementation": verifier.BLS_IMPLEMENTATION,
                "dependency": "py-ecc",
                "version": verifier.PY_ECC_VERSION,
                "dst": verifier.BLS_DST.decode("ascii"),
            },
        },
        "parameters": {
            "horizon": 200_000,
            "state_count": 24,
            "action_count": 2,
            "initial_state": 0,
            "initial_action": 0,
            "true_gamma": "149/200",
            "family": "refreshEnvironment",
            "behavior_policy": "behavior_uniform",
            "prng_version": verifier.PRNG_VERSION,
            "sampling_version": verifier.SAMPLING_VERSION,
            "binary_version": verifier.BINARY_VERSION,
            "binary_magic_hex": verifier.BINARY_MAGIC.hex(),
            "binary_expected_bytes": 400_036,
        },
        "inputs": inputs,
        "outputs": outputs,
        "manifest_note": "canonical JSON; the manifest is written last and is not recursively self-hashed",
        "nonclaims": verifier.NONCLAIMS,
    }
    _write(paths["manifest"], manifest)
    return {"paths": paths, "code_paths": code_paths}


@pytest.fixture(scope="session")
def base_fixture(tmp_path_factory: pytest.TempPathFactory) -> Path:
    directory = tmp_path_factory.mktemp("prospective-trace-verifier")
    _build_fixture(directory)
    return directory


def _copy_fixture(base: Path, destination: Path) -> dict[str, Any]:
    root = destination / "fixture"
    shutil.copytree(base, root)
    built = _build_fixture  # keep the file-name mapping visibly independent
    del built
    paths = {
        "protocol": root / "structured-ope-protocol-v1.json",
        "osf_registration_response": root / "osf-registration-v1.json",
        "osf_registration_binding": root / "code-freeze-binding-v1.json",
        "osf_registration_binding_file": root / "osf-code-freeze-binding-file-v1.json",
        "quicknet_chain_info": root / "quicknet-chain-info-v1.json",
        "quicknet_round": root / "quicknet-round-v1.json",
        "model_input": root / "model-v1.json",
        "model_manifest": root / "model-v1-manifest.json",
        "model_tables": root / "model-v1-tables.json",
        "trace": root / "structured-ope-trace-v1.bin",
        "counts": root / "structured-ope-trace-v1-counts.json",
        "manifest": root / "structured-ope-trace-v1-manifest.json",
    }
    code_paths = {
        role: root / f"fixture-{role}.py"
        for role, _path, _actual in verifier.CODE_FILES
    }
    manifest = json.loads(paths["manifest"].read_bytes())
    for row in manifest["inputs"]:
        row["path"] = paths[row["role"]].resolve().as_posix()
    output_paths = {"trace_binary": paths["trace"], "trace_counts": paths["counts"]}
    for row in manifest["outputs"]:
        row["path"] = output_paths[row["role"]].resolve().as_posix()
    paths["manifest"].write_bytes(_canonical(manifest))
    return {"paths": paths, "code_paths": code_paths}


def _patch_evidence(monkeypatch: pytest.MonkeyPatch, fixture: dict[str, Any]) -> None:
    code_paths = fixture["code_paths"]
    monkeypatch.setattr(
        verifier,
        "CODE_FILES",
        tuple(
            (role, path_text, code_paths[role])
            for role, path_text, _path in verifier.CODE_FILES
        ),
    )

    def verify_signature(round_number: int, signature: bytes, public_key: bytes) -> None:
        assert round_number == _fixture_round()[0]
        assert public_key == bytes.fromhex(verifier.PUBLIC_KEY)
        if signature != TEST_SIGNATURE:
            raise verifier.VerificationError("test BLS verification rejected signature")

    monkeypatch.setattr(verifier, "_verify_quicknet_signature", verify_signature)
    monkeypatch.setattr(verifier, "_verify_git_tree", lambda *_args: None)
    monkeypatch.setattr(verifier, "_verify_git_file", lambda *_args: None)
    monkeypatch.setattr(verifier, "_verify_git_ancestor", lambda *_args: None)


def _verify(fixture: dict[str, Any]) -> None:
    paths = fixture["paths"]
    verifier.verify_paths(
        paths["protocol"],
        paths["osf_registration_response"],
        paths["osf_registration_binding"],
        paths["osf_registration_binding_file"],
        paths["quicknet_chain_info"],
        paths["quicknet_round"],
        paths["model_input"],
        paths["model_manifest"],
        paths["model_tables"],
        paths["trace"],
        paths["counts"],
        paths["manifest"],
    )


def _rewrite_manifest_file_binding(fixture: dict[str, Any], role: str) -> None:
    paths = fixture["paths"]
    manifest = json.loads(paths["manifest"].read_bytes())
    row = next(
        row
        for row in [*manifest["inputs"], *manifest["outputs"]]
        if row["role"] == role
    )
    key = "trace" if role == "trace_binary" else "counts" if role == "trace_counts" else role
    raw = paths[key].read_bytes()
    row["bytes"] = len(raw)
    row["sha256"] = _sha(raw)
    paths["manifest"].write_bytes(_canonical(manifest))


def test_independent_verifier_accepts_full_synthetic_replay(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    before = {key: _sha(path.read_bytes()) for key, path in fixture["paths"].items()}
    _verify(fixture)
    after = {key: _sha(path.read_bytes()) for key, path in fixture["paths"].items()}
    assert after == before
    metadata = json.loads(
        fixture["paths"]["osf_registration_binding_file"].read_bytes()
    )
    assert metadata["data"]["attributes"]["materialized_path"].startswith(
        "/Archive of OSF Storage/"
    )
    assert "node" not in metadata["data"]["relationships"]


def test_verifier_source_has_no_generator_import() -> None:
    source = Path(verifier.__file__).read_text()
    tree = ast.parse(source)
    forbidden = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module and "generate_controlled_queue" in node.module:
            forbidden.append(node.module)
        if isinstance(node, ast.Import):
            forbidden.extend(
                alias.name for alias in node.names if "generate_controlled_queue" in alias.name
            )
    assert forbidden == []


def test_tampered_rehashed_trace_fails_independent_replay(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    raw = bytearray(fixture["paths"]["trace"].read_bytes())
    state_offset = len(verifier.BINARY_MAGIC) + 24 + 17
    raw[state_offset] = (raw[state_offset] + 1) % 24
    fixture["paths"]["trace"].write_bytes(raw)
    _rewrite_manifest_file_binding(fixture, "trace_binary")
    with pytest.raises(verifier.VerificationError, match="replay"):
        _verify(fixture)


def test_rehashed_count_tamper_fails_reconstruction(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    counts = json.loads(fixture["paths"]["counts"].read_bytes())
    counts["counts"]["transition_action_counts"][0] -= 1
    fixture["paths"]["counts"].write_bytes(_canonical(counts))
    _rewrite_manifest_file_binding(fixture, "trace_counts")
    with pytest.raises(verifier.VerificationError, match="independently replayed"):
        _verify(fixture)


def test_wrong_formula_round_fails_even_after_manifest_rehash(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    response = json.loads(fixture["paths"]["quicknet_round"].read_bytes())
    response["round"] += 1
    fixture["paths"]["quicknet_round"].write_bytes(_canonical(response))
    _rewrite_manifest_file_binding(fixture, "quicknet_round")
    with pytest.raises(verifier.VerificationError, match="formula-selected"):
        _verify(fixture)


def test_wrong_signature_fails_after_randomness_and_manifest_rehash(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    response = json.loads(fixture["paths"]["quicknet_round"].read_bytes())
    signature = bytearray.fromhex(response["signature"])
    signature[-1] ^= 1
    response["signature"] = bytes(signature).hex()
    response["randomness"] = _sha(bytes(signature))
    fixture["paths"]["quicknet_round"].write_bytes(_canonical(response))
    _rewrite_manifest_file_binding(fixture, "quicknet_round")
    with pytest.raises(verifier.VerificationError, match="BLS verification"):
        _verify(fixture)


def test_osf_file_metadata_must_prove_registered_binding_bytes(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    metadata = json.loads(
        fixture["paths"]["osf_registration_binding_file"].read_bytes()
    )
    metadata["data"]["attributes"]["extra"]["hashes"]["sha256"] = "0" * 64
    fixture["paths"]["osf_registration_binding_file"].write_bytes(_canonical(metadata))
    _rewrite_manifest_file_binding(fixture, "osf_registration_binding_file")
    with pytest.raises(verifier.VerificationError, match="binding-file SHA-256"):
        _verify(fixture)


def test_cross_role_manifest_provenance_is_rejected(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    manifest = json.loads(fixture["paths"]["manifest"].read_bytes())
    manifest["inputs"][4], manifest["inputs"][5] = (
        manifest["inputs"][5],
        manifest["inputs"][4],
    )
    fixture["paths"]["manifest"].write_bytes(_canonical(manifest))
    with pytest.raises(verifier.VerificationError, match="role"):
        _verify(fixture)


def test_cross_role_input_path_alias_is_rejected(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    fixture["paths"]["quicknet_chain_info"] = fixture["paths"]["quicknet_round"]
    with pytest.raises(verifier.VerificationError, match="alias each other"):
        _verify(fixture)


def test_binary_action_path_requires_dummy_plus_A1_through_AH(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    raw = bytearray(fixture["paths"]["trace"].read_bytes())
    action_count_offset = len(verifier.BINARY_MAGIC) + 16
    struct.pack_into(">Q", raw, action_count_offset, 200_000)
    fixture["paths"]["trace"].write_bytes(raw)
    _rewrite_manifest_file_binding(fixture, "trace_binary")
    with pytest.raises(verifier.VerificationError, match="binary action count"):
        _verify(fixture)


def test_controlled_json_must_be_canonical_and_external_types_fail_closed(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    fixture["paths"]["osf_registration_binding"].write_bytes(
        fixture["paths"]["osf_registration_binding"].read_bytes() + b" "
    )
    with pytest.raises(verifier.VerificationError, match="canonical OSF binding"):
        _verify(fixture)

    fixture = _copy_fixture(base_fixture, tmp_path / "second")
    _patch_evidence(monkeypatch, fixture)
    response = json.loads(fixture["paths"]["quicknet_round"].read_bytes())
    response["round"] = True
    fixture["paths"]["quicknet_round"].write_bytes(_canonical(response))
    with pytest.raises(verifier.VerificationError, match="must be an integer"):
        _verify(fixture)


def test_duplicate_keys_in_raw_api_evidence_are_rejected(
    base_fixture: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _copy_fixture(base_fixture, tmp_path)
    _patch_evidence(monkeypatch, fixture)
    raw = fixture["paths"]["quicknet_chain_info"].read_bytes()
    fixture["paths"]["quicknet_chain_info"].write_bytes(
        b'{"chain_hash":"' + verifier.CHAIN_HASH.encode() + b'",' + raw.lstrip()[1:]
    )
    with pytest.raises(verifier.VerificationError, match="duplicate JSON key"):
        _verify(fixture)


def test_low_level_quicknet_crypto_vector_or_missing_dependency_fails_closed() -> None:
    signature = bytes.fromhex(
        "95a9f9f5b231b7714de1553105d8ffdf3dcda24cfdb1e689319bccf79a9c8ce4"
        "30a91b811fbfaf763900bc998b5d686a"
    )
    public_key = bytes.fromhex(verifier.PUBLIC_KEY)
    try:
        verifier._verify_quicknet_signature(42, signature, public_key)
    except verifier.VerificationError as error:
        assert f"py-ecc=={verifier.PY_ECC_VERSION} is required" in str(error)
        return
    with pytest.raises(verifier.VerificationError, match="signature verification failed"):
        verifier._verify_quicknet_signature(43, signature, public_key)


def test_git_object_proof_checks_tree_committed_and_current_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo = tmp_path / "git-proof"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    subprocess.run(["git", "-C", str(repo), "config", "user.name", "Fixture"], check=True)
    subprocess.run(
        ["git", "-C", str(repo), "config", "user.email", "fixture@example.invalid"],
        check=True,
    )
    tracked = repo / "proof.txt"
    raw = b"committed proof bytes\n"
    tracked.write_bytes(raw)
    subprocess.run(["git", "-C", str(repo), "add", "proof.txt"], check=True)
    subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "fixture"], check=True)
    commit = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    tree = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD^{tree}"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    monkeypatch.setattr(verifier, "ROOT", repo)
    verifier._verify_git_tree(commit, tree, "fixture")
    verifier._verify_git_ancestor(commit, commit)
    verifier._verify_git_file(commit, "proof.txt", raw, _sha(raw), len(raw), "fixture")
    with pytest.raises(verifier.VerificationError, match="git object check failed"):
        verifier._verify_git_ancestor("0" * 40, commit)
    dirty = b"dirty substitution\n"
    with pytest.raises(verifier.VerificationError, match="current versus committed"):
        verifier._verify_git_file(
            commit, "proof.txt", dirty, _sha(raw), len(raw), "fixture"
        )
