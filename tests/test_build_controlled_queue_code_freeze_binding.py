from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import runpy
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_controlled_queue_code_freeze_binding.py"
SPEC = importlib.util.spec_from_file_location("code_freeze_binding_builder", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


def _git(root: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def _fixture_repository(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.name", "FormalSLT Test")
    _git(root, "config", "user.email", "tests@example.invalid")

    protocol_raw = b'{"protocol":"frozen"}\n'
    _write(root / builder.PROTOCOL_PATH, protocol_raw)
    _git(root, "add", builder.PROTOCOL_PATH)
    _git(root, "commit", "-q", "-m", "protocol")
    protocol_commit = _git(root, "rev-parse", "HEAD^{commit}")
    protocol_tree = _git(root, "rev-parse", "HEAD^{tree}")

    for index, (_role, path_text) in enumerate(builder.CODE_FILES):
        _write(root / path_text, f"# frozen code {index}\n".encode())
    _git(root, "add", *[path for _role, path in builder.CODE_FILES])
    _git(root, "commit", "-q", "-m", "code freeze")
    freeze_commit = _git(root, "rev-parse", "HEAD^{commit}")
    freeze_tree = _git(root, "rev-parse", "HEAD^{tree}")

    monkeypatch.setattr(builder, "PROTOCOL_COMMIT", protocol_commit)
    monkeypatch.setattr(builder, "PROTOCOL_TREE", protocol_tree)
    monkeypatch.setattr(builder, "PROTOCOL_SHA256", hashlib.sha256(protocol_raw).hexdigest())
    monkeypatch.setattr(builder, "CODE_FREEZE_COMMIT", freeze_commit)
    monkeypatch.setattr(builder, "CODE_FREEZE_TREE", freeze_tree)
    monkeypatch.setattr(builder, "EXPECTED_BINDING_BYTES", -1)
    monkeypatch.setattr(builder, "EXPECTED_BINDING_SHA256", "fixture")
    return root


def test_exact_code_freeze_binding_and_existing_consumers_accept() -> None:
    raw = builder.expected_binding_bytes()
    assert len(raw) == 1_501
    assert hashlib.sha256(raw).hexdigest() == (
        "9dea4b601331717358bf0b9e8610384a4f7fbe71c332c563700ec91dd3a2064e"
    )
    assert b"registration_id" not in raw
    binding = json.loads(raw)
    assert binding["code_freeze"] == {
        "commit": "6c3f7de49d545be3e6bcfbb32f70b4aa86ef55de",
        "tree": "12248252ab3dc2bcd549b61f2678d40618fb1c7e",
    }
    assert [row["role"] for row in binding["code_files"]] == [
        "trace_generator",
        "trace_verifier",
        "receipt_generator",
        "receipt_verifier",
    ]

    builder.validate_existing_consumers(raw)

    protocol_raw = (ROOT / builder.PROTOCOL_PATH).read_bytes()
    trace_generator = runpy.run_path(
        str(ROOT / "scripts/generate_controlled_queue_prospective_trace.py")
    )
    trace_generator["validate_osf_binding"](raw, protocol_raw, root=ROOT)
    trace_verifier = runpy.run_path(
        str(ROOT / "scripts/verify_controlled_queue_prospective_trace.py")
    )
    trace_verifier["_verify_binding"](binding, protocol_raw)
    receipt_verifier = runpy.run_path(
        str(ROOT / "scripts/verify_controlled_queue_prospective_receipt.py")
    )
    receipt_verifier["_validate_code_freeze_binding"](binding, protocol_raw)


def test_binding_is_canonical_json() -> None:
    raw = builder.expected_binding_bytes()
    value = json.loads(raw)
    assert raw == builder.canonical_json_bytes(value)


def test_fixture_reconstructs_git_objects_and_current_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    value = builder.build_binding(root=root)
    assert value["protocol"]["commit"] == builder.PROTOCOL_COMMIT
    assert value["code_freeze"]["commit"] == builder.CODE_FREEZE_COMMIT
    assert len(value["code_files"]) == 4


def test_fixture_git_queries_ignore_replacement_refs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    subprocess.run(
        [
            "/usr/bin/git",
            "-C",
            str(root),
            "replace",
            builder.PROTOCOL_COMMIT,
            builder.CODE_FREEZE_COMMIT,
        ],
        check=True,
    )
    assert builder.build_binding(root=root)["protocol"]["tree"] == (
        builder.PROTOCOL_TREE
    )


def test_rejects_current_code_drift(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    _role, path_text = builder.CODE_FILES[0]
    (root / path_text).write_text("# changed after freeze\n")
    with pytest.raises(builder.RegistrationBindingError, match="current code file"):
        builder.build_binding(root=root)


def test_rejects_wrong_frozen_tree(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    monkeypatch.setattr(builder, "CODE_FREEZE_TREE", "0" * 40)
    with pytest.raises(builder.RegistrationBindingError, match="tree mismatch"):
        builder.build_binding(root=root)


def test_rejects_wrong_protocol_hash(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    monkeypatch.setattr(builder, "PROTOCOL_SHA256", "0" * 64)
    with pytest.raises(builder.RegistrationBindingError, match="protocol SHA-256"):
        builder.build_binding(root=root)


def test_rejects_existing_prospective_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = _fixture_repository(tmp_path, monkeypatch)
    appeared = root / builder.FRESH_OUTPUT_PATHS[0]
    _write(appeared, b"must not exist")
    with pytest.raises(builder.RegistrationBindingError, match="already exists"):
        builder.build_binding(root=root)


def test_exclusive_write_and_stale_check(tmp_path: Path) -> None:
    output = tmp_path / "evidence" / "code-freeze-binding-v1.json"
    expected = b'{"exact":true}\n'
    builder._write_exclusive(output, expected)
    assert output.read_bytes() == expected
    assert output.stat().st_mode & 0o777 == 0o644
    assert builder.check_binding(output, expected)
    assert not builder.check_binding(output, b'{"exact":false}\n')
    with pytest.raises(builder.RegistrationBindingError, match="overwrite or alias"):
        builder._write_exclusive(output, expected)


def test_exclusive_write_rejects_parent_swap(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    parent = tmp_path / "evidence"
    parent.mkdir()
    displaced = tmp_path / "displaced"
    output = parent / "code-freeze-binding-v1.json"
    real_link = os.link

    def swap_parent_then_link(*args: object, **kwargs: object) -> None:
        parent.rename(displaced)
        parent.mkdir()
        real_link(*args, **kwargs)

    monkeypatch.setattr(builder.os, "link", swap_parent_then_link)
    with pytest.raises(builder.RegistrationBindingError, match="directory changed"):
        builder._write_exclusive(output, b"binding\n")
    assert not output.exists()
    assert list(displaced.iterdir()) == []


def test_rejects_symlinked_output_parent(tmp_path: Path) -> None:
    real = tmp_path / "real"
    real.mkdir()
    linked = tmp_path / "linked"
    linked.symlink_to(real, target_is_directory=True)
    output = linked / "code-freeze-binding-v1.json"
    with pytest.raises(builder.RegistrationBindingError, match="symbolic link"):
        builder._write_exclusive(output, b"binding\n")


def test_rejects_case_and_unicode_output_aliases(tmp_path: Path) -> None:
    parent = tmp_path / "evidence"
    parent.mkdir()
    target = parent / "code-freeze-binding-v1.json"
    (parent / "CODE-FREEZE-BINDING-V1.JSON").write_text("alias\n")
    with pytest.raises(builder.RegistrationBindingError, match="overwrite or alias"):
        builder._write_exclusive(target, b"binding\n")

    other = tmp_path / "unicode"
    other.mkdir()
    unicode_target = other / "café.json"
    (other / "cafe\N{COMBINING ACUTE ACCENT}.json").write_text("alias\n")
    with pytest.raises(builder.RegistrationBindingError, match="overwrite or alias"):
        builder._write_exclusive(unicode_target, b"binding\n")


def test_rejects_custom_output_path(tmp_path: Path) -> None:
    with pytest.raises(builder.RegistrationBindingError, match="must be exactly"):
        builder._validate_output_path(tmp_path / "binding.json")


def test_cli_requires_explicit_mode() -> None:
    with pytest.raises(SystemExit) as error:
        builder.parse_args([])
    assert error.value.code == 2


def test_builder_has_no_network_or_generation_imports() -> None:
    source = SCRIPT.read_text()
    assert "urllib" not in source
    assert "requests" not in source
    assert "socket" not in source
    assert "quicknet-round" not in source
    assert "structured-ope-trace-v1.bin" in source  # absence check only
    assert "random" not in source
    assert "time." not in source


def test_no_reserved_prospective_output_exists() -> None:
    for path_text in builder.FRESH_OUTPUT_PATHS:
        path = ROOT / path_text
        assert not path.exists()
        assert not path.is_symlink()
