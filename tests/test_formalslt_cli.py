from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
SPEC = importlib.util.spec_from_file_location("formalslt_cli", SCRIPTS / "formalslt.py")
assert SPEC is not None and SPEC.loader is not None
CLI = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CLI)

PROTOCOL = ROOT / "applications/brier_monitor/gjp-compact-certificate-protocol-v1.json"
CERTIFICATE = ROOT / "docs/site/monitor/gjp-certificate-v1.json"


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def test_registered_protocol_loads() -> None:
    protocol, raw = CLI.load_protocol(PROTOCOL)
    assert protocol["certificate_profile"] in CLI.PROFILE_REGISTRY
    assert raw == canonical(protocol)


def test_unknown_protocol_field_fails(tmp_path: Path) -> None:
    protocol = json.loads(PROTOCOL.read_text())
    protocol["unregistered_claim"] = True
    path = tmp_path / "protocol.json"
    path.write_bytes(canonical(protocol))
    with pytest.raises(CLI.ToolError, match="extra=.*unregistered_claim"):
        CLI.load_protocol(path)


def test_unregistered_profile_fails(tmp_path: Path) -> None:
    protocol = json.loads(PROTOCOL.read_text())
    protocol["certificate_profile"] = "arbitrary-upload-v1"
    path = tmp_path / "protocol.json"
    path.write_bytes(canonical(protocol))
    with pytest.raises(CLI.ToolError, match="unsupported certificate profile"):
        CLI.load_protocol(path)


def test_artifact_digest_mismatch_fails() -> None:
    protocol, _raw = CLI.load_protocol(PROTOCOL)
    artifacts = {
        "manifest_sha256": protocol["expected_artifacts"]["manifest_sha256"],
        "receipt": {"protocol_sha256": protocol["expected_artifacts"]["protocol_sha256"]},
        "receipt_sha256": protocol["expected_artifacts"]["receipt_sha256"],
        "stream_sha256": "0" * 64,
    }
    with pytest.raises(CLI.ToolError, match="profile artifact stream_sha256"):
        CLI.validate_profile_artifacts(protocol, artifacts)


def test_profiles_json_is_machine_readable(capsys: pytest.CaptureFixture[str]) -> None:
    assert CLI.main(["profiles", "--json"]) == 0
    output = json.loads(capsys.readouterr().out)
    assert output[CLI.certificate_engine.PROFILE]["status"] == "SUPPORTED"


def test_published_certificate_verifies_without_lean(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert CLI.main(["verify", str(CERTIFICATE), "--skip-lean"]) == 0
    assert "FormalSLT compact certificate: PASS" in capsys.readouterr().out
