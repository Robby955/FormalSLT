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


def tabular_protocol(input_format: str) -> dict[str, object]:
    return {
        "analysis": "brier_monitor",
        "claim": {"quantity": CLI.tabular_brier.CLAIM_QUANTITY},
        "data": {
            "input_format": input_format,
            "outcome_column": "outcome",
            "prediction_encoding": "scaled_integer",
            "prediction_scale": 1_000_000,
            "require_strict_time_order": True,
            "time_column": "time",
        },
        "models": [{"column": "model_a_ppm", "id": "model-a"}],
        "protocol_id": "unit-test-brier-stream",
        "provenance": {
            "evidence_sha256": None,
            "prediction_timing": "PRE_OUTCOME",
            "tier": "DECLARED",
        },
        "schema_version": CLI.tabular_brier.PROTOCOL_SCHEMA,
        "statistics": {
            "delta": "1/20",
            "posterior": {"model-a": "1"},
            "prior": {"model-a": "1"},
            "tilt": "1/2",
            "wake": 0,
        },
    }


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


def test_prepare_csv_computes_exact_statistics(tmp_path: Path) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "2,1,750000\n"
        "3,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    preparation = CLI.tabular_brier.prepare(protocol_path, data_path)
    assert preparation["artifact_status"] == "PREPARED_NOT_CERTIFIED"
    assert preparation["statistics"]["posterior_empirical_brier_risk"] == "1/16"
    assert (
        preparation["statistics"]["posterior_suffix_predictor_quadratic_variation"]
        == "49/256"
    )
    assert preparation["verification"]["lean_kernel"] == "NOT_RUN"


def test_independent_replay_accepts_preparation(tmp_path: Path) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "2,1,750000\n"
        "3,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    preparation = CLI.tabular_brier.prepare(protocol_path, data_path)
    preparation_path = tmp_path / "preparation.json"
    preparation_path.write_bytes(CLI.tabular_brier.canonical_json_bytes(preparation))
    replayed = CLI.tabular_replay.verify(preparation_path, protocol_path, data_path)
    assert replayed == preparation


def test_prepare_and_replay_commands(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "2,1,750000\n"
        "3,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    preparation_path = tmp_path / "preparation.json"
    assert CLI.main(
        ["prepare", str(protocol_path), str(data_path), "--out", str(preparation_path)]
    ) == 0
    assert CLI.main(
        ["verify-preparation", str(preparation_path), str(protocol_path), str(data_path)]
    ) == 0
    output = capsys.readouterr().out
    assert "Certificate verification:   NOT ISSUED" in output
    assert "FormalSLT tabular replay:     PASS" in output


def test_certify_tabular_issues_compact_lean_receipt(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "2,1,750000\n"
        "3,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    output = tmp_path / "certificate"
    assert CLI.main(
        ["certify", str(protocol_path), str(data_path), "--out", str(output)]
    ) == 0
    certificate_path = output / CLI.tabular_certificate.CERTIFICATE_NAME
    certificate = json.loads(certificate_path.read_text())
    assert certificate["artifact_status"] == "CERTIFIED"
    assert certificate["certificate_profile"] == CLI.tabular_certificate.PROFILE
    assert certificate["replay"]["independent_replay"] == "PASS"
    assert certificate["kernel"]["result"] == "PASS"
    assert certificate["data"]["provenance"]["tier"] == "DECLARED"
    assert CLI.main(
        [
            "verify",
            str(certificate_path),
            "--protocol",
            str(protocol_path),
            "--data",
            str(data_path),
        ]
    ) == 0
    rendered = capsys.readouterr().out
    assert "FormalSLT compact Brier certificate: PASS" in rendered
    assert "Independent data replay:             PASS" in rendered

    tampered = json.loads(certificate_path.read_text())
    tampered["claim"]["upper_bound"] = "1/100"
    tampered_path = output / "tampered-certificate.json"
    tampered_path.write_bytes(canonical(tampered))
    with pytest.raises(
        CLI.tabular_certificate.CertificateError,
        match="certificate claim mismatch",
    ):
        CLI.tabular_certificate.verify(tampered_path)


def test_compact_checker_supports_multiple_models_and_zero_posterior(
    tmp_path: Path,
) -> None:
    protocol = tabular_protocol("csv")
    protocol["models"] = [
        {"column": "model_a_ppm", "id": "model-a"},
        {"column": "model_b_ppm", "id": "model-b"},
    ]
    protocol["statistics"]["prior"] = {"model-a": "1/2", "model-b": "1/2"}
    protocol["statistics"]["posterior"] = {"model-a": "1", "model-b": "0"}
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(protocol))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm,model_b_ppm\n"
        "1,1,750000,500000\n"
        "2,1,750000,500000\n"
        "3,1,750000,500000\n"
        "4,1,750000,500000\n",
        encoding="utf-8",
    )
    output = tmp_path / "certificate"
    certificate_path = CLI.tabular_certificate.issue(protocol_path, data_path, output)
    certificate = CLI.tabular_certificate.verify(
        certificate_path, protocol_path, data_path
    )
    assert certificate["kernel"]["result"] == "PASS"
    assert certificate["statistics"]["kl_upper"] == "7/10"


def test_independent_replay_rejects_tampered_statistic(tmp_path: Path) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "2,1,750000\n"
        "3,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    preparation = CLI.tabular_brier.prepare(protocol_path, data_path)
    preparation["statistics"]["posterior_empirical_brier_risk"] = "0"
    preparation_path = tmp_path / "preparation.json"
    preparation_path.write_bytes(CLI.tabular_brier.canonical_json_bytes(preparation))
    with pytest.raises(
        CLI.tabular_replay.ReplayError,
        match="posterior_empirical_brier_risk mismatch",
    ):
        CLI.tabular_replay.verify(preparation_path, protocol_path, data_path)


def test_prepare_rejects_nonchronological_rows(tmp_path: Path) -> None:
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("csv")))
    data_path = tmp_path / "predictions.csv"
    data_path.write_text(
        "time,outcome,model_a_ppm\n"
        "1,1,750000\n"
        "3,1,750000\n"
        "2,1,750000\n"
        "4,1,750000\n",
        encoding="utf-8",
    )
    with pytest.raises(CLI.tabular_brier.PreparationError, match="not strictly increasing"):
        CLI.tabular_brier.prepare(protocol_path, data_path)


def test_prepare_parquet_matches_csv_statistics(tmp_path: Path) -> None:
    pyarrow = pytest.importorskip("pyarrow")
    parquet = pytest.importorskip("pyarrow.parquet")
    protocol_path = tmp_path / "protocol.json"
    protocol_path.write_bytes(canonical(tabular_protocol("parquet")))
    data_path = tmp_path / "predictions.parquet"
    table = pyarrow.table(
        {
            "time": [1, 2, 3, 4],
            "outcome": [1, 1, 1, 1],
            "model_a_ppm": [750000, 750000, 750000, 750000],
        }
    )
    parquet.write_table(table, data_path)
    preparation = CLI.tabular_brier.prepare(protocol_path, data_path)
    preparation_path = tmp_path / "preparation.json"
    preparation_path.write_bytes(CLI.tabular_brier.canonical_json_bytes(preparation))
    CLI.tabular_replay.verify(preparation_path, protocol_path, data_path)
    assert preparation["statistics"]["posterior_empirical_brier_risk"] == "1/16"
    assert (
        preparation["statistics"]["posterior_suffix_predictor_quadratic_variation"]
        == "49/256"
    )
