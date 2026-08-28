from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import pytest

from scripts import generate_brier_monitor_synthetic_receipt as generator
from scripts import verify_brier_monitor_synthetic_receipt as verifier


def _temporary_arguments(tmp_path: Path, input_path: Path | None = None) -> tuple[list[str], dict[str, Path]]:
    paths = {
        "input": input_path or generator.DEFAULT_INPUT,
        "receipt": tmp_path / "receipt.json",
        "manifest": tmp_path / "manifest.json",
        "lean": tmp_path / "BrierMonitorSyntheticProofOfLifeData.lean",
    }
    arguments = [
        "--input",
        str(paths["input"]),
        "--receipt",
        str(paths["receipt"]),
        "--manifest",
        str(paths["manifest"]),
        "--lean",
        str(paths["lean"]),
    ]
    return arguments, paths


def test_tracked_artifacts_match_generator_and_independent_replay() -> None:
    assert generator.main(["--check"]) == 0
    assert verifier.main(["--check"]) == 0
    verifier_source = Path(verifier.__file__).read_text(encoding="utf-8")
    assert "from scripts import generate_brier_monitor_synthetic_receipt" not in verifier_source
    assert "import generate_brier_monitor_synthetic_receipt" not in verifier_source


def test_custom_outputs_are_byte_deterministic_and_replayable(tmp_path: Path) -> None:
    arguments, paths = _temporary_arguments(tmp_path)
    assert generator.main(arguments) == 0
    first = {key: path.read_bytes() for key, path in paths.items() if key != "input"}
    assert generator.main(arguments) == 0
    second = {key: path.read_bytes() for key, path in paths.items() if key != "input"}
    assert first == second
    assert verifier.main([*arguments, "--check"]) == 0


def test_receipt_recomputes_expected_soft_brier_branch() -> None:
    receipt = json.loads(generator.DEFAULT_RECEIPT.read_bytes())
    selected = receipt["selected_witness"]
    assert receipt["stream"]["horizon"] == 512
    assert selected["wake"] == 0
    assert selected["tilt_atom"] == 0
    assert Fraction(selected["tilt"]) == Fraction(1, 2)
    assert Fraction(selected["posterior_empirical_brier_risk"]) == Fraction(1, 16)
    assert Fraction(selected["suffix_predictor_quadratic_variation"]) == Fraction(49, 256)
    assert Fraction(selected["boundary_interval"]["upper"]) < Fraction(1, 10)
    assert Fraction(selected["exact_selection_margin_lower"]) > 0
    assert len(receipt["boundary_rows"]) == 24
    assert receipt["stream"]["losses_recomputed_from_predictions_and_outcomes"] == "true"


def test_input_schema_rejects_a_supplied_loss_column(tmp_path: Path) -> None:
    spec = json.loads(generator.DEFAULT_INPUT.read_bytes())
    spec["stream_segments"][0]["losses"] = ["1/16", "9/16"]
    input_path = tmp_path / "with-loss-column.json"
    input_path.write_bytes(generator.canonical_json_bytes(spec))
    arguments, _paths = _temporary_arguments(tmp_path / "outputs", input_path)
    assert generator.main(arguments) == 1
    assert verifier.main([*arguments, "--check"]) == 1


@pytest.mark.parametrize("mutation", ["float", "duplicate", "noncanonical_rational"])
def test_input_parser_fails_closed_on_noncanonical_json(tmp_path: Path, mutation: str) -> None:
    raw = generator.DEFAULT_INPUT.read_bytes()
    if mutation == "float":
        mutated = raw.replace(b'"count": 1', b'"count": 1.0', 1)
    elif mutation == "duplicate":
        needle = b'  "artifact_status": "SYNTHETIC PROOF-OF-LIFE INPUT",\n'
        mutated = raw.replace(needle, needle + needle, 1)
    else:
        spec = json.loads(raw)
        spec["confidence_delta"] = "2/320"
        mutated = generator.canonical_json_bytes(spec)
    input_path = tmp_path / f"{mutation}.json"
    input_path.write_bytes(mutated)
    arguments, _paths = _temporary_arguments(tmp_path / "outputs", input_path)
    assert generator.main(arguments) == 1


def test_independent_verifier_detects_receipt_tampering(tmp_path: Path) -> None:
    arguments, paths = _temporary_arguments(tmp_path)
    assert generator.main(arguments) == 0
    receipt = json.loads(paths["receipt"].read_bytes())
    receipt["selected_witness"]["posterior_empirical_brier_risk"] = "0"
    paths["receipt"].write_bytes(generator.canonical_json_bytes(receipt))
    assert verifier.main([*arguments, "--check"]) == 1


def test_independent_verifier_detects_changed_predictions_with_stale_outputs(
    tmp_path: Path,
) -> None:
    spec = json.loads(generator.DEFAULT_INPUT.read_bytes())
    spec["stream_segments"][1]["predictions"][0] = "2/3"
    input_path = tmp_path / "changed-prediction.json"
    input_path.write_bytes(generator.canonical_json_bytes(spec))
    arguments = [
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
    assert verifier.main(arguments) == 1


def test_manifest_binds_scripts_sources_and_generated_outputs() -> None:
    manifest = json.loads(generator.DEFAULT_MANIFEST.read_bytes())
    rows = {row["role"]: row for row in manifest["files"]}
    assert set(rows) == {
        "input",
        "generator",
        "independent_verifier",
        "oracle_source",
        "proof_of_life_checker",
        "receipt",
        "lean_data",
        "lean_receipt_source",
        "lean_receipt_checker",
    }
    assert manifest["formal_slt_commit"] == "62d8fc08b00bd41b7f6927f566e622573affacd7"
    assert rows["receipt"]["sha256"] == generator.sha256_bytes(
        generator.DEFAULT_RECEIPT.read_bytes()
    )
    assert rows["lean_data"]["sha256"] == generator.sha256_bytes(
        generator.DEFAULT_LEAN.read_bytes()
    )
    assert rows["lean_receipt_source"]["sha256"] == generator.sha256_bytes(
        generator.DEFAULT_LEAN_RECEIPT.read_bytes()
    )
    assert rows["lean_receipt_checker"]["sha256"] == generator.sha256_bytes(
        generator.DEFAULT_LEAN_CHECKER.read_bytes()
    )
