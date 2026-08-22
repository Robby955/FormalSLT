from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (
    ROOT
    / "FormalSLT/Applications/ControlledQueueSharpStructuredRetrospectiveReceipt.lean"
)
SHARP_OPE_SOURCE = (
    ROOT / "FormalSLT/Applications/ControlledQueueSharpStructuredOPE.lean"
)


def test_receipt_is_bound_to_the_aligned_retrospective_summary() -> None:
    text = SOURCE.read_text()

    assert "knownKernelReceiptHorizon" in text
    assert "HasReceiptSuffixEdgeHistogram" in text
    assert "KnownKernelReceiptPathSummary" in text
    assert "152266" in text
    assert (
        "45318758321311224310665458696783373002366549 /\n"
        "    659558894102351266671449077672292808728248320"
    ) in text


def test_receipt_source_uses_no_oracle_identifiers() -> None:
    text = SOURCE.read_text()

    forbidden = (
        "knownKernelSelectedPosteriorRisk_eq",
        "queueThreshold_nominalModelOverload_stationaryRisk",
        "queueThreshold_nominalModelOverload_catalogStationaryRisk",
        "selectedStationaryRisk",
        "sharpStructuredTruePersistence",
        "sharpStructuredHorizon",
        "true_gamma",
        "native_decide",
    )
    for identifier in forbidden:
        assert identifier not in text


def test_candidate_drift_oscillation_is_direct_and_oracle_free() -> None:
    # This source check gives a readable failure near the edited proof. The
    # Lean checker performs the transitive declaration-dependency audit.
    sharp_ope_text = SHARP_OPE_SOURCE.read_text()
    proof_start = sharp_ope_text.index(
        "private theorem knownKernelSelectedCandidateDrift_mem_Icc"
    )
    proof_end = sharp_ope_text.index(
        "private def sharpSelectedSensitivityLower", proof_start
    )
    drift_proof = sharp_ope_text[proof_start:proof_end]

    assert "targetPolicyRowRisk" in drift_proof
    assert "candidateEnvironment_apply_toReal" in drift_proof
    assert "knownKernelSelectedPotential" in drift_proof
    forbidden = (
        "knownKernelSelectedCandidateDrift_sub_eq_residual_sub",
        "knownKernelSelectedResidual",
        "selectedResidualTable",
        "knownKernelSelectedPotential_residual_eq",
        "queueThreshold_nominalModelOverload_stationaryRisk",
        "queueThreshold_nominalModelOverload_catalogStationaryRisk",
        "knownKernelSelectedPosteriorRisk_eq",
        "selectedStationaryRisk",
        "queueHypothesisStationary",
    )
    for identifier in forbidden:
        assert identifier not in drift_proof
