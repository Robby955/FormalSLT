/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceiptRows03To05

/-!
# Controlled-queue receipt row certificates 6 through 8

This bounded arithmetic module checks three physical-state rows of the aligned
suffix histogram against the selected transition score.  Splitting the 24
rows keeps each elaboration process within a predictable memory envelope.
-/

open Finset ProbabilityTheory
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData
open KnownKernelReceiptInternal

noncomputable section

private theorem certificate_6 :
    RowCertificate (6 : PhysicalState) := by
  constructor
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreSquareRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem certificate_7 :
    RowCertificate (7 : PhysicalState) := by
  constructor
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreSquareRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

private theorem certificate_8 :
    RowCertificate (8 : PhysicalState) := by
  constructor
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]
  · intro action
    fin_cases action <;>
      norm_num [knownKernelReceiptSuffixEdgeCount, suffixEdgeRow,
        selectedScoreSquareRowSum, knownKernelSelectedTransitionScore,
        knownKernelSelectedPotential, knownKernelPotentialSpan,
        selectedPotentialTable, selectedPotentialSpan,
        queueThresholdTargetIndex, nominalModelOverloadPredictorIndex,
        targetPolicy_apply_toReal, behaviorPolicy_apply_toReal,
        targetPolicyTableIndex, policyTableMass, fixedBrierScore,
        fixedPredictorProbability,
        fixedPredictorTableValue_stateActionRowEquiv,
        fixedPredictorTableValueStateAction, overloadOutcome,
        overloadOutcomeTableValue, ControlledQueueData.policyTable,
        ControlledQueueData.fixedPredictorTable,
        ControlledQueueData.overloadOutcomeTable, Fin.sum_univ_succ]

/-- Exact score and squared-score histogram certificates for physical states
six through eight. -/
theorem certificates06To08 :
    RowCertificate (6 : PhysicalState) ∧
      RowCertificate (7 : PhysicalState) ∧
        RowCertificate (8 : PhysicalState) :=
  ⟨certificate_6, certificate_7, certificate_8⟩

end

end FormalSLT.Applications.ControlledQueue
