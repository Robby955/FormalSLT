/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceiptNumerics

/-!
# Controlled-queue receipt row certificates 0 through 2

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

private theorem certificate_0 :
    RowCertificate (0 : PhysicalState) := by
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

private theorem certificate_1 :
    RowCertificate (1 : PhysicalState) := by
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

private theorem certificate_2 :
    RowCertificate (2 : PhysicalState) := by
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
zero through two. -/
theorem certificates00To02 :
    RowCertificate (0 : PhysicalState) ∧
      RowCertificate (1 : PhysicalState) ∧
        RowCertificate (2 : PhysicalState) :=
  ⟨certificate_0, certificate_1, certificate_2⟩

end

end FormalSLT.Applications.ControlledQueue
