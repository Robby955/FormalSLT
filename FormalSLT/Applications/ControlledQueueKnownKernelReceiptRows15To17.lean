/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceiptRows12To14

/-!
# Controlled-queue receipt row certificates 15 through 17

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

private theorem certificate_15 :
    RowCertificate (15 : PhysicalState) := by
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

private theorem certificate_16 :
    RowCertificate (16 : PhysicalState) := by
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

private theorem certificate_17 :
    RowCertificate (17 : PhysicalState) := by
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
fifteen through seventeen. -/
theorem certificates15To17 :
    RowCertificate (15 : PhysicalState) ∧
      RowCertificate (16 : PhysicalState) ∧
        RowCertificate (17 : PhysicalState) :=
  ⟨certificate_15, certificate_16, certificate_17⟩

end

end FormalSLT.Applications.ControlledQueue
