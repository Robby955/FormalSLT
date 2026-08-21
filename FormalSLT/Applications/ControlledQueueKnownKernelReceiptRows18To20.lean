/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceiptRows15To17

/-!
# Controlled-queue receipt row certificates 18 through 20

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

private theorem certificate_18 :
    RowCertificate (18 : PhysicalState) := by
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

private theorem certificate_19 :
    RowCertificate (19 : PhysicalState) := by
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

private theorem certificate_20 :
    RowCertificate (20 : PhysicalState) := by
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
eighteen through twenty. -/
theorem certificates18To20 :
    RowCertificate (18 : PhysicalState) ∧
      RowCertificate (19 : PhysicalState) ∧
        RowCertificate (20 : PhysicalState) :=
  ⟨certificate_18, certificate_19, certificate_20⟩

end

end FormalSLT.Applications.ControlledQueue
