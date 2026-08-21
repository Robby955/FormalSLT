/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelReceiptRows00To02

/-!
# Controlled-queue receipt row certificates 3 through 5

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

private theorem certificate_3 :
    RowCertificate (3 : PhysicalState) := by
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

private theorem certificate_4 :
    RowCertificate (4 : PhysicalState) := by
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

private theorem certificate_5 :
    RowCertificate (5 : PhysicalState) := by
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
three through five. -/
theorem certificates03To05 :
    RowCertificate (3 : PhysicalState) ∧
      RowCertificate (4 : PhysicalState) ∧
        RowCertificate (5 : PhysicalState) :=
  ⟨certificate_3, certificate_4, certificate_5⟩

end

end FormalSLT.Applications.ControlledQueue
