/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueKnownKernelSelection
import FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

/-!
# Lightweight numerics for the controlled-queue known-kernel receipt

This module exposes only the generated potential, aligned histogram, and
selected-score interface needed by the bounded row-certificate modules.  It
deliberately avoids importing the explicit invariant-law proof so each
arithmetic certificate elaborates in a small environment.

The generated data records exact rational values.  This module does not prove
raw-byte hashes, good-event membership, or a statistical confidence claim.
-/

open Finset ProbabilityTheory
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

/-- Common span of the selected shifted potential. -/
def knownKernelPotentialSpan : ℝ := (selectedPotentialSpan : ℝ)

private theorem generatedSelectedPotentialTable_length :
    selectedPotentialTable.length = 24 := rfl

/-- Shifted potential table supplied for the selected depth-twelve atom.

The shift makes the minimum value zero. Additive shifts do not change either
the Poisson correction or its residual. -/
def knownKernelSelectedPotential (state : PhysicalState) : ℝ :=
  (selectedPotentialTable.get
      (Fin.cast generatedSelectedPotentialTable_length.symm state) : ℚ)

/-- Number of scored controlled transitions in the deterministic summary. -/
def knownKernelReceiptHorizon : ℕ := receiptHorizon

/-- Exact selected normalized-score sum supplied by the trace summary. -/
def knownKernelReceiptScoreSum : ℝ := (observedScoreSum : ℝ)

/-- Exact selected normalized squared-score sum supplied by the trace
summary. -/
def knownKernelReceiptSquaredScoreSum : ℝ :=
  (observedScoreSquareSum : ℝ)

/-- The selected normalized observed score on a controlled path. -/
def knownKernelSelectedObservedScore
    (path : ℕ → Observation) (k : ℕ) : ℝ :=
  stationaryTargetPolicyObservedScore
    (markovBehaviorPolicyAsHistory behaviorPolicy)
    (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
    (queueHypothesisScore queueThresholdNominalModelHypothesis)
    knownKernelSelectedPotential knownKernelPotentialSpan (3 / 2 : ℝ)
    k path

/-- The selected normalized score as a function of one physical
state/action/next-state triple. -/
def knownKernelSelectedTransitionScore
    (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) : ℝ :=
  ((targetPolicy queueThresholdTargetIndex state action).toReal /
      (behaviorPolicy state action).toReal) *
    ((fixedBrierScore nominalModelOverloadPredictorIndex
          state action nextState +
        knownKernelSelectedPotential nextState -
        knownKernelSelectedPotential state + knownKernelPotentialSpan) /
      (1 + 2 * knownKernelPotentialSpan)) /
    (3 / 2 : ℝ)

/-- The pathwise selected observed score depends only on its physical
state/action/next-state triple. -/
theorem knownKernelSelectedObservedScore_eq_transitionScore
    (path : ℕ → Observation) (k : ℕ) :
    knownKernelSelectedObservedScore path k =
      knownKernelSelectedTransitionScore
        (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
  unfold knownKernelSelectedObservedScore
    stationaryTargetPolicyObservedScore controlledObservedImportanceScore
    observedTrajectoryScore controlledNormalizedImportanceScore
    controlledImportanceRatio targetPolicyPoissonControlledScore
    markovTargetPolicyAsHistory markovBehaviorPolicyAsHistory
    knownKernelSelectedTransitionScore queueHypothesisTargetPolicy
    queueHypothesisScore queueThresholdNominalModelHypothesis
  simp only [Preorder.frestrictLe_apply]

private theorem generatedSuffixEdgeRow_length
    (state : PhysicalState) (action : Action) :
    (suffixEdgeRow state action).length = 24 := by
  fin_cases state <;> fin_cases action <;> rfl

/-- Generated count for one aligned suffix edge. -/
def knownKernelReceiptSuffixEdgeCount
    (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) : ℕ :=
  (suffixEdgeRow state action).get
    (Fin.cast (generatedSuffixEdgeRow_length state action).symm nextState)

/-- Universal test-function characterization of the generated aligned suffix
histogram. Quantifying over every real test function is equivalent to fixing
every individual edge count and is convenient for exact score aggregation. -/
def HasReceiptSuffixEdgeHistogram (path : ℕ → Observation) : Prop :=
  ∀ f : PhysicalState → Action → PhysicalState → ℝ,
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      f (path k).2 (path (k + 1)).1 (path (k + 1)).2) =
    ∑ state : PhysicalState, ∑ action : Action,
      ∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          f state action nextState

/-- Unaligned numerical path summary: the selected score sum and squared-score
sum. A separate suffix-edge-histogram theorem is required to bind this summary
to the intended frozen-trace alignment, because an off-by-one slice can have
the same two scalar sums. -/
def KnownKernelReceiptPathSummary (path : ℕ → Observation) : Prop :=
  (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      knownKernelSelectedObservedScore path k) =
      knownKernelReceiptScoreSum ∧
  (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      (knownKernelSelectedObservedScore path k) ^ 2) =
      knownKernelReceiptSquaredScoreSum

namespace KnownKernelReceiptInternal

/-- Opaque certificate that one physical-state row of the aligned histogram
reproduces the generated selected-score and squared-score subtotals. -/
structure RowCertificate (state : PhysicalState) : Prop where
  score :
    ∀ action : Action,
      (∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          knownKernelSelectedTransitionScore state action nextState) =
        (selectedScoreRowSum state action : ℝ)
  square :
    ∀ action : Action,
      (∑ nextState : PhysicalState,
        (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
          (knownKernelSelectedTransitionScore state action nextState) ^ 2) =
        (selectedScoreSquareRowSum state action : ℝ)

end KnownKernelReceiptInternal

end

end FormalSLT.Applications.ControlledQueue
