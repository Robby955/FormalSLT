/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueSharpStructuredOPE

/-!
# Generic sharp structured controlled-queue receipt reduction

This module is the pre-data arithmetic interface for the prospective sharp
structured controlled-queue receipt.  It reduces any physical
`state/action/next-state` histogram at the frozen horizon to an exact rational
upper bound on `sharpStructuredOPEBoundary`.

The reduction always uses the affine Bessel branch, the frozen log-cost
upper bounds `9` and `7`, and the frozen cumulant bounds `1 / 480` and
`1 / 8064`.  It does not contain a generated trace, assert membership in a
theorem-produced good event, inspect a receipt value, or prove that the
resulting upper bound is below any threshold.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.StabilityBridge
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

/-! ## Histogram and exact sufficient statistics -/

/-- A physical controlled-transition count tensor. -/
abbrev PhysicalTransitionHistogram :=
  PhysicalState → Action → PhysicalState → ℕ

/-- Universal test-function characterization of a physical transition
histogram.  Transition `k` uses current physical state `(path k).2`, action
`(path (k + 1)).1`, and next physical state `(path (k + 1)).2`. -/
def HasPhysicalTransitionHistogram
    (counts : PhysicalTransitionHistogram) (n : ℕ)
    (path : ℕ → Observation) : Prop :=
  ∀ f : PhysicalState → Action → PhysicalState → ℝ,
    (∑ k ∈ Finset.range n,
      f (path k).2 (path (k + 1)).1 (path (k + 1)).2) =
    ∑ state : PhysicalState, ∑ action : Action,
      ∑ nextState : PhysicalState,
        (counts state action nextState : ℝ) * f state action nextState

/-- Histogram sum of the selected normalized Poisson-corrected score. -/
def sharpStructuredHistogramScoreSum
    (counts : PhysicalTransitionHistogram) : ℝ :=
  ∑ state : PhysicalState, ∑ action : Action,
    ∑ nextState : PhysicalState,
      (counts state action nextState : ℝ) *
        knownKernelSelectedTransitionScore state action nextState

/-- Histogram sum of squared selected normalized scores. -/
def sharpStructuredHistogramSquaredScoreSum
    (counts : PhysicalTransitionHistogram) : ℝ :=
  ∑ state : PhysicalState, ∑ action : Action,
    ∑ nextState : PhysicalState,
      (counts state action nextState : ℝ) *
        (knownKernelSelectedTransitionScore state action nextState) ^ 2

/-- Number of transitions landing on the deterministic persistence
destination of their physical source/action row. -/
def sharpStructuredHistogramPersistenceHitCount
    (counts : PhysicalTransitionHistogram) : ℕ :=
  ∑ state : PhysicalState, ∑ action : Action,
    counts state action (candidateKernelStepStateAction state action)

/-- Exact centered selected-score sum of squares reconstructed from the
histogram sufficient statistics. -/
def sharpStructuredHistogramScoreBesselQ
    (counts : PhysicalTransitionHistogram) : ℝ :=
  sharpStructuredHistogramSquaredScoreSum counts -
    (sharpStructuredHistogramScoreSum counts) ^ 2 /
      (sharpStructuredHorizon : ℝ)

/-- Frozen affine first-branch upper bound on the selected score's hybrid
Bessel penalty. -/
def sharpStructuredHistogramScoreAffinePenalty
    (counts : PhysicalTransitionHistogram) : ℝ :=
  (1 : ℝ) / 2 + 3 / 2 * sharpStructuredHistogramScoreBesselQ counts

/-- Exact centered sum of squares of the binary persistence-hit sequence. -/
def sharpStructuredHistogramPersistenceBesselQ
    (counts : PhysicalTransitionHistogram) : ℝ :=
  (sharpStructuredHistogramPersistenceHitCount counts : ℝ) -
    (sharpStructuredHistogramPersistenceHitCount counts : ℝ) ^ 2 /
      (sharpStructuredHorizon : ℝ)

/-- Frozen affine first-branch upper bound on either orientation of the
persistence-hit hybrid Bessel penalty. -/
def sharpStructuredHistogramPersistenceAffinePenalty
    (counts : PhysicalTransitionHistogram) : ℝ :=
  (1 : ℝ) / 2 + 3 / 2 *
    sharpStructuredHistogramPersistenceBesselQ counts

/-! ## Frozen exact endpoint arithmetic -/

/-- Risk part of the primary endpoint, using log-cost upper `9`, cumulant
upper `1 / 480`, and no data-dependent choice of Bessel branch. -/
def sharpStructuredHistogramRiskUpper
    (counts : PhysicalTransitionHistogram) : ℝ :=
  knownKernelNormalizedScale *
      (sharpStructuredHistogramScoreSum counts /
          (sharpStructuredHorizon : ℝ) +
        (9 + (1 / 480 : ℝ) *
            sharpStructuredHistogramScoreAffinePenalty counts) /
          ((sharpStructuredHorizon : ℝ) * (1 / 16 : ℝ))) -
    knownKernelPotentialSpan

/-- Two-sided persistence radius upper bound, using log-cost upper `7`,
cumulant upper `1 / 8064`, and the affine Bessel branch. -/
def sharpStructuredHistogramPersistenceRadiusUpper
    (counts : PhysicalTransitionHistogram) : ℝ :=
  (7 + (1 / 8064 : ℝ) *
      sharpStructuredHistogramPersistenceAffinePenalty counts) /
    ((sharpStructuredHorizon : ℝ) * (1 / 64 : ℝ))

/-- Histogram upper bound on the nominal-candidate persistence TV budget. -/
def sharpStructuredHistogramPersistenceBudgetUpper
    (counts : PhysicalTransitionHistogram) : ℝ :=
  |candidatePersistenceHitProbability nominalCandidateIndex -
      (sharpStructuredHistogramPersistenceHitCount counts : ℝ) /
        (sharpStructuredHorizon : ℝ)| +
    sharpStructuredHistogramPersistenceRadiusUpper counts

/-- Frozen sharp residual evaluated from the histogram persistence count. -/
def sharpStructuredHistogramResidualUpper
    (counts : PhysicalTransitionHistogram) : ℝ :=
  sharpSelectedCandidateDriftOscillation +
    sharpSelectedRefreshSensitivityOscillation *
      sharpStructuredHistogramPersistenceBudgetUpper counts

/-- Exact rational upper bound on the frozen primary pathwise endpoint. -/
def sharpStructuredHistogramUpper
    (counts : PhysicalTransitionHistogram) : ℝ :=
  sharpStructuredHistogramRiskUpper counts +
    sharpStructuredHistogramResidualUpper counts

/-! ## Histogram-to-path identities -/

private def physicalPersistenceHitTransitionScore
    (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) : ℝ :=
  if nextState = candidateKernelStepStateAction state action then 1 else 0

private theorem observedPersistenceHitScore_eq_transitionScore
    (path : ℕ → Observation) (k : ℕ) :
    observedTrajectoryScore (orientedPersistenceHitScore false) k path =
      physicalPersistenceHitTransitionScore
        (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
  unfold observedTrajectoryScore orientedPersistenceHitScore
    markovTransitionTrajectoryScore orientedPersistenceHitMarkovScore
    persistenceDestinationHitScore physicalPersistenceHitTransitionScore
  simp only [Preorder.frestrictLe_apply, Bool.false_eq_true, if_false]

private theorem histogram_selectedScoreSum_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    (∑ k ∈ Finset.range sharpStructuredHorizon,
      knownKernelSelectedObservedScore path k) =
        sharpStructuredHistogramScoreSum counts := by
  calc
    (∑ k ∈ Finset.range sharpStructuredHorizon,
        knownKernelSelectedObservedScore path k) =
        ∑ k ∈ Finset.range sharpStructuredHorizon,
          knownKernelSelectedTransitionScore
            (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact knownKernelSelectedObservedScore_eq_transitionScore path k
    _ = sharpStructuredHistogramScoreSum counts := by
      simpa only [sharpStructuredHistogramScoreSum] using
        hhist knownKernelSelectedTransitionScore

private theorem histogram_selectedSquaredScoreSum_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    (∑ k ∈ Finset.range sharpStructuredHorizon,
      (knownKernelSelectedObservedScore path k) ^ 2) =
        sharpStructuredHistogramSquaredScoreSum counts := by
  calc
    (∑ k ∈ Finset.range sharpStructuredHorizon,
        (knownKernelSelectedObservedScore path k) ^ 2) =
        ∑ k ∈ Finset.range sharpStructuredHorizon,
          (knownKernelSelectedTransitionScore
            (path k).2 (path (k + 1)).1 (path (k + 1)).2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [knownKernelSelectedObservedScore_eq_transitionScore]
    _ = sharpStructuredHistogramSquaredScoreSum counts := by
      simpa only [sharpStructuredHistogramSquaredScoreSum] using
        hhist (fun state action nextState ↦
          (knownKernelSelectedTransitionScore state action nextState) ^ 2)

private theorem histogram_persistenceHitSum_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    (∑ k ∈ Finset.range sharpStructuredHorizon,
      observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) =
      (sharpStructuredHistogramPersistenceHitCount counts : ℝ) := by
  calc
    (∑ k ∈ Finset.range sharpStructuredHorizon,
        observedTrajectoryScore
          (orientedPersistenceHitScore false) k path) =
        ∑ k ∈ Finset.range sharpStructuredHorizon,
          physicalPersistenceHitTransitionScore
            (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact observedPersistenceHitScore_eq_transitionScore path k
    _ = ∑ state : PhysicalState, ∑ action : Action,
        ∑ nextState : PhysicalState,
          (counts state action nextState : ℝ) *
            physicalPersistenceHitTransitionScore state action nextState :=
      hhist physicalPersistenceHitTransitionScore
    _ = (sharpStructuredHistogramPersistenceHitCount counts : ℝ) := by
      have hrow (state : PhysicalState) (action : Action) :
          (∑ nextState : PhysicalState,
            (counts state action nextState : ℝ) *
              physicalPersistenceHitTransitionScore
                state action nextState) =
            (counts state action
              (candidateKernelStepStateAction state action) : ℝ) := by
        rw [Finset.sum_eq_single
          (candidateKernelStepStateAction state action)]
        · simp [physicalPersistenceHitTransitionScore]
        · intro nextState _hnextState hne
          simp [physicalPersistenceHitTransitionScore, hne]
        · simp
      simp_rw [hrow]
      unfold sharpStructuredHistogramPersistenceHitCount
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro state _hstate
      rw [Nat.cast_sum]

private theorem histogram_persistenceHitSquaredSum_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    (∑ k ∈ Finset.range sharpStructuredHorizon,
      (observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) ^ 2) =
      (sharpStructuredHistogramPersistenceHitCount counts : ℝ) := by
  rw [← histogram_persistenceHitSum_eq counts path hhist]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [observedPersistenceHitScore_eq_transitionScore]
  unfold physicalPersistenceHitTransitionScore
  split_ifs <;> norm_num

private theorem forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardBesselQ v n =
      (∑ k ∈ Finset.range n, (v k) ^ 2) -
        (∑ k ∈ Finset.range n, v k) ^ 2 / (n : ℝ) := by
  let m : ℝ := forwardPrefixMean v n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdecomp :
      (∑ k ∈ Finset.range n, (v k) ^ 2) =
        forwardBesselQ v n + (n : ℝ) * m ^ 2 := by
    have h :=
      FormalSLT.Statistics.ClassicalEstimation.sum_sq_sub_eq_sum_sq_sub_mean_add_card
        hn (fun i : Fin n ↦ v i) 0
    have hsum (f : ℕ → ℝ) :
        (∑ i : Fin n, f i) = ∑ i ∈ Finset.range n, f i :=
      Fin.sum_univ_eq_sum_range f n
    rw [hsum (fun i ↦ (v i - 0) ^ 2),
      hsum (fun i ↦ (v i - FormalSLT.Statistics.sampleMean
        (fun j : Fin n ↦ v j)) ^ 2)] at h
    rw [← forwardPrefixMean_eq_sampleMean v n] at h
    simpa [m, forwardBesselQ] using h
  have hsum : (∑ k ∈ Finset.range n, v k) = (n : ℝ) * m := by
    unfold m forwardPrefixMean
    field_simp [hn0]
  rw [hdecomp, hsum]
  field_simp [hn0]
  ring

private theorem histogram_selectedBesselQ_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    forwardBesselQ (knownKernelSelectedObservedScore path)
        sharpStructuredHorizon =
      sharpStructuredHistogramScoreBesselQ counts := by
  rw [forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := knownKernelSelectedObservedScore path)
    (n := sharpStructuredHorizon)
    (by norm_num [sharpStructuredHorizon])]
  rw [histogram_selectedScoreSum_eq counts path hhist,
    histogram_selectedSquaredScoreSum_eq counts path hhist]
  rfl

private theorem histogram_persistenceBesselQ_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (orientedPersistenceHitScore false) k path)
        sharpStructuredHorizon =
      sharpStructuredHistogramPersistenceBesselQ counts := by
  rw [forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := fun k ↦ observedTrajectoryScore
      (orientedPersistenceHitScore false) k path)
    (n := sharpStructuredHorizon)
    (by norm_num [sharpStructuredHorizon])]
  rw [histogram_persistenceHitSum_eq counts path hhist,
    histogram_persistenceHitSquaredSum_eq counts path hhist]
  rfl

private theorem orientedPersistenceObservedScore_true_eq_one_sub
    (path : ℕ → Observation) :
    (fun k ↦ observedTrajectoryScore
      (orientedPersistenceHitScore true) k path) =
    (fun k ↦ 1 - observedTrajectoryScore
      (orientedPersistenceHitScore false) k path) := by
  funext k
  rfl

private theorem histogram_orientedPersistenceBesselQ_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path)
    (complement : Bool) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (orientedPersistenceHitScore complement) k path)
        sharpStructuredHorizon =
      sharpStructuredHistogramPersistenceBesselQ counts := by
  cases complement
  · exact histogram_persistenceBesselQ_eq counts path hhist
  · rw [orientedPersistenceObservedScore_true_eq_one_sub,
      forwardBesselQ_one_sub]
    exact histogram_persistenceBesselQ_eq counts path hhist

private theorem histogram_empiricalPersistenceHitRate_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    empiricalPersistenceHitRate sharpStructuredHorizon path =
      (sharpStructuredHistogramPersistenceHitCount counts : ℝ) /
        (sharpStructuredHorizon : ℝ) := by
  unfold empiricalPersistenceHitRate trajectoryEmpiricalPrequentialRisk
    runningMean runningSum
  rw [histogram_persistenceHitSum_eq counts path hhist]

/-! ## Frozen affine-bound evaluations -/

private theorem histogram_selectedEmpiricalScore_eq
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    stationaryTargetPolicyPosteriorEmpiricalScore
        (markovBehaviorPolicyAsHistory behaviorPolicy)
        queueHypothesisTargetPolicy queueHypothesisScore knownKernelPotential
        knownKernelPotentialSpan (3 / 2 : ℝ) knownKernelSelectedPosterior
        sharpStructuredHorizon path =
      sharpStructuredHistogramScoreSum counts /
        (sharpStructuredHorizon : ℝ) := by
  unfold stationaryTargetPolicyPosteriorEmpiricalScore
    knownKernelSelectedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  change forwardPrefixMean (knownKernelSelectedObservedScore path)
      sharpStructuredHorizon = _
  unfold forwardPrefixMean
  rw [histogram_selectedScoreSum_eq counts path hhist]

private theorem histogram_selectedPenalty_le
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
        (fun hypothesis k path ↦
          stationaryTargetPolicyObservedScore
            (markovBehaviorPolicyAsHistory behaviorPolicy)
            (queueHypothesisTargetPolicy hypothesis)
            (queueHypothesisScore hypothesis)
            (knownKernelPotential hypothesis) knownKernelPotentialSpan
            (3 / 2 : ℝ) k path)
        sharpStructuredHorizon path ≤
      sharpStructuredHistogramScoreAffinePenalty counts := by
  unfold forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  change forwardHybridBesselPenalty (knownKernelSelectedObservedScore path)
      sharpStructuredHorizon ≤ _
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ (knownKernelSelectedObservedScore path)
            sharpStructuredHorizon)
        (((sharpStructuredHorizon : ℝ) /
            ((sharpStructuredHorizon : ℝ) - 1) *
              forwardBesselQ (knownKernelSelectedObservedScore path)
                sharpStructuredHorizon) +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (sharpStructuredHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ (knownKernelSelectedObservedScore path)
          sharpStructuredHorizon := min_le_left _ _
    _ = sharpStructuredHistogramScoreAffinePenalty counts := by
      rw [histogram_selectedBesselQ_eq counts path hhist]
      rfl

private theorem histogram_orientedPersistencePenalty_le
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path)
    (complement : Bool) :
    trajectoryPosteriorHybridBesselPenalty (diracPosterior complement)
        orientedPersistenceHitScore sharpStructuredHorizon path ≤
      sharpStructuredHistogramPersistenceAffinePenalty counts := by
  unfold trajectoryPosteriorHybridBesselPenalty
  rw [pacBayesPosteriorAverage_dirac]
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (orientedPersistenceHitScore complement) k path)
            sharpStructuredHorizon)
        (((sharpStructuredHorizon : ℝ) /
            ((sharpStructuredHorizon : ℝ) - 1) *
              forwardBesselQ
                (fun k ↦ observedTrajectoryScore
                  (orientedPersistenceHitScore complement) k path)
                sharpStructuredHorizon) +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (sharpStructuredHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (orientedPersistenceHitScore complement) k path)
          sharpStructuredHorizon := min_le_left _ _
    _ = sharpStructuredHistogramPersistenceAffinePenalty counts := by
      rw [histogram_orientedPersistenceBesselQ_eq counts path hhist complement]
      rfl

private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private theorem sharpStructuredPersistenceLogCost_le_seven
    (complement : Bool) :
    klDiv (diracPosterior complement) (finiteUniformRealPMF Bool) +
        Real.log (1 /
          (sharpStructuredPersistenceFailureBudget *
            sharpStructuredPersistenceTiltWeight ())) ≤ 7 := by
  rw [klDiv_dirac_finiteUniformRealPMF]
  norm_num [sharpStructuredPersistenceFailureBudget,
    sharpStructuredPersistenceTiltWeight, finiteUniformRealPMF]
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (40 : ℝ) ≠ 0)]
  calc
    Real.log ((2 : ℝ) * 40) ≤ Real.log 128 :=
      Real.log_le_log (by norm_num) (by norm_num)
    _ = Real.log ((2 : ℝ) ^ (7 : ℕ)) := by norm_num
    _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 7 := by linarith [log_two_le_one]

private theorem sharpStructuredRiskBoundary_le_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    knownKernelOPEBoundary knownKernelSelectedPosterior
        sharpStructuredHorizon path ≤
      sharpStructuredHistogramRiskUpper counts := by
  have hpen := histogram_selectedPenalty_le counts path hhist
  have hq : 0 ≤ sharpStructuredHistogramScoreBesselQ counts := by
    rw [← histogram_selectedBesselQ_eq counts path hhist]
    exact forwardBesselQ_nonneg _ _
  have haffine : 0 ≤ sharpStructuredHistogramScoreAffinePenalty counts := by
    unfold sharpStructuredHistogramScoreAffinePenalty
    positivity
  have hpsi := knownKernelRiskTilt_psi_le_one_fourEighty
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) *
          forwardPosteriorHybridBesselPenalty knownKernelSelectedPosterior
            (fun hypothesis k path ↦
              stationaryTargetPolicyObservedScore
                (markovBehaviorPolicyAsHistory behaviorPolicy)
                (queueHypothesisTargetPolicy hypothesis)
                (queueHypothesisScore hypothesis)
                (knownKernelPotential hypothesis) knownKernelPotentialSpan
                (3 / 2 : ℝ) k path)
            sharpStructuredHorizon path ≤
        (1 / 480 : ℝ) *
          sharpStructuredHistogramScoreAffinePenalty counts := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) *
          sharpStructuredHistogramScoreAffinePenalty counts :=
        mul_le_mul_of_nonneg_left hpen hpsi0
      _ ≤ (1 / 480 : ℝ) *
          sharpStructuredHistogramScoreAffinePenalty counts :=
        mul_le_mul_of_nonneg_right hpsi haffine
  have hcost := knownKernelReceipt_selectedLogCost_le_nine
  have hemp := histogram_selectedEmpiricalScore_eq counts path hhist
  have hscale : 0 ≤ knownKernelNormalizedScale := by
    norm_num [knownKernelNormalizedScale, selectedNormalizedScale]
  unfold knownKernelOPEBoundary stationaryTargetPolicyOPEBoundary
    forwardPredictableMeanBesselPACBayesBoundary
  rw [hemp]
  rw [knownKernelNormalizedScale_eq]
  norm_num [knownKernelRiskTilt, sharpStructuredHorizon,
    sharpStructuredHistogramRiskUpper] at hproduct hcost ⊢
  nlinarith

private theorem sharpStructuredPersistenceBoundary_le_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path)
    (complement : Bool) :
    persistenceHitBoundary sharpStructuredPersistenceTiltWeight
        sharpStructuredPersistenceTilt complement
        sharpStructuredPersistenceFailureBudget ()
        sharpStructuredHorizon path ≤
      sharpStructuredHistogramPersistenceRadiusUpper counts := by
  have hpen :=
    histogram_orientedPersistencePenalty_le counts path hhist complement
  have hq : 0 ≤ sharpStructuredHistogramPersistenceBesselQ counts := by
    rw [← histogram_orientedPersistenceBesselQ_eq
      counts path hhist complement]
    exact forwardBesselQ_nonneg _ _
  have haffine :
      0 ≤ sharpStructuredHistogramPersistenceAffinePenalty counts := by
    unfold sharpStructuredHistogramPersistenceAffinePenalty
    positivity
  have hpsi :=
    sharpStructuredPersistenceTilt_psi_le_one_eightThousandSixtyFour
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) *
          trajectoryPosteriorHybridBesselPenalty
            (diracPosterior complement) orientedPersistenceHitScore
            sharpStructuredHorizon path ≤
        (1 / 8064 : ℝ) *
          sharpStructuredHistogramPersistenceAffinePenalty counts := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) *
          sharpStructuredHistogramPersistenceAffinePenalty counts :=
        mul_le_mul_of_nonneg_left hpen hpsi0
      _ ≤ (1 / 8064 : ℝ) *
          sharpStructuredHistogramPersistenceAffinePenalty counts :=
        mul_le_mul_of_nonneg_right hpsi haffine
  have hcost := sharpStructuredPersistenceLogCost_le_seven complement
  unfold persistenceHitBoundary trajectoryEmpiricalBernsteinPACBayesBoundary
  norm_num [sharpStructuredPersistenceTilt,
    sharpStructuredPersistenceFailureBudget,
    sharpStructuredPersistenceTiltWeight, sharpStructuredHorizon,
    sharpStructuredHistogramPersistenceRadiusUpper]
    at hproduct hcost ⊢
  nlinarith

private theorem sharpStructuredPersistenceRadius_le_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    persistenceHitRadius sharpStructuredPersistenceTiltWeight
        sharpStructuredPersistenceTilt sharpStructuredPersistenceFailureBudget
        () sharpStructuredHorizon path ≤
      sharpStructuredHistogramPersistenceRadiusUpper counts := by
  unfold persistenceHitRadius
  exact max_le
    (sharpStructuredPersistenceBoundary_le_histogram counts path hhist false)
    (sharpStructuredPersistenceBoundary_le_histogram counts path hhist true)

private theorem sharpStructuredPersistenceBudget_le_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    sharpStructuredPersistenceBudget sharpStructuredHorizon path ≤
      sharpStructuredHistogramPersistenceBudgetUpper counts := by
  unfold sharpStructuredPersistenceBudget structuredCandidateTVBudget
    sharpStructuredHistogramPersistenceBudgetUpper
  rw [histogram_empiricalPersistenceHitRate_eq counts path hhist]
  exact add_le_add le_rfl
    (sharpStructuredPersistenceRadius_le_histogram counts path hhist)

private theorem sharpStructuredResidual_le_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist : HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    sharpStructuredResidual sharpStructuredHorizon path ≤
      sharpStructuredHistogramResidualUpper counts := by
  unfold sharpStructuredResidual sharpStructuredHistogramResidualUpper
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (sharpStructuredPersistenceBudget_le_histogram counts path hhist)
      (by norm_num [sharpSelectedRefreshSensitivityOscillation]))

/-- Any path with the supplied physical transition histogram has its frozen
sharp structured primary boundary bounded by the preregistered exact rational
histogram endpoint.  The theorem is generic in the counts and contains no
future trace values. -/
theorem sharpStructuredReceiptBoundary_evaluation_of_histogram
    (counts : PhysicalTransitionHistogram) (path : ℕ → Observation)
    (hhist :
      HasPhysicalTransitionHistogram counts sharpStructuredHorizon path) :
    sharpStructuredOPEBoundary sharpStructuredHorizon path ≤
      sharpStructuredHistogramUpper counts := by
  unfold sharpStructuredOPEBoundary sharpStructuredHistogramUpper
  exact add_le_add
    (sharpStructuredRiskBoundary_le_histogram counts path hhist)
    (sharpStructuredResidual_le_histogram counts path hhist)

end

end FormalSLT.Applications.ControlledQueue
