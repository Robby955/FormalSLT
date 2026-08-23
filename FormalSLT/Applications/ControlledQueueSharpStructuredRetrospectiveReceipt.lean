/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueSharpStructuredOPE

/-!
# Retrospective sharp structured controlled-queue receipt

This module evaluates the sharp structured OPE boundary on the existing
aligned known-kernel suffix histogram.  That histogram contains `199999`
controlled transitions, so this receipt is deliberately separate from the
prospective `200000`-transition receipt interface.

The numerical reduction uses only observable sufficient statistics from the
histogram: the selected score sum, selected squared-score sum, and the number
of persistence-destination hits.  It does not use the true persistence
parameter, an exact invariant law, or an exact stationary-risk value.  The
outer-mass theorem is pointwise for each fixed admissible persistence
parameter under the path law started at `knownKernelReceiptInitial`, namely
`(action = 1, state = 1)`. Its failure-event corollary bounds by `1 / 20` the
outer mass of the paths on which the frozen histogram is observed while the
displayed risk conclusion fails. It does not assert good-event membership for
a named trace or coverage conditional on observing that histogram.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.StabilityBridge FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.Applications.ControlledQueueKnownKernelReceiptData

noncomputable section

/-! ## Observable retrospective summary -/

/-- The known-kernel score summary together with the exact number of aligned
persistence-destination hits. -/
def SharpStructuredRetrospectivePathSummary
    (path : ℕ → Observation) : Prop :=
  KnownKernelReceiptPathSummary path ∧
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) = 152266

private def retrospectivePersistenceHitTransitionScore
    (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) : ℝ :=
  if nextState = candidateKernelStepStateAction state action then 1 else 0

private theorem observedPersistenceHitScore_eq_retrospectiveTransitionScore
    (path : ℕ → Observation) (k : ℕ) :
    observedTrajectoryScore (orientedPersistenceHitScore false) k path =
      retrospectivePersistenceHitTransitionScore
        (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
  unfold observedTrajectoryScore orientedPersistenceHitScore
    markovTransitionTrajectoryScore orientedPersistenceHitMarkovScore
    persistenceDestinationHitScore
    retrospectivePersistenceHitTransitionScore
  simp only [Preorder.frestrictLe_apply, Bool.false_eq_true, if_false]

private def retrospectivePersistenceHitCount : ℕ :=
  ∑ state : PhysicalState, ∑ action : Action,
    knownKernelReceiptSuffixEdgeCount state action
      (candidateKernelStepStateAction state action)

private theorem retrospectivePersistenceHitCount_eq :
    retrospectivePersistenceHitCount = 152266 := by
  decide

private theorem retrospectiveHistogramPersistenceHitSum_eq
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) = 152266 := by
  calc
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
        observedTrajectoryScore
          (orientedPersistenceHitScore false) k path) =
        ∑ k ∈ Finset.range knownKernelReceiptHorizon,
          retrospectivePersistenceHitTransitionScore
            (path k).2 (path (k + 1)).1 (path (k + 1)).2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact observedPersistenceHitScore_eq_retrospectiveTransitionScore path k
    _ = ∑ state : PhysicalState, ∑ action : Action,
        ∑ nextState : PhysicalState,
          (knownKernelReceiptSuffixEdgeCount state action nextState : ℝ) *
            retrospectivePersistenceHitTransitionScore
              state action nextState :=
      hhist retrospectivePersistenceHitTransitionScore
    _ = (retrospectivePersistenceHitCount : ℝ) := by
      have hrow (state : PhysicalState) (action : Action) :
          (∑ nextState : PhysicalState,
            (knownKernelReceiptSuffixEdgeCount
                state action nextState : ℝ) *
              retrospectivePersistenceHitTransitionScore
                state action nextState) =
            (knownKernelReceiptSuffixEdgeCount state action
              (candidateKernelStepStateAction state action) : ℝ) := by
        rw [Finset.sum_eq_single
          (candidateKernelStepStateAction state action)]
        · simp [retrospectivePersistenceHitTransitionScore]
        · intro nextState _hnextState hne
          simp [retrospectivePersistenceHitTransitionScore, hne]
        · simp
      simp_rw [hrow]
      unfold retrospectivePersistenceHitCount
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro state _hstate
      rw [Nat.cast_sum]
    _ = 152266 := by rw [retrospectivePersistenceHitCount_eq]; norm_num

/-- The generated aligned suffix histogram implies all three retrospective
sufficient statistics. -/
theorem sharpStructuredRetrospectivePathSummary_of_suffixEdgeHistogram
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    SharpStructuredRetrospectivePathSummary path := by
  exact ⟨knownKernelReceiptPathSummary_of_suffixEdgeHistogram path hhist,
    retrospectiveHistogramPersistenceHitSum_eq path hhist⟩

/-! ## Exact endpoint arithmetic -/

/-- Affine first-branch Bessel statistic for the binary persistence-hit
sequence at the retrospective horizon. -/
def sharpStructuredRetrospectivePersistenceBesselQ : ℝ :=
  152266 - (152266 : ℝ) ^ 2 / knownKernelReceiptHorizon

/-- Affine first-branch hybrid-Bessel penalty for either hit orientation. -/
def sharpStructuredRetrospectivePersistenceAffinePenalty : ℝ :=
  (1 : ℝ) / 2 + 3 / 2 *
    sharpStructuredRetrospectivePersistenceBesselQ

/-- Risk-side upper bound using the sharper `1 / 480` cumulant estimate. -/
def sharpStructuredRetrospectiveRiskUpper : ℝ :=
  knownKernelNormalizedScale *
      (knownKernelReceiptScoreSum / knownKernelReceiptHorizon +
        (9 + (1 / 480 : ℝ) * knownKernelReceiptAffinePenalty) /
          ((knownKernelReceiptHorizon : ℝ) * (1 / 16 : ℝ))) -
    knownKernelPotentialSpan

/-- Two-sided persistence radius using the `1 / 8064` cumulant estimate. -/
def sharpStructuredRetrospectivePersistenceRadiusUpper : ℝ :=
  (7 + (1 / 8064 : ℝ) *
      sharpStructuredRetrospectivePersistenceAffinePenalty) /
    ((knownKernelReceiptHorizon : ℝ) * (1 / 64 : ℝ))

/-- Absolute discrepancy between the nominal candidate hit probability and
the observed retrospective hit rate. -/
def sharpStructuredRetrospectiveCandidateGap : ℝ :=
  |candidatePersistenceHitProbability nominalCandidateIndex -
    (152266 : ℝ) / knownKernelReceiptHorizon|

/-- Candidate discrepancy plus the retrospective persistence radius. -/
def sharpStructuredRetrospectivePersistenceBudgetUpper : ℝ :=
  sharpStructuredRetrospectiveCandidateGap +
    sharpStructuredRetrospectivePersistenceRadiusUpper

/-- Sharp drift/sensitivity residual evaluated at the retrospective budget. -/
def sharpStructuredRetrospectiveResidualUpper : ℝ :=
  sharpSelectedCandidateDriftOscillation +
    sharpSelectedRefreshSensitivityOscillation *
      sharpStructuredRetrospectivePersistenceBudgetUpper

/-- Exact rational form of the retrospective primary endpoint. -/
def sharpStructuredRetrospectivePrimaryUpper : ℚ :=
  45318758321311224310665458696783373002366549 /
    659558894102351266671449077672292808728248320

/-- Exact retrospective score-side risk upper bound. -/
theorem sharpStructuredRetrospectiveRiskUpper_eq :
    sharpStructuredRetrospectiveRiskUpper =
      551767839558372204619597184793599353373353 /
        8193278187606848033185702828227239859978240 := by
  norm_num [sharpStructuredRetrospectiveRiskUpper,
    knownKernelNormalizedScale, knownKernelPotentialSpan,
    knownKernelReceiptHorizon, knownKernelReceiptScoreSum,
    knownKernelReceiptAffinePenalty, receiptHorizon, observedScoreSum,
    observedHybridPenaltyUpper, selectedNormalizedScale,
    selectedPotentialSpan]

/-- Exact retrospective binary-hit Bessel statistic. -/
theorem sharpStructuredRetrospectivePersistenceBesselQ_eq :
    sharpStructuredRetrospectivePersistenceBesselQ =
      7268112978 / 199999 := by
  norm_num [sharpStructuredRetrospectivePersistenceBesselQ,
    knownKernelReceiptHorizon, receiptHorizon]

/-- Exact affine persistence penalty used by both hit orientations. -/
theorem sharpStructuredRetrospectivePersistenceAffinePenalty_eq :
    sharpStructuredRetrospectivePersistenceAffinePenalty =
      21804538933 / 399998 := by
  rw [sharpStructuredRetrospectivePersistenceAffinePenalty,
    sharpStructuredRetrospectivePersistenceBesselQ_eq]
  norm_num

/-- Exact absolute discrepancy from the fixed nominal candidate. -/
theorem sharpStructuredRetrospectiveCandidateGap_eq :
    sharpStructuredRetrospectiveCandidateGap = 17609 / 19199904 := by
  norm_num [sharpStructuredRetrospectiveCandidateGap,
    candidatePersistenceHitProbability, candidatePersistenceParameter,
    persistenceHitProbability, candidateGamma, candidateGammaRat,
    nominalCandidateIndex, knownKernelReceiptHorizon, receiptHorizon,
    ControlledQueueData.candidateGammaTable]

/-- Exact two-sided persistence radius upper bound. -/
theorem sharpStructuredRetrospectivePersistenceRadiusUpper_eq :
    sharpStructuredRetrospectivePersistenceRadiusUpper =
      44383626037 / 10079899200252 := by
  rw [sharpStructuredRetrospectivePersistenceRadiusUpper,
    sharpStructuredRetrospectivePersistenceAffinePenalty_eq]
  norm_num [knownKernelReceiptHorizon, receiptHorizon]

/-- Exact nominal-candidate persistence budget. -/
theorem sharpStructuredRetrospectivePersistenceBudgetUpper_eq :
    sharpStructuredRetrospectivePersistenceBudgetUpper =
      429026438507 / 80639193602016 := by
  rw [sharpStructuredRetrospectivePersistenceBudgetUpper,
    sharpStructuredRetrospectiveCandidateGap_eq,
    sharpStructuredRetrospectivePersistenceRadiusUpper_eq]
  norm_num

/-- Exact sharp drift/sensitivity residual upper bound. -/
theorem sharpStructuredRetrospectiveResidualUpper_eq :
    sharpStructuredRetrospectiveResidualUpper =
      237836924342876093772442411 /
        174017349415050426720385499136 := by
  rw [sharpStructuredRetrospectiveResidualUpper,
    sharpStructuredRetrospectivePersistenceBudgetUpper_eq]
  norm_num [sharpSelectedCandidateDriftOscillation,
    sharpSelectedRefreshSensitivityOscillation]

/-- The componentwise risk and residual evaluation equals the displayed
exact rational endpoint. -/
theorem sharpStructuredRetrospectiveUpper_eq_primary :
    sharpStructuredRetrospectiveRiskUpper +
        sharpStructuredRetrospectiveResidualUpper =
      (sharpStructuredRetrospectivePrimaryUpper : ℝ) := by
  norm_num [sharpStructuredRetrospectiveRiskUpper,
    sharpStructuredRetrospectiveResidualUpper,
    sharpStructuredRetrospectivePersistenceBudgetUpper,
    sharpStructuredRetrospectiveCandidateGap,
    sharpStructuredRetrospectivePersistenceRadiusUpper,
    sharpStructuredRetrospectivePersistenceAffinePenalty,
    sharpStructuredRetrospectivePersistenceBesselQ,
    sharpStructuredRetrospectivePrimaryUpper,
    knownKernelNormalizedScale, knownKernelPotentialSpan,
    knownKernelReceiptHorizon, knownKernelReceiptScoreSum,
    knownKernelReceiptAffinePenalty, knownKernelReceiptBesselQ,
    sharpSelectedCandidateDriftOscillation,
    sharpSelectedRefreshSensitivityOscillation,
    candidatePersistenceHitProbability, candidatePersistenceParameter,
    persistenceHitProbability, candidateGamma, candidateGammaRat,
    nominalCandidateIndex,
    receiptHorizon, observedScoreSum, observedScoreBesselQ,
    observedHybridPenaltyUpper, selectedNormalizedScale,
    selectedPotentialSpan, ControlledQueueData.candidateGammaTable]

/-- The exact retrospective primary endpoint is below `0.069`. -/
theorem sharpStructuredRetrospectivePrimaryUpper_lt_sixtyNineThousandths :
    (sharpStructuredRetrospectivePrimaryUpper : ℝ) < 69 / 1000 := by
  norm_num [sharpStructuredRetrospectivePrimaryUpper]

/-! ## Pathwise reduction -/

private theorem retrospective_forwardBesselQ_eq_sum_sq_sub_sq_sum_div
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

private theorem retrospectivePersistenceHitSquaredSum_eq
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    (∑ k ∈ Finset.range knownKernelReceiptHorizon,
      (observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) ^ 2) = 152266 := by
  rw [← hsummary.2]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [observedPersistenceHitScore_eq_retrospectiveTransitionScore]
  unfold retrospectivePersistenceHitTransitionScore
  split_ifs <;> norm_num

private theorem retrospectivePersistenceBesselQ_eq
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (orientedPersistenceHitScore false) k path)
        knownKernelReceiptHorizon =
      sharpStructuredRetrospectivePersistenceBesselQ := by
  rw [retrospective_forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := fun k ↦ observedTrajectoryScore
      (orientedPersistenceHitScore false) k path)
    (n := knownKernelReceiptHorizon)
    (by norm_num [knownKernelReceiptHorizon, receiptHorizon])]
  rw [hsummary.2, retrospectivePersistenceHitSquaredSum_eq path hsummary]
  rfl

private theorem retrospectiveOrientedPersistenceScore_true_eq_one_sub
    (path : ℕ → Observation) :
    (fun k ↦ observedTrajectoryScore
      (orientedPersistenceHitScore true) k path) =
    (fun k ↦ 1 - observedTrajectoryScore
      (orientedPersistenceHitScore false) k path) := by
  funext k
  rfl

private theorem retrospectiveOrientedPersistenceBesselQ_eq
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path)
    (complement : Bool) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (orientedPersistenceHitScore complement) k path)
        knownKernelReceiptHorizon =
      sharpStructuredRetrospectivePersistenceBesselQ := by
  cases complement
  · exact retrospectivePersistenceBesselQ_eq path hsummary
  · rw [retrospectiveOrientedPersistenceScore_true_eq_one_sub,
      forwardBesselQ_one_sub]
    exact retrospectivePersistenceBesselQ_eq path hsummary

private theorem retrospectiveEmpiricalPersistenceHitRate_eq
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    empiricalPersistenceHitRate knownKernelReceiptHorizon path =
      (152266 : ℝ) / knownKernelReceiptHorizon := by
  unfold empiricalPersistenceHitRate trajectoryEmpiricalPrequentialRisk
    runningMean runningSum
  rw [hsummary.2]

private theorem retrospectiveSelectedRiskBoundary_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    knownKernelOPEBoundary knownKernelSelectedPosterior
        knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectiveRiskUpper := by
  have hpen := knownKernelReceipt_selectedPenalty_le path hsummary.1
  have hpsi := knownKernelRiskTilt_psi_le_one_fourEighty
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have haffine : 0 ≤ knownKernelReceiptAffinePenalty := by
    norm_num [knownKernelReceiptAffinePenalty, observedHybridPenaltyUpper]
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
            knownKernelReceiptHorizon path ≤
        (1 / 480 : ℝ) * knownKernelReceiptAffinePenalty := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 16 : ℝ) *
          knownKernelReceiptAffinePenalty :=
        mul_le_mul_of_nonneg_left hpen hpsi0
      _ ≤ (1 / 480 : ℝ) * knownKernelReceiptAffinePenalty :=
        mul_le_mul_of_nonneg_right hpsi haffine
  have hcost := knownKernelReceipt_selectedLogCost_le_nine
  have hemp := knownKernelReceipt_selectedEmpiricalScore_eq path hsummary.1
  unfold knownKernelOPEBoundary stationaryTargetPolicyOPEBoundary
    forwardPredictableMeanBesselPACBayesBoundary
  rw [hemp, knownKernelNormalizedScale_eq]
  norm_num [knownKernelRiskTilt, knownKernelReceiptHorizon,
    sharpStructuredRetrospectiveRiskUpper, receiptHorizon,
    knownKernelNormalizedScale, selectedNormalizedScale]
    at hproduct hcost ⊢
  nlinarith

private theorem retrospectiveOrientedPersistencePenalty_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path)
    (complement : Bool) :
    trajectoryPosteriorHybridBesselPenalty (diracPosterior complement)
        orientedPersistenceHitScore knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectivePersistenceAffinePenalty := by
  unfold trajectoryPosteriorHybridBesselPenalty
  rw [pacBayesPosteriorAverage_dirac]
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (orientedPersistenceHitScore complement) k path)
            knownKernelReceiptHorizon)
        (((knownKernelReceiptHorizon : ℝ) /
            ((knownKernelReceiptHorizon : ℝ) - 1) *
              forwardBesselQ
                (fun k ↦ observedTrajectoryScore
                  (orientedPersistenceHitScore complement) k path)
                knownKernelReceiptHorizon) +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (knownKernelReceiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (orientedPersistenceHitScore complement) k path)
          knownKernelReceiptHorizon := min_le_left _ _
    _ = sharpStructuredRetrospectivePersistenceAffinePenalty := by
      rw [retrospectiveOrientedPersistenceBesselQ_eq
        path hsummary complement]
      rfl

private theorem retrospectiveLogTwo_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private theorem retrospectivePersistenceLogCost_le_seven
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
    _ ≤ 7 := by linarith [retrospectiveLogTwo_le_one]

private theorem retrospectivePersistenceBoundary_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path)
    (complement : Bool) :
    persistenceHitBoundary sharpStructuredPersistenceTiltWeight
        sharpStructuredPersistenceTilt complement
        sharpStructuredPersistenceFailureBudget ()
        knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectivePersistenceRadiusUpper := by
  have hpen :=
    retrospectiveOrientedPersistencePenalty_le path hsummary complement
  have hpsi :=
    sharpStructuredPersistenceTilt_psi_le_one_eightThousandSixtyFour
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have haffine :
      0 ≤ sharpStructuredRetrospectivePersistenceAffinePenalty := by
    norm_num [sharpStructuredRetrospectivePersistenceAffinePenalty,
      sharpStructuredRetrospectivePersistenceBesselQ,
      knownKernelReceiptHorizon, receiptHorizon]
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) *
          trajectoryPosteriorHybridBesselPenalty
            (diracPosterior complement) orientedPersistenceHitScore
            knownKernelReceiptHorizon path ≤
        (1 / 8064 : ℝ) *
          sharpStructuredRetrospectivePersistenceAffinePenalty := by
    calc
      _ ≤ forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) *
          sharpStructuredRetrospectivePersistenceAffinePenalty :=
        mul_le_mul_of_nonneg_left hpen hpsi0
      _ ≤ (1 / 8064 : ℝ) *
          sharpStructuredRetrospectivePersistenceAffinePenalty :=
        mul_le_mul_of_nonneg_right hpsi haffine
  have hcost := retrospectivePersistenceLogCost_le_seven complement
  unfold persistenceHitBoundary trajectoryEmpiricalBernsteinPACBayesBoundary
  norm_num [sharpStructuredPersistenceTilt,
    sharpStructuredPersistenceFailureBudget,
    sharpStructuredPersistenceTiltWeight, knownKernelReceiptHorizon,
    sharpStructuredRetrospectivePersistenceRadiusUpper, receiptHorizon]
    at hproduct hcost ⊢
  nlinarith

private theorem retrospectivePersistenceRadius_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    persistenceHitRadius sharpStructuredPersistenceTiltWeight
        sharpStructuredPersistenceTilt sharpStructuredPersistenceFailureBudget
        () knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectivePersistenceRadiusUpper := by
  unfold persistenceHitRadius
  exact max_le
    (retrospectivePersistenceBoundary_le path hsummary false)
    (retrospectivePersistenceBoundary_le path hsummary true)

private theorem retrospectivePersistenceBudget_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    sharpStructuredPersistenceBudget knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectivePersistenceBudgetUpper := by
  unfold sharpStructuredPersistenceBudget structuredCandidateTVBudget
    sharpStructuredRetrospectivePersistenceBudgetUpper
  rw [retrospectiveEmpiricalPersistenceHitRate_eq path hsummary]
  exact add_le_add le_rfl
    (retrospectivePersistenceRadius_le path hsummary)

private theorem retrospectiveResidual_le
    (path : ℕ → Observation)
    (hsummary : SharpStructuredRetrospectivePathSummary path) :
    sharpStructuredResidual knownKernelReceiptHorizon path ≤
      sharpStructuredRetrospectiveResidualUpper := by
  unfold sharpStructuredResidual sharpStructuredRetrospectiveResidualUpper
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (retrospectivePersistenceBudget_le path hsummary)
      (by norm_num [sharpSelectedRefreshSensitivityOscillation]))

/-- Every path with the existing aligned suffix histogram has its sharp
structured boundary bounded by the displayed exact rational endpoint. -/
theorem sharpStructuredRetrospectiveBoundary_le
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    sharpStructuredOPEBoundary knownKernelReceiptHorizon path ≤
      (sharpStructuredRetrospectivePrimaryUpper : ℝ) := by
  have hsummary :=
    sharpStructuredRetrospectivePathSummary_of_suffixEdgeHistogram path hhist
  calc
    sharpStructuredOPEBoundary knownKernelReceiptHorizon path ≤
        sharpStructuredRetrospectiveRiskUpper +
          sharpStructuredRetrospectiveResidualUpper := by
      unfold sharpStructuredOPEBoundary
      exact add_le_add
        (retrospectiveSelectedRiskBoundary_le path hsummary)
        (retrospectiveResidual_le path hsummary)
    _ = (sharpStructuredRetrospectivePrimaryUpper : ℝ) :=
      sharpStructuredRetrospectiveUpper_eq_primary

/-- The aligned retrospective pathwise boundary is strictly below `0.069`. -/
theorem sharpStructuredRetrospectiveBoundary_lt_sixtyNineThousandths
    (path : ℕ → Observation) (hhist : HasReceiptSuffixEdgeHistogram path) :
    sharpStructuredOPEBoundary knownKernelReceiptHorizon path < 69 / 1000 :=
  (sharpStructuredRetrospectiveBoundary_le path hhist).trans_lt
    sharpStructuredRetrospectivePrimaryUpper_lt_sixtyNineThousandths

/-! ## Pointwise confidence statement -/

/-- For every admissible persistence parameter, under the path law started at
`knownKernelReceiptInitial = (action = 1, state = 1)`, one event of complement
mass at most `1 / 20` validates the retrospective `< 0.069` endpoint whenever
the observed path has the frozen aligned suffix histogram. No named trace is
asserted to lie in the theorem-produced event. -/
theorem exists_controlledQueueSharpStructuredRetrospective_event
    (gamma : PersistenceParameter) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy)
          knownKernelReceiptInitial).real goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, HasReceiptSuffixEdgeHistogram path →
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment gamma)
            queueHypothesisTargetPolicy
            (queueHypothesisStationary (refreshEnvironment gamma))
            queueHypothesisScore knownKernelSelectedPosterior <
          (sharpStructuredRetrospectivePrimaryUpper : ℝ) := by
  rcases exists_controlledQueueSharpStructuredOPE_event
      gamma knownKernelReceiptInitial with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro path hpath hhist
  exact (hgood path hpath knownKernelReceiptHorizon
      (by norm_num [knownKernelReceiptHorizon, receiptHorizon])).trans_le
    (sharpStructuredRetrospectiveBoundary_le path hhist)

/-- Failure event for the aligned retrospective sharp receipt at a fixed true
persistence parameter. It records paths with the frozen histogram on which
the displayed risk conclusion would fail. -/
def sharpStructuredRetrospectiveFailureEvent
    (gamma : PersistenceParameter) : Set (ℕ → Observation) :=
  {path | HasReceiptSuffixEdgeHistogram path ∧
    ¬stationaryTargetPolicyPosteriorRisk
        (refreshEnvironment gamma)
        queueHypothesisTargetPolicy
        (queueHypothesisStationary (refreshEnvironment gamma))
        queueHypothesisScore knownKernelSelectedPosterior <
      (sharpStructuredRetrospectivePrimaryUpper : ℝ)}

/-- For each fixed admissible persistence parameter, under the path law started
at `knownKernelReceiptInitial = (action = 1, state = 1)`, the outer mass of the
paths on which the frozen aligned histogram is observed while the displayed
sharp risk bound fails is at most `1 / 20`. This removes good-event membership
from the public receipt conclusion; it is unconditional under the fixed-initial
refresh-family path law in the outer-mass sense, not coverage conditional on
observing that histogram. No measurability claim for this failure set is made
here. -/
theorem sharpStructuredRetrospectiveFailureEvent_mass_le
    (gamma : PersistenceParameter) :
    (controlledTrajectoryMeasure
        (refreshEnvironment gamma)
        (markovBehaviorPolicyAsHistory behaviorPolicy)
        knownKernelReceiptInitial).real
      (sharpStructuredRetrospectiveFailureEvent gamma) ≤ 1 / 20 := by
  rcases exists_controlledQueueSharpStructuredRetrospective_event gamma with
    ⟨goodEvent, hmass, hgood⟩
  apply (measureReal_mono ?_).trans hmass
  intro path hfailure
  simp only [sharpStructuredRetrospectiveFailureEvent,
    Set.mem_setOf_eq] at hfailure
  simp only [Set.mem_compl_iff]
  intro hpath
  exact hfailure.2 (hgood path hpath hfailure.1)

end

end FormalSLT.Applications.ControlledQueue
