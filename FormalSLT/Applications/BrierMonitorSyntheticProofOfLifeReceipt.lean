/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeData
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingSuffixVarianceOracle

/-!
# Checked arithmetic for the synthetic Brier-monitor receipt

This module reconstructs the selected Brier-loss sequence from the declared
two-segment forecasts and outcomes.  It proves the empirical loss and
forward-predictor quadratic variation recorded by the generated receipt,
checks the tracked rational endpoint and selection margin, and connects the
supported geometric atom to the exact finite-prefix selector.

The final statistical statement remains conditional on a good-event
inequality supplied by the sleeping suffix-variance theorem.  Nothing here
proves that this named synthetic path belongs to that theorem-produced event.
-/

open Finset
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle
open scoped BigOperators

namespace FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeReceipt

open FormalSLT.StochasticDynamics

noncomputable section

private abbrev receiptHorizon : Nat :=
  BrierMonitorSyntheticProofOfLifeData.horizon

/-! ## Declared synthetic stream -/

/-- Both tracked stream segments have binary outcome one. -/
def declaredOutcomeQ (_k : Nat) : Rat := 1

/-- The first model always forecasts `3/4`.  The second forecasts `1/4` at
time zero and `3/4` on the remaining 511 observations. -/
def declaredPredictionQ (model : Bool) (k : Nat) : Rat :=
  if model then 3 / 4 else if k = 0 then 1 / 4 else 3 / 4

/-- Brier loss reconstructed from a declared forecast and outcome. -/
def declaredBrierLossQ (model : Bool) (k : Nat) : Rat :=
  (declaredPredictionQ model k - declaredOutcomeQ k) ^ 2

theorem declared_first_segment_predictions :
    declaredPredictionQ true 0 = 3 / 4 ∧
      declaredPredictionQ false 0 = 1 / 4 ∧
      declaredOutcomeQ 0 = 1 := by
  norm_num [declaredPredictionQ, declaredOutcomeQ]

theorem declared_second_segment_predictions (k : Nat) :
    declaredPredictionQ true (k + 1) = 3 / 4 ∧
      declaredPredictionQ false (k + 1) = 3 / 4 ∧
      declaredOutcomeQ (k + 1) = 1 := by
  norm_num [declaredPredictionQ, declaredOutcomeQ]

/-- The selected first model incurs exact Brier loss `1/16` on every declared
observation.  This is derived from `3/4` and outcome one. -/
theorem declaredSelectedBrierLossQ_eq (k : Nat) :
    declaredBrierLossQ true k = 1 / 16 := by
  norm_num [declaredBrierLossQ, declaredPredictionQ, declaredOutcomeQ]

/-- Rational prefix-mean predictor with the same `1/2` seed as
`forwardPredictor`. -/
def declaredForwardPredictorQ (k : Nat) : Rat :=
  if k = 0 then 1 / 2
  else
    (∑ i ∈ Finset.range k, declaredBrierLossQ true i) / (k : Rat)

theorem declaredForwardPredictorQ_zero :
    declaredForwardPredictorQ 0 = 1 / 2 := by
  norm_num [declaredForwardPredictorQ]

theorem declaredForwardPredictorQ_eq {k : Nat} (hk : 0 < k) :
    declaredForwardPredictorQ k = 1 / 16 := by
  have hkq : (k : Rat) ≠ 0 := by exact_mod_cast hk.ne'
  simp [declaredForwardPredictorQ, hk.ne', declaredSelectedBrierLossQ_eq,
    hkq]

/-- Empirical Brier risk recomputed from the declared selected forecasts and
outcomes. -/
def declaredEmpiricalBrierRiskQ : Rat :=
  (∑ k ∈ Finset.range receiptHorizon, declaredBrierLossQ true k) /
    (receiptHorizon : Rat)

theorem declaredEmpiricalBrierRiskQ_eq :
    declaredEmpiricalBrierRiskQ =
      BrierMonitorSyntheticProofOfLifeData.posteriorEmpiricalBrierRisk := by
  norm_num [declaredEmpiricalBrierRiskQ, receiptHorizon,
    declaredSelectedBrierLossQ_eq,
    BrierMonitorSyntheticProofOfLifeData.posteriorEmpiricalBrierRisk,
    BrierMonitorSyntheticProofOfLifeData.horizon]

/-- Raw observable suffix variation recomputed from the selected loss
sequence. -/
def declaredSuffixPredictorQuadraticVariationQ : Rat :=
  ∑ k ∈ Finset.range receiptHorizon,
    (declaredBrierLossQ true k - declaredForwardPredictorQ k) ^ 2

private theorem declaredQuadraticTermQ_eq (k : Nat) :
    (declaredBrierLossQ true k - declaredForwardPredictorQ k) ^ 2 =
      if k = 0 then 49 / 256 else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num [declaredSelectedBrierLossQ_eq, declaredForwardPredictorQ_zero]
  · rw [if_neg hk, declaredSelectedBrierLossQ_eq,
      declaredForwardPredictorQ_eq (Nat.pos_of_ne_zero hk)]
    ring

theorem declaredSuffixPredictorQuadraticVariationQ_eq :
    declaredSuffixPredictorQuadraticVariationQ =
      BrierMonitorSyntheticProofOfLifeData.suffixPredictorQuadraticVariation := by
  unfold declaredSuffixPredictorQuadraticVariationQ
  calc
    (∑ k ∈ Finset.range receiptHorizon,
        (declaredBrierLossQ true k - declaredForwardPredictorQ k) ^ 2) =
        ∑ k ∈ Finset.range receiptHorizon,
          if k = 0 then (49 / 256 : Rat) else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact declaredQuadraticTermQ_eq k
    _ = BrierMonitorSyntheticProofOfLifeData.suffixPredictorQuadraticVariation := by
      rw [Finset.sum_eq_single 0]
      · norm_num [BrierMonitorSyntheticProofOfLifeData.suffixPredictorQuadraticVariation]
      · intro k _hk hk0
        simp [hk0]
      · simp [receiptHorizon, BrierMonitorSyntheticProofOfLifeData.horizon]

/-! ## Real-valued theorem inputs reconstructed from the same declarations -/

def declaredPath (_k : Nat) : Bool := true

def declaredBrierScore (model : Bool) : TrajectoryScore Bool :=
  fun k _prefix outcome =>
    ((declaredPredictionQ model k : Real) - if outcome then 1 else 0) ^ 2

def uniformPrior (_model : Bool) : Real := 1 / 2

def selectedPosterior (model : Bool) : Real := if model then 1 else 0

theorem observed_selectedBrierLoss_eq (k : Nat) :
    observedTrajectoryScore (declaredBrierScore true) k declaredPath =
      (1 : Real) / 16 := by
  norm_num [observedTrajectoryScore, declaredBrierScore, declaredPath,
    declaredPredictionQ]

theorem selectedBrier_forwardPredictor_eq {k : Nat} (hk : 0 < k) :
    forwardPredictorProcess
        (observedTrajectoryScore (declaredBrierScore true)) k declaredPath =
      (1 : Real) / 16 := by
  simp [forwardPredictorProcess, forwardPredictor, hk.ne', forwardPrefixMean,
    observed_selectedBrierLoss_eq]

theorem selectedPosterior_kl_eq_log_two :
    klDiv selectedPosterior uniformPrior = Real.log 2 := by
  unfold klDiv
  rw [Fintype.sum_bool]
  norm_num [selectedPosterior, uniformPrior]

theorem selected_empiricalSuffixRisk_eq :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        declaredBrierScore selectedPosterior 0 512 declaredPath =
      (1 : Real) / 16 := by
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk posteriorAverage
  rw [Fintype.sum_bool]
  simp [selectedPosterior, observed_selectedBrierLoss_eq]

private theorem selectedQuadraticTerm_eq (k : Nat) :
    (observedTrajectoryScore (declaredBrierScore true) k declaredPath -
        forwardPredictorProcess
          (observedTrajectoryScore (declaredBrierScore true)) k declaredPath) ^ 2 =
      if k = 0 then (49 : Real) / 256 else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num [observed_selectedBrierLoss_eq, forwardPredictorProcess,
      forwardPredictor]
  · rw [if_neg hk, observed_selectedBrierLoss_eq,
      selectedBrier_forwardPredictor_eq (Nat.pos_of_ne_zero hk)]
    ring

set_option maxRecDepth 10000 in
theorem selected_suffixPredictorQuadraticVariation_eq :
    finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
        declaredBrierScore selectedPosterior 0 512 declaredPath =
      (49 : Real) / 256 := by
  unfold finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation posteriorAverage
  rw [Fintype.sum_bool]
  simp only [selectedPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  rw [add_zero]
  rw [Nat.Ico_zero_eq_range]
  calc
    (∑ k ∈ Finset.range 512,
        (observedTrajectoryScore (declaredBrierScore true) k declaredPath -
          forwardPredictorProcess
            (observedTrajectoryScore (declaredBrierScore true)) k declaredPath) ^ 2) =
        ∑ k ∈ Finset.range 512,
          if k = 0 then (49 / 256 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact selectedQuadraticTerm_eq k
    _ = (49 : Real) / 256 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro k _hk hk0
        simp [hk0]
      · simp

theorem tracked_empiricalRisk_matches_reconstruction :
    (BrierMonitorSyntheticProofOfLifeData.posteriorEmpiricalBrierRisk : Real) =
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        declaredBrierScore selectedPosterior 0 512 declaredPath := by
  rw [selected_empiricalSuffixRisk_eq]
  norm_num [BrierMonitorSyntheticProofOfLifeData.posteriorEmpiricalBrierRisk]

theorem tracked_quadraticVariation_matches_reconstruction :
    (BrierMonitorSyntheticProofOfLifeData.suffixPredictorQuadraticVariation : Real) =
      finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
        declaredBrierScore selectedPosterior 0 512 declaredPath := by
  rw [selected_suffixPredictorQuadraticVariation_eq]
  norm_num [BrierMonitorSyntheticProofOfLifeData.suffixPredictorQuadraticVariation]

/-! ## Tracked rational checks -/

theorem trackedBoundaryUpper_lt_ninetyOneThousandths :
    BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper <
      (91 : Rat) / 1000 := by
  norm_num [BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper]

theorem trackedSelectionMargin_pos :
    0 < BrierMonitorSyntheticProofOfLifeData.exactSelectionMarginLower := by
  norm_num [BrierMonitorSyntheticProofOfLifeData.exactSelectionMarginLower]

/-! ## Supported atom and exact finite-prefix selector -/

private theorem receipt_log_two_lt :
    Real.log 2 < (6931471805599454 : Real) / 10000000000000000 := by
  have habs : |(1 / 2 : Real)| = 1 / 2 := by norm_num
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 2 : Real)| < 1 by norm_num) 70
  rw [habs, show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num,
    one_div (2 : Real), Real.log_inv, ← sub_eq_add_neg,
    _root_.abs_sub_comm] at h
  have hupper := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ] at hupper ⊢
  linarith

private theorem receipt_log_five_fourths_lt :
    Real.log (5 / 4 : Real) <
      (2231435513142098 : Real) / 10000000000000000 := by
  have habs : |(1 / 5 : Real)| = 1 / 5 := by norm_num
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 5 : Real)| < 1 by norm_num) 30
  have hlog : Real.log (4 / 5 : Real) = -Real.log (5 / 4 : Real) := by
    rw [show (4 / 5 : Real) = (5 / 4 : Real)⁻¹ by norm_num,
      Real.log_inv]
  rw [habs, show (1 - (1 / 5 : Real)) = 4 / 5 by norm_num,
    hlog, ← sub_eq_add_neg, _root_.abs_sub_comm] at h
  have hupper := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ] at hupper ⊢
  linarith

private theorem log_five_eq :
    Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4 : Real) := by
  calc
    Real.log 5 = Real.log ((4 : Real) * (5 / 4)) := by norm_num
    _ = Real.log 4 + Real.log (5 / 4 : Real) := by
      rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0)
        (by norm_num : (5 / 4 : Real) ≠ 0)]
    _ = 2 * Real.log 2 + Real.log (5 / 4 : Real) := by
      rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
      norm_num

private theorem psi_half_eq :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) =
      Real.log 2 - 1 / 2 := by
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num]
  rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  ring

private theorem log_sixHundredForty_eq :
    Real.log 640 = 7 * Real.log 2 + Real.log 5 := by
  calc
    Real.log 640 = Real.log ((2 : Real) ^ 7 * 5) := by norm_num
    _ = Real.log ((2 : Real) ^ 7) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by norm_num : (5 : Real) ≠ 0)]
    _ = 7 * Real.log 2 + Real.log 5 := by
      rw [Real.log_pow]
      norm_num

theorem supportedAtomBoundary_eq :
    finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        uniformPrior selectedPosterior declaredBrierScore
        (1 / 160 : Real) 0 0 512 declaredPath =
      (1 : Real) / 16 +
        (8 * Real.log 2 + Real.log 5 +
          (Real.log 2 - 1 / 2) * (49 / 256)) / 256 := by
  unfold finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
    geometricForwardBesselPACBayesComplexity
  dsimp
  rw [selected_empiricalSuffixRisk_eq,
    selected_suffixPredictorQuadraticVariation_eq,
    selectedPosterior_kl_eq_log_two]
  norm_num [continuousTrajectorySleepingSuffixEffectiveConfidence,
    polynomialEpochWeight, geometricForwardTilt]
  rw [psi_half_eq, log_sixHundredForty_eq]
  ring

/-- The existing high-precision log series close the actual real-valued
supported atom below the tracked rational upper endpoint. -/
theorem supportedAtomBoundary_lt_trackedUpper :
    finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        uniformPrior selectedPosterior declaredBrierScore
        (1 / 160 : Real) 0 0 512 declaredPath <
      (BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper : Real) := by
  rw [supportedAtomBoundary_eq, log_five_eq]
  have hlogTwo := receipt_log_two_lt
  have hlogFiveFourths := receipt_log_five_fourths_lt
  norm_num [BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper]
  nlinarith

theorem selectedBoundary_lt_trackedUpper :
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        uniformPrior selectedPosterior declaredBrierScore
        (1 / 160 : Real) 0 512 declaredPath <
      (BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper : Real) := by
  have hAtom : (0 : Nat) ∈ Finset.range
      (finiteTrajectorySleepingSuffixVarianceMaxIndex 0 512 + 1) := by
    simp
  exact lt_of_le_of_lt
    (finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le
      uniformPrior selectedPosterior declaredBrierScore
      (1 / 160 : Real) 0 512 declaredPath hAtom)
    supportedAtomBoundary_lt_trackedUpper

theorem selectedBoundary_lt_ninetyOneThousandths :
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        uniformPrior selectedPosterior declaredBrierScore
        (1 / 160 : Real) 0 512 declaredPath <
      (91 : Real) / 1000 := by
  exact selectedBoundary_lt_trackedUpper.trans
    (by
      norm_num [BrierMonitorSyntheticProofOfLifeData.selectedBoundaryUpper])

/-- Conditional receipt composition.  The premise is the good-event
inequality delivered by the statistical theorem; this module does not prove
that premise for `declaredPath`. -/
theorem conditionalRisk_lt_ninetyOneThousandths_of_goodEventInequality
    {conditionalRisk : Real}
    (hgood : conditionalRisk <
      finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        uniformPrior selectedPosterior declaredBrierScore
        (1 / 160 : Real) 0 512 declaredPath) :
    conditionalRisk < (91 : Real) / 1000 :=
  hgood.trans selectedBoundary_lt_ninetyOneThousandths

end

end FormalSLT.Applications.BrierMonitorSyntheticProofOfLifeReceipt
