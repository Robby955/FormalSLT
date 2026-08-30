/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.GJPBrierMonitorReplayPathDataBase
import FormalSLT.StochasticDynamics.FiniteTrajectoryCountableSleepingStrategyOrdinaryRiskPACBayes

/-!
# Compact countable-strategy certificate for the GJP Brier monitor

This module instantiates the countable sleeping-strategy ordinary-risk theorem
with a now-fixed constant tilt `1 / 2` and the exact summaries of the
175-observation GJP replay.  Lean checks the statistical theorem specialization
and the arithmetic from those summaries.  A separate replay checker must
derive the summaries from the hash-bound, quantized input stream; this compact
module does not verify that checker's execution or the source hashes.

This is a retrospective application of the newer countable-strategy theorem.
It is not the preregistered GJP endpoint: the original protocol allocated wake
time and geometric tilt separately, whereas this different catalog fixes the
half tilt at every integer wake and the reporting posterior selects wake zero.
The resulting fixed-catalog expression contains `log 320` rather than the
original `log 640`.  It does not replace the preregistered endpoint or provide
prospective error control for choosing this catalog after seeing the data.

The target is posterior-averaged conditional Brier loss encountered on the
monitored prefix.  It is not future, population, stationary, or deployment
risk.  The preregistered scientific comparison remains a separate `FAIL`.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
open scoped BigOperators

namespace FormalSLT.Applications.GJPBrierMonitorCountableStrategyCertificate

open FormalSLT.StochasticDynamics
open GJPBrierMonitorReplayData
open GJPBrierMonitorReplayReceipt
open GJPBrierMonitorReplayPathData

noncomputable section

abbrev Model := GJPBrierMonitorReplayData.Model

/-- Every atom in the now-fixed catalog uses the legal constant tilt `1 / 2`;
the countable master supplies the atom-dependent sleeping time. -/
def halfTiltStrategy (_j : Nat) : TrajectoryPredictableTilt Bool :=
  fun _n _u => 1 / 2

/-- The first active strategy atom at the 175-observation reporting time. -/
def firstAtom : Fin horizon :=
  ⟨0, by norm_num [horizon]⟩

/-- Reporting posterior concentrated on the predeclared atom that was awake
from time zero. -/
def firstAtomPosterior (j : Fin horizon) : Real :=
  if j = firstAtom then 1 else 0

theorem halfTiltStrategy_mem_Icc :
    ∀ j n u, halfTiltStrategy j n u ∈ Set.Icc (0 : Real) (1 / 2) := by
  intro j n u
  norm_num [halfTiltStrategy]

theorem firstAtomPosterior_isPMF : IsPMF firstAtomPosterior := by
  refine ⟨?_, ?_⟩
  · intro j
    by_cases h : j = firstAtom <;> simp [firstAtomPosterior, h]
  · simp [firstAtomPosterior]

theorem firstAtomPosterior_kl_eq_log_two :
    klDiv (liftPolynomialActivePosterior firstAtomPosterior)
        (polynomialActiveTailPrior horizon) = Real.log 2 := by
  rw [klDiv_liftPolynomialActivePosterior]
  simp [firstAtomPosterior, firstAtom, polynomialEpochWeight, horizon]

private theorem receipt_log_two_lt_6932_tenThousandths :
    Real.log 2 < (6932 : Real) / 10000 := by
  have habs : |(1 / 2 : Real)| = 1 / 2 := by norm_num
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 2 : Real)| < 1 by norm_num) 70
  rw [habs, show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num,
    one_div (2 : Real), Real.log_inv, ← sub_eq_add_neg,
    _root_.abs_sub_comm] at h
  have hupper := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ] at hupper ⊢
  linarith

private theorem selectedPosterior_term00_nonpos :
    selectedPosterior (false, false) *
        Real.log (selectedPosterior (false, false) /
          uniformPrior (false, false)) ≤ 0 := by
  have hp : 0 ≤ selectedPosterior (false, false) :=
    selectedPosterior_isPMF.nonneg _
  have hlog :
      Real.log (selectedPosterior (false, false) /
        uniformPrior (false, false)) ≤ 0 := by
    apply Real.log_nonpos
    · norm_num [selectedPosterior, posteriorQ, uniformPrior]
    · norm_num [selectedPosterior, posteriorQ, uniformPrior]
  exact mul_nonpos_of_nonneg_of_nonpos hp hlog

private theorem selectedPosterior_term01_nonpos :
    selectedPosterior (false, true) *
        Real.log (selectedPosterior (false, true) /
          uniformPrior (false, true)) ≤ 0 := by
  have hp : 0 ≤ selectedPosterior (false, true) :=
    selectedPosterior_isPMF.nonneg _
  have hlog :
      Real.log (selectedPosterior (false, true) /
        uniformPrior (false, true)) ≤ 0 := by
    apply Real.log_nonpos
    · norm_num [selectedPosterior, posteriorQ, uniformPrior]
    · norm_num [selectedPosterior, posteriorQ, uniformPrior]
  exact mul_nonpos_of_nonneg_of_nonpos hp hlog

private theorem selectedPosterior_term10_lt :
    selectedPosterior (true, false) *
        Real.log (selectedPosterior (true, false) /
          uniformPrior (true, false)) <
      ((507 : Real) / 1000) * ((7072 : Real) / 10000) := by
  let p : Real := selectedPosterior (true, false)
  have hp : 0 < p := selectedPosterior_pos _
  have hp507 : p < (507 : Real) / 1000 := by
    norm_num [p, selectedPosterior, posteriorQ]
  have hratio :
      p / uniformPrior (true, false) = 2 * (2 * p) := by
    norm_num [uniformPrior]
    ring
  have hlogSplit :
      Real.log (p / uniformPrior (true, false)) =
        Real.log 2 + Real.log (2 * p) := by
    rw [hratio, Real.log_mul (by norm_num) (by positivity)]
  have hlogTangent := Real.log_le_sub_one_of_pos (show 0 < 2 * p by positivity)
  have hsubUpper : 2 * p - 1 < (14 : Real) / 1000 := by
    norm_num [p, selectedPosterior, posteriorQ]
  have hlogTwiceP : Real.log (2 * p) < (14 : Real) / 1000 :=
    hlogTangent.trans_lt hsubUpper
  have hlogUpper :
      Real.log (p / uniformPrior (true, false)) <
        (7072 : Real) / 10000 := by
    rw [hlogSplit]
    have hlogTwo := receipt_log_two_lt_6932_tenThousandths
    linarith
  have hlogNonneg :
      0 ≤ Real.log (p / uniformPrior (true, false)) := by
    apply Real.log_nonneg
    rw [hratio]
    norm_num [p, selectedPosterior, posteriorQ]
  calc
    p * Real.log (p / uniformPrior (true, false)) ≤
        ((507 : Real) / 1000) *
          Real.log (p / uniformPrior (true, false)) :=
      mul_le_mul_of_nonneg_right hp507.le hlogNonneg
    _ < ((507 : Real) / 1000) * ((7072 : Real) / 10000) :=
      mul_lt_mul_of_pos_left hlogUpper (by norm_num)

private theorem selectedPosterior_term11_lt :
    selectedPosterior (true, true) *
        Real.log (selectedPosterior (true, true) /
          uniformPrior (true, true)) <
      ((492 : Real) / 1000) * ((6932 : Real) / 10000) := by
  let p : Real := selectedPosterior (true, true)
  have hp : 0 < p := selectedPosterior_pos _
  have hp492 : p < (492 : Real) / 1000 := by
    norm_num [p, selectedPosterior, posteriorQ]
  have hratio : p / uniformPrior (true, true) = 2 * (2 * p) := by
    norm_num [uniformPrior]
    ring
  have hsmall : 2 * p ≤ 1 := by
    norm_num [p, selectedPosterior, posteriorQ]
  have hlogSmall : Real.log (2 * p) ≤ 0 :=
    Real.log_nonpos (by positivity) hsmall
  have hlogSplit :
      Real.log (p / uniformPrior (true, true)) =
        Real.log 2 + Real.log (2 * p) := by
    rw [hratio, Real.log_mul (by norm_num) (by positivity)]
  have hlogUpper :
      Real.log (p / uniformPrior (true, true)) <
        (6932 : Real) / 10000 := by
    rw [hlogSplit]
    linarith [receipt_log_two_lt_6932_tenThousandths]
  have hlogNonneg :
      0 ≤ Real.log (p / uniformPrior (true, true)) := by
    apply Real.log_nonneg
    rw [hratio]
    norm_num [p, selectedPosterior, posteriorQ]
  calc
    p * Real.log (p / uniformPrior (true, true)) ≤
        ((492 : Real) / 1000) *
          Real.log (p / uniformPrior (true, true)) :=
      mul_le_mul_of_nonneg_right hp492.le hlogNonneg
    _ < ((492 : Real) / 1000) * ((6932 : Real) / 10000) :=
      mul_lt_mul_of_pos_left hlogUpper (by norm_num)

/-- The exact GJP model posterior costs less than `0.7` nats relative to the
uniform four-model prior. -/
theorem selectedPosterior_kl_lt_seven_tenths :
    klDiv selectedPosterior uniformPrior < (7 : Real) / 10 := by
  unfold klDiv
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have h00 := selectedPosterior_term00_nonpos
  have h01 := selectedPosterior_term01_nonpos
  have h10 := selectedPosterior_term10_lt
  have h11 := selectedPosterior_term11_lt
  linarith

private theorem halfTilt_effectiveWeight_eq (x : Nat → Bool) (k : Nat) :
    finiteStrategyPosteriorEffectiveTrajectoryWeight firstAtomPosterior
        (fun j : Fin horizon =>
          countableSleepingTrajectoryStrategy halfTiltStrategy j.1)
        k x = (1 / 2 : Real) := by
  classical
  unfold finiteStrategyPosteriorEffectiveTrajectoryWeight posteriorAverage
  rw [Finset.sum_eq_single firstAtom]
  · simp [firstAtomPosterior, firstAtom, countableSleepingTrajectoryStrategy,
      observedTrajectoryPredictableTilt, halfTiltStrategy]
  · intro j _hj hne
    simp [firstAtomPosterior, hne]
  · simp

theorem halfTilt_exposure_eq (x : Nat → Bool) :
    finiteTrajectoryCountableSleepingStrategyExposure
        halfTiltStrategy firstAtomPosterior x =
      (1 / 2 : Real) * horizon := by
  unfold finiteTrajectoryCountableSleepingStrategyExposure
    finiteStrategyPosteriorSleepingExposure
  simp_rw [halfTilt_effectiveWeight_eq x]
  norm_num [horizon]

theorem halfTilt_uniformDiscrepancy_eq_zero (x : Nat → Bool) :
      finiteTrajectoryCountableSleepingStrategyUniformDiscrepancy
        halfTiltStrategy firstAtomPosterior x = 0 := by
  have hexposure :
      finiteStrategyPosteriorSleepingExposure firstAtomPosterior
          (fun j : Fin horizon =>
            countableSleepingTrajectoryStrategy halfTiltStrategy j.1)
          0 horizon x = (1 / 2 : Real) * horizon := by
    simpa [finiteTrajectoryCountableSleepingStrategyExposure] using
      halfTilt_exposure_eq x
  unfold finiteTrajectoryCountableSleepingStrategyUniformDiscrepancy
    finiteStrategyPosteriorSleepingUniformDiscrepancy
    finiteUniformNormalizedWeightDiscrepancy
  simp_rw [halfTilt_effectiveWeight_eq x]
  rw [hexposure]
  norm_num [horizon]

theorem halfTilt_quadraticPenalty_eq (x : Nat → Bool) :
    finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
        monitorBrierScore halfTiltStrategy selectedPosterior
        firstAtomPosterior x =
      forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
          monitorBrierScore selectedPosterior 0 horizon x := by
  unfold finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
    trajectoryPredictableStrategyPosteriorQuadraticPenalty
    trajectoryPredictableTiltPosteriorQuadraticPenalty
    forwardPredictableTiltPosteriorQuadraticPenalty
    finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
    posteriorAverage modelStrategyProductPrior
    finiteTrajectoryActiveSleepingStrategyCatalog
    countableSleepingTrajectoryStrategy
    observedTrajectoryPredictableTilt
    halfTiltStrategy firstAtomPosterior firstAtom
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  simp
  apply Finset.sum_congr rfl
  intro model _hmodel
  apply Finset.sum_congr rfl
  intro k _hk
  ring

private theorem log_threeHundredTwenty_eq :
    Real.log 320 = 6 * Real.log 2 + Real.log 5 := by
  calc
    Real.log 320 = Real.log ((2 : Real) ^ 6 * 5) := by norm_num
    _ = Real.log ((2 : Real) ^ 6) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by norm_num)]
    _ = 6 * Real.log 2 + Real.log 5 := by
      rw [Real.log_pow]
      norm_num

private theorem log_threeHundredTwenty_lt_fiveHundredSeventySeven_hundredths :
    Real.log 320 < (577 : Real) / 100 := by
  rw [log_threeHundredTwenty_eq]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem psi_half_eq :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) =
      Real.log 2 - 1 / 2 := by
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num]
  rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  ring

private theorem psi_half_lt_1932_tenThousandths :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) <
      (1932 : Real) / 10000 := by
  rw [psi_half_eq]
  linarith [receipt_log_two_lt_6932_tenThousandths]

private theorem tracked_quadraticVariation_lt_3821_thousandths :
    (suffixPredictorQuadraticVariation : Real) <
      (3821 : Real) / 1000 := by
  norm_num [suffixPredictorQuadraticVariation]

private theorem tracked_psi_mul_quadraticVariation_lt_739_thousandths :
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        (suffixPredictorQuadraticVariation : Real) <
      (739 : Real) / 1000 := by
  have hpsi0 : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 2 : Real) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (suffixPredictorQuadraticVariation : Real) :=
    tracked_quadraticVariation_nonneg
  calc
    forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        (suffixPredictorQuadraticVariation : Real) ≤
      ((1932 : Real) / 10000) *
        (suffixPredictorQuadraticVariation : Real) :=
      mul_le_mul_of_nonneg_right psi_half_lt_1932_tenThousandths.le hq0
    _ < ((1932 : Real) / 10000) * ((3821 : Real) / 1000) :=
      mul_lt_mul_of_pos_left tracked_quadraticVariation_lt_3821_thousandths
        (by norm_num)
    _ < (739 : Real) / 1000 := by norm_num

/-- Exact summary expression for the retrospective combined-strategy
certificate. -/
def countableStrategySummaryEndpoint : Real :=
  (posteriorEmpiricalBrierRisk : Real) +
    (klDiv selectedPosterior uniformPrior + Real.log 320 +
      forwardEmpiricalBernsteinPsi (1 / 2 : Real) *
        (suffixPredictorQuadraticVariation : Real)) /
      ((1 / 2 : Real) * horizon)

/-- Kernel-checked endpoint arithmetic from the replay summaries. -/
theorem countableStrategySummaryEndpoint_lt_oneHundredThirtyOne_thousandths :
    countableStrategySummaryEndpoint < (131 : Real) / 1000 := by
  unfold countableStrategySummaryEndpoint
  have hemp := tracked_empiricalBrierRisk_lt_fortyEight_thousandths
  have hkl := selectedPosterior_kl_lt_seven_tenths
  have hlog :=
    log_threeHundredTwenty_lt_fiveHundredSeventySeven_hundredths
  have hquad := tracked_psi_mul_quadraticVariation_lt_739_thousandths
  norm_num [horizon] at ⊢
  nlinarith

private theorem log_two_add_log_oneHundredSixty_eq_log_threeHundredTwenty :
    Real.log 2 + Real.log 160 = Real.log 320 := by
  rw [← Real.log_mul (by norm_num : (2 : Real) ≠ 0)
    (by norm_num : (160 : Real) ≠ 0)]
  norm_num

/-- Composition from two supplied summary bindings to the exact boundary
checked above. These premises are the explicit trust boundary: this compact
module neither derives them from raw rows nor verifies a replay-checker PASS.
The existing full Lean row replay can discharge them at substantially greater
certificate size. -/
theorem replay_countableBoundary_eq_summary
    (hempirical :
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (posteriorEmpiricalBrierRisk : Real))
    (hquadratic :
      finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (suffixPredictorQuadraticVariation : Real)) :
    finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
        uniformPrior selectedPosterior monitorBrierScore halfTiltStrategy
        firstAtomPosterior ((1 : Real) / 160) replayPath =
      countableStrategySummaryEndpoint := by
  unfold finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
    countableStrategySummaryEndpoint
  rw [hempirical, firstAtomPosterior_kl_eq_log_two,
    halfTilt_quadraticPenalty_eq replayPath, hquadratic,
    halfTilt_exposure_eq replayPath,
    halfTilt_uniformDiscrepancy_eq_zero replayPath]
  norm_num
  rw [add_assoc]
  rw [log_two_add_log_oneHundredSixty_eq_log_threeHundredTwenty]

/-- Conditional replay endpoint.  Statistical confidence comes from the
coverage event below; realized good-event membership is not asserted. -/
theorem replay_conditionalRisk_lt_oneHundredThirtyOne_thousandths_of_summary
    {conditionalRisk : Real}
    (hempirical :
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (posteriorEmpiricalBrierRisk : Real))
    (hquadratic :
      finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (suffixPredictorQuadraticVariation : Real))
    (hgood : conditionalRisk <
      finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
        uniformPrior selectedPosterior monitorBrierScore halfTiltStrategy
        firstAtomPosterior ((1 : Real) / 160) replayPath) :
    conditionalRisk < (131 : Real) / 1000 := by
  rw [replay_countableBoundary_eq_summary hempirical hquadratic] at hgood
  exact hgood.trans
    countableStrategySummaryEndpoint_lt_oneHundredThirtyOne_thousandths

/-! ## Statistical coverage event -/

/-- The exact coverage event for a supplied history-dependent Boolean kernel.
It contains no deterministic assertion that the realized GJP path is good. -/
def replayCountableStrategyRiskEvent
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real) :
    Set (Nat → Bool) :=
  {x | finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
      P monitorBrierScore selectedPosterior 0 horizon x <
    finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
      uniformPrior selectedPosterior monitorBrierScore halfTiltStrategy
      firstAtomPosterior ((1 : Real) / 160) x}

/-- For this now-fixed wake catalog, the certificate event fails with outer
mass at most `1 / 160` for every supplied finite Boolean trajectory kernel.
This does not account for retrospective selection among different catalogs. -/
theorem replayCountableStrategyRiskEvent_failureMass_le
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real)
    (hP : ∀ n u, IsPMF (P n u)) :
    (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        (replayCountableStrategyRiskEvent P)ᶜ ≤ (1 : Real) / 160 := by
  rcases
      exists_finiteTrajectoryCountableSleepingStrategyPACBayes_ordinaryPrefixRisk_event
        (finiteTrajectoryKernel P hP) false monitorBrierScore_mem_Icc
        (strategy := halfTiltStrategy) (L := (1 : Real) / 2)
        (by norm_num) halfTiltStrategy_mem_Icc
        uniformPrior_isFullSupportPMF
        (delta := (1 : Real) / 160) (by norm_num) with
    ⟨goodEvent, hmass, hgood⟩
  have hsubset : goodEvent ⊆ replayCountableStrategyRiskEvent P := by
    intro x hx
    have hbound := hgood x hx horizon (by norm_num [horizon])
      selectedPosterior selectedPosterior_isPMF
      firstAtomPosterior firstAtomPosterior_isPMF
      (by rw [halfTilt_exposure_eq x]; positivity)
    rw [finiteTrajectoryPosteriorAverageConditionalSuffixRisk_finiteTrajectoryKernel
      P hP] at hbound
    exact hbound
  calc
    (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        (replayCountableStrategyRiskEvent P)ᶜ ≤
      (trajectoryMeasure (finiteTrajectoryKernel P hP) false).real
        goodEventᶜ := by
          refine measureReal_mono ?_ (by finiteness)
          exact Set.compl_subset_compl.mpr hsubset
    _ ≤ (1 : Real) / 160 := hmass

/-- Conditional named-path result at the external summary-binding boundary.
The failure-mass theorem above supplies coverage; this theorem does not assert
realized good-event membership. -/
theorem replayPath_conditionalRisk_lt_oneHundredThirtyOne_thousandths
    (P : (n : Nat) → ((i : Finset.Iic n) → Bool) → Bool → Real)
    (_hP : ∀ n u, IsPMF (P n u))
    (hpath : replayPath ∈ replayCountableStrategyRiskEvent P)
    (hempirical :
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (posteriorEmpiricalBrierRisk : Real))
    (hquadratic :
      finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
          monitorBrierScore selectedPosterior 0 horizon replayPath =
        (suffixPredictorQuadraticVariation : Real)) :
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        P monitorBrierScore selectedPosterior 0 horizon replayPath <
      (131 : Real) / 1000 := by
  exact replay_conditionalRisk_lt_oneHundredThirtyOne_thousandths_of_summary
    hempirical hquadratic hpath

end

end FormalSLT.Applications.GJPBrierMonitorCountableStrategyCertificate
