/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadReceipt

/-!
# Matched baselines for the twenty-state random-refresh load model

This module records three comparisons for the deterministic balanced-path
receipt:

* a fixed unit-range Poisson construction;
* a fixed depth-five construction that does not pay for post-data depth
  selection; and
* a non-variance-adaptive fixed-tilt construction.

The three constructions use different corrected-score catalogs or confidence
allocations.  Their exceptional events are therefore declared separately.
No theorem in this file calls them same-event comparisons, and no theorem
asserts that the deterministic balanced path belongs to any good event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadBaselines

open RandomRefreshLoadModel RandomRefreshLoadPath RandomRefreshLoadReceipt

noncomputable section

attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000

/-! ## Fixed unit-range baseline -/

/-- The fixed-range comparison uses only the generic unit-range oscillation
bound, independently of the model-specific Brier oscillation calculation. -/
def fixedRangeD (_c : Candidate) : ℝ := 1

theorem fixedRangeD_nonneg (c : Candidate) : 0 ≤ fixedRangeD c := by
  norm_num [fixedRangeD]

theorem brierScore_centeredOscillation_le_fixedRange
    (c : Candidate) (i : Predictor) :
    finiteOscillation
        (centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
          (brierScore i)) ≤ fixedRangeD c := by
  simpa [fixedRangeD, candidateReference] using
    centeredMarkovRowRisk_finiteOscillation_le_one
      (refreshKernel c) (candidateReference c) (brierScore_mem_Icc i)

/-- Depth-five potential used by the fixed-range normalization. -/
def fixedRangePotential : Predictor → State → ℝ :=
  empiricalStationaryCatalogPotential refreshKernel candidateReference
    brierScore Candidate.nominal 5

/-- The generic unit-range span is `1 + 1/4 + ... + (1/4)^4`. -/
theorem fixedRangeSpan_eq :
    empiricalStationaryCatalogSpan refreshKernel fixedRangeD
        Candidate.nominal 5 = 341 / 256 := by
  norm_num [empiricalStationaryCatalogSpan,
    finiteDepthPoissonClosedSpanBound,
    refreshKernel_dobrushinCoefficient, candidateGamma, candidateGammaNN,
    fixedRangeD]

/-- The unit-range depth-five residual is `(1/4)^5`. -/
theorem fixedRangeResidual_eq :
    finiteDobrushinCoefficient (refreshKernel Candidate.nominal) ^ 5 *
        fixedRangeD Candidate.nominal = 1 / 1024 := by
  norm_num [refreshKernel_dobrushinCoefficient, candidateGamma,
    candidateGammaNN, fixedRangeD]

/-- Corrected transition score underlying the fixed-range catalog. -/
def fixedRangeCorrectedTransitionScore (i : Predictor) :
    MarkovTransitionScore State :=
  poissonCorrectedTransitionScore (341 / 256) (brierScore i)
    (fixedRangePotential i)

/-- Corrected trajectory score underlying the fixed-range catalog. -/
def fixedRangeCorrectedScore (i : Predictor) : TrajectoryScore State :=
  markovTransitionTrajectoryScore (fixedRangeCorrectedTransitionScore i)

theorem fixedRangeCorrectedScore_eq_catalog :
    fixedRangeCorrectedScore =
      empiricalStationaryCatalogCorrectedScore refreshKernel
        candidateReference brierScore fixedRangeD Candidate.nominal 5 := by
  funext i
  unfold fixedRangeCorrectedScore fixedRangeCorrectedTransitionScore
    empiricalStationaryCatalogCorrectedScore
  rw [fixedRangeSpan_eq]
  rfl

/-- The centered sum of squares scales quadratically under an affine change
of observations. -/
private theorem forwardBesselQ_affine
    (v : ℕ → ℝ) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    forwardBesselQ (fun k ↦ a * v k + b) n =
      a ^ 2 * forwardBesselQ v n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmean :
      forwardPrefixMean (fun k ↦ a * v k + b) n =
        a * forwardPrefixMean v n + b := by
    unfold forwardPrefixMean
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hn0]
  unfold forwardBesselQ
  rw [hmean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Changing only the valid range bound leaves the raw Poisson-corrected
numerator unchanged, so the fixed-range score is an affine transform of the
primary corrected score. -/
theorem fixedRangeCorrectedScore_affine_primary
    (i : Predictor) (k : ℕ) (x : ℕ → State) :
    observedTrajectoryScore (fixedRangeCorrectedScore i) k x =
      (7507 / 18760) * observedTrajectoryScore (receiptCorrectedScore i) k x +
        11253 / 37520 := by
  unfold observedTrajectoryScore fixedRangeCorrectedScore
    fixedRangeCorrectedTransitionScore receiptCorrectedScore
    empiricalStationaryCatalogCorrectedScore
    markovTransitionTrajectoryScore poissonCorrectedTrajectoryScore
    poissonCorrectedTransitionScore
  rw [receiptSpan_eq]
  change
    (brierScore i (x k) (x (k + 1)) +
          fixedRangePotential i (x (k + 1)) - fixedRangePotential i (x k) +
        341 / 256) /
        (1 + 2 * (341 / 256)) =
      7507 / 18760 *
          ((brierScore i (x k) (x (k + 1)) +
                fixedRangePotential i (x (k + 1)) -
              fixedRangePotential i (x k) + 2387 / 10240) /
            (1 + 2 * (2387 / 10240))) +
        11253 / 37520
  ring

/-- Exact fixed-range corrected-score Bessel statistic on the balanced path.
The proof reuses the checked primary statistic and the affine score identity,
avoiding a second 400-edge potential-table evaluation. -/
theorem balancedPath_fixedRangeCorrectedScoreBesselQ_eq :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (fixedRangeCorrectedScore Predictor.oracle) k balancedPath)
        receiptHorizon = 28914146385 / 28155008 := by
  rw [show
      (fun k ↦ observedTrajectoryScore
        (fixedRangeCorrectedScore Predictor.oracle) k balancedPath) =
      (fun k ↦ (7507 / 18760) *
          observedTrajectoryScore
            (receiptCorrectedScore Predictor.oracle) k balancedPath +
        11253 / 37520) by
    funext k
    exact fixedRangeCorrectedScore_affine_primary
      Predictor.oracle k balancedPath]
  rw [forwardBesselQ_affine _ _ _ (by norm_num [receiptHorizon]),
    balancedPath_correctedScoreBesselQ_eq]
  norm_num

/-- Exact first-branch upper bound for the fixed-range hybrid penalty. -/
theorem fixedRangeCorrectedPenalty_le :
    trajectoryPosteriorHybridBesselPenalty oraclePosterior
        fixedRangeCorrectedScore receiptHorizon balancedPath ≤
      86770594163 / 56310016 := by
  unfold trajectoryPosteriorHybridBesselPenalty oraclePosterior
  rw [pacBayesPosteriorAverage_dirac]
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (fixedRangeCorrectedScore Predictor.oracle) k balancedPath)
            receiptHorizon)
        ((receiptHorizon : ℝ) / ((receiptHorizon : ℝ) - 1) *
            forwardBesselQ
              (fun k ↦ observedTrajectoryScore
                (fixedRangeCorrectedScore Predictor.oracle) k balancedPath)
              receiptHorizon +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (receiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (fixedRangeCorrectedScore Predictor.oracle) k balancedPath)
          receiptHorizon := min_le_left _ _
    _ = 86770594163 / 56310016 := by
      rw [balancedPath_fixedRangeCorrectedScoreBesselQ_eq]
      norm_num

/-- The fixed-range comparison has its own catalog exceptional event. -/
def fixedRangeExceptionalEvent : Set (ℕ → State) :=
  empiricalStationaryCatalogExceptionalEvent
    (refreshKernel Candidate.nominal) refreshKernel candidateReference
      brierScore fixedRangeD candidateWeight predictorPrior riskFailureBudget

theorem fixedRangeExceptionalEvent_mass_le :
    (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
        fixedRangeExceptionalEvent ≤ riskFailureBudget := by
  exact empiricalStationaryCatalogExceptionalEvent_mass_le
    (refreshKernel Candidate.nominal) (0 : State)
    refreshKernel candidateReference brierScore_mem_Icc
    fixedRangeD_nonneg refreshKernel_dobrushinCoefficient_lt_one
    brierScore_centeredOscillation_le_fixedRange
    candidateWeight_isFullSupport predictorPrior_isFullSupport
    riskFailureBudget_pos

/-- Fixed-range trajectory term at geometric tilt `1/64`. -/
def fixedRangeTrajectoryBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  trajectoryCountableEmpiricalBernsteinPACBayesBoundary predictorPrior
    fixedRangeCorrectedScore oraclePosterior
    (riskFailureBudget * candidateWeight Candidate.nominal *
      polynomialForwardTiltWeight 5)
    5 n x

theorem balancedPath_fixedRangeTrajectoryBoundary_le :
    fixedRangeTrajectoryBoundary receiptHorizon balancedPath ≤
      4627610284403 / 709506201600000 := by
  unfold fixedRangeTrajectoryBoundary
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    predictorPrior fixedRangeCorrectedScore oraclePosterior
    (by norm_num [riskFailureBudget, candidateWeight, finiteUniformRealPMF,
      polynomialForwardTiltWeight,
      FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight])]
  have hpsiNonneg :
      0 ≤ forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) :=
    forwardEmpiricalBernsteinPsi_nonneg
      (geometricForwardTilt_pos 5).le (geometricForwardTilt_lt_one 5)
  have hproduct :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
          trajectoryPosteriorHybridBesselPenalty oraclePosterior
            fixedRangeCorrectedScore receiptHorizon balancedPath ≤
        (1 / 4032 : ℝ) * (86770594163 / 56310016) := by
    calc
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            trajectoryPosteriorHybridBesselPenalty oraclePosterior
              fixedRangeCorrectedScore receiptHorizon balancedPath ≤
          forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            (86770594163 / 56310016) :=
        mul_le_mul_of_nonneg_left fixedRangeCorrectedPenalty_le hpsiNonneg
      _ ≤ (1 / 4032 : ℝ) * (86770594163 / 56310016) := by
        apply mul_le_mul_of_nonneg_right
        · have hlam : geometricForwardTilt 5 = (1 / 64 : ℝ) := by
            norm_num [geometricForwardTilt]
          rw [hlam]
          exact receiptPsi_one_sixtyFour_le
        · norm_num
  have hcost := receiptRiskLogCost_le_twenty
  norm_num [geometricForwardTilt, receiptHorizon] at hproduct ⊢
  nlinarith

/-- Complete fixed-range known-kernel boundary. -/
def fixedRangeBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    brierScore fixedRangeD candidateWeight predictorPrior oraclePosterior
    riskFailureBudget 0 Candidate.nominal 5 5 n x

theorem balancedPath_fixedRangeBoundary_le :
    fixedRangeBoundary receiptHorizon balancedPath ≤
      4818000751859 / 193639219200000 := by
  have htrajectory := balancedPath_fixedRangeTrajectoryBoundary_le
  unfold fixedRangeBoundary empiricalStationaryCatalogBoundary
  rw [← fixedRangeCorrectedScore_eq_catalog]
  change
    (1 + 2 * empiricalStationaryCatalogSpan refreshKernel
        fixedRangeD Candidate.nominal 5) *
        fixedRangeTrajectoryBoundary receiptHorizon balancedPath +
      empiricalStationaryCatalogSpan refreshKernel fixedRangeD
          Candidate.nominal 5 / (receiptHorizon : ℝ) +
      finiteDobrushinCoefficient (refreshKernel Candidate.nominal) ^ 5 *
          fixedRangeD Candidate.nominal +
      2 * ((1 + empiricalStationaryCatalogSpan refreshKernel
          fixedRangeD Candidate.nominal 5) * 0) ≤
        4818000751859 / 193639219200000
  rw [fixedRangeSpan_eq, fixedRangeResidual_eq]
  norm_num [receiptHorizon] at htrajectory ⊢
  nlinarith

theorem balancedPath_fixedRangeRightHandSide_lt :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        fixedRangeBoundary receiptHorizon balancedPath <
      1749 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_fixedRangeBoundary_le]

/-- Outside its own event, the fixed-range construction is a valid
stationary-risk certificate at the displayed balanced path. -/
theorem balancedPath_fixedRange_certificate_of_not_mem
    (hx : balancedPath ∉ fixedRangeExceptionalEvent) :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw brierScore
        oraclePosterior <
      empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        fixedRangeBoundary receiptHorizon balancedPath := by
  let P := refreshKernel Candidate.nominal
  have hrowZero : ∀ z : State,
      finitePMFTotalVariation (P z) (refreshKernel Candidate.nominal z) ≤ 0 := by
    intro z
    simp [P, finitePMFTotalVariation]
  have h := empiricalStationaryCatalog_allPosteriors_of_not_mem
    P uniformLaw (uniformLaw_invariant Candidate.nominal)
    refreshKernel candidateReference brierScore_mem_Icc
    fixedRangeD_nonneg refreshKernel_dobrushinCoefficient_lt_one
    brierScore_centeredOscillation_le_fixedRange
    candidateWeight_isFullSupport predictorPrior_isFullSupport
    riskFailureBudget_pos hx Candidate.nominal 5 5
    (eta := 0) (by norm_num) hrowZero oraclePosterior
    (diracPosterior_isPMF Predictor.oracle) receiptHorizon
    (by norm_num [receiptHorizon])
  simpa [P, fixedRangeBoundary] using h

/-! ## A local Poisson transfer used by the fixed-depth comparisons -/

/-- Application-local transfer from a corrected-score trajectory inequality
to the original stationary-risk scale.  This lemma contains no probability
claim; its caller must supply an inequality obtained outside the caller's
named exceptional event. -/
theorem stationaryRisk_lt_empirical_add_of_corrected
    (potential : Predictor → State → ℝ)
    {B R w : ℝ} (hB : 0 ≤ B)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    (hR : 0 ≤ R)
    (hresidual : ∀ i z,
      |approximatePoissonResidual
        (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) (potential i) z| ≤ R)
    {n : ℕ} (hn : 0 < n) {x : ℕ → State}
    (hbase :
      trajectoryPosteriorAverageConditionalRisk
          (prefixKernel (refreshKernel Candidate.nominal))
          (fun i ↦ poissonCorrectedTrajectoryScore B
            (brierScore i) (potential i))
          oraclePosterior n x <
        trajectoryPosteriorEmpiricalPrequentialRisk
            (fun i ↦ poissonCorrectedTrajectoryScore B
              (brierScore i) (potential i))
            oraclePosterior n x + w) :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw brierScore
        oraclePosterior <
      empiricalTransitionPosteriorRisk brierScore oraclePosterior n x +
        (1 + 2 * B) * w + B / (n : ℝ) + R := by
  have hposterior : IsPMF oraclePosterior :=
    diracPosterior_isPMF Predictor.oracle
  have hden : 0 < 1 + 2 * B := by linarith
  rw [trajectoryPosteriorAverageConditionalRisk_poissonCorrected
      hB (refreshKernel Candidate.nominal) uniformLaw brierScore potential
      oraclePosterior hposterior n hn x,
    trajectoryPosteriorEmpiricalPrequentialRisk_poissonCorrected
      hB brierScore potential oraclePosterior hposterior n hn x] at hbase
  have hscaled := mul_lt_mul_of_pos_right hbase hden
  field_simp [ne_of_gt hden] at hscaled
  have hendpoint := posteriorPoissonEndpointCorrection_le
    hB hspan hposterior n hn x
  have hres := neg_posteriorPoissonResidualAverage_le
    (refreshKernel Candidate.nominal) uniformLaw brierScore potential
    (residualEnvelope := fun _i : Predictor ↦ R)
    (fun _i ↦ hR) hresidual hposterior n hn x
  have hposteriorResidual :
      posteriorAverage oraclePosterior (fun _i : Predictor ↦ R) = R := by
    unfold posteriorAverage
    rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
  rw [hposteriorResidual] at hres
  linarith

/-! ## Fixed depth without a depth-selection allocation -/

/-- The model-specific depth-five potential used in the primary receipt. -/
def primaryPotential : Predictor → State → ℝ :=
  empiricalStationaryCatalogPotential refreshKernel candidateReference
    brierScore Candidate.nominal 5

theorem receiptCorrectedScore_eq_primary :
    receiptCorrectedScore =
      fun i ↦ poissonCorrectedTrajectoryScore (2387 / 10240)
        (brierScore i) (primaryPotential i) := by
  funext i
  unfold receiptCorrectedScore empiricalStationaryCatalogCorrectedScore
    primaryPotential
  rw [receiptSpan_eq]

theorem primaryPotential_span (i : Predictor) (x y : State) :
    |primaryPotential i y - primaryPotential i x| ≤ 2387 / 10240 := by
  change
    |finiteDepthPoissonPotential
        (refreshKernel Candidate.nominal) uniformLaw (brierScore i) 5 y -
      finiteDepthPoissonPotential
        (refreshKernel Candidate.nominal) uniformLaw (brierScore i) 5 x| ≤
      2387 / 10240
  rw [← receiptSpan_eq]
  rw [show empiricalStationaryCatalogSpan refreshKernel
      candidateOscillation Candidate.nominal 5 =
      finiteDepthPoissonSpanBound
        (finiteDobrushinCoefficient (refreshKernel Candidate.nominal))
        (candidateOscillation Candidate.nominal) 5 by
    unfold empiricalStationaryCatalogSpan
    exact (finiteDepthPoissonSpanBound_closed
      (refreshKernel_dobrushinCoefficient_lt_one Candidate.nominal) 5).symm]
  exact finiteDepthPoissonPotential_span
    (refreshKernel Candidate.nominal) uniformLaw (brierScore i) 5
    (finiteDobrushinCoefficient_nonneg _)
    (finiteDobrushinCoefficient_isOscillationContraction _)
    (brierScore_centeredOscillation_le Candidate.nominal i) x y

theorem primaryPotential_residual (i : Predictor) (z : State) :
    |approximatePoissonResidual
        (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) (primaryPotential i) z| ≤ 7 / 40960 := by
  have h := finiteDepthPoissonResidual_le
    (refreshKernel Candidate.nominal) uniformLaw
    (uniformLaw_invariant Candidate.nominal) (brierScore i) 5
    (finiteDobrushinCoefficient_nonneg _)
    (finiteDobrushinCoefficient_isOscillationContraction _)
    (brierScore_centeredOscillation_le Candidate.nominal i) z
  rw [receiptDepthResidual_eq] at h
  simpa [primaryPotential, empiricalStationaryCatalogPotential,
    candidateReference] using h

/-- Removing only the depth allocation leaves candidate confidence `1/120`. -/
def fixedDepthRiskDelta : ℝ :=
  riskFailureBudget * candidateWeight Candidate.nominal

theorem fixedDepthRiskDelta_eq : fixedDepthRiskDelta = 1 / 120 := by
  have hcandidate : Fintype.card Candidate = 3 := by decide
  norm_num [fixedDepthRiskDelta, riskFailureBudget, candidateWeight,
    finiteUniformRealPMF, hcandidate]

private theorem baseline_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- Fixing the depth removes the polynomial depth-allocation price; the
remaining KL plus candidate and geometric-tilt cost is at most `15`. -/
theorem fixedDepthRiskLogCost_le_fifteen :
    klDiv oraclePosterior predictorPrior +
        Real.log
          ((((5 : ℝ) + 1) * ((5 : ℝ) + 2)) /
            fixedDepthRiskDelta) ≤ 15 := by
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have hpow : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [hpow]
    linarith [baseline_log_two_le_one]
  have hlog5040 : Real.log (5040 : ℝ) ≤ 13 := by
    have hmono : Real.log (5040 : ℝ) ≤ Real.log (8192 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hpow : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 13 using 1 <;> norm_num
    rw [hpow] at hmono
    linarith [baseline_log_two_le_one]
  rw [show predictorPrior = finiteUniformRealPMF Predictor by rfl]
  unfold oraclePosterior
  rw [klDiv_dirac_finiteUniformRealPMF]
  have hpredictor : Fintype.card Predictor = 4 := by decide
  rw [hpredictor, fixedDepthRiskDelta_eq]
  norm_num
  nlinarith

/-- Fixed-depth empirical-Bernstein event.  It is not the primary catalog
event because the depth-allocation factor has been removed. -/
def fixedDepthExceptionalEvent : Set (ℕ → State) :=
  trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
    (prefixKernel (refreshKernel Candidate.nominal)) predictorPrior
      receiptCorrectedScore fixedDepthRiskDelta

theorem fixedDepthExceptionalEvent_mass_le :
    (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
        fixedDepthExceptionalEvent ≤ fixedDepthRiskDelta := by
  have hmass :=
    trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
      (prefixKernel (refreshKernel Candidate.nominal)) (0 : State)
      receiptCorrectedScore_mem_Icc predictorPrior_isFullSupport
      (show 0 < fixedDepthRiskDelta by rw [fixedDepthRiskDelta_eq]; norm_num)
  simpa [fixedDepthExceptionalEvent,
    trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass

/-- The fixed-depth trajectory term at geometric tilt `1/64`. -/
def fixedDepthTrajectoryBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  trajectoryCountableEmpiricalBernsteinPACBayesBoundary predictorPrior
    receiptCorrectedScore oraclePosterior fixedDepthRiskDelta 5 n x

/-- Complete fixed-depth width, without a depth-selection confidence cost. -/
def fixedDepthBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  (7507 / 5120) * fixedDepthTrajectoryBoundary n x +
    (2387 / 10240) / (n : ℝ) + 7 / 40960

theorem balancedPath_fixedDepthTrajectoryBoundary_le :
    fixedDepthTrajectoryBoundary receiptHorizon balancedPath ≤
      15802087143053 / 2840294469600000 := by
  unfold fixedDepthTrajectoryBoundary
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    predictorPrior receiptCorrectedScore oraclePosterior
    (by rw [fixedDepthRiskDelta_eq]; norm_num)]
  have hpsiNonneg :
      0 ≤ forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) :=
    forwardEmpiricalBernsteinPsi_nonneg
      (geometricForwardTilt_pos 5).le (geometricForwardTilt_lt_one 5)
  have hproduct :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
          trajectoryPosteriorHybridBesselPenalty oraclePosterior
            receiptCorrectedScore receiptHorizon balancedPath ≤
        (1 / 4032 : ℝ) *
          (2168673688973 / 225420196) := by
    calc
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            trajectoryPosteriorHybridBesselPenalty oraclePosterior
              receiptCorrectedScore receiptHorizon balancedPath ≤
          forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            (2168673688973 / 225420196) :=
        mul_le_mul_of_nonneg_left receiptCorrectedPenalty_le_exact hpsiNonneg
      _ ≤ (1 / 4032 : ℝ) *
          (2168673688973 / 225420196) := by
        apply mul_le_mul_of_nonneg_right
        · have hlam : geometricForwardTilt 5 = (1 / 64 : ℝ) := by
            norm_num [geometricForwardTilt]
          rw [hlam]
          exact receiptPsi_one_sixtyFour_le
        · norm_num
  have hcost := fixedDepthRiskLogCost_le_fifteen
  norm_num [geometricForwardTilt, receiptHorizon] at hproduct ⊢
  nlinarith

theorem balancedPath_fixedDepthBoundary_le :
    fixedDepthBoundary receiptHorizon balancedPath ≤
      16135403663387 / 1937166336000000 := by
  have htrajectory := balancedPath_fixedDepthTrajectoryBoundary_le
  unfold fixedDepthBoundary
  norm_num [receiptHorizon] at htrajectory ⊢
  nlinarith

theorem balancedPath_fixedDepthRightHandSide_lt :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        fixedDepthBoundary receiptHorizon balancedPath <
      1584 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_fixedDepthBoundary_le]

/-- Outside its own event, the fixed-depth construction is a valid
stationary-risk certificate at the balanced path. -/
theorem balancedPath_fixedDepth_certificate_of_not_mem
    (hx : balancedPath ∉ fixedDepthExceptionalEvent) :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw brierScore
        oraclePosterior <
      empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        fixedDepthBoundary receiptHorizon balancedPath := by
  have hbase :=
    trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      (prefixKernel (refreshKernel Candidate.nominal))
      receiptCorrectedScore_mem_Icc predictorPrior_isFullSupport
      (show 0 < fixedDepthRiskDelta by rw [fixedDepthRiskDelta_eq]; norm_num)
      hx 5 oraclePosterior (diracPosterior_isPMF Predictor.oracle)
      receiptHorizon (by norm_num [receiptHorizon])
  rw [receiptCorrectedScore_eq_primary] at hbase
  have htransfer := stationaryRisk_lt_empirical_add_of_corrected
    primaryPotential (B := 2387 / 10240) (R := 7 / 40960)
    (by norm_num) primaryPotential_span (by norm_num)
    primaryPotential_residual (n := receiptHorizon)
    (by norm_num [receiptHorizon]) (x := balancedPath) hbase
  unfold fixedDepthBoundary fixedDepthTrajectoryBoundary
  rw [receiptCorrectedScore_eq_primary]
  norm_num [receiptHorizon] at htransfer ⊢
  linarith

/-! ## Fixed-tilt non-variance-adaptive comparison -/

/-- Singleton tilt catalog for the non-variance-adaptive comparison. -/
def nonVarianceWeight : Unit → ℝ := finiteUniformRealPMF Unit

/-- The matched fixed tilt is `1/64`. -/
def nonVarianceTilt (_u : Unit) : ℝ := 1 / 64

theorem nonVarianceWeight_isFullSupport :
    IsFullSupportPMF nonVarianceWeight := by
  exact finiteUniformRealPMF_isFullSupport Unit

theorem nonVarianceTilt_pos (u : Unit) : 0 < nonVarianceTilt u := by
  cases u
  norm_num [nonVarianceTilt]

theorem nonVarianceTilt_lt_three (u : Unit) : nonVarianceTilt u < 3 := by
  cases u
  norm_num [nonVarianceTilt]

/-- The fixed-tilt event is charged the same candidate, depth, and selected
geometric-tilt atom as the primary receipt.  Unlike the empirical-Bernstein
event, it contains no countable tilt union. -/
def nonVarianceRiskDelta : ℝ :=
  riskFailureBudget * candidateWeight Candidate.nominal *
    polynomialForwardTiltWeight 5 * polynomialForwardTiltWeight 5

theorem nonVarianceRiskDelta_pos : 0 < nonVarianceRiskDelta := by
  unfold nonVarianceRiskDelta
  exact mul_pos
    (mul_pos
      (mul_pos riskFailureBudget_pos
        (candidateWeight_isFullSupport.pos Candidate.nominal))
      (polynomialForwardTiltWeight_pos 5))
    (polynomialForwardTiltWeight_pos 5)

/-- The fixed-tilt logarithmic term is exactly the selected atom cost already
bounded in the primary receipt. -/
theorem nonVarianceRiskLogCost_le_twenty :
    klDiv oraclePosterior predictorPrior +
        Real.log
      (1 / (nonVarianceRiskDelta * nonVarianceWeight ())) ≤ 20 := by
  have h := receiptRiskLogCost_le_twenty
  have hcandidate : Fintype.card Candidate = 3 := by decide
  convert h using 1
  · norm_num [nonVarianceRiskDelta, nonVarianceWeight,
      riskFailureBudget, candidateWeight, finiteUniformRealPMF, hcandidate,
      polynomialForwardTiltWeight,
      FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight]

theorem nonVarianceSubGamma_eq :
    nonVarianceTilt () / (8 * (1 - nonVarianceTilt () / 3)) = 3 / 1528 := by
  norm_num [nonVarianceTilt]

/-- Complete stationary-risk width from the fixed-tilt sub-gamma trajectory
certificate and the same depth-five Poisson transfer terms. -/
def nonVarianceBoundary (n : ℕ) : ℝ :=
  (7507 / 5120) *
      (nonVarianceTilt () /
          (8 * (1 - nonVarianceTilt () / 3)) +
        (klDiv oraclePosterior predictorPrior +
            Real.log
              (1 / (nonVarianceRiskDelta * nonVarianceWeight ()))) /
          ((n : ℝ) * nonVarianceTilt ())) +
    (2387 / 10240) / (n : ℝ) + 7 / 40960

theorem balancedPath_nonVarianceBoundary_le :
    nonVarianceBoundary receiptHorizon ≤
      4863978637 / 391168000000 := by
  have hcost := nonVarianceRiskLogCost_le_twenty
  unfold nonVarianceBoundary
  rw [nonVarianceSubGamma_eq]
  norm_num [receiptHorizon, nonVarianceTilt] at hcost ⊢
  nlinarith

theorem balancedPath_nonVarianceRightHandSide_lt :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        nonVarianceBoundary receiptHorizon <
      1625 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_nonVarianceBoundary_le]

/-- A separate fixed-tilt event supports the non-variance-adaptive
stationary-risk comparison.  The event is existentially supplied by the
trajectory tilt-mixture theorem and is not identified with either
empirical-Bernstein event above. -/
theorem exists_nonVarianceAdaptive_event :
    ∃ exceptionalEvent : Set (ℕ → State),
      MeasurableSet exceptionalEvent ∧
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          exceptionalEvent ≤ nonVarianceRiskDelta ∧
      ∀ x ∉ exceptionalEvent,
        stationaryPosteriorMarkovRisk
            (refreshKernel Candidate.nominal) uniformLaw brierScore
            oraclePosterior <
          empiricalTransitionPosteriorRisk brierScore oraclePosterior
              receiptHorizon x +
            nonVarianceBoundary receiptHorizon := by
  rcases trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
      (prefixKernel (refreshKernel Candidate.nominal)) (0 : State)
      receiptCorrectedScore_mem_Icc predictorPrior_isFullSupport
      nonVarianceWeight_isFullSupport nonVarianceRiskDelta_pos
      nonVarianceTilt_pos nonVarianceTilt_lt_three with
    ⟨exceptionalEvent, hmeasurable, hmass, hgood⟩
  refine ⟨exceptionalEvent, hmeasurable, ?_, ?_⟩
  · simpa [trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass
  · intro x hx
    have hbase := hgood x hx () oraclePosterior
      (diracPosterior_isPMF Predictor.oracle) receiptHorizon
      (by norm_num [receiptHorizon])
    rw [receiptCorrectedScore_eq_primary] at hbase
    have hbase' :
        trajectoryPosteriorAverageConditionalRisk
            (prefixKernel (refreshKernel Candidate.nominal))
            (fun i ↦ poissonCorrectedTrajectoryScore (2387 / 10240)
              (brierScore i) (primaryPotential i))
            oraclePosterior receiptHorizon x <
          trajectoryPosteriorEmpiricalPrequentialRisk
              (fun i ↦ poissonCorrectedTrajectoryScore (2387 / 10240)
                (brierScore i) (primaryPotential i))
              oraclePosterior receiptHorizon x +
            (nonVarianceTilt () /
                (8 * (1 - nonVarianceTilt () / 3)) +
              (klDiv oraclePosterior predictorPrior +
                  Real.log
                    (1 / (nonVarianceRiskDelta * nonVarianceWeight ()))) /
                ((receiptHorizon : ℝ) * nonVarianceTilt ())) := by
      linarith
    have htransfer := stationaryRisk_lt_empirical_add_of_corrected
      primaryPotential (B := 2387 / 10240) (R := 7 / 40960)
      (by norm_num) primaryPotential_span (by norm_num)
      primaryPotential_residual (n := receiptHorizon)
      (by norm_num [receiptHorizon]) (x := x) hbase'
    norm_num [nonVarianceBoundary, receiptHorizon] at htransfer ⊢
    linarith

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadBaselines
