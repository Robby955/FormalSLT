/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadCertificate
import FormalSLT.Applications.RandomRefreshLoadPath

/-!
# Numerical receipt for the twenty-state random-refresh load model

This module evaluates the depth-five stationary-risk certificate on the
deterministic balanced path from `RandomRefreshLoadPath`.  The path has
`200,000` transitions, visits every source row `10,000` times, and realizes
the nominal transition table exactly.  The oracle's empirical Brier risk is
exactly `3/20`.

The exact corrected-score Bessel statistic sharpens the known-kernel width to
`20679874814747 / 1937166336000000`, giving a reported right-hand side below
`1607/10000`.  The empirical transition layer has the checked budget
`174387/896000`; together these yield an unknown-kernel width at most
`3802036720268663 / 7748665344000000` and a total reported right-hand side
`4964336521868663 / 7748665344000000 < 6407/10000`.

The deterministic path is an arithmetic witness, not a typicality claim.
The final probabilistic theorem is therefore conditional: one common event
has complement real outer mass at most `1/20`, and the numerical certificate
applies if the named path belongs to that event.  No measurability or
membership claim is made for that event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadReceipt

open RandomRefreshLoadModel RandomRefreshLoadPath

noncomputable section

set_option maxRecDepth 100000

/-- Reported deterministic horizon. -/
def receiptHorizon : ℕ := 200000

@[simp] theorem receiptHorizon_eq : receiptHorizon = 200000 := rfl

/-- Finite transition scores can be regrouped by their empirical edge table. -/
theorem empiricalTransitionRisk_eq_edgeMass_sum
    (score : MarkovTransitionScore State) (n : ℕ) (x : ℕ → State) :
    empiricalTransitionRisk score n x =
      (∑ z : State, ∑ y : State,
        transitionEdgeMass z y n x * score z y) / (n : ℝ) := by
  have hpoint (k : ℕ) :
      score (x k) (x (k + 1)) =
        ∑ z : State, ∑ y : State,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
    classical
    symm
    rw [Finset.sum_eq_single (x k)]
    · rw [Finset.sum_eq_single (x (k + 1))]
      · simp [transitionIndicatorScore]
      · intro y _hy hy
        simp [transitionIndicatorScore, Ne.symm hy]
      · intro hy
        exact False.elim (hy (Finset.mem_univ (x (k + 1))))
    · intro z _hz hz
      simp [transitionIndicatorScore, Ne.symm hz]
    · intro hz
      exact False.elim (hz (Finset.mem_univ (x k)))
  unfold empiricalTransitionRisk runningMean runningSum
  congr 1
  calc
    ∑ k ∈ Finset.range n, score (x k) (x (k + 1)) =
        ∑ k ∈ Finset.range n, ∑ z : State, ∑ y : State,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact hpoint k
    _ = ∑ z : State, ∑ y : State, ∑ k ∈ Finset.range n,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro z _hz
            rw [Finset.sum_comm]
    _ = ∑ z : State, ∑ y : State,
          transitionEdgeMass z y n x * score z y := by
            apply Finset.sum_congr rfl
            intro z _hz
            apply Finset.sum_congr rfl
            intro y _hy
            rw [transitionEdgeMass, Finset.sum_mul]

/-- The point posterior reduces the empirical catalog risk to the oracle
score on the named balanced path. -/
theorem balancedPath_oracle_empiricalRisk :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
        receiptHorizon balancedPath = 3 / 20 := by
  unfold empiricalTransitionPosteriorRisk oraclePosterior
  rw [pacBayesPosteriorAverage_dirac]
  rw [empiricalTransitionRisk_eq_edgeMass_sum]
  have hedge (z y : State) :
      transitionEdgeMass z y receiptHorizon balancedPath =
        10000 * (refreshKernel Candidate.nominal z y).toReal := by
    rw [receiptHorizon_eq, balancedPath_transitionEdgeMass,
      refreshKernel_apply_toReal]
    by_cases h : y = successor z
    · simp [h, candidateBase, candidateBaseNN]
      norm_num [candidateGamma, candidateGammaNN]
    · simp [h, candidateBase, candidateBaseNN]
      norm_num
  simp_rw [hedge]
  have hdouble :
      (∑ z : State, ∑ y : State,
        (10000 * (refreshKernel Candidate.nominal z y).toReal) *
          brierScore Predictor.oracle z y) =
        10000 * (∑ z : State, ∑ y : State,
          (refreshKernel Candidate.nominal z y).toReal *
            brierScore Predictor.oracle z y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  rw [hdouble]
  calc
    (10000 * (∑ z : State, ∑ y : State,
          (refreshKernel Candidate.nominal z y).toReal *
            brierScore Predictor.oracle z y)) /
        (receiptHorizon : ℝ) =
      stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore Predictor.oracle) := by
          unfold stationaryMarkovRisk markovRowRisk
          simp only [PMF.integral_eq_sum, smul_eq_mul,
            uniformLaw_apply_toReal, receiptHorizon]
          rw [show
            (∑ z : State,
              (1 / 20 : ℝ) * (∑ y : State,
                (refreshKernel Candidate.nominal z y).toReal *
                  brierScore Predictor.oracle z y)) =
              (1 / 20 : ℝ) *
                (∑ z : State, ∑ y : State,
                  (refreshKernel Candidate.nominal z y).toReal *
                    brierScore Predictor.oracle z y) by
              rw [Finset.mul_sum]]
          ring
    _ = 3 / 20 := nominal_stationaryRisk Predictor.oracle

/-- The point posterior's stationary risk is also exactly `3/20`. -/
theorem oraclePosterior_stationaryRisk :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw brierScore
        oraclePosterior = 3 / 20 := by
  unfold stationaryPosteriorMarkovRisk oraclePosterior
  rw [pacBayesPosteriorAverage_dirac]
  exact nominal_stationaryRisk Predictor.oracle

/-! ## Known-kernel depth-five width -/

/-- Corrected depth-five score catalog used by the reported boundary. -/
def receiptCorrectedScore : Predictor → TrajectoryScore State :=
  empiricalStationaryCatalogCorrectedScore refreshKernel candidateReference
    brierScore candidateOscillation Candidate.nominal 5

/-- Homogeneous transition-score form of the primary depth-five correction. -/
def receiptCorrectedTransitionScore : MarkovTransitionScore State :=
  poissonCorrectedTransitionScore (2387 / 10240)
    (brierScore Predictor.oracle)
    (empiricalStationaryCatalogPotential refreshKernel candidateReference
      brierScore Candidate.nominal 5 Predictor.oracle)

/-- Exact depth-five geometric Poisson span. -/
theorem receiptSpan_eq :
    empiricalStationaryCatalogSpan refreshKernel candidateOscillation
        Candidate.nominal 5 = 2387 / 10240 := by
  norm_num [empiricalStationaryCatalogSpan,
    finiteDepthPoissonClosedSpanBound,
    refreshKernel_dobrushinCoefficient, candidateGamma, candidateGammaNN,
    candidateOscillation]

/-- The oracle catalog score is the homogeneous primary corrected score. -/
theorem receiptCorrectedScore_oracle_eq :
    receiptCorrectedScore Predictor.oracle =
      markovTransitionTrajectoryScore receiptCorrectedTransitionScore := by
  unfold receiptCorrectedScore empiricalStationaryCatalogCorrectedScore
    receiptCorrectedTransitionScore
  rw [receiptSpan_eq]
  rfl

/-- Every corrected score remains unit-valued. -/
theorem receiptCorrectedScore_mem_Icc :
    ∀ i n u y, receiptCorrectedScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  exact empiricalStationaryCatalogCorrectedScore_mem_Icc
    refreshKernel candidateReference brierScore_mem_Icc
    candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
    brierScore_centeredOscillation_le Candidate.nominal 5

/-- The depth-five residual is exact. -/
theorem receiptDepthResidual_eq :
    finiteDobrushinCoefficient (refreshKernel Candidate.nominal) ^ 5 *
        candidateOscillation Candidate.nominal = 7 / 40960 := by
  norm_num [refreshKernel_dobrushinCoefficient, candidateGamma,
    candidateGammaNN, candidateOscillation]

/-- The affine normalization of the corrected score is exact. -/
theorem receiptCorrectedNormalization_eq :
    1 + 2 *
        empiricalStationaryCatalogSpan refreshKernel candidateOscillation
          Candidate.nominal 5 = 7507 / 5120 := by
  rw [receiptSpan_eq]
  norm_num

/-- Elementary logarithmic estimate for powers of two. -/
private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- Risk KL plus the candidate/depth/tilt allocation costs at most `20`. -/
theorem receiptRiskLogCost_le_twenty :
    klDiv oraclePosterior predictorPrior +
        Real.log
          ((((5 : ℝ) + 1) * ((5 : ℝ) + 2)) /
            (riskFailureBudget * candidateWeight Candidate.nominal *
              polynomialForwardTiltWeight 5)) ≤ 20 := by
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have hpow : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [hpow]
    linarith [log_two_le_one]
  have hlog211680 : Real.log (211680 : ℝ) ≤ 18 := by
    have hmono : Real.log (211680 : ℝ) ≤ Real.log (262144 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hpow : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 18 using 1 <;> norm_num
    rw [hpow] at hmono
    linarith [log_two_le_one]
  rw [show predictorPrior = finiteUniformRealPMF Predictor by rfl]
  unfold oraclePosterior
  rw [
    klDiv_dirac_finiteUniformRealPMF]
  have hpredictor : Fintype.card Predictor = 4 := by decide
  have hcandidate : Fintype.card Candidate = 3 := by decide
  rw [hpredictor]
  norm_num [oraclePosterior, riskFailureBudget, candidateWeight,
    finiteUniformRealPMF, hcandidate, polynomialForwardTiltWeight,
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight]
  nlinarith [hlog4, hlog211680]

/-- At tilt `1/64`, the empirical-Bernstein cumulant is at most `1/4032`. -/
theorem receiptPsi_one_sixtyFour_le :
    forwardEmpiricalBernsteinPsi (1 / 64 : ℝ) ≤ 1 / 4032 := by
  have hlog : Real.log ((64 : ℝ) / 63) ≤ 1 / 63 := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 64 / 63 by norm_num)
    norm_num at h ⊢
    exact h
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 64 : ℝ)) = 63 / 64 by norm_num, ← Real.log_inv]
  norm_num only [inv_div]
  linarith

/-- A pathwise upper bound for the oracle corrected-score hybrid penalty. -/
theorem receiptCorrectedPenalty_le :
    trajectoryPosteriorHybridBesselPenalty oraclePosterior
        receiptCorrectedScore receiptHorizon balancedPath ≤ 150001 / 2 := by
  unfold trajectoryPosteriorHybridBesselPenalty oraclePosterior
  rw [pacBayesPosteriorAverage_dirac]
  have hq := forwardBesselQ_le_quarter_card
    (fun k ↦ observedTrajectoryScore
      (receiptCorrectedScore Predictor.oracle) k balancedPath)
    (n := receiptHorizon) (by norm_num [receiptHorizon])
    (fun k _hk ↦ observedTrajectoryScore_mem_Icc
      (receiptCorrectedScore_mem_Icc Predictor.oracle) k balancedPath)
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (receiptCorrectedScore Predictor.oracle) k balancedPath)
            receiptHorizon)
        ((receiptHorizon : ℝ) / ((receiptHorizon : ℝ) - 1) *
            forwardBesselQ
              (fun k ↦ observedTrajectoryScore
                (receiptCorrectedScore Predictor.oracle) k balancedPath)
              receiptHorizon +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (receiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (receiptCorrectedScore Predictor.oracle) k balancedPath)
          receiptHorizon := min_le_left _ _
    _ ≤ 150001 / 2 := by
      norm_num [receiptHorizon] at hq ⊢
      nlinarith

/-- The countable-tilt trajectory term is below the checked rational value. -/
theorem receiptTrajectoryBoundary_le :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        predictorPrior receiptCorrectedScore oraclePosterior
        (riskFailureBudget * candidateWeight Candidate.nominal *
          polynomialForwardTiltWeight 5)
        5 receiptHorizon balancedPath ≤ 311281 / 25200000 := by
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    predictorPrior receiptCorrectedScore oraclePosterior
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
            receiptCorrectedScore receiptHorizon balancedPath ≤
        (1 / 4032 : ℝ) * (150001 / 2) := by
    calc
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            trajectoryPosteriorHybridBesselPenalty oraclePosterior
              receiptCorrectedScore receiptHorizon balancedPath ≤
          forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            (150001 / 2) :=
        mul_le_mul_of_nonneg_left receiptCorrectedPenalty_le hpsiNonneg
      _ ≤ (1 / 4032 : ℝ) * (150001 / 2) := by
        apply mul_le_mul_of_nonneg_right
        · have hlam : geometricForwardTilt 5 = (1 / 64 : ℝ) := by
            norm_num [geometricForwardTilt]
          rw [hlam]
          exact receiptPsi_one_sixtyFour_le
        · norm_num
  have hcost := receiptRiskLogCost_le_twenty
  norm_num [geometricForwardTilt, receiptHorizon] at hproduct ⊢
  nlinarith

/-- The complete known-kernel depth-five width. -/
theorem balancedPath_knownKernelBoundary_le :
    selectedKnownKernelBoundary receiptHorizon balancedPath ≤
      73718339 / 4032000000 := by
  have htrajectory := receiptTrajectoryBoundary_le
  unfold selectedKnownKernelBoundary empiricalStationaryCatalogBoundary
  change
    (1 + 2 * empiricalStationaryCatalogSpan refreshKernel
        candidateOscillation Candidate.nominal 5) *
        trajectoryCountableEmpiricalBernsteinPACBayesBoundary predictorPrior
          receiptCorrectedScore oraclePosterior
          (riskFailureBudget * candidateWeight Candidate.nominal *
            polynomialForwardTiltWeight 5)
          5 receiptHorizon balancedPath +
      empiricalStationaryCatalogSpan refreshKernel candidateOscillation
          Candidate.nominal 5 / (receiptHorizon : ℝ) +
      finiteDobrushinCoefficient (refreshKernel Candidate.nominal) ^ 5 *
          candidateOscillation Candidate.nominal +
      2 * ((1 + empiricalStationaryCatalogSpan refreshKernel
          candidateOscillation Candidate.nominal 5) * 0) ≤
        73718339 / 4032000000
  rw [receiptSpan_eq, receiptDepthResidual_eq]
  norm_num [receiptHorizon] at htrajectory ⊢
  nlinarith

/-- The empirical risk plus known-kernel width is strictly below `0.1683`. -/
theorem balancedPath_knownKernelRightHandSide_lt :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedKnownKernelBoundary receiptHorizon balancedPath <
      1683 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_knownKernelBoundary_le]

/-! ## Empirical transition budget -/

/-- Algebraic form of the finite centered sum of squares. -/
theorem forwardBesselQ_eq_sum_sq_sub_sq_sum_div
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

/-- A homogeneous score's Bessel statistic depends only on the transition
table and its empirical mean.  This is the reusable bridge from the balanced
edge receipt to corrected-score variance calculations. -/
theorem forwardBesselQ_transitionTable
    (score : MarkovTransitionScore State) {n : ℕ} (hn : 0 < n)
    (x : ℕ → State) :
    forwardBesselQ (fun k ↦ score (x k) (x (k + 1))) n =
      (∑ z : State, ∑ y : State,
        transitionEdgeMass z y n x * (score z y) ^ 2) -
        (n : ℝ) * (empiricalTransitionRisk score n x) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsquare := empiricalTransitionRisk_eq_edgeMass_sum
    (fun z y ↦ (score z y) ^ 2) n x
  unfold empiricalTransitionRisk runningMean runningSum at hsquare
  have hsquareSum :
      (∑ k ∈ Finset.range n, (score (x k) (x (k + 1))) ^ 2) =
        ∑ z : State, ∑ y : State,
          transitionEdgeMass z y n x * (score z y) ^ 2 := by
    field_simp [hn0] at hsquare
    exact hsquare
  rw [forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := fun k ↦ score (x k) (x (k + 1))) (n := n) hn,
    hsquareSum]
  unfold empiricalTransitionRisk runningMean runningSum
  field_simp [hn0]

/-- Exact state table for the depth-five oracle potential. -/
def receiptOraclePotentialValue (z : State) : ℝ :=
  if z.val = 11 then -189 / 6400
  else if z.val = 12 then -711 / 25600
  else if z.val = 13 then -531 / 25600
  else if z.val = 14 then 189 / 25600
  else if z.val = 15 then 12231 / 102400
  else if z.val = 16 then 12051 / 102400
  else if z.val = 17 then 11331 / 102400
  else if z.val = 18 then 8451 / 102400
  else -3069 / 102400

/-- Exact centered nominal row risk of the oracle. -/
def receiptOracleCenteredValue (z : State) : ℝ :=
  if 15 ≤ z.val ∧ z.val ≤ 18 then 9 / 100 else -9 / 400

theorem receiptOracleCenteredValue_eq (z : State) :
    centeredMarkovRowRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore Predictor.oracle) z = receiptOracleCenteredValue z := by
  fin_cases z <;>
    norm_num [receiptOracleCenteredValue, centeredMarkovRowRisk,
      markovRowRisk_brierScore, nominal_stationaryRisk, brierRowRisk,
      predictorProbability, candidateOverloadProbability, candidateBase,
      candidateBaseNN, candidateGamma, candidateGammaNN, successor_val]

theorem receiptOracleCenteredValue_sum_eq_zero :
    ∑ z : State, receiptOracleCenteredValue z = 0 := by
  norm_num [receiptOracleCenteredValue, Fin.sum_univ_succ]

/-- Closed form of the nominal refresh expectation operator. -/
theorem nominal_markovPotentialMean_eq (f : State → ℝ) (z : State) :
    markovPotentialMean (refreshKernel Candidate.nominal) f z =
      (3 / 80) * (∑ y : State, f y) + (1 / 4) * f (successor z) := by
  unfold markovPotentialMean
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  simp_rw [refreshKernel_apply_toReal, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num [candidateBase, candidateBaseNN, candidateGamma,
    candidateGammaNN]

/-- The automatically constructed primary potential reduces to the exact
twenty-state table above. -/
theorem receiptOraclePotential_eq (z : State) :
    empiricalStationaryCatalogPotential refreshKernel candidateReference
        brierScore Candidate.nominal 5 Predictor.oracle z =
      receiptOraclePotentialValue z := by
  let f : State → ℝ := receiptOracleCenteredValue
  have hcentered :
      centeredMarkovRowRisk (refreshKernel Candidate.nominal) uniformLaw
          (brierScore Predictor.oracle) = f := by
    funext y
    exact receiptOracleCenteredValue_eq y
  have h0 :
      iteratedMarkovPotentialMean (refreshKernel Candidate.nominal) 0 f = f := by
    rfl
  have h1 :
      iteratedMarkovPotentialMean (refreshKernel Candidate.nominal) 1 f =
        fun y ↦ (1 / 4 : ℝ) * f (successor y) := by
    funext y
    rw [show iteratedMarkovPotentialMean
        (refreshKernel Candidate.nominal) 1 f y =
        markovPotentialMean (refreshKernel Candidate.nominal) f y by
      rfl, nominal_markovPotentialMean_eq,
      receiptOracleCenteredValue_sum_eq_zero]
    simp [f]
  have hsum1 :
      ∑ y : State, (1 / 4 : ℝ) * f (successor y) = 0 := by
    norm_num [f, receiptOracleCenteredValue, successor_val,
      Fin.sum_univ_succ]
  have h2 :
      iteratedMarkovPotentialMean (refreshKernel Candidate.nominal) 2 f =
        fun y ↦ (1 / 16 : ℝ) * f (successor (successor y)) := by
    funext y
    rw [show iteratedMarkovPotentialMean
        (refreshKernel Candidate.nominal) 2 f =
        markovPotentialMean (refreshKernel Candidate.nominal)
          (iteratedMarkovPotentialMean
            (refreshKernel Candidate.nominal) 1 f) by
      rw [show 2 = 1 + 1 by norm_num, iteratedMarkovPotentialMean_succ],
      h1, nominal_markovPotentialMean_eq, hsum1]
    ring
  have hsum2 :
      ∑ y : State, (1 / 16 : ℝ) * f (successor (successor y)) = 0 := by
    norm_num [f, receiptOracleCenteredValue, successor_val,
      Fin.sum_univ_succ]
  have h3 :
      iteratedMarkovPotentialMean (refreshKernel Candidate.nominal) 3 f =
        fun y ↦ (1 / 64 : ℝ) *
          f (successor (successor (successor y))) := by
    funext y
    rw [show iteratedMarkovPotentialMean
        (refreshKernel Candidate.nominal) 3 f =
        markovPotentialMean (refreshKernel Candidate.nominal)
          (iteratedMarkovPotentialMean
            (refreshKernel Candidate.nominal) 2 f) by
      rw [show 3 = 2 + 1 by norm_num, iteratedMarkovPotentialMean_succ],
      h2, nominal_markovPotentialMean_eq, hsum2]
    ring
  have hsum3 :
      ∑ y : State, (1 / 64 : ℝ) *
          f (successor (successor (successor y))) = 0 := by
    norm_num [f, receiptOracleCenteredValue, successor_val,
      Fin.sum_univ_succ]
  have h4 :
      iteratedMarkovPotentialMean (refreshKernel Candidate.nominal) 4 f =
        fun y ↦ (1 / 256 : ℝ) *
          f (successor (successor (successor (successor y)))) := by
    funext y
    rw [show iteratedMarkovPotentialMean
        (refreshKernel Candidate.nominal) 4 f =
        markovPotentialMean (refreshKernel Candidate.nominal)
          (iteratedMarkovPotentialMean
            (refreshKernel Candidate.nominal) 3 f) by
      rw [show 4 = 3 + 1 by norm_num, iteratedMarkovPotentialMean_succ],
      h3, nominal_markovPotentialMean_eq, hsum3]
    ring
  unfold empiricalStationaryCatalogPotential finiteDepthPoissonPotential
  simp only [candidateReference]
  rw [hcentered]
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4]
  fin_cases z <;>
    norm_num [f, receiptOraclePotentialValue, receiptOracleCenteredValue,
      successor_val]

/-- Pointwise closed form of the primary corrected transition score. -/
theorem receiptCorrectedTransitionScore_apply (z y : State) :
    receiptCorrectedTransitionScore z y =
      (brierScore Predictor.oracle z y + receiptOraclePotentialValue y -
          receiptOraclePotentialValue z + 2387 / 10240) /
        (1 + 2 * (2387 / 10240)) := by
  unfold receiptCorrectedTransitionScore poissonCorrectedTransitionScore
  rw [receiptOraclePotential_eq z, receiptOraclePotential_eq y]

set_option maxHeartbeats 2000000 in
/-- Exact Bessel statistic of the primary depth-five corrected oracle score on
the balanced transition table. -/
theorem balancedPath_correctedScoreBesselQ_eq :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (receiptCorrectedScore Predictor.oracle) k balancedPath)
        receiptHorizon = 722853659625 / 112710098 := by
  rw [receiptCorrectedScore_oracle_eq]
  change forwardBesselQ
      (fun k ↦ receiptCorrectedTransitionScore
        (balancedPath k) (balancedPath (k + 1))) receiptHorizon = _
  rw [forwardBesselQ_transitionTable receiptCorrectedTransitionScore
    (by norm_num [receiptHorizon]) balancedPath]
  rw [empiricalTransitionRisk_eq_edgeMass_sum]
  rw [receiptHorizon_eq]
  simp_rw [balancedPath_transitionEdgeMass]
  simp_rw [receiptCorrectedTransitionScore_apply]
  norm_num [receiptOraclePotentialValue,
    predictorProbability, brierScore,
    overloadIndicator, Fin.ext_iff, successor_val, Fin.sum_univ_succ]

/-- Exact first-branch upper bound for the primary hybrid Bessel penalty. -/
theorem receiptCorrectedPenalty_le_exact :
    trajectoryPosteriorHybridBesselPenalty oraclePosterior
        receiptCorrectedScore receiptHorizon balancedPath ≤
      2168673688973 / 225420196 := by
  unfold trajectoryPosteriorHybridBesselPenalty oraclePosterior
  rw [pacBayesPosteriorAverage_dirac]
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (receiptCorrectedScore Predictor.oracle) k balancedPath)
            receiptHorizon)
        ((receiptHorizon : ℝ) / ((receiptHorizon : ℝ) - 1) *
            forwardBesselQ
              (fun k ↦ observedTrajectoryScore
                (receiptCorrectedScore Predictor.oracle) k balancedPath)
              receiptHorizon +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (receiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (receiptCorrectedScore Predictor.oracle) k balancedPath)
          receiptHorizon := min_le_left _ _
    _ = 2168673688973 / 225420196 := by
      rw [balancedPath_correctedScoreBesselQ_eq]
      norm_num

/-- Exact-variance trajectory term at the selected geometric tilt. -/
theorem receiptTrajectoryBoundary_le_exact :
    trajectoryCountableEmpiricalBernsteinPACBayesBoundary
        predictorPrior receiptCorrectedScore oraclePosterior
        (riskFailureBudget * candidateWeight Candidate.nominal *
          polynomialForwardTiltWeight 5)
        5 receiptHorizon balancedPath ≤
      20346558294413 / 2840294469600000 := by
  rw [trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
    predictorPrior receiptCorrectedScore oraclePosterior
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
            receiptCorrectedScore receiptHorizon balancedPath ≤
        (1 / 4032 : ℝ) * (2168673688973 / 225420196) := by
    calc
      forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            trajectoryPosteriorHybridBesselPenalty oraclePosterior
              receiptCorrectedScore receiptHorizon balancedPath ≤
          forwardEmpiricalBernsteinPsi (geometricForwardTilt 5) *
            (2168673688973 / 225420196) :=
        mul_le_mul_of_nonneg_left receiptCorrectedPenalty_le_exact hpsiNonneg
      _ ≤ (1 / 4032 : ℝ) * (2168673688973 / 225420196) := by
        apply mul_le_mul_of_nonneg_right
        · have hlam : geometricForwardTilt 5 = (1 / 64 : ℝ) := by
            norm_num [geometricForwardTilt]
          rw [hlam]
          exact receiptPsi_one_sixtyFour_le
        · norm_num
  have hcost := receiptRiskLogCost_le_twenty
  norm_num [geometricForwardTilt, receiptHorizon] at hproduct ⊢
  nlinarith

/-- Primary exact-variance known-kernel depth-five width. -/
theorem balancedPath_knownKernelBoundary_le_exact :
    selectedKnownKernelBoundary receiptHorizon balancedPath ≤
      20679874814747 / 1937166336000000 := by
  have htrajectory := receiptTrajectoryBoundary_le_exact
  unfold selectedKnownKernelBoundary empiricalStationaryCatalogBoundary
  change
    (1 + 2 * empiricalStationaryCatalogSpan refreshKernel
        candidateOscillation Candidate.nominal 5) *
        trajectoryCountableEmpiricalBernsteinPACBayesBoundary predictorPrior
          receiptCorrectedScore oraclePosterior
          (riskFailureBudget * candidateWeight Candidate.nominal *
            polynomialForwardTiltWeight 5)
          5 receiptHorizon balancedPath +
      empiricalStationaryCatalogSpan refreshKernel candidateOscillation
          Candidate.nominal 5 / (receiptHorizon : ℝ) +
      finiteDobrushinCoefficient (refreshKernel Candidate.nominal) ^ 5 *
          candidateOscillation Candidate.nominal +
      2 * ((1 + empiricalStationaryCatalogSpan refreshKernel
          candidateOscillation Candidate.nominal 5) * 0) ≤
        20679874814747 / 1937166336000000
  rw [receiptSpan_eq, receiptDepthResidual_eq]
  norm_num [receiptHorizon] at htrajectory ⊢
  nlinarith

/-- The primary exact-variance known-kernel right-hand side is below
`0.1607`. -/
theorem balancedPath_knownKernelRightHandSide_lt_primary :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedKnownKernelBoundary receiptHorizon balancedPath <
      1607 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_knownKernelBoundary_le_exact]

/-- Exact direct-indicator Bessel variance from the balanced edge counts. -/
theorem balancedPath_directCoordinateBesselQ (z y : State) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, false⟩ : TransitionCoordinate State)) k balancedPath)
        receiptHorizon =
      if y = successor z then 181355 / 64 else 23955 / 64 := by
  rw [forwardBesselQ_eq_sum_sq_sub_sq_sum_div
    (v := fun k ↦ observedTrajectoryScore
      (transitionCoordinateTrajectoryScore
        (⟨z, y, false⟩ : TransitionCoordinate State)) k balancedPath)
    (n := receiptHorizon) (by norm_num [receiptHorizon])]
  have hsum :
      (∑ k ∈ Finset.range receiptHorizon,
        observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, false⟩ : TransitionCoordinate State)) k balancedPath) =
        transitionEdgeMass z y receiptHorizon balancedPath := by
    rfl
  have hsq :
      (∑ k ∈ Finset.range receiptHorizon,
        (observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, false⟩ : TransitionCoordinate State)) k balancedPath) ^ 2) =
        transitionEdgeMass z y receiptHorizon balancedPath := by
    unfold transitionEdgeMass
    apply Finset.sum_congr rfl
    intro k _hk
    change
      (transitionIndicatorScore z y (balancedPath k)
        (balancedPath (k + 1))) ^ 2 =
      transitionIndicatorScore z y (balancedPath k) (balancedPath (k + 1))
    unfold transitionIndicatorScore
    split_ifs <;> norm_num
  rw [hsum, hsq, receiptHorizon_eq,
    balancedPath_transitionEdgeMass]
  split_ifs <;> norm_num

/-- Complementing a transition indicator leaves its Bessel variance unchanged. -/
theorem balancedPath_complementCoordinateBesselQ (z y : State) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, true⟩ : TransitionCoordinate State)) k balancedPath)
        receiptHorizon =
      if y = successor z then 181355 / 64 else 23955 / 64 := by
  rw [show
      (fun k ↦ observedTrajectoryScore
        (transitionCoordinateTrajectoryScore
          (⟨z, y, true⟩ : TransitionCoordinate State)) k balancedPath) =
        (fun k ↦ 1 - observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, false⟩ : TransitionCoordinate State)) k balancedPath) by
      funext k
      rfl]
  rw [forwardBesselQ_one_sub,
    balancedPath_directCoordinateBesselQ]

/-- Exact Bessel variance for either side of every transition coordinate. -/
theorem balancedPath_coordinateBesselQ (z y : State) (complement : Bool) :
    forwardBesselQ
        (fun k ↦ observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, complement⟩ : TransitionCoordinate State)) k balancedPath)
        receiptHorizon =
      if y = successor z then 181355 / 64 else 23955 / 64 := by
  cases complement
  · exact balancedPath_directCoordinateBesselQ z y
  · exact balancedPath_complementCoordinateBesselQ z y

/-- Coordinate penalties distinguish the successor edge from the other
nineteen destinations. -/
theorem balancedPath_coordinatePenalty_le
    (z y : State) (complement : Bool) :
    trajectoryPosteriorHybridBesselPenalty
        (diracPosterior (⟨z, y, complement⟩ : TransitionCoordinate State))
        transitionCoordinateTrajectoryScore receiptHorizon balancedPath ≤
      if y = successor z then 544129 / 128 else 71929 / 128 := by
  unfold trajectoryPosteriorHybridBesselPenalty
  rw [pacBayesPosteriorAverage_dirac]
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (transitionCoordinateTrajectoryScore
                (⟨z, y, complement⟩ : TransitionCoordinate State)) k
              balancedPath) receiptHorizon)
        ((receiptHorizon : ℝ) / ((receiptHorizon : ℝ) - 1) *
            forwardBesselQ
              (fun k ↦ observedTrajectoryScore
                (transitionCoordinateTrajectoryScore
                  (⟨z, y, complement⟩ : TransitionCoordinate State)) k
                balancedPath) receiptHorizon +
          (1 : ℝ) / 4 *
            (1 + ((harmonic (receiptHorizon - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (transitionCoordinateTrajectoryScore
              (⟨z, y, complement⟩ : TransitionCoordinate State)) k
            balancedPath) receiptHorizon := min_le_left _ _
    _ ≤ if y = successor z then 544129 / 128 else 71929 / 128 := by
      rw [balancedPath_coordinateBesselQ]
      split_ifs <;> norm_num

/-- Transition-coordinate KL and confidence cost is below `11`. -/
theorem receiptTransitionLogCost_le_eleven
    (z y : State) (complement : Bool) :
    klDiv
          (diracPosterior
            (⟨z, y, complement⟩ : TransitionCoordinate State))
          transitionPrior +
        Real.log (1 / (transitionFailureBudget * transitionWeight ())) ≤
      11 := by
  rw [show transitionPrior =
      finiteUniformRealPMF (TransitionCoordinate State) by rfl,
    klDiv_dirac_finiteUniformRealPMF]
  norm_num [transitionFailureBudget, transitionWeight,
    finiteUniformRealPMF]
  have hcard : Fintype.card (TransitionCoordinate State) = 800 := by
    decide
  rw [hcard]
  norm_num only [Nat.cast_ofNat]
  have hcombine : Real.log (800 : ℝ) + Real.log 40 =
      Real.log 32000 := by
    rw [← Real.log_mul (by norm_num : (800 : ℝ) ≠ 0)
      (by norm_num : (40 : ℝ) ≠ 0)]
    norm_num
  rw [hcombine]
  have hmono : Real.log (32000 : ℝ) ≤ Real.log (32768 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hpow : Real.log (32768 : ℝ) = 15 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 15 using 1 <;> norm_num
  rw [hpow] at hmono
  have hlog2 := Real.log_two_lt_d9
  linarith

/-- At tilt `1/8`, the transition cumulant is at most `1/56`. -/
theorem receiptPsi_one_eighth_le :
    forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) ≤ 1 / 56 := by
  have hlog : Real.log ((8 : ℝ) / 7) ≤ 1 / 7 := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 8 / 7 by norm_num)
    norm_num at h ⊢
    exact h
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num, ← Real.log_inv]
  norm_num only [inv_div]
  linarith

/-- Numerical direct/complement boundary for every coordinate. -/
theorem balancedPath_coordinateBoundary_le
    (z y : State) (complement : Bool) :
    transitionCoordinateBoundary transitionPrior transitionWeight
        transitionTilt z y complement transitionFailureBudget ()
        receiptHorizon balancedPath ≤
      if y = successor z then
        622977 / 179200000
      else
        150777 / 179200000 := by
  have hpsiNonneg :
      0 ≤ forwardEmpiricalBernsteinPsi (transitionTilt ()) :=
    forwardEmpiricalBernsteinPsi_nonneg
      (transitionTilt_pos ()).le (transitionTilt_lt_one ())
  have hproduct :
      forwardEmpiricalBernsteinPsi (transitionTilt ()) *
          trajectoryPosteriorHybridBesselPenalty
            (diracPosterior
              (⟨z, y, complement⟩ : TransitionCoordinate State))
            transitionCoordinateTrajectoryScore receiptHorizon balancedPath ≤
        if y = successor z then
          (1 / 56 : ℝ) * (544129 / 128)
        else
          (1 / 56 : ℝ) * (71929 / 128) := by
    have hpen := balancedPath_coordinatePenalty_le z y complement
    have hpenNonneg :
        0 ≤ trajectoryPosteriorHybridBesselPenalty
          (diracPosterior
            (⟨z, y, complement⟩ : TransitionCoordinate State))
          transitionCoordinateTrajectoryScore receiptHorizon balancedPath := by
      unfold trajectoryPosteriorHybridBesselPenalty
      rw [pacBayesPosteriorAverage_dirac]
      exact forwardHybridBesselPenalty_nonneg_of_unit
        (fun k ↦ observedTrajectoryScore
          (transitionCoordinateTrajectoryScore
            (⟨z, y, complement⟩ : TransitionCoordinate State)) k balancedPath)
        (by norm_num [receiptHorizon])
        (fun k _hk ↦ observedTrajectoryScore_mem_Icc
          (transitionCoordinateTrajectoryScore_mem_Icc
            (⟨z, y, complement⟩ : TransitionCoordinate State)) k balancedPath)
    have hpsi : forwardEmpiricalBernsteinPsi (transitionTilt ()) ≤ 1 / 56 := by
      simpa [transitionTilt] using receiptPsi_one_eighth_le
    have hmul := mul_le_mul hpsi hpen hpenNonneg (by norm_num)
    by_cases hsucc : y = successor z
    · rw [if_pos hsucc] at hpen hmul ⊢
      exact hmul
    · rw [if_neg hsucc] at hpen hmul ⊢
      exact hmul
  have hdirac :
      @diracPosterior (TransitionCoordinate State)
          (inferInstance : DecidableEq (TransitionCoordinate State))
          (⟨z, y, complement⟩ : TransitionCoordinate State) =
        @diracPosterior (TransitionCoordinate State)
          (@instDecidableEqTransitionCoordinate State
            (fun a b ↦ Classical.propDecidable (a = b)))
          (⟨z, y, complement⟩ : TransitionCoordinate State) := by
    funext c
    unfold diracPosterior
    by_cases h : c =
        (⟨z, y, complement⟩ : TransitionCoordinate State) <;> simp [h]
  have hcost := receiptTransitionLogCost_le_eleven z y complement
  rw [hdirac] at hcost hproduct
  unfold transitionCoordinateBoundary
    trajectoryEmpiricalBernsteinPACBayesBoundary
  norm_num only [receiptHorizon, transitionTilt, Nat.cast_ofNat]
  norm_num only [receiptHorizon, transitionTilt] at hproduct
  by_cases hsucc : y = successor z
  · rw [if_pos hsucc] at hproduct ⊢
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25000)).2
    have hsum := add_le_add hcost hproduct
    norm_num at hsum ⊢
    exact hsum
  · rw [if_neg hsucc] at hproduct ⊢
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25000)).2
    have hsum := add_le_add hcost hproduct
    norm_num at hsum ⊢
    exact hsum

/-- The row-normalized coordinate radius, using `10,000` visits per row. -/
theorem balancedPath_coordinateRadius_le (z y : State) :
    transitionCoordinateRadius transitionPrior transitionWeight transitionTilt
        z y transitionFailureBudget () receiptHorizon balancedPath ≤
      if y = successor z then
        622977 / 8960000
      else
        150777 / 8960000 := by
  have hmax :
      max
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y false transitionFailureBudget ()
            receiptHorizon balancedPath)
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y true transitionFailureBudget ()
            receiptHorizon balancedPath) ≤
        if y = successor z then
          622977 / 179200000
        else
          150777 / 179200000 :=
    max_le_iff.2 ⟨balancedPath_coordinateBoundary_le z y false,
      balancedPath_coordinateBoundary_le z y true⟩
  unfold transitionCoordinateRadius
  rw [receiptHorizon_eq, balancedPath_transitionVisitMass]
  norm_num only [Nat.cast_ofNat]
  by_cases hsucc : y = successor z
  · rw [if_pos hsucc] at hmax ⊢
    calc
      20 * max
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y false transitionFailureBudget () 200000
            balancedPath)
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y true transitionFailureBudget () 200000
            balancedPath) ≤
          20 * (622977 / 179200000) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 622977 / 8960000 := by norm_num
  · rw [if_neg hsucc] at hmax ⊢
    calc
      20 * max
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y false transitionFailureBudget () 200000
            balancedPath)
          (transitionCoordinateBoundary transitionPrior transitionWeight
            transitionTilt z y true transitionFailureBudget () 200000
            balancedPath) ≤
          20 * (150777 / 179200000) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 150777 / 8960000 := by norm_num

/-- All twenty coordinate radii give the stronger checked row-TV budget. -/
theorem balancedPath_transitionRowRadius_le (z : State) :
    empiricalTransitionRowRadius transitionPrior transitionWeight transitionTilt
        z transitionFailureBudget () receiptHorizon balancedPath ≤
      174387 / 896000 := by
  have hsum :
      (∑ y : State,
        (if y = successor z then
          (622977 / 8960000 : ℝ)
        else
          150777 / 8960000)) =
        2 * (174387 / 896000 : ℝ) := by
    calc
      (∑ y : State,
          (if y = successor z then
            (622977 / 8960000 : ℝ)
          else
            150777 / 8960000)) =
          ∑ y : State,
            ((150777 / 8960000 : ℝ) +
              if y = successor z then
                (622977 - 150777) / 8960000
              else 0) := by
                apply Finset.sum_congr rfl
                intro y _hy
                by_cases h : y = successor z
                · rw [if_pos h, if_pos h]
                  ring
                · rw [if_neg h, if_neg h]
                  ring
      _ = 2 * (174387 / 896000 : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, nsmul_eq_mul]
        norm_num
  unfold empiricalTransitionRowRadius
  calc
    (1 / 2 : ℝ) * ∑ y : State,
        transitionCoordinateRadius transitionPrior transitionWeight
          transitionTilt z y transitionFailureBudget () receiptHorizon
          balancedPath ≤
      (1 / 2 : ℝ) * ∑ y : State,
        (if y = successor z then
          622977 / 8960000
        else
          150777 / 8960000) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun y _hy ↦
                balancedPath_coordinateRadius_le z y
            · norm_num
    _ = 174387 / 896000 := by rw [hsum]; ring

/-- The candidate transition table exactly matches the balanced frequencies. -/
theorem balancedPath_candidateDiscrepancy_eq_zero (z : State) :
    empiricalCandidateRowTotalVariation
        (refreshKernel Candidate.nominal) z receiptHorizon balancedPath = 0 := by
  unfold empiricalCandidateRowTotalVariation
  have hpoint (y : State) :
      (refreshKernel Candidate.nominal z y).toReal =
        empiricalTransitionFrequency z y receiptHorizon balancedPath := by
    rw [receiptHorizon_eq,
      balancedPath_empiricalTransitionFrequency,
      refreshKernel_apply_toReal]
    by_cases h : y = successor z
    · simp [h, candidateBase, candidateBaseNN]
      norm_num [candidateGamma, candidateGammaNN]
    · simp [h, candidateBase, candidateBaseNN]
  simp_rw [hpoint]
  simp

/-- Strong numerical empirical-kernel TV budget. -/
theorem balancedPath_empiricalKernelTVBudget_le_strong :
    selectedEmpiricalKernelTVBudget receiptHorizon balancedPath ≤
      174387 / 896000 := by
  unfold selectedEmpiricalKernelTVBudget
    empiricalCandidateKernelTVBudget finiteMaximum
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro z _hz
  rw [balancedPath_candidateDiscrepancy_eq_zero]
  simpa using balancedPath_transitionRowRadius_le z

/-- Rounded empirical-kernel TV budget used by the public receipt. -/
theorem balancedPath_empiricalKernelTVBudget_le :
    selectedEmpiricalKernelTVBudget receiptHorizon balancedPath ≤
      3181 / 14000 := by
  exact balancedPath_empiricalKernelTVBudget_le_strong.trans (by norm_num)

/-- The rounded empirical transfer budget still certifies strict contraction. -/
theorem balancedPath_transferredCoefficient_lt_one :
    finiteDobrushinCoefficient (refreshKernel Candidate.nominal) +
        2 * selectedEmpiricalKernelTVBudget receiptHorizon balancedPath < 1 := by
  have heta := balancedPath_empiricalKernelTVBudget_le
  rw [refreshKernel_dobrushinCoefficient]
  norm_num [candidateGamma, candidateGammaNN] at heta ⊢
  nlinarith

/-! ## Unknown-kernel width and end-to-end conditional receipt -/

/-- The empirical transition transfer gives the checked unknown-kernel width. -/
theorem balancedPath_unknownKernelBoundary_le :
    selectedUnknownKernelBoundary receiptHorizon balancedPath ≤
      9332332931 / 16128000000 := by
  have hknown := balancedPath_knownKernelBoundary_le
  have heta := balancedPath_empiricalKernelTVBudget_le
  unfold selectedUnknownKernelBoundary empiricalStationaryCatalogBoundary
  unfold selectedKnownKernelBoundary empiricalStationaryCatalogBoundary at hknown
  rw [receiptSpan_eq] at ⊢ hknown
  norm_num at heta ⊢ hknown
  nlinarith

/-- Primary exact-variance unknown-kernel width using the strong row-TV
budget rather than the rounded display budget. -/
theorem balancedPath_unknownKernelBoundary_le_primary :
    selectedUnknownKernelBoundary receiptHorizon balancedPath ≤
      3802036720268663 / 7748665344000000 := by
  have hknown := balancedPath_knownKernelBoundary_le_exact
  have heta := balancedPath_empiricalKernelTVBudget_le_strong
  unfold selectedUnknownKernelBoundary empiricalStationaryCatalogBoundary
  unfold selectedKnownKernelBoundary empiricalStationaryCatalogBoundary at hknown
  rw [receiptSpan_eq] at ⊢ hknown
  norm_num at heta ⊢ hknown
  nlinarith

/-- The primary unknown-kernel total is the advertised exact rational
ceiling. -/
theorem balancedPath_unknownKernelRightHandSide_le_primary :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedUnknownKernelBoundary receiptHorizon balancedPath ≤
      4964336521868663 / 7748665344000000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_unknownKernelBoundary_le_primary]

/-- The primary unknown-kernel total is below `0.6407`. -/
theorem balancedPath_unknownKernelRightHandSide_lt_primary :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedUnknownKernelBoundary receiptHorizon balancedPath <
      6407 / 10000 :=
  balancedPath_unknownKernelRightHandSide_le_primary.trans_lt (by norm_num)

/-- The empirical risk plus unknown-kernel width is below `0.7287`. -/
theorem balancedPath_unknownKernelRightHandSide_lt :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedUnknownKernelBoundary receiptHorizon balancedPath <
      7287 / 10000 := by
  rw [balancedPath_oracle_empiricalRisk]
  nlinarith [balancedPath_unknownKernelBoundary_le]

theorem balancedPath_unknownKernelRightHandSide_lt_three_quarters :
    empiricalTransitionPosteriorRisk brierScore oraclePosterior
          receiptHorizon balancedPath +
        selectedUnknownKernelBoundary receiptHorizon balancedPath <
      3 / 4 :=
  balancedPath_unknownKernelRightHandSide_lt.trans (by norm_num)

/-- Event-level contract retained by the numerical receipt.  Membership and
all-row coverage, not the mere definition of a deterministic path, activate
the two matched inequalities. -/
def IsMatchedReceiptEvent (goodEvent : Set (ℕ → State)) : Prop :=
  ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
    (∀ z : State, 0 < transitionVisitMass z n x) →
      stationaryPosteriorMarkovRisk
            (refreshKernel Candidate.nominal) uniformLaw brierScore
            oraclePosterior <
          empiricalTransitionPosteriorRisk brierScore oraclePosterior n x +
            selectedKnownKernelBoundary n x ∧
        stationaryPosteriorMarkovRisk
            (refreshKernel Candidate.nominal) uniformLaw brierScore
            oraclePosterior <
          empiricalTransitionPosteriorRisk brierScore oraclePosterior n x +
            selectedUnknownKernelBoundary n x

/-- One common event with complement real outer mass at most `1/20` supports
every covered path and time.  If the named balanced path belongs to that event,
its exact arithmetic receipt gives both nonvacuous numerical right-hand sides.
The implication deliberately does not assert measurability of the event or
that the named path belongs to it. -/
theorem exists_balancedPath_conditional_numeric_certificate :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        IsMatchedReceiptEvent goodEvent ∧
        (balancedPath ∈ goodEvent →
          stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                oraclePosterior <
              empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  receiptHorizon balancedPath +
                selectedKnownKernelBoundary receiptHorizon balancedPath ∧
            stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                oraclePosterior <
              empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  receiptHorizon balancedPath +
                selectedUnknownKernelBoundary receiptHorizon balancedPath ∧
            empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  receiptHorizon balancedPath +
                selectedKnownKernelBoundary receiptHorizon balancedPath <
              1607 / 10000 ∧
            empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  receiptHorizon balancedPath +
                selectedUnknownKernelBoundary receiptHorizon balancedPath <
              6407 / 10000 ∧
            finiteDobrushinCoefficient
                  (refreshKernel Candidate.nominal) +
                2 * selectedEmpiricalKernelTVBudget
                  receiptHorizon balancedPath < 1) := by
  rcases exists_randomRefreshLoad_matched_event with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn hvisit
    have h := hgood x hx n hn hvisit
    exact ⟨h.1, h.2.1⟩
  · intro hbalanced
    have hvisit : ∀ z : State,
        0 < transitionVisitMass z receiptHorizon balancedPath := by
      intro z
      rw [receiptHorizon_eq, balancedPath_transitionVisitMass]
      norm_num
    have hcert := hgood balancedPath hbalanced receiptHorizon
      (by norm_num [receiptHorizon]) hvisit
    exact ⟨hcert.1, hcert.2.1,
      balancedPath_knownKernelRightHandSide_lt_primary,
      balancedPath_unknownKernelRightHandSide_lt_primary,
      balancedPath_transferredCoefficient_lt_one⟩

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadReceipt
