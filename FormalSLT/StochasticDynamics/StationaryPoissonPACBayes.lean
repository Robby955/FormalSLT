/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes

/-!
# Stationary-risk PAC-Bayes certificates from supplied Poisson solutions

This module turns the empirical-Bernstein trajectory certificate into a
stationary-risk certificate for a finite, time-homogeneous Markov chain.  The
bridge is deterministic: the caller supplies an invariant PMF and a bounded
potential for each hypothesis.  An exact Poisson solution makes the corrected
score's conditional mean constant; an approximate solution contributes its
explicit residual along the observed path.

The construction does not infer an invariant law, solve a Poisson equation, or
derive a potential bound from a spectral gap or mixing assumption.  Those are
separate mathematical inputs.  The statistical event is inherited from the
trajectory empirical-Bernstein theorem and remains simultaneous over all
times `n >= 2`, posterior PMFs, and atoms of a finite declared tilt catalog.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι τ Z : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- A finite-state transition score. -/
abbrev MarkovTransitionScore (Z : Type*) := Z → Z → ℝ

/-- The supplied PMF is invariant for the supplied transition matrix. -/
def IsInvariantPMF (P : Z → PMF Z) (stationary : PMF Z) : Prop :=
  stationary.bind P = stationary

/-- Risk in one transition row. -/
def markovRowRisk (P : Z → PMF Z) (score : MarkovTransitionScore Z)
    (z : Z) : ℝ :=
  ∫ y, score z y ∂(P z).toMeasure

/-- Risk when the current state has the supplied invariant distribution. -/
def stationaryMarkovRisk (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) : ℝ :=
  ∫ z, markovRowRisk P score z ∂stationary.toMeasure

/-- One-step transition average of a supplied potential. -/
def markovPotentialMean (P : Z → PMF Z) (potential : Z → ℝ) (z : Z) : ℝ :=
  ∫ y, potential y ∂(P z).toMeasure

/-- Residual in the supplied Poisson equation
`rowRisk + P potential - potential = stationaryRisk + residual`. -/
def approximatePoissonResidual
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ) (z : Z) : ℝ :=
  markovRowRisk P score z + markovPotentialMean P potential z - potential z -
    stationaryMarkovRisk P stationary score

/-- A supplied potential solves the Poisson equation exactly when its residual
vanishes at every state. -/
def IsExactPoissonSolution
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ) : Prop :=
  ∀ z, approximatePoissonResidual P stationary score potential z = 0

/-- Affine correction of a transition score by a bounded Poisson potential.
If the score is in `[0,1]` and every potential difference has absolute value
at most `B`, this corrected score is again in `[0,1]`. -/
def poissonCorrectedTransitionScore
    (B : ℝ) (score : MarkovTransitionScore Z) (potential : Z → ℝ) :
    MarkovTransitionScore Z :=
  fun x y ↦ (score x y + potential y - potential x + B) / (1 + 2 * B)

/-- A time-homogeneous transition score as a trajectory score. -/
def markovTransitionTrajectoryScore
    (score : MarkovTransitionScore Z) : TrajectoryScore Z :=
  fun n u y ↦ score (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y

/-- The corrected transition score as a trajectory score. -/
def poissonCorrectedTrajectoryScore
    (B : ℝ) (score : MarkovTransitionScore Z) (potential : Z → ℝ) :
    TrajectoryScore Z :=
  markovTransitionTrajectoryScore
    (poissonCorrectedTransitionScore B score potential)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The observed homogeneous trajectory score is the transition score on the
two consecutive path coordinates. -/
theorem observedTrajectoryScore_markovTransitionTrajectoryScore
    (score : MarkovTransitionScore Z) (n : ℕ) (x : ℕ → Z) :
    observedTrajectoryScore (markovTransitionTrajectoryScore score) n x =
      score (x n) (x (n + 1)) := by
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ] in
/-- The conditional trajectory risk of a homogeneous score is its row risk at
the current state. -/
theorem conditionalTrajectoryRisk_markovTransitionTrajectoryScore
    (P : Z → PMF Z) (score : MarkovTransitionScore Z)
    (n : ℕ) (x : ℕ → Z) :
    conditionalTrajectoryRisk (prefixKernel P)
        (markovTransitionTrajectoryScore score) n x =
      markovRowRisk P score (x n) := by
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The affine Poisson correction stays inside `[0,1]` under the explicit
oscillation bound. -/
theorem poissonCorrectedTransitionScore_mem_Icc
    {B : ℝ} (hB : 0 ≤ B)
    {score : MarkovTransitionScore Z} {potential : Z → ℝ}
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (x y : Z) :
    poissonCorrectedTransitionScore B score potential x y ∈
      Set.Icc (0 : ℝ) 1 := by
  have hden : 0 < 1 + 2 * B := by linarith
  have hdiff := hspan x y
  rw [abs_le] at hdiff
  rw [Set.mem_Icc, poissonCorrectedTransitionScore]
  constructor
  · exact div_nonneg (by linarith [(hscore x y).1]) hden.le
  · apply (div_le_one hden).2
    linarith [(hscore x y).2]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ] in
/-- Exact conditional-risk identity for the corrected score.  The invariant
PMF enters through the stationary-risk target, while the approximation error
is retained pointwise as the Poisson residual. -/
theorem markovRowRisk_poissonCorrectedTransitionScore
    {B : ℝ} (hB : 0 ≤ B)
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ) (z : Z) :
    markovRowRisk P (poissonCorrectedTransitionScore B score potential) z =
      (stationaryMarkovRisk P stationary score +
          approximatePoissonResidual P stationary score potential z + B) /
        (1 + 2 * B) := by
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  unfold poissonCorrectedTransitionScore
    approximatePoissonResidual markovPotentialMean
  simp only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul]
  have hmass : ∑ y : Z, ((P z y).toReal : ℝ) = 1 := by
    have hone := PMF.integral_eq_sum (P z) (fun _ : Z ↦ (1 : ℝ))
    simpa [smul_eq_mul] using hone.symm
  have hsum :
      ∑ y : Z, (P z y).toReal *
          (score z y + potential y - potential z + B) =
        (∑ y : Z, (P z y).toReal * score z y) +
          (∑ y : Z, (P z y).toReal * potential y) - potential z + B := by
    calc
      _ = ∑ y : Z,
          ((P z y).toReal * score z y +
              (P z y).toReal * potential y -
            (P z y).toReal * potential z + (P z y).toReal * B) := by
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ = (∑ y : Z, (P z y).toReal * score z y) +
          (∑ y : Z, (P z y).toReal * potential y) -
          (∑ y : Z, (P z y).toReal * potential z) +
          (∑ y : Z, (P z y).toReal * B) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
      _ = (∑ y : Z, (P z y).toReal * score z y) +
          (∑ y : Z, (P z y).toReal * potential y) - potential z + B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hmass]
        ring
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, hsum]
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ] in
/-- Trajectory form of the exact corrected conditional-risk identity. -/
theorem conditionalTrajectoryRisk_poissonCorrectedTrajectoryScore
    {B : ℝ} (hB : 0 ≤ B)
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ)
    (n : ℕ) (x : ℕ → Z) :
    conditionalTrajectoryRisk (prefixKernel P)
        (poissonCorrectedTrajectoryScore B score potential) n x =
      (stationaryMarkovRisk P stationary score +
          approximatePoissonResidual P stationary score potential (x n) + B) /
        (1 + 2 * B) := by
  unfold poissonCorrectedTrajectoryScore
  rw [conditionalTrajectoryRisk_markovTransitionTrajectoryScore]
  exact markovRowRisk_poissonCorrectedTransitionScore hB
    P stationary score potential (x n)

/-- Empirical mean of a homogeneous transition score. -/
def empiricalTransitionRisk
    (score : MarkovTransitionScore Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  runningMean (fun k x ↦ score (x k) (x (k + 1))) n x

/-- Endpoint correction produced by telescoping one potential along a path. -/
def poissonEndpointCorrection
    (potential : Z → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  (potential (x n) - potential (x 0)) / (n : ℝ)

/-- Average approximate-Poisson residual encountered along one path. -/
def poissonResidualAverage
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  runningMean
    (fun k x ↦ approximatePoissonResidual
      P stationary score potential (x k)) n x

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The potential increments telescope exactly along a finite prefix. -/
theorem sum_poissonPotential_increment
    (potential : Z → ℝ) (n : ℕ) (x : ℕ → Z) :
    ∑ k ∈ Finset.range n, (potential (x (k + 1)) - potential (x k)) =
      potential (x n) - potential (x 0) := by
  exact Finset.sum_range_sub (fun k ↦ potential (x k)) n

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Exact observed-risk identity: the corrected empirical risk is the affine
rescaling of the original empirical transition risk plus its telescoping
endpoint correction. -/
theorem trajectoryEmpiricalPrequentialRisk_poissonCorrected
    {B : ℝ} (hB : 0 ≤ B)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryEmpiricalPrequentialRisk
        (poissonCorrectedTrajectoryScore B score potential) n x =
      (empiricalTransitionRisk score n x +
          poissonEndpointCorrection potential n x + B) /
        (1 + 2 * B) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  have hsum :
      ∑ k ∈ Finset.range n,
          (score (x k) (x (k + 1)) + potential (x (k + 1)) -
            potential (x k) + B) =
        (∑ k ∈ Finset.range n, score (x k) (x (k + 1))) +
          (potential (x n) - potential (x 0)) + (n : ℝ) * B := by
    simp_rw [show ∀ k,
        score (x k) (x (k + 1)) + potential (x (k + 1)) -
            potential (x k) + B =
          score (x k) (x (k + 1)) +
            (potential (x (k + 1)) - potential (x k)) + B by
      intro k
      ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_poissonPotential_increment]
    simp [Finset.sum_const, nsmul_eq_mul]
  unfold trajectoryEmpiricalPrequentialRisk empiricalTransitionRisk
    poissonEndpointCorrection runningMean runningSum
    poissonCorrectedTrajectoryScore markovTransitionTrajectoryScore
    poissonCorrectedTransitionScore observedTrajectoryScore
  simp only [Preorder.frestrictLe_apply]
  rw [← Finset.sum_div, hsum]
  field_simp [hn0, hden]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ] in
/-- The average corrected conditional risk is the affine rescaling of the
stationary target plus the path-average Poisson residual. -/
theorem trajectoryAverageConditionalRisk_poissonCorrected
    {B : ℝ} (hB : 0 ≤ B)
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryAverageConditionalRisk (prefixKernel P)
        (poissonCorrectedTrajectoryScore B score potential) n x =
      (stationaryMarkovRisk P stationary score +
          poissonResidualAverage P stationary score potential n x + B) /
        (1 + 2 * B) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  unfold trajectoryAverageConditionalRisk poissonResidualAverage
    runningMean runningSum
  simp_rw [conditionalTrajectoryRisk_poissonCorrectedTrajectoryScore
    hB P stationary score potential]
  rw [← Finset.sum_div]
  simp_rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]
  field_simp [hn0, hden]

/-- Posterior stationary risk of the finite transition-score catalog. -/
def stationaryPosteriorMarkovRisk
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (posterior : ι → ℝ) : ℝ :=
  posteriorAverage posterior fun i ↦ stationaryMarkovRisk P stationary (score i)

/-- Posterior empirical transition risk along one path. -/
def empiricalTransitionPosteriorRisk
    (score : ι → MarkovTransitionScore Z) (posterior : ι → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  posteriorAverage posterior fun i ↦ empiricalTransitionRisk (score i) n x

/-- Posterior average of exact potential endpoint corrections. -/
def posteriorPoissonEndpointCorrection
    (potential : ι → Z → ℝ) (posterior : ι → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  posteriorAverage posterior fun i ↦ poissonEndpointCorrection (potential i) n x

/-- Posterior average of encountered approximate-Poisson residuals. -/
def posteriorPoissonResidualAverage
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (potential : ι → Z → ℝ)
    (posterior : ι → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  posteriorAverage posterior fun i ↦
    poissonResidualAverage P stationary (score i) (potential i) n x

omit [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ] in
/-- Posterior form of the corrected conditional-risk identity. -/
theorem trajectoryPosteriorAverageConditionalRisk_poissonCorrected
    {B : ℝ} (hB : 0 ≤ B)
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (potential : ι → Z → ℝ)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryPosteriorAverageConditionalRisk (prefixKernel P)
        (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
        posterior n x =
      (stationaryPosteriorMarkovRisk P stationary score posterior +
          posteriorPoissonResidualAverage P stationary score potential
            posterior n x + B) /
        (1 + 2 * B) := by
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  unfold trajectoryPosteriorAverageConditionalRisk
    stationaryPosteriorMarkovRisk posteriorPoissonResidualAverage
    posteriorAverage
  simp_rw [trajectoryAverageConditionalRisk_poissonCorrected
    hB P stationary _ _ n hn x]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_eq_div_iff hden hden).2
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hposterior.sum_one]
  ring

omit [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Posterior form of the corrected empirical-risk telescoping identity. -/
theorem trajectoryPosteriorEmpiricalPrequentialRisk_poissonCorrected
    {B : ℝ} (hB : 0 ≤ B)
    (score : ι → MarkovTransitionScore Z) (potential : ι → Z → ℝ)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    trajectoryPosteriorEmpiricalPrequentialRisk
        (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
        posterior n x =
      (empiricalTransitionPosteriorRisk score posterior n x +
          posteriorPoissonEndpointCorrection potential posterior n x + B) /
        (1 + 2 * B) := by
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  unfold trajectoryPosteriorEmpiricalPrequentialRisk
    empiricalTransitionPosteriorRisk posteriorPoissonEndpointCorrection
    posteriorAverage
  simp_rw [trajectoryEmpiricalPrequentialRisk_poissonCorrected
    hB _ _ n hn x]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_eq_div_iff hden hden).2
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hposterior.sum_one]
  ring

/-- Exact stationary-risk boundary: observable corrected-score
empirical-Bernstein width, plus the potential endpoint term, minus the
encountered approximate-Poisson residual. -/
def stationaryPoissonEmpiricalBernsteinPACBayesBoundary
    (prior : ι → ℝ) (weight : τ → ℝ) (lam : τ → ℝ)
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (potential : ι → Z → ℝ)
    (B : ℝ) (posterior : ι → ℝ) (delta : ℝ) (j : τ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  (1 + 2 * B) *
      trajectoryEmpiricalBernsteinPACBayesBoundary
        prior weight lam
          (fun i ↦ poissonCorrectedTrajectoryScore B (score i) (potential i))
          posterior delta j n x +
    posteriorPoissonEndpointCorrection potential posterior n x -
    posteriorPoissonResidualAverage
      P stationary score potential posterior n x

/-- Supplied-Poisson stationary-risk capstone.  One outer-probability event is
simultaneous over all `n >= 2`, posterior PMFs, and finite declared tilt atoms.
The invariant law and Poisson potentials are inputs, not conclusions.  The
invariance witness supplies the stationary interpretation of the target; the
concentration proof itself uses the supplied residual identity. -/
theorem exists_stationaryPoissonEmpiricalBernsteinPACBayes_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (_hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {potential : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  stationaryPoissonEmpiricalBernsteinPACBayesBoundary
                    prior weight lam P stationary score potential B
                      posterior delta j n x := by
  have hcorrected : ∀ i n u y,
      poissonCorrectedTrajectoryScore B (score i) (potential i) n u y ∈
        Set.Icc (0 : ℝ) 1 := by
    intro i n u y
    exact poissonCorrectedTransitionScore_mem_Icc hB (hscore i)
      (hspan i) (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
  rcases exists_trajectoryEmpiricalBernsteinPACBayes_event
      (ι := ι) (τ := τ) (K := prefixKernel P) x0
      hcorrected hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · simpa [trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass
  · intro x hx j posterior hposterior n hn
    have hnpos : 0 < n := by omega
    have hden : 0 < 1 + 2 * B := by linarith
    have hbound := hgood x hx j posterior hposterior n hn
    rw [trajectoryPosteriorAverageConditionalRisk_poissonCorrected
      hB P stationary score potential posterior hposterior n hnpos x,
      trajectoryPosteriorEmpiricalPrequentialRisk_poissonCorrected
        hB score potential posterior hposterior n hnpos x] at hbound
    have hscaled := mul_lt_mul_of_pos_right hbound hden
    unfold stationaryPoissonEmpiricalBernsteinPACBayesBoundary
    field_simp [ne_of_gt hden] at hscaled
    linarith

omit [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The posterior endpoint correction is at most `B / n` under the common
potential-oscillation bound. -/
theorem posteriorPoissonEndpointCorrection_le
    {B : ℝ} (_hB : 0 ≤ B)
    {potential : ι → Z → ℝ}
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    (n : ℕ) (_hn : 0 < n) (x : ℕ → Z) :
    posteriorPoissonEndpointCorrection potential posterior n x ≤
      B / (n : ℝ) := by
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold posteriorPoissonEndpointCorrection posteriorAverage
    poissonEndpointCorrection
  calc
    ∑ i : ι, posterior i *
        ((potential i (x n) - potential i (x 0)) / (n : ℝ)) ≤
        ∑ i : ι, posterior i * (B / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_left _ (hposterior.nonneg i)
      exact div_le_div_of_nonneg_right
        ((le_abs_self _).trans (hspan i (x 0) (x n))) hnreal
    _ = B / (n : ℝ) := by
      rw [← Finset.sum_mul, hposterior.sum_one, one_mul]

omit [DecidableEq ι] [Nonempty ι]
  [Fintype τ] [DecidableEq τ]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- A pointwise residual envelope controls the negative encountered residual
term after posterior averaging. -/
theorem neg_posteriorPoissonResidualAverage_le
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : ι → MarkovTransitionScore Z) (potential : ι → Z → ℝ)
    {residualEnvelope : ι → ℝ} (_henvelope : ∀ i, 0 ≤ residualEnvelope i)
    (hresidual : ∀ i z,
      |approximatePoissonResidual
        P stationary (score i) (potential i) z| ≤ residualEnvelope i)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    -posteriorPoissonResidualAverage
        P stationary score potential posterior n x ≤
      posteriorAverage posterior residualEnvelope := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold posteriorPoissonResidualAverage posteriorAverage
  rw [show
      -(∑ i : ι, posterior i *
          poissonResidualAverage P stationary (score i) (potential i) n x) =
        ∑ i : ι, posterior i *
          (-poissonResidualAverage P stationary (score i) (potential i) n x) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  apply Finset.sum_le_sum
  intro i _hi
  apply mul_le_mul_of_nonneg_left _ (hposterior.nonneg i)
  unfold poissonResidualAverage runningMean runningSum
  rw [← neg_div]
  apply (div_le_iff₀ hnreal).2
  have hsum :
      ∑ k ∈ Finset.range n,
          -approximatePoissonResidual
            P stationary (score i) (potential i) (x k) ≤
        ∑ _k ∈ Finset.range n, residualEnvelope i := by
    apply Finset.sum_le_sum
    intro k _hk
    exact (neg_le_abs _).trans (hresidual i (x k))
  rw [Finset.sum_neg_distrib] at hsum
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

/-- Human-readable approximate-Poisson corollary.  The exact endpoint term is
bounded by `B / n`, and the signed residual is bounded by its posterior
envelope. -/
theorem exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {potential : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    {residualEnvelope : ι → ℝ} (henvelope : ∀ i, 0 ≤ residualEnvelope i)
    (hresidual : ∀ i z,
      |approximatePoissonResidual
        P stationary (score i) (potential i) z| ≤ residualEnvelope i)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * B) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          B (score i) (potential i))
                        posterior delta j n x +
                  B / (n : ℝ) + posteriorAverage posterior residualEnvelope := by
  rcases exists_stationaryPoissonEmpiricalBernsteinPACBayes_event
      P stationary hstationary x0 hscore hB hspan
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hnpos : 0 < n := by omega
  have hbase := hgood x hx j posterior hposterior n hn
  have hendpoint := posteriorPoissonEndpointCorrection_le
    hB hspan hposterior n hnpos x
  have hres := neg_posteriorPoissonResidualAverage_le
    P stationary score potential henvelope hresidual hposterior n hnpos x
  unfold stationaryPoissonEmpiricalBernsteinPACBayesBoundary at hbase
  linarith

/-- Exact-Poisson specialization: the residual correction disappears, while
the exact telescoping endpoint term remains visible. -/
theorem exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {potential : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    (hpoisson : ∀ i,
      IsExactPoissonSolution P stationary (score i) (potential i))
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * B) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          B (score i) (potential i))
                        posterior delta j n x +
                  posteriorPoissonEndpointCorrection
                    potential posterior n x := by
  rcases exists_stationaryPoissonEmpiricalBernsteinPACBayes_event
      P stationary hstationary x0 hscore hB hspan
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hbase := hgood x hx j posterior hposterior n hn
  have hzero : ∀ i z,
      approximatePoissonResidual
        P stationary (score i) (potential i) z = 0 := by
    intro i z
    exact hpoisson i z
  have hresidual_zero :
      posteriorPoissonResidualAverage
        P stationary score potential posterior n x = 0 := by
    unfold posteriorPoissonResidualAverage poissonResidualAverage
      posteriorAverage runningMean runningSum
    simp [hzero]
  unfold stationaryPoissonEmpiricalBernsteinPACBayesBoundary at hbase
  rw [hresidual_zero] at hbase
  linarith

/-- Exact-Poisson corollary with only the simple `B / n` endpoint price. -/
theorem exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_span_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : ι → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {potential : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    (hpoisson : ∀ i,
      IsExactPoissonSolution P stationary (score i) (potential i))
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * B) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          B (score i) (potential i))
                        posterior delta j n x +
                  B / (n : ℝ) := by
  rcases exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_event
      P stationary hstationary x0 hscore hB hspan hpoisson
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hnpos : 0 < n := by omega
  have hbase := hgood x hx j posterior hposterior n hn
  have hendpoint := posteriorPoissonEndpointCorrection_le
    hB hspan hposterior n hnpos x
  linarith

end

end FormalSLT.StochasticDynamics
