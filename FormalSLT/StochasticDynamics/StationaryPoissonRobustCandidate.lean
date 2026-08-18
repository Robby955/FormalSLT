/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin

/-!
# Stationary-risk certificates from a predeclared candidate kernel

This module separates the transition kernel that generates the trajectory
from a fixed candidate kernel used to construct a Poisson correction.  For a
true kernel `P`, candidate `Q`, transition score `score`, and potential `h`,
write

`g_K(z) = rowRisk_K(z) + K h(z) - h(z)`.

If every row of `P` is within probabilists' total variation `eta` of the
corresponding row of `Q`, the score lies in `[0,1]`, and `h` has span at most
`B`, then `|g_P-g_Q| <= (1+B) eta`.  Centering at an invariant law of `P`
costs this perturbation twice: once at the queried state and once in the
stationary average.  The resulting honest residual envelope is therefore

`osc(g_Q) + 2 (1+B) eta`.

The finite-depth capstone constructs `h` from `Q` and a fixed reference PMF.
It uses the computed Dobrushin coefficient of `Q` and has residual price

`alpha_Q^m D + 2 (1+B_m) eta`.

The candidate kernel, reference PMF, depth, and potential are fixed inputs.
The theorems do not estimate the true kernel, discover its invariant law, or
justify data-dependent selection of the candidate.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Poisson drift before subtracting any stationary target. -/
def markovPoissonDrift (K : Z → PMF Z) (score : MarkovTransitionScore Z)
    (potential : Z → ℝ) (z : Z) : ℝ :=
  markovRowRisk K score z + markovPotentialMean K potential z - potential z

omit [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
lemma approximatePoissonResidual_eq_markovPoissonDrift_sub
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ) (z : Z) :
    approximatePoissonResidual P stationary score potential z =
      markovPoissonDrift P score potential z -
        stationaryMarkovRisk P stationary score := by
  rfl

/-- Maximum of a real function on the finite nonempty state space. -/
def finiteMaximum (f : Z → ℝ) : ℝ :=
  (Finset.univ : Finset Z).sup' Finset.univ_nonempty f

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma le_finiteMaximum (f : Z → ℝ) (z : Z) : f z ≤ finiteMaximum f := by
  exact Finset.le_sup' (f := f) (Finset.mem_univ z)

/-- A finite PMF average is at most the finite maximum. -/
lemma pmfIntegral_le_finiteMaximum (p : PMF Z) (f : Z → ℝ) :
    (∫ z, f z ∂p.toMeasure) ≤ finiteMaximum f := by
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  calc
    (∑ z : Z, (p z).toReal * f z) ≤
        ∑ z : Z, (p z).toReal * finiteMaximum f := by
      apply Finset.sum_le_sum
      intro z _hz
      exact mul_le_mul_of_nonneg_left (le_finiteMaximum f z)
        ENNReal.toReal_nonneg
    _ = finiteMaximum f := by
      rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

/-- Every point differs from a finite PMF average by at most the function's
oscillation. -/
lemma abs_sub_pmfIntegral_le_finiteOscillation
    (p : PMF Z) (f : Z → ℝ) (z : Z) :
    |f z - ∫ y, f y ∂p.toMeasure| ≤ finiteOscillation f := by
  have hmass : ∑ y : Z, (p y).toReal = 1 := finitePMF_real_mass_sum p
  have hrepr :
      f z - ∫ y, f y ∂p.toMeasure =
        ∑ y : Z, (p y).toReal * (f z - f y) := by
    simp only [PMF.integral_eq_sum, smul_eq_mul]
    calc
      f z - ∑ y : Z, (p y).toReal * f y =
          (∑ y : Z, (p y).toReal * f z) -
            ∑ y : Z, (p y).toReal * f y := by
        rw [← Finset.sum_mul, hmass, one_mul]
      _ = ∑ y : Z, (p y).toReal * (f z - f y) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
  rw [hrepr]
  calc
    |∑ y : Z, (p y).toReal * (f z - f y)| ≤
        ∑ y : Z, |(p y).toReal * (f z - f y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y : Z, (p y).toReal * |f z - f y| := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ y : Z, (p y).toReal * finiteOscillation f := by
      apply Finset.sum_le_sum
      intro y _hy
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa [abs_sub_comm] using abs_sub_le_finiteOscillation f z y
    _ = finiteOscillation f := by
      rw [← Finset.sum_mul, hmass, one_mul]

omit [Nonempty Z] in
/-- Pointwise absolute control transfers to the difference of finite PMF
averages with the same constant. -/
lemma abs_pmfIntegral_sub_le_of_abs_sub_le
    (p : PMF Z) (f g : Z → ℝ) {epsilon : ℝ}
    (h : ∀ z, |f z - g z| ≤ epsilon) :
    |(∫ z, f z ∂p.toMeasure) - ∫ z, g z ∂p.toMeasure| ≤ epsilon := by
  have hmass : ∑ z : Z, (p z).toReal = 1 := finitePMF_real_mass_sum p
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ z : Z, (p z).toReal * (f z - g z)| ≤
        ∑ z : Z, |(p z).toReal * (f z - g z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : Z, (p z).toReal * |f z - g z| := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ z : Z, (p z).toReal * epsilon := by
      apply Finset.sum_le_sum
      intro z _hz
      exact mul_le_mul_of_nonneg_left (h z) ENNReal.toReal_nonneg
    _ = epsilon := by
      rw [← Finset.sum_mul, hmass, one_mul]

omit [Nonempty Z] in
/-- Invariance makes the stationary average of the true Poisson drift equal
to the true stationary transition risk. -/
lemma markovPoissonDrift_stationary_mean
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    (score : MarkovTransitionScore Z) (potential : Z → ℝ) :
    (∫ z, markovPoissonDrift P score potential z ∂stationary.toMeasure) =
      stationaryMarkovRisk P stationary score := by
  have hinvariant := markovPotentialMean_invariant
    P stationary hstationary potential
  simp only [PMF.integral_eq_sum, smul_eq_mul] at hinvariant ⊢
  unfold markovPoissonDrift stationaryMarkovRisk
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  calc
    (∑ z : Z, (stationary z).toReal *
        (markovRowRisk P score z + markovPotentialMean P potential z -
          potential z)) =
      (∑ z : Z, (stationary z).toReal * markovRowRisk P score z) +
        (∑ z : Z, (stationary z).toReal * markovPotentialMean P potential z) -
          ∑ z : Z, (stationary z).toReal * potential z := by
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ z : Z, (stationary z).toReal * markovRowRisk P score z := by
      rw [hinvariant]
      ring

/-- The true and candidate Poisson drifts differ by at most `(1+B) eta`.
The factor `1` is the `[0,1]` transition score; `B` is the potential span. -/
theorem abs_markovPoissonDrift_sub_candidate_le
    (P Q : Z → PMF Z) {score : MarkovTransitionScore Z}
    {potential : Z → ℝ} {B eta : ℝ}
    (heta : 0 ≤ eta)
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (z : Z) :
    |markovPoissonDrift P score potential z -
        markovPoissonDrift Q score potential z| ≤ (1 + B) * eta := by
  have hscoreOsc : finiteOscillation (score z) ≤ 1 := by
    apply finiteOscillation_le
    intro x y
    rcases hscore z x with ⟨hx0, hx1⟩
    rcases hscore z y with ⟨hy0, hy1⟩
    rw [abs_le]
    constructor <;> linarith
  have hpotentialOsc : finiteOscillation potential ≤ B :=
    finiteOscillation_le potential hspan
  have hrow :
      |markovRowRisk P score z - markovRowRisk Q score z| ≤ eta := by
    calc
      |markovRowRisk P score z - markovRowRisk Q score z| ≤
          finitePMFTotalVariation (P z) (Q z) * finiteOscillation (score z) := by
        simpa only [markovRowRisk] using
          abs_pmfIntegral_sub_le_totalVariation_mul_oscillation
            (P z) (Q z) (score z)
      _ ≤ eta * finiteOscillation (score z) :=
        mul_le_mul_of_nonneg_right (hrowTV z) (finiteOscillation_nonneg _)
      _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hscoreOsc heta
      _ = eta := mul_one eta
  have hpotential :
      |markovPotentialMean P potential z -
          markovPotentialMean Q potential z| ≤ eta * B := by
    calc
      |markovPotentialMean P potential z -
          markovPotentialMean Q potential z| ≤
          finitePMFTotalVariation (P z) (Q z) *
            finiteOscillation potential := by
        simpa only [markovPotentialMean] using
          abs_pmfIntegral_sub_le_totalVariation_mul_oscillation
            (P z) (Q z) potential
      _ ≤ eta * finiteOscillation potential :=
        mul_le_mul_of_nonneg_right (hrowTV z) (finiteOscillation_nonneg _)
      _ ≤ eta * B := mul_le_mul_of_nonneg_left hpotentialOsc heta
  unfold markovPoissonDrift
  rw [show
      markovRowRisk P score z + markovPotentialMean P potential z - potential z -
          (markovRowRisk Q score z + markovPotentialMean Q potential z - potential z) =
        (markovRowRisk P score z - markovRowRisk Q score z) +
          (markovPotentialMean P potential z -
            markovPotentialMean Q potential z) by ring]
  calc
    |(markovRowRisk P score z - markovRowRisk Q score z) +
        (markovPotentialMean P potential z -
          markovPotentialMean Q potential z)| ≤
      |markovRowRisk P score z - markovRowRisk Q score z| +
        |markovPotentialMean P potential z -
          markovPotentialMean Q potential z| := abs_add_le _ _
    _ ≤ eta + eta * B := add_le_add hrow hpotential
    _ = (1 + B) * eta := by ring

/-- Correct robust residual transfer.  Centering at the true invariant law
uses the pointwise drift perturbation twice, hence the factor `2`. -/
theorem abs_stationaryPoissonResidual_le_candidateOscillation
    (P Q : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    {score : MarkovTransitionScore Z} {potential : Z → ℝ}
    {B eta : ℝ} (heta : 0 ≤ eta)
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (z : Z) :
    |approximatePoissonResidual P stationary score potential z| ≤
      finiteOscillation (markovPoissonDrift Q score potential) +
        2 * ((1 + B) * eta) := by
  let epsilon : ℝ := (1 + B) * eta
  have hdrift : ∀ y,
      |markovPoissonDrift P score potential y -
          markovPoissonDrift Q score potential y| ≤ epsilon := by
    intro y
    exact abs_markovPoissonDrift_sub_candidate_le
      P Q heta hscore hspan hrowTV y
  have hmeans :
      |(∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure) -
          ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure| ≤
        epsilon :=
    abs_pmfIntegral_sub_le_of_abs_sub_le stationary _ _ hdrift
  have hcandidate :
      |markovPoissonDrift Q score potential z -
          ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure| ≤
        finiteOscillation (markovPoissonDrift Q score potential) :=
    abs_sub_pmfIntegral_le_finiteOscillation
      stationary (markovPoissonDrift Q score potential) z
  rw [approximatePoissonResidual_eq_markovPoissonDrift_sub,
    ← markovPoissonDrift_stationary_mean P stationary hstationary score potential]
  rw [show
      markovPoissonDrift P score potential z -
          ∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure =
        (markovPoissonDrift P score potential z -
          markovPoissonDrift Q score potential z) +
        (markovPoissonDrift Q score potential z -
          ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) +
        ((∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) -
          ∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure) by
    ring]
  calc
    |(markovPoissonDrift P score potential z -
        markovPoissonDrift Q score potential z) +
      (markovPoissonDrift Q score potential z -
        ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) +
      ((∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) -
        ∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure)| ≤
      |markovPoissonDrift P score potential z -
        markovPoissonDrift Q score potential z| +
      |markovPoissonDrift Q score potential z -
        ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure| +
      |(∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) -
        ∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ epsilon +
        finiteOscillation (markovPoissonDrift Q score potential) + epsilon := by
      exact add_le_add (add_le_add (hdrift z) hcandidate)
        (by simpa [abs_sub_comm] using hmeans)
    _ = finiteOscillation (markovPoissonDrift Q score potential) +
        2 * ((1 + B) * eta) := by
      dsimp [epsilon]
      ring

/-- One-sided, state-sharp robust transfer.  The candidate term retains the
actual state rather than replacing it immediately by an oscillation bound. -/
theorem stationaryRisk_sub_markovPoissonDrift_le_candidateMeanGap
    (P Q : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    {score : MarkovTransitionScore Z} {potential : Z → ℝ}
    {B eta : ℝ} (heta : 0 ≤ eta)
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (z : Z) :
    stationaryMarkovRisk P stationary score -
        markovPoissonDrift P score potential z ≤
      (∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) -
        markovPoissonDrift Q score potential z +
          2 * ((1 + B) * eta) := by
  let epsilon : ℝ := (1 + B) * eta
  have hdrift : ∀ y,
      |markovPoissonDrift P score potential y -
          markovPoissonDrift Q score potential y| ≤ epsilon := by
    intro y
    exact abs_markovPoissonDrift_sub_candidate_le
      P Q heta hscore hspan hrowTV y
  have hmeans := abs_pmfIntegral_sub_le_of_abs_sub_le
    stationary (markovPoissonDrift P score potential)
      (markovPoissonDrift Q score potential) hdrift
  have hmeanUpper :
      stationaryMarkovRisk P stationary score ≤
        (∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) +
          epsilon := by
    rw [← markovPoissonDrift_stationary_mean
      P stationary hstationary score potential]
    linarith [hmeans, le_abs_self
      ((∫ y, markovPoissonDrift P score potential y ∂stationary.toMeasure) -
        ∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure)]
  have hpointLower :
      markovPoissonDrift Q score potential z - epsilon ≤
        markovPoissonDrift P score potential z := by
    linarith [hdrift z, neg_abs_le
      (markovPoissonDrift P score potential z -
        markovPoissonDrift Q score potential z)]
  dsimp [epsilon] at hmeanUpper hpointLower ⊢
  linarith

/-- Max-minus-state form of the one-sided robust residual.  This removes the
candidate stationary average and is often sharper along a realized path than
a global absolute oscillation envelope. -/
theorem stationaryRisk_sub_markovPoissonDrift_le_candidateMaxGap
    (P Q : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    {score : MarkovTransitionScore Z} {potential : Z → ℝ}
    {B eta : ℝ} (heta : 0 ≤ eta)
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (z : Z) :
    stationaryMarkovRisk P stationary score -
        markovPoissonDrift P score potential z ≤
      finiteMaximum (markovPoissonDrift Q score potential) -
        markovPoissonDrift Q score potential z +
          2 * ((1 + B) * eta) := by
  have hmeanGap :
      stationaryMarkovRisk P stationary score -
          markovPoissonDrift P score potential z ≤
        (∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) -
          markovPoissonDrift Q score potential z +
            2 * ((1 + B) * eta) :=
    stationaryRisk_sub_markovPoissonDrift_le_candidateMeanGap
      P Q stationary hstationary heta hscore hspan hrowTV z
  have hmeanMax :
      (∫ y, markovPoissonDrift Q score potential y ∂stationary.toMeasure) ≤
        finiteMaximum (markovPoissonDrift Q score potential) :=
    pmfIntegral_le_finiteMaximum stationary
      (markovPoissonDrift Q score potential)
  linarith [hmeanGap, hmeanMax]

/-- Running average of a fixed candidate drift along the observed states. -/
def candidatePoissonDriftRunningMean
    (Q : Z → PMF Z) (score : MarkovTransitionScore Z)
    (potential : Z → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  runningMean (fun k x ↦ markovPoissonDrift Q score potential (x k)) n x

/-- Running average of the candidate max-minus-state gap. -/
def candidatePoissonMaxGapAverage
    (Q : Z → PMF Z) (score : MarkovTransitionScore Z)
    (potential : Z → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  runningMean (fun k x ↦
    finiteMaximum (markovPoissonDrift Q score potential) -
      markovPoissonDrift Q score potential (x k)) n x

omit [MeasurableSingletonClass Z] in
/-- The candidate max-gap average is exactly max minus the candidate drift
average for every positive horizon. -/
lemma candidatePoissonMaxGapAverage_eq_max_sub_runningMean
    (Q : Z → PMF Z) (score : MarkovTransitionScore Z)
    (potential : Z → ℝ) (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    candidatePoissonMaxGapAverage Q score potential n x =
      finiteMaximum (markovPoissonDrift Q score potential) -
        candidatePoissonDriftRunningMean Q score potential n x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold candidatePoissonMaxGapAverage candidatePoissonDriftRunningMean
    runningMean runningSum
  have hsum :
      ∑ k ∈ Finset.range n,
          (finiteMaximum (markovPoissonDrift Q score potential) -
            markovPoissonDrift Q score potential (x k)) =
        (n : ℝ) * finiteMaximum (markovPoissonDrift Q score potential) -
          ∑ k ∈ Finset.range n,
            markovPoissonDrift Q score potential (x k) := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  field_simp [hn0]

/-- Path-sharp max-minus-average form.  Only the uniform misspecification
price is global; the candidate drift deficit is retained on the realized
states. -/
theorem neg_poissonResidualAverage_le_candidateMaxGapAverage
    (P Q : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    {score : MarkovTransitionScore Z} {potential : Z → ℝ}
    {B eta : ℝ} (heta : 0 ≤ eta)
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ x y, |potential y - potential x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (n : ℕ) (hn : 0 < n) (x : ℕ → Z) :
    -poissonResidualAverage P stationary score potential n x ≤
      candidatePoissonMaxGapAverage Q score potential n x +
        2 * ((1 + B) * eta) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum :
      ∑ k ∈ Finset.range n,
          (stationaryMarkovRisk P stationary score -
            markovPoissonDrift P score potential (x k)) ≤
        ∑ k ∈ Finset.range n,
          (finiteMaximum (markovPoissonDrift Q score potential) -
            markovPoissonDrift Q score potential (x k) +
              2 * ((1 + B) * eta)) := by
    apply Finset.sum_le_sum
    intro k _hk
    exact stationaryRisk_sub_markovPoissonDrift_le_candidateMaxGap
      P Q stationary hstationary heta hscore hspan hrowTV (x k)
  have hleft :
      -poissonResidualAverage P stationary score potential n x =
        (∑ k ∈ Finset.range n,
          (stationaryMarkovRisk P stationary score -
            markovPoissonDrift P score potential (x k))) / (n : ℝ) := by
    unfold poissonResidualAverage runningMean runningSum
    rw [← neg_div, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _hk
    change -approximatePoissonResidual P stationary score potential (x k) = _
    rw [approximatePoissonResidual_eq_markovPoissonDrift_sub]
    ring
  have hright :
      (∑ k ∈ Finset.range n,
          (finiteMaximum (markovPoissonDrift Q score potential) -
            markovPoissonDrift Q score potential (x k) +
              2 * ((1 + B) * eta))) / (n : ℝ) =
        candidatePoissonMaxGapAverage Q score potential n x +
          2 * ((1 + B) * eta) := by
    unfold candidatePoissonMaxGapAverage runningMean runningSum
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [ne_of_gt hnreal]
  rw [hleft, ← hright]
  exact div_le_div_of_nonneg_right hsum hnreal.le

omit [Nonempty Z] in
/-- The finite-depth candidate drift equals its reference risk plus the
`m`-step contracted centered row risk.  No invariance of the candidate
reference PMF is needed for this algebraic identity. -/
lemma markovPoissonDrift_finiteDepth_eq
    (Q : Z → PMF Z) (reference : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ) (z : Z) :
    markovPoissonDrift Q score
        (finiteDepthPoissonPotential Q reference score m) z =
      stationaryMarkovRisk Q reference score +
        iteratedMarkovPotentialMean Q m
          (centeredMarkovRowRisk Q reference score) z := by
  have h := finiteDepthPoisson_residual_identity Q reference score m z
  rw [approximatePoissonResidual_eq_markovPoissonDrift_sub] at h
  linarith

/-- The candidate drift of the automatic depth-`m` potential has oscillation
at most `alpha^m D`. -/
lemma finiteOscillation_markovPoissonDrift_finiteDepth_le
    (Q : Z → PMF Z) (reference : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ)
    {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : IsOscillationContraction Q alpha)
    (hD : finiteOscillation
      (centeredMarkovRowRisk Q reference score) ≤ D) :
    finiteOscillation
        (markovPoissonDrift Q score
          (finiteDepthPoissonPotential Q reference score m)) ≤
      alpha ^ m * D := by
  apply finiteOscillation_le
  intro x y
  rw [markovPoissonDrift_finiteDepth_eq,
    markovPoissonDrift_finiteDepth_eq]
  calc
    |(stationaryMarkovRisk Q reference score +
          iteratedMarkovPotentialMean Q m
            (centeredMarkovRowRisk Q reference score) y) -
        (stationaryMarkovRisk Q reference score +
          iteratedMarkovPotentialMean Q m
            (centeredMarkovRowRisk Q reference score) x)| =
      |iteratedMarkovPotentialMean Q m
          (centeredMarkovRowRisk Q reference score) y -
        iteratedMarkovPotentialMean Q m
          (centeredMarkovRowRisk Q reference score) x| := by ring_nf
    _ ≤ finiteOscillation
        (iteratedMarkovPotentialMean Q m
          (centeredMarkovRowRisk Q reference score)) :=
      abs_sub_le_finiteOscillation _ _ _
    _ ≤ alpha ^ m * finiteOscillation
        (centeredMarkovRowRisk Q reference score) :=
      iteratedMarkovPotentialMean_oscillation_le
        Q halpha hcontract _ m
    _ ≤ alpha ^ m * D :=
      mul_le_mul_of_nonneg_left hD (pow_nonneg halpha m)

variable {I T : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype T] [DecidableEq T]

/-- Empirical-Bernstein PAC-Bayes stationary-risk event for fixed candidate
Poisson potentials.  The candidate oscillation and the doubled row-TV price
are averaged under the selected posterior. -/
theorem exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_event
    (P Q : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {potential : I → Z → ℝ} {B eta : ℝ}
    (hB : 0 ≤ B) (heta : 0 ≤ eta)
    (hspan : ∀ i x y, |potential i y - potential i x| ≤ B)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : T → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : T → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : T,
          ∀ posterior : I → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * B) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          B (score i) (potential i))
                        posterior delta j n x +
                  B / (n : ℝ) +
                    posteriorAverage posterior (fun i ↦
                      finiteOscillation
                        (markovPoissonDrift Q (score i) (potential i)) +
                      2 * ((1 + B) * eta)) := by
  have henvelope : ∀ i : I,
      0 ≤ finiteOscillation
          (markovPoissonDrift Q (score i) (potential i)) +
        2 * ((1 + B) * eta) := by
    intro i
    exact add_nonneg (finiteOscillation_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) heta))
  have hresidual : ∀ i z,
      |approximatePoissonResidual P stationary (score i) (potential i) z| ≤
        finiteOscillation
            (markovPoissonDrift Q (score i) (potential i)) +
          2 * ((1 + B) * eta) := by
    intro i z
    exact abs_stationaryPoissonResidual_le_candidateOscillation
      P Q stationary hstationary heta (hscore i) (hspan i) hrowTV z
  exact exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
    P stationary hstationary x0 hscore hB hspan henvelope hresidual
      hprior hweight hdelta hlam hlam_one

/-- Automatic finite-depth robust candidate-kernel capstone.  The candidate
potential is built from `Q` and a fixed reference PMF; only the supplied
`stationary` PMF of the true kernel `P` is assumed invariant.  The residual
price is the corrected
`alpha_Q^m D + 2 (1+B_m) eta`, with `B_m` the closed geometric span bound. -/
theorem exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event
    (P Q : Z → PMF Z) (stationary reference : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D eta : ℝ} (hDnonneg : 0 ≤ D) (heta : 0 ≤ eta)
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcoefficient : finiteDobrushinCoefficient Q < 1)
    (hD : ∀ i, finiteOscillation
      (centeredMarkovRowRisk Q reference (score i)) ≤ D)
    (m : ℕ)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : T → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : T → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : T,
          ∀ posterior : I → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient Q) D m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound
                            (finiteDobrushinCoefficient Q) D m)
                          (score i)
                          (finiteDepthPoissonPotential Q reference (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient Q) D m / (n : ℝ) +
                  ((finiteDobrushinCoefficient Q) ^ m * D +
                    2 * ((1 + finiteDepthPoissonClosedSpanBound
                      (finiteDobrushinCoefficient Q) D m) * eta)) := by
  let alpha : ℝ := finiteDobrushinCoefficient Q
  let B : ℝ := finiteDepthPoissonClosedSpanBound alpha D m
  have halpha : 0 ≤ alpha := finiteDobrushinCoefficient_nonneg Q
  have hcontract : IsOscillationContraction Q alpha :=
    finiteDobrushinCoefficient_isOscillationContraction Q
  have hB : 0 ≤ B := by
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed hcoefficient m).symm]
    exact finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hspan : ∀ i x y,
      |finiteDepthPoissonPotential Q reference (score i) m y -
        finiteDepthPoissonPotential Q reference (score i) m x| ≤ B := by
    intro i x y
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed hcoefficient m).symm]
    exact finiteDepthPoissonPotential_span Q reference (score i) m
      halpha hcontract (hD i) x y
  let residual : ℝ := alpha ^ m * D + 2 * ((1 + B) * eta)
  have hresidual_nonneg : 0 ≤ residual := by
    dsimp [residual]
    exact add_nonneg (mul_nonneg (pow_nonneg halpha m) hDnonneg)
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) heta))
  have hresidual : ∀ i z,
      |approximatePoissonResidual P stationary (score i)
        (finiteDepthPoissonPotential Q reference (score i) m) z| ≤ residual := by
    intro i z
    have hrobust := abs_stationaryPoissonResidual_le_candidateOscillation
      P Q stationary hstationary heta (hscore i) (hspan i) hrowTV z
    have hosc := finiteOscillation_markovPoissonDrift_finiteDepth_le
      Q reference (score i) m halpha hcontract (hD i)
    dsimp [residual]
    exact hrobust.trans (add_le_add hosc (le_refl _))
  rcases exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
      P stationary hstationary x0 hscore hB hspan
      (fun _i : I ↦ hresidual_nonneg) hresidual
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hbase := hgood x hx j posterior hposterior n hn
  have hposteriorResidual :
      posteriorAverage posterior (fun _i : I ↦ residual) = residual := by
    unfold posteriorAverage
    rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
  rw [hposteriorResidual] at hbase
  simpa only [alpha, B, residual] using hbase

end

end FormalSLT.StochasticDynamics
