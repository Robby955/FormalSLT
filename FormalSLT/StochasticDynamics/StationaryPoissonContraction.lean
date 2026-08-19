/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonPACBayes

/-!
# Finite-depth Poisson construction under oscillation contraction

This module constructs the approximate Poisson potential used by the
stationary-risk PAC-Bayes bridge.  For the Markov operator `T`, centered row
risk `u`, and predeclared depth `m`, it uses

`h_m = sum_{t < m} T^t u`.

The construction has exact residual `T^m u`.  Under a supplied oscillation
contraction factor `alpha` and initial oscillation bound `D`, its potential
span is at most `D * sum_{t < m} alpha^t` and its residual is at most
`alpha^m * D`.  Invariance of the supplied PMF is used to convert the
oscillation bound on the residual into a pointwise absolute bound.

The module does not infer contraction from a kernel, select `m` from data, or
estimate an unknown transition matrix or invariant law.  Those are separate
interfaces.  Its capstone simply instantiates the existing supplied-Poisson
empirical-Bernstein event with the constructed finite-depth potential.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- Maximum pairwise absolute difference of a real function on a finite,
nonempty state space. -/
def finiteOscillation (f : Z → ℝ) : ℝ :=
  (Finset.univ : Finset Z).sup' Finset.univ_nonempty fun x ↦
    (Finset.univ : Finset Z).sup' Finset.univ_nonempty fun y ↦ |f y - f x|

lemma abs_sub_le_finiteOscillation (f : Z → ℝ) (x y : Z) :
    |f y - f x| ≤ finiteOscillation f := by
  unfold finiteOscillation
  exact (Finset.le_sup' (s := (Finset.univ : Finset Z))
    (fun y ↦ |f y - f x|) (Finset.mem_univ y)).trans
      (Finset.le_sup' (s := (Finset.univ : Finset Z))
        (fun x ↦ (Finset.univ : Finset Z).sup' Finset.univ_nonempty
          (fun y ↦ |f y - f x|)) (Finset.mem_univ x))

lemma finiteOscillation_le (f : Z → ℝ) {D : ℝ}
    (h : ∀ x y, |f y - f x| ≤ D) : finiteOscillation f ≤ D := by
  unfold finiteOscillation
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro x _hx
  exact Finset.sup'_le Finset.univ_nonempty _ fun y _hy ↦ h x y

lemma finiteOscillation_nonneg (f : Z → ℝ) : 0 ≤ finiteOscillation f := by
  have h := abs_sub_le_finiteOscillation f (Classical.choice inferInstance)
    (Classical.choice inferInstance)
  simpa using h

variable [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
lemma markovPotentialMean_zero (P : Z → PMF Z) :
    markovPotentialMean P (fun _ ↦ 0) = fun _ ↦ 0 := by
  funext z
  simp [markovPotentialMean]

omit [Nonempty Z] in
lemma markovPotentialMean_add (P : Z → PMF Z) (f g : Z → ℝ) :
    markovPotentialMean P (fun z ↦ f z + g z) =
      fun z ↦ markovPotentialMean P f z + markovPotentialMean P g z := by
  funext z
  simp only [markovPotentialMean, PMF.integral_eq_sum, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]

omit [Nonempty Z] in
lemma markovPotentialMean_sub (P : Z → PMF Z) (f g : Z → ℝ) :
    markovPotentialMean P (fun z ↦ f z - g z) =
      fun z ↦ markovPotentialMean P f z - markovPotentialMean P g z := by
  funext z
  simp only [markovPotentialMean, PMF.integral_eq_sum, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

omit [Nonempty Z] in
lemma markovPotentialMean_sum (P : Z → PMF Z) (m : ℕ) (f : ℕ → Z → ℝ) :
    markovPotentialMean P (fun z ↦ ∑ t ∈ Finset.range m, f t z) =
      fun z ↦ ∑ t ∈ Finset.range m, markovPotentialMean P (f t) z := by
  induction m with
  | zero => simpa using markovPotentialMean_zero P
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      rw [markovPotentialMean_add, ih]

omit [Nonempty Z] in
lemma markovPotentialMean_invariant
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (f : Z → ℝ) :
    ∫ z, markovPotentialMean P f z ∂stationary.toMeasure =
      ∫ z, f z ∂stationary.toMeasure := by
  have hpoint : ∀ y : Z,
      ∑ z : Z, (stationary z).toReal * (P z y).toReal =
        (stationary y).toReal := by
    intro y
    have heq := congrArg (fun q : PMF Z ↦ q y) hstationary
    have hreal := congrArg ENNReal.toReal heq
    rw [PMF.bind_apply, tsum_fintype] at hreal
    rw [ENNReal.toReal_sum (by
      intro a _ha
      exact ENNReal.mul_ne_top (PMF.apply_ne_top stationary a)
        (PMF.apply_ne_top (P a) y))] at hreal
    simpa only [ENNReal.toReal_mul] using hreal
  simp only [markovPotentialMean, PMF.integral_eq_sum, smul_eq_mul]
  calc
    ∑ z : Z, (stationary z).toReal *
        ∑ y : Z, (P z y).toReal * f y =
      ∑ z : Z, ∑ y : Z,
        ((stationary z).toReal * (P z y).toReal) * f y := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          ring
    _ = ∑ y : Z, ∑ z : Z,
        ((stationary z).toReal * (P z y).toReal) * f y := by
          rw [Finset.sum_comm]
    _ = ∑ y : Z, (stationary y).toReal * f y := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [← Finset.sum_mul, hpoint]

/-- Transition row risk centered at its stationary average. -/
def centeredMarkovRowRisk (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (z : Z) : ℝ :=
  markovRowRisk P score z - stationaryMarkovRisk P stationary score

/-- The `t`-fold iterate `T^t f` of the Markov expectation operator. -/
def iteratedMarkovPotentialMean (P : Z → PMF Z) (t : ℕ) (f : Z → ℝ) : Z → ℝ :=
  (markovPotentialMean P)^[t] f

/-- Truncated Neumann-series potential `h_m = ∑_{t<m} T^t (g-R)`. -/
def finiteDepthPoissonPotential (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ) (z : Z) : ℝ :=
  ∑ t ∈ Finset.range m,
    iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) z

omit [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
lemma finiteDepthPoissonPotential_zero (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) :
    finiteDepthPoissonPotential P stationary score 0 = fun _ ↦ 0 := by
  funext z
  simp [finiteDepthPoissonPotential]

omit [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
lemma finiteDepthPoissonPotential_succ (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ) :
    finiteDepthPoissonPotential P stationary score (m + 1) =
      fun z ↦ finiteDepthPoissonPotential P stationary score m z +
        iteratedMarkovPotentialMean P m (centeredMarkovRowRisk P stationary score) z := by
  funext z
  simp [finiteDepthPoissonPotential, Finset.sum_range_succ]

omit [Fintype Z] [Nonempty Z] [MeasurableSingletonClass Z] in
lemma iteratedMarkovPotentialMean_succ (P : Z → PMF Z) (t : ℕ) (f : Z → ℝ) :
    iteratedMarkovPotentialMean P (t + 1) f = markovPotentialMean P (iteratedMarkovPotentialMean P t f) := by
  simp [iteratedMarkovPotentialMean, Function.iterate_succ_apply']

omit [Nonempty Z] in
lemma finiteDepthPoisson_residual_identity_aux (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ) :
    (fun z ↦ centeredMarkovRowRisk P stationary score z +
        markovPotentialMean P (finiteDepthPoissonPotential P stationary score m) z -
          finiteDepthPoissonPotential P stationary score m z) =
      iteratedMarkovPotentialMean P m (centeredMarkovRowRisk P stationary score) := by
  induction m with
  | zero =>
      funext z
      simp [finiteDepthPoissonPotential, iteratedMarkovPotentialMean, markovPotentialMean]
  | succ m ih =>
      rw [finiteDepthPoissonPotential_succ]
      rw [markovPotentialMean_add]
      rw [iteratedMarkovPotentialMean_succ]
      funext z
      have hz := congrFun ih z
      dsimp only at hz ⊢
      linarith

omit [Nonempty Z] in
/-- The truncated potential has exact Poisson residual `T^m (g-R)`. -/
lemma finiteDepthPoisson_residual_identity (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ) (z : Z) :
    approximatePoissonResidual P stationary score
        (finiteDepthPoissonPotential P stationary score m) z =
      iteratedMarkovPotentialMean P m (centeredMarkovRowRisk P stationary score) z := by
  have h := congrFun (finiteDepthPoisson_residual_identity_aux P stationary score m) z
  unfold approximatePoissonResidual centeredMarkovRowRisk at h ⊢
  linarith

/-- The Markov expectation operator contracts finite oscillation by `alpha`. -/
def IsOscillationContraction (P : Z → PMF Z) (alpha : ℝ) : Prop :=
  ∀ f : Z → ℝ,
    finiteOscillation (markovPotentialMean P f) ≤ alpha * finiteOscillation f

omit [MeasurableSingletonClass Z] in
/-- Oscillation contraction iterates geometrically. -/
lemma iteratedMarkovPotentialMean_oscillation_le
    (P : Z → PMF Z) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : IsOscillationContraction P alpha) (f : Z → ℝ) (t : ℕ) :
    finiteOscillation (iteratedMarkovPotentialMean P t f) ≤ alpha ^ t * finiteOscillation f := by
  induction t with
  | zero => simp [iteratedMarkovPotentialMean]
  | succ t ih =>
      rw [iteratedMarkovPotentialMean_succ]
      calc
        finiteOscillation (markovPotentialMean P (iteratedMarkovPotentialMean P t f)) ≤
            alpha * finiteOscillation (iteratedMarkovPotentialMean P t f) := hcontract _
        _ ≤ alpha * (alpha ^ t * finiteOscillation f) :=
          mul_le_mul_of_nonneg_left ih halpha
        _ = alpha ^ (t + 1) * finiteOscillation f := by ring

omit [MeasurableSingletonClass Z] in
/-- The truncated potential span is bounded by the finite geometric sum. -/
lemma finiteDepthPoissonPotential_span
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) (m : ℕ)
    {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : IsOscillationContraction P alpha)
    (hD : finiteOscillation (centeredMarkovRowRisk P stationary score) ≤ D)
    (x y : Z) :
    |finiteDepthPoissonPotential P stationary score m y -
        finiteDepthPoissonPotential P stationary score m x| ≤
      (∑ t ∈ Finset.range m, alpha ^ t) * D := by
  rw [finiteDepthPoissonPotential, finiteDepthPoissonPotential, ← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ Finset.range m,
        (iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) y -
          iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) x)| ≤
      ∑ t ∈ Finset.range m,
        |iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) y -
          iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range m, alpha ^ t * D := by
      apply Finset.sum_le_sum
      intro t _ht
      calc
        |iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) y -
            iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) x| ≤
          finiteOscillation
            (iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score)) :=
              abs_sub_le_finiteOscillation _ _ _
        _ ≤ alpha ^ t *
            finiteOscillation (centeredMarkovRowRisk P stationary score) :=
              iteratedMarkovPotentialMean_oscillation_le P halpha hcontract _ t
        _ ≤ alpha ^ t * D :=
              mul_le_mul_of_nonneg_left hD (pow_nonneg halpha t)
    _ = (∑ t ∈ Finset.range m, alpha ^ t) * D := by
      rw [Finset.sum_mul]

lemma geometricSum_closed {alpha : ℝ} (halpha : alpha < 1) (m : ℕ) :
    (∑ t ∈ Finset.range m, alpha ^ t) =
      (1 - alpha ^ m) / (1 - alpha) := by
  have hne : (1 - alpha) ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  apply (eq_div_iff hne).2
  exact geom_sum_mul_neg alpha m

omit [Nonempty Z] in
/-- The stationary mean of centered row risk is zero. -/
lemma centeredMarkovRowRisk_stationary_mean_zero
    (P : Z → PMF Z) (stationary : PMF Z)
    (score : MarkovTransitionScore Z) :
    ∫ z, centeredMarkovRowRisk P stationary score z ∂stationary.toMeasure = 0 := by
  have hmass : ∑ z : Z, (stationary z).toReal = 1 := by
    have hone := PMF.integral_eq_sum stationary (fun _ : Z ↦ (1 : ℝ))
    simpa [smul_eq_mul] using hone.symm
  unfold centeredMarkovRowRisk stationaryMarkovRisk
  simp only [PMF.integral_eq_sum, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  ring

omit [Nonempty Z] in
lemma iteratedMarkovPotentialMean_stationary_mean_zero
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    (score : MarkovTransitionScore Z) (t : ℕ) :
    ∫ z, iteratedMarkovPotentialMean P t (centeredMarkovRowRisk P stationary score) z
        ∂stationary.toMeasure = 0 := by
  induction t with
  | zero => simpa [iteratedMarkovPotentialMean] using centeredMarkovRowRisk_stationary_mean_zero P stationary score
  | succ t ih =>
      rw [iteratedMarkovPotentialMean_succ]
      rw [markovPotentialMean_invariant P stationary hstationary]
      exact ih

lemma abs_le_finiteOscillation_of_stationary_mean_zero
    (stationary : PMF Z) (f : Z → ℝ)
    (hmean : ∫ z, f z ∂stationary.toMeasure = 0) (z : Z) :
    |f z| ≤ finiteOscillation f := by
  have hmass : ∑ y : Z, (stationary y).toReal = 1 := by
    have hone := PMF.integral_eq_sum stationary (fun _ : Z ↦ (1 : ℝ))
    simpa [smul_eq_mul] using hone.symm
  have hmeanSum : ∑ y : Z, (stationary y).toReal * f y = 0 := by
    simpa [PMF.integral_eq_sum, smul_eq_mul] using hmean
  have hrepr : f z =
      ∑ y : Z, (stationary y).toReal * (f z - f y) := by
    symm
    calc
      ∑ y : Z, (stationary y).toReal * (f z - f y) =
          (∑ y : Z, (stationary y).toReal * f z) -
            ∑ y : Z, (stationary y).toReal * f y := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
      _ = f z := by
        rw [← Finset.sum_mul, hmass, hmeanSum]
        ring
  rw [hrepr]
  calc
    |∑ y : Z, (stationary y).toReal * (f z - f y)| ≤
        ∑ y : Z, |(stationary y).toReal * (f z - f y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y : Z, (stationary y).toReal * |f z - f y| := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg)]
    _ ≤ ∑ y : Z, (stationary y).toReal * finiteOscillation f := by
      apply Finset.sum_le_sum
      intro y _hy
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa [abs_sub_comm] using abs_sub_le_finiteOscillation f z y
    _ = finiteOscillation f := by
      rw [← Finset.sum_mul, hmass, one_mul]

/-- Under invariance and oscillation contraction, the constructed potential's
pointwise residual is at most `alpha^m * D`. -/
lemma finiteDepthPoissonResidual_le
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary)
    (score : MarkovTransitionScore Z) (m : ℕ)
    {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : IsOscillationContraction P alpha)
    (hD : finiteOscillation (centeredMarkovRowRisk P stationary score) ≤ D)
    (z : Z) :
    |approximatePoissonResidual P stationary score
        (finiteDepthPoissonPotential P stationary score m) z| ≤ alpha ^ m * D := by
  rw [finiteDepthPoisson_residual_identity]
  calc
    |iteratedMarkovPotentialMean P m (centeredMarkovRowRisk P stationary score) z| ≤
        finiteOscillation
          (iteratedMarkovPotentialMean P m (centeredMarkovRowRisk P stationary score)) :=
      abs_le_finiteOscillation_of_stationary_mean_zero stationary _
        (iteratedMarkovPotentialMean_stationary_mean_zero P stationary hstationary score m) z
    _ ≤ alpha ^ m *
        finiteOscillation (centeredMarkovRowRisk P stationary score) :=
      iteratedMarkovPotentialMean_oscillation_le P halpha hcontract _ m
    _ ≤ alpha ^ m * D :=
      mul_le_mul_of_nonneg_left hD (pow_nonneg halpha m)

omit [Nonempty Z] in
/-- A row average of a `[0,1]` transition score remains in `[0,1]`. -/
lemma markovRowRisk_mem_Icc
    (P : Z → PMF Z) {score : MarkovTransitionScore Z}
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1) (z : Z) :
    markovRowRisk P score z ∈ Set.Icc (0 : ℝ) 1 := by
  have hrow : Integrable (score z) (P z).toMeasure := Integrable.of_finite
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y ↦ (hscore z y).1)
  · have hle := integral_mono_ae hrow (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun y ↦ (hscore z y).2)
    simpa [markovRowRisk] using hle

/-- Unit-range scores have centered row-risk oscillation at most one. -/
lemma centeredMarkovRowRisk_finiteOscillation_le_one
    (P : Z → PMF Z) (stationary : PMF Z)
    {score : MarkovTransitionScore Z}
    (hscore : ∀ x y, score x y ∈ Set.Icc (0 : ℝ) 1) :
    finiteOscillation (centeredMarkovRowRisk P stationary score) ≤ 1 := by
  apply finiteOscillation_le
  intro x y
  have hx := markovRowRisk_mem_Icc P hscore x
  have hy := markovRowRisk_mem_Icc P hscore y
  unfold centeredMarkovRowRisk
  rw [show
      markovRowRisk P score y - stationaryMarkovRisk P stationary score -
          (markovRowRisk P score x - stationaryMarkovRisk P stationary score) =
        markovRowRisk P score y - markovRowRisk P score x by ring]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Geometric-sum potential span `B_m`. -/
def finiteDepthPoissonSpanBound (alpha D : ℝ) (m : ℕ) : ℝ :=
  (∑ t ∈ Finset.range m, alpha ^ t) * D

/-- Geometric residual envelope `alpha^m D`. -/
def finiteDepthPoissonResidualBound (alpha D : ℝ) (m : ℕ) : ℝ := alpha ^ m * D

/-- Closed-form potential-span bound, valid when `alpha < 1`. -/
def finiteDepthPoissonClosedSpanBound (alpha D : ℝ) (m : ℕ) : ℝ :=
  (1 - alpha ^ m) / (1 - alpha) * D

/-- Affine scale `C_m = 1 + 2 B_m` for the geometric-sum span bound. -/
def finiteDepthPoissonScaleBound (alpha D : ℝ) (m : ℕ) : ℝ :=
  1 + 2 * finiteDepthPoissonSpanBound alpha D m

/-- Closed-form affine scale `C_m = 1 + 2 B_m` when `alpha < 1`. -/
def finiteDepthPoissonClosedScaleBound (alpha D : ℝ) (m : ℕ) : ℝ :=
  1 + 2 * finiteDepthPoissonClosedSpanBound alpha D m

lemma finiteDepthPoissonSpanBound_nonneg {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hD : 0 ≤ D) (m : ℕ) : 0 ≤ finiteDepthPoissonSpanBound alpha D m := by
  exact mul_nonneg (Finset.sum_nonneg fun t _ht ↦ pow_nonneg halpha t) hD

lemma finiteDepthPoissonResidualBound_nonneg {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hD : 0 ≤ D) (m : ℕ) : 0 ≤ finiteDepthPoissonResidualBound alpha D m := by
  exact mul_nonneg (pow_nonneg halpha m) hD

lemma finiteDepthPoissonSpanBound_closed {alpha D : ℝ} (halpha : alpha < 1) (m : ℕ) :
    finiteDepthPoissonSpanBound alpha D m =
      finiteDepthPoissonClosedSpanBound alpha D m := by
  unfold finiteDepthPoissonClosedSpanBound
  rw [finiteDepthPoissonSpanBound, geometricSum_closed halpha]

lemma finiteDepthPoissonScaleBound_closed {alpha D : ℝ}
    (halpha : alpha < 1) (m : ℕ) :
    finiteDepthPoissonScaleBound alpha D m =
      finiteDepthPoissonClosedScaleBound alpha D m := by
  unfold finiteDepthPoissonScaleBound finiteDepthPoissonClosedScaleBound
  rw [finiteDepthPoissonSpanBound_closed halpha]

variable {I T : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype T] [DecidableEq T]

theorem exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha)
    (hDnonneg : 0 ≤ D) (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i, finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    (m : ℕ)
    {prior : I → ℝ} (hprior : FormalSLT.PACBayesKL.IsFullSupportPMF prior)
    {weight : T → ℝ} (hweight : FormalSLT.PACBayesKL.IsFullSupportPMF weight)
    {lam : T → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : T,
          ∀ posterior : I → ℝ, FormalSLT.PACBayesKL.IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * finiteDepthPoissonSpanBound alpha D m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonSpanBound alpha D m) (score i)
                          (finiteDepthPoissonPotential P stationary (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonSpanBound alpha D m / (n : ℝ) +
                    finiteDepthPoissonResidualBound alpha D m := by
  have hB := finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hspan : ∀ i x y,
      |finiteDepthPoissonPotential P stationary (score i) m y -
        finiteDepthPoissonPotential P stationary (score i) m x| ≤
          finiteDepthPoissonSpanBound alpha D m := by
    intro i x y
    exact finiteDepthPoissonPotential_span P stationary (score i) m halpha hcontract
      (hD i) x y
  have henv : ∀ _i : I, 0 ≤ finiteDepthPoissonResidualBound alpha D m :=
    fun _ ↦ finiteDepthPoissonResidualBound_nonneg halpha hDnonneg m
  have hres : ∀ i z,
      |approximatePoissonResidual P stationary (score i)
        (finiteDepthPoissonPotential P stationary (score i) m) z| ≤
          finiteDepthPoissonResidualBound alpha D m := by
    intro i z
    exact finiteDepthPoissonResidual_le P stationary hstationary (score i) m
      halpha hcontract (hD i) z
  rcases exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
      P stationary hstationary x0 hscore hB hspan henv hres
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hbase := hgood x hx j posterior hposterior n hn
  have hposteriorResidual :
      posteriorAverage posterior (fun _i : I ↦ finiteDepthPoissonResidualBound alpha D m) =
        finiteDepthPoissonResidualBound alpha D m := by
    unfold posteriorAverage
    rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
  rw [hposteriorResidual] at hbase
  exact hbase

/-- Closed-form version of the finite-depth capstone.  The potential span is
`D * (1 - alpha^m) / (1 - alpha)` and the residual price is `alpha^m * D`. -/
theorem exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_closed_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D : ℝ} (halpha : 0 ≤ alpha) (halpha_one : alpha < 1)
    (hDnonneg : 0 ≤ D) (hcontract : IsOscillationContraction P alpha)
    (hD : ∀ i, finiteOscillation (centeredMarkovRowRisk P stationary (score i)) ≤ D)
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
                  (1 + 2 * finiteDepthPoissonClosedSpanBound alpha D m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound alpha D m) (score i)
                          (finiteDepthPoissonPotential P stationary (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonClosedSpanBound alpha D m / (n : ℝ) +
                    finiteDepthPoissonResidualBound alpha D m := by
  simpa only [finiteDepthPoissonSpanBound_closed halpha_one] using
    (exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_event
      P stationary hstationary x0 hscore halpha hDnonneg
      hcontract hD m hprior hweight hdelta hlam hlam_one)

/-- Unit-range convenience specialization.  The initial centered row-risk
oscillation bound `D = 1` is discharged directly from the score range. -/
theorem exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_unit_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halpha_one : alpha < 1)
    (hcontract : IsOscillationContraction P alpha) (m : ℕ)
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
                  (1 + 2 * finiteDepthPoissonClosedSpanBound alpha 1 m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound alpha 1 m) (score i)
                          (finiteDepthPoissonPotential P stationary (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonClosedSpanBound alpha 1 m / (n : ℝ) +
                    finiteDepthPoissonResidualBound alpha 1 m := by
  apply exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_closed_event
    P stationary hstationary x0 hscore halpha halpha_one (by norm_num)
    hcontract
  · intro i
    exact centeredMarkovRowRisk_finiteOscillation_le_one P stationary (hscore i)
  · exact hprior
  · exact hweight
  · exact hdelta
  · exact hlam
  · exact hlam_one

end

end FormalSLT.StochasticDynamics
