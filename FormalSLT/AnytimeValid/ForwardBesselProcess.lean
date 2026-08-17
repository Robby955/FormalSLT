/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.EProcess
import FormalSLT.Statistics.ClassicalEstimation

/-!
# Forward Bessel variance bridge

This file records the deterministic algebra needed to turn the standard
predictable plug-in squared-residual penalty into an exact Bessel-variance
penalty.  For a real sequence `x`, let

* `forwardPrefixMean x n` be the mean of `x 0, ..., x (n-1)`;
* `forwardBesselQ x n` be the centered sum of squares of that prefix, hence
  `(n - 1)` times its Bessel sample variance when `n >= 2`;
* `forwardPredictableQuadratic x n` use the seed predictor `1 / 2` for the
  first observation and the preceding prefix mean thereafter.

Welford's identity gives the exact one-step increment of `forwardBesselQ`.
For observations in `[0,1]`, the first two observations cost at most `1 / 2`
and every later predictable squared residual is at most `3 / 2` times the
corresponding Welford increment.  Consequently

`forwardPredictableQuadratic x n <= 1/2 + (3/2) * forwardBesselQ x n`

for every `n >= 2`.  The coefficient `1` is false already on the two-point
Boolean sample `(0,1)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Mean of the first `n` values of a sequence.  As elsewhere in FormalSLT,
division is total; results that use this as a genuine mean state `0 < n`. -/
def forwardPrefixMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i) / (n : ℝ)

/-- The exact centered sum of squares of the first `n` observations. -/
def forwardBesselQ (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (x i - forwardPrefixMean x n) ^ 2

/-- Predict from `1/2` before the first observation and from the empirical
prefix mean thereafter. -/
def forwardPredictor (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (1 : ℝ) / 2 else forwardPrefixMean x k

/-- Sum of squared one-step-ahead prediction residuals through time `n`. -/
def forwardPredictableQuadratic (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (x k - forwardPredictor x k) ^ 2

lemma forwardPrefixMean_eq_sampleMean (x : ℕ → ℝ) (n : ℕ) :
    forwardPrefixMean x n =
      FormalSLT.Statistics.sampleMean (fun i : Fin n ↦ x i) := by
  simp [forwardPrefixMean,
    FormalSLT.Statistics.sampleMean,
    Fin.sum_univ_eq_sum_range]

/-- `Q_n` is exactly `(n-1)` times the Bessel sample variance. -/
theorem forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    forwardBesselQ x n =
      ((n : ℝ) - 1) *
        FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin n ↦ x i) := by
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  unfold forwardBesselQ
  rw [FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel]
  rw [← forwardPrefixMean_eq_sampleMean]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (x i - forwardPrefixMean x n) ^ 2) n]
  field_simp [hden]

/-- The centered sum of squares is nonnegative. -/
lemma forwardBesselQ_nonneg (x : ℕ → ℝ) (n : ℕ) :
    0 ≤ forwardBesselQ x n := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Online mean update. -/
lemma forwardPrefixMean_succ (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardPrefixMean x (n + 1) =
      forwardPrefixMean x n +
        (x n - forwardPrefixMean x n) / ((n : ℝ) + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnp10 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold forwardPrefixMean
  rw [Finset.sum_range_succ]
  push_cast
  field_simp [hn0, hnp10]
  ring

/-- Welford's exact one-step identity for the centered sum of squares. -/
theorem forwardBesselQ_succ (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardBesselQ x (n + 1) =
      forwardBesselQ x n +
        (n : ℝ) / ((n : ℝ) + 1) *
          (x n - forwardPrefixMean x n) ^ 2 := by
  let m : ℝ := forwardPrefixMean x n
  let m' : ℝ := forwardPrefixMean x (n + 1)
  have hdecomp :
      ∑ i ∈ Finset.range n, (x i - m') ^ 2 =
        forwardBesselQ x n + (n : ℝ) * (m - m') ^ 2 := by
    have h :=
      FormalSLT.Statistics.ClassicalEstimation.sum_sq_sub_eq_sum_sq_sub_mean_add_card
        hn (fun i : Fin n ↦ x i) m'
    have hsum (a : ℝ) :
        (∑ i : Fin n, (x i - a) ^ 2) =
          ∑ i ∈ Finset.range n, (x i - a) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun i ↦ (x i - a) ^ 2) n
    have hprefix :
        FormalSLT.Statistics.sampleMean (fun i : Fin n ↦ x i) = m := by
      simpa [m] using (forwardPrefixMean_eq_sampleMean x n).symm
    rw [hsum m', hsum, hprefix] at h
    simpa [forwardBesselQ] using h
  have hmean : m' = m + (x n - m) / ((n : ℝ) + 1) := by
    simpa [m, m'] using forwardPrefixMean_succ x hn
  have hnp10 : (n : ℝ) + 1 ≠ 0 := by positivity
  change (∑ i ∈ Finset.range (n + 1),
      (x i - forwardPrefixMean x (n + 1)) ^ 2) = _
  rw [Finset.sum_range_succ]
  change (∑ i ∈ Finset.range n, (x i - m') ^ 2) + (x n - m') ^ 2 = _
  rw [hdecomp, hmean]
  field_simp [hnp10]
  ring

lemma forwardPredictableQuadratic_succ (x : ℕ → ℝ) (n : ℕ) :
    forwardPredictableQuadratic x (n + 1) =
      forwardPredictableQuadratic x n + (x n - forwardPredictor x n) ^ 2 := by
  simp [forwardPredictableQuadratic, Finset.sum_range_succ]

lemma forwardPredictor_eq_prefixMean (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardPredictor x n = forwardPrefixMean x n := by
  simp [forwardPredictor, hn.ne']

lemma forwardPredictableQuadratic_two (x : ℕ → ℝ) :
    forwardPredictableQuadratic x 2 =
      (x 0 - (1 : ℝ) / 2) ^ 2 + (x 1 - x 0) ^ 2 := by
  norm_num [forwardPredictableQuadratic, forwardPredictor, forwardPrefixMean,
    Finset.sum_range_succ]

lemma forwardBesselQ_two (x : ℕ → ℝ) :
    forwardBesselQ x 2 = (x 0 - x 1) ^ 2 / 2 := by
  norm_num [forwardBesselQ, forwardPrefixMean, Finset.sum_range_succ]
  ring

/-- The two-observation seed costs at most `1/2` beyond the `3/2 Q_2`
term for `[0,1]` observations. -/
lemma forwardPredictableQuadratic_two_le
    (x : ℕ → ℝ)
    (hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1) (hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1) :
    forwardPredictableQuadratic x 2 ≤
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x 2 := by
  rw [forwardPredictableQuadratic_two, forwardBesselQ_two]
  have hseed : (x 0 - (1 : ℝ) / 2) ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg hx0.1 (sub_nonneg.mpr hx0.2)]
  have hdiff : (x 0 - x 1) ^ 2 ≤ (1 : ℝ) := by
    have hlo : -(1 : ℝ) ≤ x 0 - x 1 := by linarith
    have hhi : x 0 - x 1 ≤ (1 : ℝ) := by linarith
    nlinarith
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- Exact-Bessel domination of the predictable plug-in quadratic penalty.

The coefficient `3/2` is forced by the first nontrivial Welford update.  From
time two onward it is preserved inductively because
`1 <= (3/2) * n/(n+1)` for every `n >= 2`. -/
theorem forwardPredictableQuadratic_le_half_add_three_halves_besselQ
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hx : ∀ i < n, 0 ≤ x i ∧ x i ≤ 1) :
    forwardPredictableQuadratic x n ≤
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x n := by
  induction n, hn using Nat.le_induction with
  | base =>
      exact forwardPredictableQuadratic_two_le x (hx 0 (by omega)) (hx 1 (by omega))
  | succ n hn ih =>
      have hnpos : 0 < n := by omega
      have ih' := ih (fun i hi ↦ hx i (by omega))
      rw [forwardPredictableQuadratic_succ, forwardBesselQ_succ x hnpos,
        forwardPredictor_eq_prefixMean x hnpos]
      have hsq : 0 ≤ (x n - forwardPrefixMean x n) ^ 2 := sq_nonneg _
      have hden : 0 < (n : ℝ) + 1 := by positivity
      have hcoef :
          (1 : ℝ) ≤ (3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1)) := by
        rw [show (3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1)) =
          (((3 : ℝ) / 2) * (n : ℝ)) / ((n : ℝ) + 1) by ring]
        rw [le_div_iff₀ hden]
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have hstep :
          (x n - forwardPrefixMean x n) ^ 2 ≤
            ((3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1))) *
              (x n - forwardPrefixMean x n) ^ 2 :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hsq
      nlinarith

/-- Pointwise obstruction to replacing `3/2` by `1`: the Boolean sample
`(false,true)`, encoded as `(0,1)`, violates the proposed bound at `n = 2`. -/
theorem forwardBessel_coefficient_one_bool_obstruction :
    let x : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 1
    (1 : ℝ) / 2 + forwardBesselQ x 2 < forwardPredictableQuadratic x 2 := by
  dsimp
  norm_num [forwardPredictableQuadratic_two, forwardBesselQ_two]

/-! ### Honest stochastic interface

The deterministic Bessel envelope below does not by itself preserve the
supermartingale property.  The stochastic object is the standard exponential
process with the realized predictable-residual penalty.  Once its exact
one-step conditional-expectation inequality is supplied, it is an `EProcess`;
the Bessel expression is then a pointwise lower envelope of that e-process.
This separation prevents a deterministic domination argument from being
mistaken for a supermartingale closure theorem.
-/

/-- Predictable-residual exponential process for observations `X` and candidate
mean `mean`.  The scalar `psi` is the one-step cumulant multiplier. -/
def forwardPlugInExponentialProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam psi : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k ω - mean)) -
      psi * forwardPredictableQuadratic (fun k ↦ X k ω) n)

/-- Exact-Bessel lower envelope of `forwardPlugInExponentialProcess`. -/
def forwardBesselExponentialEnvelope {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam psi : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k ω - mean)) -
      psi * ((1 : ℝ) / 2 + (3 : ℝ) / 2 *
        forwardBesselQ (fun k ↦ X k ω) n))

/-- Under `[0,1]` observations and a nonnegative cumulant multiplier, the
exact-Bessel expression is a pointwise lower envelope of the predictable
plug-in process. -/
theorem forwardBesselExponentialEnvelope_le_forwardPlugIn
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mean lam psi : ℝ)
    {n : ℕ} (hn : 2 ≤ n) (hpsi : 0 ≤ psi) (ω : Ω)
    (hX : ∀ i < n, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    forwardBesselExponentialEnvelope X mean lam psi n ω ≤
      forwardPlugInExponentialProcess X mean lam psi n ω := by
  apply Real.exp_le_exp.mpr
  have hq :=
    forwardPredictableQuadratic_le_half_add_three_halves_besselQ
      (fun k ↦ X k ω) hn hX
  have hpen := mul_le_mul_of_nonneg_left hq hpsi
  linarith

/-- The predictable-residual exponential is an e-process once its exact
conditional one-step inequality, adaptedness, and integrability obligations
have been discharged.  This is the reusable handoff point for any particular
plug-in empirical-Bernstein one-step lemma. -/
theorem forwardPlugIn_eProcess_of_condExp_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam psi : ℝ}
    (hadapted : MeasureTheory.StronglyAdapted ℱ
      (forwardPlugInExponentialProcess X mean lam psi))
    (hintegrable : ∀ n,
      MeasureTheory.Integrable (forwardPlugInExponentialProcess X mean lam psi n) μ)
    (hstep : ∀ n,
      μ[forwardPlugInExponentialProcess X mean lam psi (n + 1) | ℱ n]
        ≤ᵐ[μ] forwardPlugInExponentialProcess X mean lam psi n) :
    EProcess μ ℱ (forwardPlugInExponentialProcess X mean lam psi) where
  nonneg := fun _ _ ↦ (Real.exp_pos _).le
  start_one := fun ω ↦ by
    simp [forwardPlugInExponentialProcess, forwardPredictableQuadratic]
  supermartingale := MeasureTheory.supermartingale_nat hadapted hintegrable hstep

/-- A single checked certificate packages both the stochastic e-process and
its exact-Bessel lower envelope.  Notice that the conclusion intentionally
does not assert that the lower envelope itself is a supermartingale. -/
theorem forwardBesselEnvelope_certified_by_eProcess
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam psi : ℝ}
    (hpsi : 0 ≤ psi)
    (hadapted : MeasureTheory.StronglyAdapted ℱ
      (forwardPlugInExponentialProcess X mean lam psi))
    (hintegrable : ∀ n,
      MeasureTheory.Integrable (forwardPlugInExponentialProcess X mean lam psi n) μ)
    (hstep : ∀ n,
      μ[forwardPlugInExponentialProcess X mean lam psi (n + 1) | ℱ n]
        ≤ᵐ[μ] forwardPlugInExponentialProcess X mean lam psi n)
    (hX : ∀ n ≥ 2, ∀ ω, ∀ i < n, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    EProcess μ ℱ (forwardPlugInExponentialProcess X mean lam psi) ∧
      ∀ n ≥ 2, ∀ ω,
        forwardBesselExponentialEnvelope X mean lam psi n ω ≤
          forwardPlugInExponentialProcess X mean lam psi n ω := by
  refine ⟨forwardPlugIn_eProcess_of_condExp_step hadapted hintegrable hstep, ?_⟩
  intro n hn ω
  exact forwardBesselExponentialEnvelope_le_forwardPlugIn
    X mean lam psi hn hpsi ω (hX n hn ω)

end

end FormalSLT.AnytimeValid
