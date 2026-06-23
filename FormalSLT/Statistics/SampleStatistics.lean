/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Concentration.NamedTails

/-!
# Sample statistics: named sample mean and sample variance

The "statistics" half of "prob + stats" was previously implicit: the sample mean
appears inside `empiricalRisk` and `iidEmpiricalAverage`, but there is no named
`sampleMean` / `sampleVariance` a user can reach for, and no sample-mean tail
exposed as a corollary keyed to the sample mean. This file supplies those.

* `sampleMean x` — the average `(1/n) ∑ x i` of a finite sample `x : Fin n → ℝ`.
* `sampleVariance x` — the (population-form, divide-by-`n`) empirical variance
  `(1/n) ∑ (x i - x̄)²`.
* `sampleVariance_nonneg`, `sampleVariance_eq_secondMoment_sub_meanSq` — the
  basic identities (`Var ≥ 0`, `Var = E[X²] − X̄²`).
* `sampleMean_hoeffding_tail` — the two-sided Hoeffding tail for the random
  sample mean of `n` independent `[a, b]`-valued draws, restated with the named
  `sampleMean` in place of the inline `(∑ X i) / n`. It is exactly
  `FormalSLT.Concentration.NamedTails.hoeffding_mean_tail_twoSided` rephrased
  through `sampleMean`.

No new analytic content: the deterministic identities are algebra, and the tail
is the named Hoeffding corollary read through the `sampleMean` definition.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open FormalSLT.Concentration.NamedTails

namespace FormalSLT.Statistics

noncomputable section

/-- **Sample mean** of a finite sample `x : Fin n → ℝ`: `x̄ = (1/n) ∑ x i`.
Lean's total real division gives `0` at `n = 0`. -/
def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / (n : ℝ)

/-- **Sample variance** (population / divide-by-`n` form) of `x : Fin n → ℝ`:
`(1/n) ∑ (x i - x̄)²`. -/
def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / (n : ℝ)

/-! ### Deterministic identities -/

/-- The sample variance is nonnegative. -/
theorem sampleVariance_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sampleVariance x := by
  unfold sampleVariance
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact Nat.cast_nonneg n

/-- The sum form of the sample mean: `n · x̄ = ∑ x i` when `0 < n`. -/
theorem sampleMean_mul_card {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (n : ℝ) * sampleMean x = ∑ i, x i := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sampleMean; field_simp

/-- **Variance decomposition.** `Var = E[X²] − x̄²` for the population-form sample
variance: `(1/n) ∑ (x i)² − x̄² = sampleVariance x` when `0 < n`. -/
theorem sampleVariance_eq_secondMoment_sub_meanSq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    sampleVariance x = (∑ i, (x i) ^ 2) / (n : ℝ) - (sampleMean x) ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sampleVariance sampleMean
  have hexpand : ∀ i, (x i - (∑ j, x j) / (n : ℝ)) ^ 2
      = (x i) ^ 2 - 2 * ((∑ j, x j) / (n : ℝ)) * x i + ((∑ j, x j) / (n : ℝ)) ^ 2 := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => hexpand i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-! ### The named sample-mean tail -/

/-- **Two-sided Hoeffding tail for the sample mean.**

For `n` independent draws `X i`, each almost surely in `[a, b]` with `a < b`, the
random sample mean `sampleMean (X · ω)` satisfies

`P(|x̄ - E x̄| ≥ t) ≤ 2 · exp(-2 n t² / (b - a)²)`,

stated through the named `sampleMean`. This is
`FormalSLT.Concentration.NamedTails.hoeffding_mean_tail_twoSided` read through the
`sampleMean` definition — the inequality applied work most often reaches for,
now keyed to the named estimator. -/
theorem sampleMean_hoeffding_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} (hIndep : iIndepFun X μ)
    {a b : ℝ} (hab : a < b)
    (hMeas : ∀ i, AEMeasurable (X i) μ)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |sampleMean (fun i => X i ω)
        - μ[fun ω => sampleMean (fun i => X i ω)]|}
      ≤ 2 * Real.exp (-2 * (n : ℝ) * t ^ 2 / (b - a) ^ 2) := by
  have hrw : (fun ω => sampleMean (fun i => X i ω))
      = (fun ω => (∑ i, X i ω) / (n : ℝ)) := by
    funext ω; rfl
  rw [hrw]
  exact hoeffding_mean_tail_twoSided hn hIndep hab hMeas hBound ht

end

end FormalSLT.Statistics
