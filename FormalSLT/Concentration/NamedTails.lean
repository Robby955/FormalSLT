/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Probability.Concentration
import FormalSLT.Probability.BernsteinMGF
import Mathlib.Probability.Moments.SubGaussian

/-!
# Named two-sided tail-probability corollaries

The concentration engine elsewhere in the library is stated at the
moment-generating-function (MGF) level: `HasSubgaussianMGF`, the finite Bennett
MGF (`FormalSLT.Probability.BernsteinMGF.bennett_mgf`), and the one-sided
Markov/Chernoff step. The textbook statement a reader reaches for is the
*two-sided tail probability* `P(|S - E S| ≥ t) ≤ …`. This file assembles those
named corollaries directly from the existing MGF/Chernoff lemmas. No new
analytic content is introduced; each result is the corresponding one-sided lemma
applied to `X` and to `-X` and combined by a union bound.

## Contents

* `chernoff_tail` — generic one-step corollary: a sub-Gaussian MGF bound yields
  the two-sided tail `P(|X| ≥ t) ≤ 2 exp(-t² / (2c))`.
* `subGaussianMGF_tail_twoSided` — the same statement written for a centered
  variable `X - E X`, the form most often cited.
* `hoeffding_mean_tail_twoSided` — two-sided Hoeffding bound for the sample
  **mean** of bounded independent variables,
  `P(|X̄ - E X̄| ≥ t) ≤ 2 exp(-2 n t² / (b - a)²)`.
* `bernstein_tail` — two-sided Bernstein tail for a bounded-variance finite
  distribution, `P(|X| ≥ ε) ≤ 2 exp(-ε² / (2 (v + b ε / 3)))`.
* `bennett_tail` — two-sided Bennett / sub-Gamma tail in the denominator form
  `P(|X| ≥ ε) ≤ 2 exp(λ² v / (2 (1 - λ b / 3)) - λ ε)` at a chosen `λ`.

These are standard corollaries packaged for usability; they are not new
theorems.
-/

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.NamedTails

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Generic Chernoff two-sided tail.**

If `X` has a sub-Gaussian moment generating function with proxy variance `c`
(`HasSubgaussianMGF X c μ`), then for every threshold `0 ≤ t` the absolute
deviation obeys the textbook two-sided sub-Gaussian tail bound

`P(|X| ≥ t) ≤ 2 · exp(-t² / (2 c))`.

This is the one-step "MGF ⇒ tail" corollary. The right tail uses mathlib's
`HasSubgaussianMGF.measure_ge_le`; the left tail applies the same bound to `-X`
(sub-Gaussian closure under negation); the two are combined by a union bound.
Apply it to a centered variable `X - E X` to recover the centered form. -/
theorem chernoff_tail [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hSubG : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * (c : ℝ))) := by
  classical
  set bound : ℝ := Real.exp (-t ^ 2 / (2 * (c : ℝ))) with hbound
  -- Right tail of `X`.
  have hUpper : μ.real {ω | t ≤ X ω} ≤ bound := hSubG.measure_ge_le ht
  -- Left tail of `X` = right tail of `-X` (sub-Gaussian closure under negation).
  have hNegSubG : HasSubgaussianMGF (-X) c μ := hSubG.neg
  have hNeg : μ.real {ω | t ≤ (-X) ω} ≤ bound := hNegSubG.measure_ge_le ht
  have hLower : μ.real {ω | t ≤ -X ω} ≤ bound := by
    simpa using hNeg
  -- `{t ≤ |X|}` is contained in the union of the two one-sided tails.
  have hsubset : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} :=
        measureReal_union_le _ _
    _ ≤ bound + bound := add_le_add hUpper hLower
    _ = 2 * bound := by ring

/-- **Two-sided sub-Gaussian tail for a centered variable.**

The centered specialization of `chernoff_tail`: if `X - E X` has a sub-Gaussian
MGF with proxy `c`, then `P(|X - E X| ≥ t) ≤ 2 · exp(-t² / (2 c))`. This is the
form most references display. -/
theorem subGaussianMGF_tail_twoSided [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hSubG : HasSubgaussianMGF (fun ω => X ω - μ[X]) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω - μ[X]|} ≤ 2 * Real.exp (-t ^ 2 / (2 * (c : ℝ))) :=
  chernoff_tail hSubG ht

/-- **Two-sided Hoeffding tail for the sample mean.**

For `n` independent random variables, each almost surely supported in `[a, b]`
with `a ≤ b`, the empirical mean `X̄ = (1/n) ∑ X i` satisfies the textbook
two-sided Hoeffding bound

`P(|X̄ - E X̄| ≥ t) ≤ 2 · exp(-2 n t² / (b - a)²)`,

for every `0 < n` and `0 ≤ t`. This is the single inequality most often cited in
applied work. It is assembled from Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc`, the bounded ⇒ sub-Gaussian step), independent
sub-Gaussian closure (`HasSubgaussianMGF.sum_of_iIndepFun`), and the generic
two-sided `chernoff_tail`; the `1/n` scaling turns the sum proxy into the mean
proxy `(b-a)² / (4 n)`, whose Chernoff exponent is exactly `-2 n t² / (b-a)²`. -/
theorem hoeffding_mean_tail_twoSided
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hIndep : iIndepFun X μ)
    {a b : ℝ} (hab : a < b)
    (hMeas : ∀ i, AEMeasurable (X i) μ)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(fun ω => (∑ i, X i ω) / (n : ℝ)) ω
        - μ[fun ω => (∑ i, X i ω) / (n : ℝ)]|}
      ≤ 2 * Real.exp (-2 * (n : ℝ) * t ^ 2 / (b - a) ^ 2) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  -- Per-coordinate centered sub-Gaussian proxy.
  have hCenteredSubG : ∀ i,
      HasSubgaussianMGF (fun ω => X i ω - μ[X i]) ((‖b - a‖₊ / 2) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc (hMeas i) (hBound i)
  -- Each `1/n`-scaled centered coordinate is sub-Gaussian (proxy from `const_mul`).
  have hScaledSubG : ∀ i,
      HasSubgaussianMGF (fun ω => (1 / n : ℝ) * (X i ω - μ[X i]))
        (⟨(1 / n : ℝ) ^ 2, sq_nonneg _⟩ * (‖b - a‖₊ / 2) ^ 2) μ := fun i =>
    (hCenteredSubG i).const_mul (1 / n : ℝ)
  -- Independence of the scaled centered coordinates.
  have hScaledIndep :
      iIndepFun (fun i ω => (1 / n : ℝ) * (X i ω - μ[X i])) μ := by
    have h := hIndep.comp (fun i x => (1 / n : ℝ) * (x - μ[X i]))
      (fun _ => (measurable_id.sub measurable_const).const_mul _)
    change iIndepFun (fun i => (fun x => (1 / n : ℝ) * (x - μ[X i])) ∘ X i) μ
    exact h
  -- Their sum is sub-Gaussian with the summed proxy.
  have hSumSubG :
      HasSubgaussianMGF
        (fun ω => ∑ i, (1 / n : ℝ) * (X i ω - μ[X i]))
        (∑ _i : Fin n, (⟨(1 / n : ℝ) ^ 2, sq_nonneg _⟩ * (‖b - a‖₊ / 2) ^ 2)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hScaledIndep (fun i _ => hScaledSubG i)
  -- Each `X i` is integrable (bounded under a probability measure).
  have hXint : ∀ i, Integrable (X i) μ := fun i =>
    Integrable.of_mem_Icc a b (hMeas i) (hBound i)
  -- E[mean] = (∑ E[X i]) / n.
  have hintM : μ[fun ω => (∑ i, X i ω) / (n : ℝ)] = (∑ i, μ[X i]) / (n : ℝ) := by
    rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hXint i)]
  -- The sum of the scaled centered coordinates equals `mean - E mean` pointwise.
  have hSumEq : (fun ω => ∑ i, (1 / n : ℝ) * (X i ω - μ[X i]))
      = fun ω => (∑ i, X i ω) / (n : ℝ) - μ[fun ω => (∑ i, X i ω) / (n : ℝ)] := by
    funext ω
    rw [hintM]
    have hL : ∑ i, (1 / n : ℝ) * (X i ω - μ[X i])
        = (1 / n : ℝ) * (∑ i, X i ω) - (1 / n : ℝ) * (∑ i, μ[X i]) := by
      rw [← Finset.mul_sum, ← mul_sub, Finset.sum_sub_distrib]
    rw [hL]
    field_simp
  rw [hSumEq] at hSumSubG
  -- Apply the generic two-sided Chernoff corollary and identify the exponent.
  have hTail := chernoff_tail hSumSubG ht
  refine hTail.trans (le_of_eq ?_)
  congr 2
  have hsum_proxy :
      ((∑ _i : Fin n, (⟨(1 / n : ℝ) ^ 2, sq_nonneg _⟩ * (‖b - a‖₊ / 2) ^ 2) : ℝ≥0) : ℝ)
        = (b - a) ^ 2 / (4 * n) := by
    rw [NNReal.coe_sum]
    have hterm : ∀ _i : Fin n,
        (((⟨(1 / n : ℝ) ^ 2, sq_nonneg _⟩ * (‖b - a‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ)
        = (1 / n : ℝ) ^ 2 * ((b - a) / 2) ^ 2 := by
      intro _
      rw [NNReal.coe_mul]
      congr 1
      rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg hba.le]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnNe]
    ring
  rw [hsum_proxy]
  have hbane : (b - a) ≠ 0 := ne_of_gt hba
  field_simp
  ring

end

end FormalSLT.Concentration.NamedTails

/-! ## Finite-distribution Bernstein / Bennett two-sided tails

These work over a finite type `Z` with a probability mass function `p` and an
observable `X` that is centered (`∑ p z · X z = 0`). The one-sided pieces live in
`FormalSLT.Probability.BernsteinMGF`; here we expose the two-sided tail
probability on the absolute deviation `{z | ε ≤ |X z|}` by applying the one-sided
bounds to `X` and to `-X`.
-/

namespace FormalSLT.Concentration.NamedTails

open FormalSLT.Probability.BernsteinMGF

variable {Z : Type*} [Fintype Z]

/-- The two-sided absolute-deviation mass splits into the two one-sided masses.
A discrete union bound: `{z | ε ≤ |X z|} ⊆ {z | ε ≤ X z} ∪ {z | ε ≤ -X z}`, and
the weight of a union is at most the sum of the weights. -/
private lemma twoSided_mass_le (p X : Z → ℝ) (eps : ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
      ≤ (∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z)
        + ∑ z ∈ Finset.univ.filter (fun z => eps ≤ -X z), p z := by
  classical
  have hsub :
      (Finset.univ.filter (fun z => eps ≤ |X z|))
        ⊆ (Finset.univ.filter (fun z => eps ≤ X z))
          ∪ (Finset.univ.filter (fun z => eps ≤ -X z)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.mp hz.2 with h | h
    · exact Or.inl ⟨hz.1, h⟩
    · exact Or.inr ⟨hz.1, h⟩
  set A := Finset.univ.filter (fun z => eps ≤ X z) with hA
  set B := Finset.univ.filter (fun z => eps ≤ -X z) with hB
  have hunion_le : ∑ z ∈ A ∪ B, p z ≤ (∑ z ∈ A, p z) + ∑ z ∈ B, p z := by
    have hinter : 0 ≤ ∑ z ∈ A ∩ B, p z :=
      Finset.sum_nonneg (fun z _ => hp_nonneg z)
    have heq : (∑ z ∈ A ∪ B, p z) + ∑ z ∈ A ∩ B, p z
        = (∑ z ∈ A, p z) + ∑ z ∈ B, p z := Finset.sum_union_inter
    linarith
  calc
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
        ≤ ∑ z ∈ A ∪ B, p z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hp_nonneg z)
    _ ≤ (∑ z ∈ A, p z) + ∑ z ∈ B, p z := hunion_le

/-- **Two-sided Bernstein tail (finite distribution).**

For a finite probability mass function `p` and a centered observable `X`
(`∑ p z · X z = 0`) that is two-sidedly bounded (`|X z| ≤ b`, `0 < b`) with
variance proxy `∑ p z · X z² ≤ v`, `0 < v`, the two-sided deviation obeys the
standard Bernstein inequality

`P(|X| ≥ ε) ≤ 2 · exp(-ε² / (2 (v + b ε / 3)))`  for `0 ≤ ε`.

The upper and lower tails are each the one-sided
`FormalSLT.Probability.BernsteinMGF.bernstein_tail`; the lower tail is that lemma
applied to `-X`, whose bound `-(X z) ≤ b` and variance `∑ p z · (-X z)² = ∑ p z · X z²`
both follow from the two-sided bound. The factor `2` comes from the union bound.
This is the one-sample tail; the averaged `exp(-n ε² / …)` form is
`FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail`. -/
theorem bernstein_tail (p X : Z → ℝ)
    {b v eps : ℝ} (hb : 0 < b) (hv : 0 < v) (heps : 0 ≤ eps)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0)
    (hbound : ∀ z, |X z| ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
      ≤ 2 * Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) := by
  classical
  have hbound_up : ∀ z, X z ≤ b := fun z => (abs_le.mp (hbound z)).2
  have hbound_lo : ∀ z, -(X z) ≤ b := fun z => by
    have := (abs_le.mp (hbound z)).1; linarith
  -- Upper tail.
  have hUpper :
      ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z
        ≤ Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) :=
    FormalSLT.Probability.BernsteinMGF.bernstein_tail p X hb hv heps
      hp_nonneg hp_sum hcenter hbound_up hvar
  -- Lower tail: apply the one-sided bound to `-X`.
  have hcenterNeg : ∑ z, p z * (-(X z)) = 0 := by
    have : ∑ z, p z * (-(X z)) = -(∑ z, p z * X z) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [this, hcenter, neg_zero]
  have hvarNeg : ∑ z, p z * (-(X z)) ^ 2 ≤ v := by
    have heq : ∑ z, p z * (-(X z)) ^ 2 = ∑ z, p z * X z ^ 2 :=
      Finset.sum_congr rfl (fun z _ => by ring)
    rw [heq]; exact hvar
  have hLower :
      ∑ z ∈ Finset.univ.filter (fun z => eps ≤ -X z), p z
        ≤ Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) :=
    FormalSLT.Probability.BernsteinMGF.bernstein_tail p (fun z => -(X z))
      hb hv heps hp_nonneg hp_sum hcenterNeg hbound_lo hvarNeg
  calc
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
        ≤ (∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z)
          + ∑ z ∈ Finset.univ.filter (fun z => eps ≤ -X z), p z :=
        twoSided_mass_le p X eps hp_nonneg
    _ ≤ Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3)))
          + Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) :=
        add_le_add hUpper hLower
    _ = 2 * Real.exp (-(eps ^ 2) / (2 * (v + b * eps / 3))) := by ring

/-- **Two-sided Bennett / sub-Gamma tail (finite distribution), fixed `λ`.**

For a finite probability mass function `p` and a centered observable `X`
(`∑ p z · X z = 0`) two-sidedly bounded (`|X z| ≤ b`, `0 < b`) with variance
proxy `∑ p z · X z² ≤ v`, and a parameter `0 ≤ λ` with `λ b < 3`, the two-sided
deviation obeys the Bennett sub-Gamma tail

`P(|X| ≥ ε) ≤ 2 · exp(λ² v / (2 (1 - λ b / 3)) - λ ε)`.

This is the variance-aware Bennett analogue of `bernstein_tail`: the exponent
carries the genuine variance `v` and is left at a free `λ`, so a caller can keep
the exact sub-Gamma form or optimize `λ`. Each one-sided tail is
`FormalSLT.Probability.BernsteinMGF.bernstein_tail_mgf`; the lower tail uses the
negated observable, and the factor `2` is the union bound. -/
theorem bennett_tail (p X : Z → ℝ)
    {b v lam eps : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) (hlb : lam * b < 3)
    (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (hcenter : ∑ z, p z * X z = 0)
    (hbound : ∀ z, |X z| ≤ b)
    (hvar : ∑ z, p z * X z ^ 2 ≤ v) :
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
      ≤ 2 * Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) := by
  classical
  have hbound_up : ∀ z, X z ≤ b := fun z => (abs_le.mp (hbound z)).2
  have hbound_lo : ∀ z, -(X z) ≤ b := fun z => by
    have := (abs_le.mp (hbound z)).1; linarith
  have hUpper :
      ∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z
        ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) :=
    FormalSLT.Probability.BernsteinMGF.bernstein_tail_mgf p X hb hlam hlb
      hp_nonneg hp_sum hcenter hbound_up hvar
  have hcenterNeg : ∑ z, p z * (-(X z)) = 0 := by
    have : ∑ z, p z * (-(X z)) = -(∑ z, p z * X z) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [this, hcenter, neg_zero]
  have hvarNeg : ∑ z, p z * (-(X z)) ^ 2 ≤ v := by
    have heq : ∑ z, p z * (-(X z)) ^ 2 = ∑ z, p z * X z ^ 2 :=
      Finset.sum_congr rfl (fun z _ => by ring)
    rw [heq]; exact hvar
  have hLower :
      ∑ z ∈ Finset.univ.filter (fun z => eps ≤ -X z), p z
        ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) :=
    FormalSLT.Probability.BernsteinMGF.bernstein_tail_mgf p (fun z => -(X z))
      hb hlam hlb hp_nonneg hp_sum hcenterNeg hbound_lo hvarNeg
  calc
    ∑ z ∈ Finset.univ.filter (fun z => eps ≤ |X z|), p z
        ≤ (∑ z ∈ Finset.univ.filter (fun z => eps ≤ X z), p z)
          + ∑ z ∈ Finset.univ.filter (fun z => eps ≤ -X z), p z :=
        twoSided_mass_le p X eps hp_nonneg
    _ ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps)
          + Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) :=
        add_le_add hUpper hLower
    _ = 2 * Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3)) - lam * eps) := by ring

end FormalSLT.Concentration.NamedTails
