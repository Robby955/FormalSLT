import FormalSLT.Rademacher.FiniteSample
import FormalSLT.Azuma.BoundedDifferences
import FormalSLT.Azuma.HasBoundedDifferences
import FormalSLT.Rademacher.Decoupling
import FormalSLT.Azuma.GenGapTail

/-!
# Bounded differences for empirical Rademacher complexity

The data-dependent generalization analysis needs the empirical Rademacher
complexity `R̂` to concentrate around its mean, so the *population* threshold
`2·E[Rad]` in the existing global high-probability bound can be replaced by the
*data-dependent, observable* threshold `2·R̂(S)`.

This module supplies the missing ingredient: `R̂` satisfies the abstract
`HasBoundedDifferences` predicate with the same per-coordinate constant `2B/n`
as the generalization gap. Composed with the generic
`hasBoundedDifferences_tail_azuma`, this gives a two-sided McDiarmid
concentration of `R̂` (developed in a later step).
-/

open scoped BigOperators NNReal
open MeasureTheory
open FormalSLT.Rademacher.FiniteSample
open FormalSLT.Azuma.BoundedDifferences
open FormalSLT.Azuma.ExposureMartingale

namespace FormalSLT.Rademacher

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]

/-- **Single-coordinate update bound for empirical Rademacher complexity.**
Replacing one sample point shifts `R̂` by at most `2B/n`, for a uniformly
`B`-bounded loss class. The signed average shifts by ≤ `2B/n` per hypothesis,
the `sup'` over the class is 1-Lipschitz, and the discrete `σ`-average is
1-Lipschitz. -/
lemma abs_empiricalRademacher_update_le_of_bdd
    (ℓ : ι → Z → ℝ) {B : ℝ} (hℓ : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) (k : Fin n) (z' : Z) :
    |empiricalRademacherComplexity ℓ S
        - empiricalRademacherComplexity ℓ (Function.update S k z')| ≤ 2 * B / n := by
  classical
  have hn_pos : (0:ℝ) < n := by exact_mod_cast hn
  have hninv : (0:ℝ) < (n:ℝ)⁻¹ := inv_pos.mpr hn_pos
  set a : (Fin n → Z) → (Fin n → Bool) → ι → ℝ :=
    fun T σ i => (n : ℝ)⁻¹ * ∑ j : Fin n, signOfBool (σ j) * ℓ i (T j) with ha
  have hai : ∀ σ : Fin n → Bool, ∀ i : ι,
      |a S σ i - a (Function.update S k z') σ i| ≤ 2 * B / n := by
    intro σ i
    have hcollapse :
        (∑ j : Fin n, signOfBool (σ j) * ℓ i (S j))
          - (∑ j : Fin n, signOfBool (σ j) * ℓ i (Function.update S k z' j))
          = signOfBool (σ k) * (ℓ i (S k) - ℓ i z') := by
      rw [← Finset.sum_sub_distrib,
        Finset.sum_eq_single k
          (fun j _ hjk => by rw [Function.update_of_ne hjk]; ring)
          (fun h => absurd (Finset.mem_univ k) h)]
      rw [Function.update_self]; ring
    have hval : a S σ i - a (Function.update S k z') σ i
        = (n : ℝ)⁻¹ * (signOfBool (σ k) * (ℓ i (S k) - ℓ i z')) := by
      simp only [ha]; rw [← mul_sub, hcollapse]
    have hdiff : |ℓ i (S k) - ℓ i z'| ≤ 2 * B := by
      have h1 := abs_le.mp (hℓ i (S k))
      have h2 := abs_le.mp (hℓ i z')
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [hval, abs_mul, abs_mul, abs_signOfBool, abs_of_pos hninv, one_mul]
    calc (n : ℝ)⁻¹ * |ℓ i (S k) - ℓ i z'|
        ≤ (n : ℝ)⁻¹ * (2 * B) := mul_le_mul_of_nonneg_left hdiff (le_of_lt hninv)
      _ = 2 * B / n := by ring
  have hsupσ : ∀ σ : Fin n → Bool,
      |(Finset.univ : Finset ι).sup' Finset.univ_nonempty (a S σ)
        - (Finset.univ : Finset ι).sup' Finset.univ_nonempty (a (Function.update S k z') σ)|
        ≤ 2 * B / n := by
    intro σ
    refine (abs_sup'_sub_sup'_le_sup'_abs_sub Finset.univ Finset.univ_nonempty
      (a S σ) (a (Function.update S k z') σ)).trans ?_
    exact Finset.sup'_le _ _ (fun i _ => hai σ i)
  unfold empiricalRademacherComplexity
  rw [← mul_sub, abs_mul, abs_of_pos two_pow_inv_pos, ← Finset.sum_sub_distrib]
  calc ((2:ℝ) ^ n)⁻¹ * |∑ σ : Fin n → Bool,
          ((Finset.univ : Finset ι).sup' Finset.univ_nonempty (a S σ)
            - (Finset.univ : Finset ι).sup' Finset.univ_nonempty
                (a (Function.update S k z') σ))|
      ≤ ((2:ℝ) ^ n)⁻¹ * ∑ _σ : Fin n → Bool, (2 * B / n) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt two_pow_inv_pos)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum (fun σ _ => hsupσ σ)
    _ = 2 * B / n := by
        have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        have h2 : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by push_cast; ring
        rw [h2, inv_mul_cancel_left₀ (pow_pos (by norm_num : (0:ℝ) < 2) n).ne']

/-- **`empiricalRademacherComplexity` has bounded differences** with
per-coordinate constant `2B/n` — the same constant as the generalization gap,
so its McDiarmid tail composes with the genGap tail. -/
lemma empiricalRademacher_hasBoundedDifferences
    (ℓ : ι → Z → ℝ) {B : ℝ} (hℓ : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    HasBoundedDifferences (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
      (fun _ : Fin n => 2 * B / n) :=
  fun S k z' => abs_empiricalRademacher_update_le_of_bdd ℓ hℓ hn S k z'

/-! ## McDiarmid concentration for empirical Rademacher complexity

Composing the bounded-differences property with the generic Azuma/McDiarmid tail
`hasBoundedDifferences_tail_azuma` gives two-sided concentration of `R̂` around its
mean. The lower tail is the one the data-dependent threshold needs: `R̂(S)` is not
much below `E[R̂]`, so the observable `2·R̂(S)` lower-bounds the population
`2·E[Rad]`. -/

/-- Integrability of `R̂` on the iid product measure, from boundedness. -/
lemma empiricalRademacher_integrable [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i)) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
      (Measure.pi (fun _ : Fin n => μ)) := by
  refine ⟨(Decoupling.measurable_empiricalRademacherComplexity
      hℓ_meas).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := B) ?_
  exact Filter.Eventually.of_forall (fun S =>
    (Real.norm_eq_abs _) ▸
      Decoupling.abs_empiricalRademacherComplexity_le hB hℓ_bdd hn S)

/-- **Upper McDiarmid tail for empirical Rademacher complexity:** `R̂(S)` is not
much above its mean. -/
theorem empiricalRademacher_tail_bound_azuma [MeasurableSpace Z] (μ : Measure Z)
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i)) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | (∫ s, empiricalRademacherComplexity ℓ s ∂(Measure.pi (fun _ : Fin n => μ))) + ε
              ≤ empiricalRademacherComplexity ℓ S}
      ≤ Real.exp (- ε ^ 2 / (2 * (∑ _k : Fin n, ‖(2 * B / n : ℝ)‖₊ ^ 2 : ℝ≥0))) := by
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  exact hasBoundedDifferences_tail_azuma
    (empiricalRademacher_hasBoundedDifferences ℓ hℓ_bdd hn)
    (Decoupling.measurable_empiricalRademacherComplexity hℓ_meas).stronglyMeasurable
    (empiricalRademacher_integrable μ ℓ hB hℓ_meas hℓ_bdd hn)
    (fun _ => div_nonneg (by linarith) hn_real) hε

/-- **Lower McDiarmid tail for empirical Rademacher complexity:** `R̂(S)` is not
much below its mean — the form the data-dependent threshold needs. -/
theorem empiricalRademacher_lower_tail_bound_azuma [MeasurableSpace Z] (μ : Measure Z)
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i)) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | empiricalRademacherComplexity ℓ S + ε
              ≤ ∫ s, empiricalRademacherComplexity ℓ s ∂(Measure.pi (fun _ : Fin n => μ))}
      ≤ Real.exp (- ε ^ 2 / (2 * (∑ _k : Fin n, ‖(2 * B / n : ℝ)‖₊ ^ 2 : ℝ≥0))) := by
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hbdd_neg : HasBoundedDifferences
      (fun S : Fin n → Z => -empiricalRademacherComplexity ℓ S)
      (fun _ : Fin n => 2 * B / n) := by
    intro S k z'
    have h := empiricalRademacher_hasBoundedDifferences ℓ hℓ_bdd hn S k z'
    have heq : -empiricalRademacherComplexity ℓ S
          - -empiricalRademacherComplexity ℓ (Function.update S k z')
        = -(empiricalRademacherComplexity ℓ S
          - empiricalRademacherComplexity ℓ (Function.update S k z')) := by ring
    rw [heq, abs_neg]; exact h
  have hbase := hasBoundedDifferences_tail_azuma (μ := μ) hbdd_neg
    ((Decoupling.measurable_empiricalRademacherComplexity hℓ_meas).neg).stronglyMeasurable
    (empiricalRademacher_integrable μ ℓ hB hℓ_meas hℓ_bdd hn).neg
    (fun _ => div_nonneg (by linarith) hn_real) hε
  have hset :
      {S : Fin n → Z | empiricalRademacherComplexity ℓ S + ε
            ≤ ∫ s, empiricalRademacherComplexity ℓ s ∂(Measure.pi (fun _ : Fin n => μ))}
        = {S : Fin n → Z |
            (∫ s, -empiricalRademacherComplexity ℓ s ∂(Measure.pi (fun _ : Fin n => μ))) + ε
              ≤ -empiricalRademacherComplexity ℓ S} := by
    ext S
    simp only [Set.mem_setOf_eq, integral_neg]
    constructor <;> intro h <;> linarith
  rw [hset]; exact hbase

end FormalSLT.Rademacher
