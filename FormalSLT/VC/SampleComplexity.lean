import FormalSLT.VC.SauerShelah
import FormalSLT.VC.Rademacher
import FormalSLT.Rademacher.HighProbability
import FormalSLT.Rademacher.UniformDeviation
import FormalSLT.ERM

/-!
# VC-dimension sample complexity via Rademacher complexity

## Scope

Composes the Sauer-Shelah polynomial bound with the effective-class Massart
bound to obtain the classic VC-dimension Rademacher complexity bound:

    empiricalRademacherComplexity ℓ z ≤ B · √(2d · log(en/d) / n)

and derives the high-probability VC sample-complexity theorem:

    P(genGap ≥ 2B · √(2d · log(en/d) / n) + ε) ≤ exp(-ε²n/(2B²))

## Chain of composition

1. **Sauer-Shelah polynomial** (`sauerShelah_polynomial_bound`):
   `∑_{k≤d} C(n,k) ≤ (en/d)^d`

2. **Effective-class Massart** (`empiricalRademacherComplexity_le_massart_effective`):
   `Rad(z) ≤ B · √(2 · log(effectiveClass.card) / n)`

3. **Log monotonicity + log of power**:
   `log(effectiveClass.card) ≤ log((en/d)^d) = d · log(en/d)`

4. **High-probability Rademacher** (`genGap_highProb_rademacher`):
   `P(genGap ≥ 2·E[Rad] + ε) ≤ exp(-ε²n/(2B²))`

## Assumptions

The main public theorems assume a finite hypothesis type, a finite-sample
effective-class growth bound, bounded losses with envelope `B`, measurable
losses, and an iid product sample law.

## Current boundaries

The VC route is a finite-sample high-probability wrapper. It uses the checked
sharp genGap tail where the concentration exponent appears, but it does not
state an arbitrary non-iid product-space theorem or a localized-Rademacher
sample-complexity theorem.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter ProbabilityTheory Real Finset

open FormalSLT.VC.SauerShelah (sauerShelah_polynomial_bound)
open FormalSLT.VC.Rademacher
  (effectiveClass effectiveClass_nonempty empiricalRademacherComplexity_le_massart_effective)
open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity)
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap)
open FormalSLT.Risk (uniformDeviation risk empiricalRisk)
open FormalSLT.Rademacher.UniformDeviation
  (uniformDeviation_subset_genGap_union)
open FormalSLT.ERM (IsERM erm_excessRisk_le_two_uniformDeviation)
open FormalSLT.Rademacher.HighProbability
  (genGap_highProb_rademacher)

noncomputable section

namespace FormalSLT.VC.SampleComplexity

open FormalSLT.Rademacher.FiniteSample (sum_signOfBool_eq_zero signOfBool)
open FormalSLT.VC.Rademacher (sup'_eq_sup'_effectiveClass)

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]

/-- When the effective class is a singleton, the empirical Rademacher complexity
is zero. If all hypotheses produce the same loss pattern on the sample, the sup
collapses and the sign-average cancels by symmetry. -/
private lemma empiricalRademacherComplexity_eq_zero_of_singleton
    {ℓ : ι → Z → ℝ} {n : ℕ} (z : Fin n → Z)
    (hCard : (effectiveClass ℓ z).card ≤ 1) :
    empiricalRademacherComplexity ℓ z = 0 := by
  -- Since effectiveClass is nonempty and card ≤ 1, it's a singleton {v}.
  have hne := effectiveClass_nonempty ℓ z
  have hCard_eq : (effectiveClass ℓ z).card = 1 :=
    Nat.le_antisymm hCard (Finset.Nonempty.card_pos hne)
  obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp hCard_eq
  -- Rewrite using sup'_eq_sup'_effectiveClass: sup over ι = sup over {v}.
  unfold empiricalRademacherComplexity
  have h_sum_zero : ∑ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)) = 0 := by
    -- Each σ-term equals f v since effectiveClass = {v}.
    have h_rewrite : ∀ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
        = (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * v k := by
      intro σ
      rw [sup'_eq_sup'_effectiveClass ℓ z σ]
      -- sup' over singleton = f v. Use exists_mem_eq_sup' to avoid dependent rw.
      have h_unique : ∀ w ∈ effectiveClass ℓ z, w = v := by
        intro w hw; rw [hv_eq] at hw; exact Finset.mem_singleton.mp hw
      obtain ⟨w, hw_mem, hw_eq⟩ := Finset.exists_mem_eq_sup'
        (effectiveClass_nonempty ℓ z)
        (fun w => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * w k)
      rw [hw_eq, h_unique w hw_mem]
    simp_rw [h_rewrite]
    -- Factor n⁻¹ outside: ∑_σ (n⁻¹ * f σ) = n⁻¹ * ∑_σ f σ.
    rw [← Finset.mul_sum]
    -- Suffices: ∑_σ ∑_k sign(σ_k) * v_k = 0.
    suffices h_zero : ∑ σ : Fin n → Bool, ∑ k : Fin n, signOfBool (σ k) * v k = 0 by
      rw [h_zero]; simp
    -- Swap sums and use sign cancellation.
    rw [Finset.sum_comm (f := fun (σ : Fin n → Bool) (k : Fin n) => signOfBool (σ k) * v k)]
    apply Finset.sum_eq_zero
    intro k _
    -- ∑_σ sign(σ_k) * v_k = (∑_σ sign(σ_k)) * v_k = 0 * v_k = 0.
    rw [← Finset.sum_mul]
    rw [sum_signOfBool_eq_zero k, zero_mul]
  rw [h_sum_zero, mul_zero]

/-- **Pointwise VC-Rademacher bound.**

For a sample `z` where the effective class (distinct loss patterns) has
cardinality bounded by the Sauer-Shelah growth function `∑_{k≤d} C(n,k)`,
the empirical Rademacher complexity satisfies:

    Rad(z) ≤ B · √(2d · log(en/d) / n)

This replaces `log|H|` in the standard Massart bound with the tighter
`d · log(en/d)`, where `d` is the VC dimension (or any upper bound on the
effective class growth exponent).

The singleton case (all hypotheses agree on the sample) is handled by
showing Rad = 0, which is ≤ the nonneg bound. -/
theorem vcRademacher_pointwise
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (z : Fin n → Z) (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth : (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k) :
    empiricalRademacherComplexity ℓ z
      ≤ B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ)) := by
  -- Case split: singleton effective class vs. nontrivial.
  by_cases hEffCard_gt : 1 < (effectiveClass ℓ z).card
  · -- Nontrivial case: use Massart + Sauer-Shelah.
    -- Step 1: Massart effective-class bound.
    have h_massart := empiricalRademacherComplexity_le_massart_effective hB hℓ_bdd z hn hEffCard_gt
    -- Step 2: Bound effective class card by (en/d)^d via Sauer-Shelah.
    have h_sauer := sauerShelah_polynomial_bound hd hdn
    -- Effective class card (as ℝ) ≤ (en/d)^d.
    have hCardR : (↑(effectiveClass ℓ z).card : ℝ) ≤ (Real.exp 1 * ↑n / ↑d) ^ d := by
      calc (↑(effectiveClass ℓ z).card : ℝ)
          ≤ (↑(∑ k ∈ Finset.range (d + 1), n.choose k) : ℝ) := by
            exact_mod_cast hGrowth
        _ = ∑ k ∈ Finset.range (d + 1), (↑(n.choose k) : ℝ) := by
            push_cast; rfl
        _ ≤ (Real.exp 1 * ↑n / ↑d) ^ d := h_sauer
    -- Step 3: log is monotone, so log(card) ≤ log((en/d)^d) = d·log(en/d).
    have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdn)
    have h_end_pos : (0 : ℝ) < Real.exp 1 * ↑n / ↑d := by
      apply div_pos
      · exact mul_pos (Real.exp_pos 1) hnR
      · exact hdR
    have hCardPos : (0 : ℝ) < ↑(effectiveClass ℓ z).card := by
      exact_mod_cast lt_trans Nat.zero_lt_one hEffCard_gt
    have h_log : Real.log (↑(effectiveClass ℓ z).card)
        ≤ ↑d * Real.log (Real.exp 1 * ↑n / ↑d) := by
      calc Real.log (↑(effectiveClass ℓ z).card)
          ≤ Real.log ((Real.exp 1 * ↑n / ↑d) ^ d) :=
            Real.log_le_log hCardPos hCardR
        _ = ↑d * Real.log (Real.exp 1 * ↑n / ↑d) := by
            rw [Real.log_pow]
    -- Step 4: sqrt is monotone, so √(2·log(card)/n) ≤ √(2d·log(en/d)/n).
    have h_sqrt : Real.sqrt (2 * Real.log (↑(effectiveClass ℓ z).card) / (n : ℝ))
        ≤ Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ hnR.le
      linarith [h_log]
    -- Chain: Rad ≤ B·√(2·log(card)/n) ≤ B·√(2d·log(en/d)/n).
    calc empiricalRademacherComplexity ℓ z
        ≤ B * Real.sqrt (2 * Real.log (↑(effectiveClass ℓ z).card) / (n : ℝ)) := h_massart
      _ ≤ B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h_sqrt hB.le
  · -- Singleton case: all hypotheses agree on the sample, Rad = 0.
    have hCard_le : (effectiveClass ℓ z).card ≤ 1 := not_lt.mp hEffCard_gt
    have h_zero := empiricalRademacherComplexity_eq_zero_of_singleton z hCard_le
    rw [h_zero]
    positivity

/-- The expected empirical Rademacher complexity is bounded by the VC-Rademacher
bound. The pointwise bound holds for ALL samples (handling both the singleton
and nontrivial effective-class cases), so the integral is also bounded.

Hypothesis `hGrowth_uniform`: for every sample z, the effective class card is
bounded by the growth function ∑_{k≤d} C(n,k). This follows from the
hypothesis class having VC dimension ≤ d. -/
lemma expected_rademacher_le_vc
    [MeasurableSpace Z]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth_uniform : ∀ z : Fin n → Z,
      (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (ν : Measure (Fin n → Z)) [IsProbabilityMeasure ν] :
    ∫ S, empiricalRademacherComplexity ℓ S ∂ν
      ≤ B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ)) := by
  set C := B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
  have hC_nn : (0 : ℝ) ≤ C := by positivity
  -- Pointwise bound for all z.
  have h_pointwise : ∀ z : Fin n → Z, empiricalRademacherComplexity ℓ z ≤ C :=
    fun z => vcRademacher_pointwise hB hℓ_bdd z hn hd hdn (hGrowth_uniform z)
  -- Split on integrability.
  by_cases h_int : Integrable (fun z => empiricalRademacherComplexity ℓ z) ν
  · calc ∫ S, empiricalRademacherComplexity ℓ S ∂ν
        ≤ ∫ _S, C ∂ν := integral_mono h_int (integrable_const C) h_pointwise
      _ = C := by simp [integral_const]
  · rw [integral_undef h_int]
    exact hC_nn

/-- **High-probability VC sample-complexity bound.**

For a hypothesis class with uniformly bounded effective class cardinality
(as guaranteed by VC dimension ≤ d via Sauer-Shelah), with `B`-bounded loss
and an iid sample `S ~ μⁿ`:

    P(genGap(S) ≥ 2B · √(2d · log(en/d) / n) + ε) ≤ exp(-ε²n/(2B²))

This is the classic VC sample-complexity theorem expressed through the
Rademacher complexity route: Sauer-Shelah → Massart → Rademacher high-probability
bound with the sharp genGap tail.

The one-sided genGap is `sup_h (risk(h) - empiricalRisk(h))`, so this
bounds the worst-case overfitting of any hypothesis in the class. -/
theorem genGap_highProb_vcClass
    [MeasurableSpace Z] [Nonempty Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth_uniform : ∀ z : Fin n → Z,
      (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
              + ε ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  -- Step 1: High-prob Rademacher gives P(genGap ≥ 2·E[Rad] + ε) ≤ exp(...).
  have h_highProb := genGap_highProb_rademacher (μ := μ) (n := n) hB hℓ_meas hℓ_bdd hn hε
  -- Step 2: E[Rad] ≤ B·√(2d·log(en/d)/n) by the VC bound.
  have h_vc : ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n)
      ≤ B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ)) := by
    have : IsProbabilityMeasure (piMeasure μ n) := by
      unfold piMeasure; infer_instance
    exact expected_rademacher_le_vc hB hℓ_bdd hn hd hdn
      hGrowth_uniform (piMeasure μ n)
  -- Step 3: Monotonicity: the event {genGap ≥ 2·VC_bound + ε} ⊆ {genGap ≥ 2·E[Rad] + ε}.
  simp only [piMeasure] at h_highProb h_vc ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  set E_rad := ∫ S', empiricalRademacherComplexity ℓ S' ∂μn
  calc μn.real {S | 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / ↑n)
            + ε ≤ genGap μ ℓ S}
      ≤ μn.real {S | 2 * E_rad + ε ≤ genGap μ ℓ S} := by
        apply measureReal_mono
        · intro S hS
          simp only [Set.mem_setOf_eq] at hS ⊢
          linarith [h_vc]
        · exact measure_ne_top μn _
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := h_highProb

/-- **Two-sided VC uniform deviation bound.**

For a hypothesis class with VC dimension ≤ d (effective class card bounded by
the growth function for all samples), with `B`-bounded loss and iid sample:

    P(sup_h |risk(h) - emp(h)| ≥ 2B·√(2d·log(en/d)/n) + ε) ≤ 2·exp(-ε²n/(2B²))

Follows from `genGap_highProb_vcClass` applied to both ℓ and -ℓ with a
union bound. -/
theorem uniformDeviation_highProb_vcClass
    [MeasurableSpace Z] [Nonempty Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth_uniform : ∀ z : Fin n → Z,
      (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (hGrowth_neg : ∀ z : Fin n → Z,
      (effectiveClass (fun i w => -ℓ i w) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
              + ε ≤ uniformDeviation μ ℓ S}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  set threshold := 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (↑n : ℝ)) + ε
  -- Subset inclusion: uniformDeviation ≥ t → genGap(ℓ) ≥ t ∨ genGap(-ℓ) ≥ t.
  have h_subset : {S : Fin n → Z | threshold ≤ uniformDeviation μ ℓ S}
      ⊆ {S | threshold ≤ genGap μ ℓ S}
        ∪ {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S} :=
    uniformDeviation_subset_genGap_union
  simp only [piMeasure] at h_subset ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  -- Upper tail: P(genGap(ℓ) ≥ threshold) ≤ exp(-ε²n/(2B²)).
  have h_upper : μn.real {S | threshold ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := by
    have := genGap_highProb_vcClass (μ := μ) (n := n) hB hℓ_meas hℓ_bdd hn hd hdn
      hGrowth_uniform hε
    simp only [piMeasure] at this
    exact this
  -- Lower tail: P(genGap(-ℓ) ≥ threshold) ≤ exp(-ε²n/(2B²)).
  have h_lower : μn.real {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := by
    have := genGap_highProb_vcClass (μ := μ) (n := n) hB
      (fun i => (hℓ_meas i).neg)
      (fun i z => by
        rw [Pi.neg_apply, abs_neg]
        exact hℓ_bdd i z)
      hn hd hdn hGrowth_neg hε
    simp only [piMeasure] at this
    exact this
  -- Combine via monotonicity + union bound.
  calc μn.real {S | threshold ≤ uniformDeviation μ ℓ S}
      ≤ μn.real ({S | threshold ≤ genGap μ ℓ S}
          ∪ {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S}) :=
        measureReal_mono h_subset (measure_ne_top μn _)
    _ ≤ μn.real {S | threshold ≤ genGap μ ℓ S}
        + μn.real {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2))
        + Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) :=
        add_le_add h_upper h_lower
    _ = 2 * Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := by ring

/-- **VC-ERM excess-risk tail bound.**

For a hypothesis class with VC dimension ≤ d, uniformly `B`-bounded loss,
an iid sample `S ~ μⁿ`, and any exact empirical-risk minimizer `hhat(S)`:

    P(risk(hhat(S)) - risk(i*) ≥ 4B·√(2d·log(en/d)/n) + 2ε) ≤ 2·exp(-ε²n/(2B²))

This is the standard PAC-learning guarantee for finite VC-dimension classes:
ERM achieves excess risk O(√(d·log(n/d)/n)) with high probability.

Proof chains:
1. Deterministic ERM: excessRisk(ERM) ≤ 2·uniformDeviation
2. VC uniform deviation: P(uniformDev ≥ 2B√(2d·log(en/d)/n) + ε) ≤ 2·exp(...)
3. Combine via subset monotonicity. -/
theorem vc_erm_excessRisk_tail
    [MeasurableSpace Z] [Nonempty Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth_uniform : ∀ z : Fin n → Z,
      (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (hGrowth_neg : ∀ z : Fin n → Z,
      (effectiveClass (fun i w => -ℓ i w) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | risk μ ℓ i_star
              + 4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
              + 2 * ε
            ≤ risk μ ℓ (hhat S)}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  set t := 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (↑n : ℝ)) + ε
  -- Subset inclusion: ERM bad event ⊆ uniform deviation bad event.
  have h_subset :
      {S : Fin n → Z | risk μ ℓ i_star +
            4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / ↑n)
            + 2 * ε
          ≤ risk μ ℓ (hhat S)}
        ⊆ {S | t ≤ uniformDeviation μ ℓ S} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    have h_det := erm_excessRisk_le_two_uniformDeviation (μ := μ) (ℓ := ℓ)
      (z := S) (î := hhat S) (i_star := i_star) (hERM S)
    linarith
  -- The VC uniform deviation tail bound.
  have h_ud := uniformDeviation_highProb_vcClass (μ := μ) (n := n)
    hB hℓ_meas hℓ_bdd hn hd hdn
    hGrowth_uniform hGrowth_neg hε
  -- Chain via monotonicity.
  simp only [piMeasure] at h_subset h_ud ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  calc μn.real {S | risk μ ℓ i_star +
        4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / ↑n)
        + 2 * ε ≤ risk μ ℓ (hhat S)}
      ≤ μn.real {S | t ≤ uniformDeviation μ ℓ S} :=
        measureReal_mono h_subset (measure_ne_top μn _)
    _ ≤ 2 * Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := h_ud

/-- **VC-ERM closed-form sample complexity.**

For a hypothesis class with VC dimension ≤ d, uniformly `B`-bounded loss,
an iid sample `S ~ μⁿ`, and any exact ERM `ĥ(S)`, if the sample size satisfies

    n · ε² ≥ 72 · B² · (d · log(en/d) + log(2/δ))

then with probability at least 1 − δ over S, the ERM has excess risk ≤ ε:

    P(risk(ĥ(S)) − risk(i★) ≥ ε) ≤ δ

This is the classical PAC sample-complexity statement for finite VC classes,
expressed with the explicit constant **C = 72 B²**.

**Proof sketch.** Apply `vc_erm_excessRisk_tail` with tail parameter `ε' := ε/6`,
yielding the bound on the event {excess ≥ 4B·√(2d·log(en/d)/n) + ε/3}. The
hypothesis splits into two halves (each ≤ n·ε² since the discarded summand is
nonnegative):

* `72 B² · d · log(en/d) ≤ n ε²`: ensures `4B·√(2d·log(en/d)/n) ≤ 2ε/3`, so
  the deterministic VC piece is absorbed.
* `72 B² · log(2/δ) ≤ n ε²`: ensures `2 · exp(-(ε/6)² n / (2B²)) ≤ δ`,
  i.e. the concentration tail is at most δ.

Combining via subset monotonicity gives the closed-form statement. -/
theorem vc_erm_sample_complexity
    [MeasurableSpace Z] [Nonempty Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n d : ℕ} (hn_pos : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth_uniform : ∀ z : Fin n → Z,
      (effectiveClass ℓ z).card ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (hGrowth_neg : ∀ z : Fin n → Z,
      (effectiveClass (fun i w => -ℓ i w) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 72 * B ^ 2 * (↑d * Real.log (Real.exp 1 * ↑n / ↑d) + Real.log (2 / δ))
        ≤ ↑n * ε ^ 2) :
    (piMeasure μ n).real
        {S | risk μ ℓ i_star + ε ≤ risk μ ℓ (hhat S)}
      ≤ δ := by
  -- Real-valued positivity facts.
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_en_pos : (0 : ℝ) < Real.exp 1 * ↑n := mul_pos (Real.exp_pos 1) hnR
  have h72B2_nn : (0 : ℝ) ≤ 72 * B ^ 2 := by positivity
  -- log(en/d) ≥ 0 because Real.log (Real.exp 1) = 1 and d ≤ n.
  have h_log_nn : 0 ≤ Real.log (Real.exp 1 * ↑n / ↑d) := by
    have h_split : Real.log (Real.exp 1 * ↑n / ↑d)
        = 1 + Real.log (n : ℝ) - Real.log (d : ℝ) := by
      rw [Real.log_div h_en_pos.ne' hdR.ne',
          Real.log_mul (Real.exp_pos 1).ne' hnR.ne', Real.log_exp]
    rw [h_split]
    have h_mono : Real.log (d : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hdR (Nat.cast_le.mpr hdn)
    linarith
  -- log(2/δ) ≥ 0 because δ ≤ 1 ≤ 2.
  have h_log_2δ_nn : 0 ≤ Real.log (2 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]; linarith
  -- d · log(en/d) ≥ 0.
  have h_VC_term_nn : 0 ≤ (d : ℝ) * Real.log (Real.exp 1 * ↑n / ↑d) :=
    mul_nonneg (Nat.cast_nonneg d) h_log_nn
  -- Distribute hn over the sum, then split into two halves.
  have h_dist : 72 * B ^ 2 *
        (↑d * Real.log (Real.exp 1 * ↑n / ↑d) + Real.log (2 / δ))
      = 72 * B ^ 2 * (↑d * Real.log (Real.exp 1 * ↑n / ↑d))
        + 72 * B ^ 2 * Real.log (2 / δ) := by ring
  have hn_split := hn
  rw [h_dist] at hn_split
  have h_tail_term_nn : 0 ≤ 72 * B ^ 2 * Real.log (2 / δ) :=
    mul_nonneg h72B2_nn h_log_2δ_nn
  have h_VC_full_nn : 0 ≤ 72 * B ^ 2 * (↑d * Real.log (Real.exp 1 * ↑n / ↑d)) :=
    mul_nonneg h72B2_nn h_VC_term_nn
  have hn_VC :
      72 * B ^ 2 * (↑d * Real.log (Real.exp 1 * ↑n / ↑d)) ≤ ↑n * ε ^ 2 := by
    linarith
  have hn_tail : 72 * B ^ 2 * Real.log (2 / δ) ≤ ↑n * ε ^ 2 := by
    linarith
  -- Apply the sharp tail bound with ε' := ε/6.
  have hε6 : (0 : ℝ) ≤ ε / 6 := by linarith
  have h_tail := vc_erm_excessRisk_tail (μ := μ) hB hℓ_meas hℓ_bdd
    hn_pos hd hdn hGrowth_uniform hGrowth_neg hhat hERM i_star (ε := ε / 6) hε6
  -- Step 1: 4B · √(2d·log(en/d)/n) ≤ 2ε/3 (from hn_VC).
  have h_VC_bound :
      4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
        ≤ 2 * ε / 3 := by
    have h23ε_nn : (0 : ℝ) ≤ 2 * ε / 3 := by linarith
    have h4B_nn : (0 : ℝ) ≤ 4 * B := by linarith
    -- Rewrite 4B·√x as √((4B)² · x) and 2ε/3 as √((2ε/3)²); then sqrt is monotone.
    have h_LHS_eq :
        4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
          = Real.sqrt
              ((4 * B) ^ 2 * (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h4B_nn]
    rw [h_LHS_eq, show (2 * ε / 3 : ℝ) = Real.sqrt ((2 * ε / 3) ^ 2) from
      (Real.sqrt_sq h23ε_nn).symm]
    apply Real.sqrt_le_sqrt
    -- Reduce to: 32 · B² · (d · log) / n ≤ (2ε/3)², i.e. 72 B² d log ≤ n ε².
    have h_alg :
        (4 * B) ^ 2 * (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
          = 32 * B ^ 2 * (↑d * Real.log (Real.exp 1 * ↑n / ↑d)) / (n : ℝ) := by ring
    rw [h_alg, div_le_iff₀ hnR]
    nlinarith [hn_VC]
  -- Step 2: 2 · exp(-(ε/6)² · n / (2 B²)) ≤ δ (from hn_tail).
  have h_exp_bound : 2 * Real.exp (-(ε / 6) ^ 2 * ↑n / (2 * B ^ 2)) ≤ δ := by
    have hδ2_pos : (0 : ℝ) < δ / 2 := by linarith
    have h2B2_pos : (0 : ℝ) < 2 * B ^ 2 := by positivity
    have h_log_eq : Real.log (δ / 2) = -Real.log (2 / δ) := by
      rw [Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0),
          Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hδ.ne']; ring
    have h_inner : -(ε / 6) ^ 2 * ↑n / (2 * B ^ 2) ≤ Real.log (δ / 2) := by
      rw [h_log_eq, div_le_iff₀ h2B2_pos]
      nlinarith [hn_tail]
    have h_exp_le : Real.exp (-(ε / 6) ^ 2 * ↑n / (2 * B ^ 2)) ≤ δ / 2 := by
      have h_step := Real.exp_le_exp.mpr h_inner
      rwa [Real.exp_log hδ2_pos] at h_step
    linarith
  -- Step 3: subset inclusion + measure monotonicity + chain through h_tail.
  have h_subset :
      {S : Fin n → Z | risk μ ℓ i_star + ε ≤ risk μ ℓ (hhat S)}
        ⊆ {S | risk μ ℓ i_star
              + 4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
              + 2 * (ε / 6) ≤ risk μ ℓ (hhat S)} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    linarith
  simp only [piMeasure] at h_tail ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  calc μn.real {S | risk μ ℓ i_star + ε ≤ risk μ ℓ (hhat S)}
      ≤ μn.real {S | risk μ ℓ i_star
            + 4 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
            + 2 * (ε / 6) ≤ risk μ ℓ (hhat S)} :=
        measureReal_mono h_subset (measure_ne_top μn _)
    _ ≤ 2 * Real.exp (-(ε / 6) ^ 2 * ↑n / (2 * B ^ 2)) := h_tail
    _ ≤ δ := h_exp_bound

end FormalSLT.VC.SampleComplexity
