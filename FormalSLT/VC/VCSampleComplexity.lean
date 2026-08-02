import FormalSLT.VC.SauerShelah
import FormalSLT.VC.VCRademacher
import FormalSLT.Rademacher.HighProbRademacher
import FormalSLT.Rademacher.UniformDeviation
import FormalSLT.ERM

/-!
# VC-dimension sample complexity via Rademacher complexity

Composes the Sauer-Shelah polynomial bound with the effective-class Massart
bound to obtain the classic VC-dimension Rademacher complexity bound:

    empiricalRademacherComplexity ℓ z ≤ B · √(2d · log(en/d) / n)

and derives the high-probability VC sample-complexity theorem:

    P(genGap ≥ 2B · √(2d · log(en/d) / n) + ε) ≤ exp(-ε²n/(8B²))

## Chain of composition

1. **Sauer-Shelah polynomial** (`sauerShelah_polynomial_bound`):
   `∑_{k≤d} C(n,k) ≤ (en/d)^d`

2. **Effective-class Massart** (`empiricalRademacherComplexity_le_massart_effective`):
   `Rad(z) ≤ B · √(2 · log(effectiveClass.card) / n)`

3. **Log monotonicity + log of power**:
   `log(effectiveClass.card) ≤ log((en/d)^d) = d · log(en/d)`

4. **High-probability Rademacher** (`genGap_highProb_rademacher`):
   `P(genGap ≥ 2·E[Rad] + ε) ≤ exp(-ε²n/(8B²))`

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter ProbabilityTheory Real Finset

open FormalSLT.VC.SauerShelah (sauerShelah_polynomial_bound)
open FormalSLT.VC.VCRademacher
  (effectiveClass effectiveClass_nonempty empiricalRademacherComplexity_le_massart_effective)
open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity)
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap)
open FormalSLT.Risk (uniformDeviation risk empiricalRisk)
open FormalSLT.Rademacher.UniformDeviation
  (uniformDeviation_subset_genGap_union)
open FormalSLT.ERM (IsERM erm_excessRisk_le_two_uniformDeviation)
open FormalSLT.Rademacher.HighProbRademacher
  (genGap_highProb_rademacher)

noncomputable section

namespace FormalSLT.VC.VCSampleComplexity

open FormalSLT.Rademacher.FiniteSample (sum_signOfBool_eq_zero signOfBool)
open FormalSLT.VC.VCRademacher (sup'_eq_sup'_effectiveClass)

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
showing Rad = 0, which is ≤ the nonneg bound.

Claim-facing wrapper for theorempath.com evidence entry `claim:rademacher-complexity::vc-style-rademacher-bound`.
-/
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

    P(genGap(S) ≥ 2B · √(2d · log(en/d) / n) + ε) ≤ exp(-ε²n/(8B²))

This is the classic VC sample-complexity theorem expressed through the
Rademacher complexity route: Sauer-Shelah → Massart → Rademacher → Azuma.

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
      ≤ Real.exp (- ε ^ 2 * ↑n / (8 * B ^ 2)) := by
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
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := h_highProb

/-- **Two-sided VC uniform deviation bound.**

For a hypothesis class with VC dimension ≤ d (effective class card bounded by
the growth function for all samples), with `B`-bounded loss and iid sample:

    P(sup_h |risk(h) - emp(h)| ≥ 2B·√(2d·log(en/d)/n) + ε) ≤ 2·exp(-ε²n/(8B²))

Follows from `genGap_highProb_vcClass` applied to both ℓ and -ℓ with a
union bound.

Claim-facing wrapper for theorempath.com evidence entry `claim:uniform-convergence::vc-style-uniform-deviation-bound`.
-/
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
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (8 * B ^ 2)) := by
  set threshold := 2 * B * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (↑n : ℝ)) + ε
  -- Subset inclusion: uniformDeviation ≥ t → genGap(ℓ) ≥ t ∨ genGap(-ℓ) ≥ t.
  have h_subset : {S : Fin n → Z | threshold ≤ uniformDeviation μ ℓ S}
      ⊆ {S | threshold ≤ genGap μ ℓ S}
        ∪ {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S} :=
    uniformDeviation_subset_genGap_union
  simp only [piMeasure] at h_subset ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  -- Upper tail: P(genGap(ℓ) ≥ threshold) ≤ exp(-ε²n/(8B²)).
  have h_upper : μn.real {S | threshold ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := by
    have := genGap_highProb_vcClass (μ := μ) (n := n) hB hℓ_meas hℓ_bdd hn hd hdn
      hGrowth_uniform hε
    simp only [piMeasure] at this
    exact this
  -- Lower tail: P(genGap(-ℓ) ≥ threshold) ≤ exp(-ε²n/(8B²)).
  have h_lower : μn.real {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := by
    have := genGap_highProb_vcClass (μ := μ) (n := n) hB
      (fun i => (hℓ_meas i).neg)
      (fun i z => by simp only [abs_neg]; exact hℓ_bdd i z)
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
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2))
        + Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) :=
        add_le_add h_upper h_lower
    _ = 2 * Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := by ring

/-- **VC-ERM excess-risk tail bound.**

For a hypothesis class with VC dimension ≤ d, uniformly `B`-bounded loss,
an iid sample `S ~ μⁿ`, and any exact empirical-risk minimizer `hhat(S)`:

    P(risk(hhat(S)) - risk(i*) ≥ 4B·√(2d·log(en/d)/n) + 2ε) ≤ 2·exp(-ε²n/(8B²))

This is the standard PAC-learning guarantee for finite VC-dimension classes:
ERM achieves excess risk O(√(d·log(n/d)/n)) with high probability.

Proof chains:
1. Deterministic ERM: excessRisk(ERM) ≤ 2·uniformDeviation
2. VC uniform deviation: P(uniformDev ≥ 2B√(2d·log(en/d)/n) + ε) ≤ 2·exp(...)
3. Combine via subset monotonicity.

Claim-facing wrapper for theorempath.com evidence entry `claim:empirical-risk-minimization::vc-style-erm-excess-risk-tail`.
-/
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
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (8 * B ^ 2)) := by
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
    _ ≤ 2 * Real.exp (-ε ^ 2 * ↑n / (8 * B ^ 2)) := h_ud

end FormalSLT.VC.VCSampleComplexity
