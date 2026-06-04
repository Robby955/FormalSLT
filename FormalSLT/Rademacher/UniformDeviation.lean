import FormalSLT.Rademacher.FiniteClassHighProb
import FormalSLT.Risk

/-!
# Two-sided uniform deviation via Rademacher/Massart

Proves the two-sided high-probability uniform convergence bound:

  P(uniformDeviation μ ℓ S ≥ 2B·√(2·log|H|/n) + ε) ≤ 2·exp(-ε²n/(2B²))

The proof combines:
1. `genGap_highProb_finiteClass` for the upper side (risk - emp)
2. The same bound applied to `-ℓ` for the lower side (emp - risk)
3. A union bound to handle the absolute value

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter ProbabilityTheory Real Finset
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap)
open FormalSLT.Rademacher.FiniteClassHighProb
  (genGap_highProb_finiteClass)
open FormalSLT.Risk

noncomputable section

namespace FormalSLT.Rademacher.UniformDeviation

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-- Negating the loss flips the generalization gap to the reverse direction:
`genGap μ (-ℓ) S = sup_i (empiricalRisk S ℓ i - risk μ ℓ i)`.

No integrability hypothesis is needed because `integral_neg` holds
unconditionally for the Bochner integral. -/
lemma genGap_neg_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    {ℓ : ι → Z → ℝ} {n : ℕ} (S : Fin n → Z) :
    genGap μ (fun i z => -ℓ i z) S
      = (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => empiricalRisk S ℓ i - risk μ ℓ i) := by
  unfold genGap
  refine Finset.sup'_congr _ rfl (fun i _ => ?_)
  unfold risk empiricalRisk
  simp only [integral_neg, Finset.sum_neg_distrib, mul_neg, neg_sub_neg]

/-- The uniform deviation event is contained in the union of the two
one-sided genGap events (upper and lower).

If `c ≤ sup_i |emp_i - risk_i|`, then either `c ≤ sup_i (risk_i - emp_i)`
(the genGap of ℓ) or `c ≤ sup_i (emp_i - risk_i)` (the genGap of -ℓ). -/
lemma uniformDeviation_subset_genGap_union {ι : Type*} [Fintype ι] [Nonempty ι]
    {ℓ : ι → Z → ℝ} {n : ℕ} {c : ℝ} :
    {S : Fin n → Z | c ≤ uniformDeviation μ ℓ S}
      ⊆ {S | c ≤ genGap μ ℓ S}
        ∪ {S | c ≤ genGap μ (fun i z => -ℓ i z) S} := by
  intro S hS
  simp only [Set.mem_setOf_eq, Set.mem_union] at hS ⊢
  -- uniformDeviation = sup'_i |emp_i - risk_i|
  unfold uniformDeviation at hS
  -- Extract a witness i₀ that attains the supremum (ℝ is a LinearOrder)
  obtain ⟨i₀, _, hi₀_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => |empiricalRisk S ℓ i - risk μ ℓ i|)
  have hi₀ : c ≤ |empiricalRisk S ℓ i₀ - risk μ ℓ i₀| := hi₀_eq ▸ hS
  -- Case split on the sign of (emp_{i₀} - risk_{i₀})
  by_cases h_nn : 0 ≤ empiricalRisk S ℓ i₀ - risk μ ℓ i₀
  · -- emp_{i₀} - risk_{i₀} ≥ 0: the absolute value is emp - risk,
    -- so genGap(-ℓ) = sup_i (emp_i - risk_i) ≥ c
    right
    rw [abs_of_nonneg h_nn] at hi₀
    rw [genGap_neg_eq S]
    exact le_trans hi₀ (Finset.le_sup'
      (fun i => empiricalRisk S ℓ i - risk μ ℓ i) (Finset.mem_univ i₀))
  · -- emp_{i₀} - risk_{i₀} < 0: the absolute value is risk - emp,
    -- so genGap(ℓ) = sup_i (risk_i - emp_i) ≥ c
    left
    have h_neg : empiricalRisk S ℓ i₀ - risk μ ℓ i₀ < 0 := not_le.mp h_nn
    rw [abs_of_neg h_neg] at hi₀
    -- hi₀ : c ≤ -(emp_{i₀} - risk_{i₀}) = risk_{i₀} - emp_{i₀}
    unfold genGap
    have h_eq : -(empiricalRisk S ℓ i₀ - risk μ ℓ i₀)
        = risk μ ℓ i₀ - empiricalRisk S ℓ i₀ := neg_sub _ _
    rw [h_eq] at hi₀
    exact le_trans hi₀ (Finset.le_sup'
      (fun i => risk μ ℓ i - empiricalRisk S ℓ i) (Finset.mem_univ i₀))

/-- **Two-sided high-probability finite-class uniform deviation bound.**

For a finite hypothesis class `ι` with `|ι| > 1`, uniformly `B`-bounded loss,
and an iid sample `S ~ μⁿ`:

    P(uniformDeviation S ≥ 2B · √(2 · log|H| / n) + ε) ≤ 2 · exp(-ε²n/(2B²))

This follows from the one-sided `genGap_highProb_finiteClass` applied to both
`ℓ` (upper tail: risk - emp) and `-ℓ` (lower tail: emp - risk), combined
with a union bound on the two one-sided events. -/
theorem uniformDeviation_highProb_finiteClass {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + ε ≤ uniformDeviation μ ℓ S}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  set threshold := 2 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ)) + ε
  -- Subset inclusion: uniformDeviation ≥ t → genGap(ℓ) ≥ t ∨ genGap(-ℓ) ≥ t.
  have h_subset : {S : Fin n → Z | threshold ≤ uniformDeviation μ ℓ S}
      ⊆ {S | threshold ≤ genGap μ ℓ S}
        ∪ {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S} :=
    uniformDeviation_subset_genGap_union
  -- Unfold piMeasure and set μn.
  simp only [piMeasure] at h_subset ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  -- Upper tail: P(genGap(ℓ) ≥ threshold) ≤ exp(-ε²n/(2B²)).
  have h_upper : μn.real {S | threshold ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := by
    have := genGap_highProb_finiteClass (μ := μ) (n := n) hB hℓ_meas hℓ_bdd hn hCard hε
    simp only [piMeasure] at this
    exact this
  -- Lower tail: P(genGap(-ℓ) ≥ threshold) ≤ exp(-ε²n/(2B²)).
  have h_lower : μn.real {S | threshold ≤ genGap μ (fun i z => -ℓ i z) S}
      ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := by
    have := genGap_highProb_finiteClass (μ := μ) (n := n) hB
      (fun i => (hℓ_meas i).neg)
      (fun i z => by simp only [abs_neg]; exact hℓ_bdd i z)
      hn hCard hε
    simp only [piMeasure] at this
    exact this
  -- Combine via monotonicity and the union bound.
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

end FormalSLT.Rademacher.UniformDeviation
