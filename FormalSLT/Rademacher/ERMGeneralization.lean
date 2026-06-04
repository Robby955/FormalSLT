import FormalSLT.Rademacher.UniformDeviation
import FormalSLT.ERM

/-!
# Rademacher-route ERM generalization bound (finite class)

Combines the Rademacher/Massart two-sided uniform deviation bound:

    P(uniformDeviation S ≥ 2B√(2log|H|/n) + ε) ≤ 2·exp(-ε²n/(2B²))

with the deterministic ERM excess-risk inequality:

    risk(ERM(S)) ≤ risk(i*) + 2·uniformDeviation(S)

to obtain a high-probability ERM generalization bound:

    P(risk(ERM(S)) - risk(i*) ≥ 4B√(2log|H|/n) + 2ε) ≤ 2·exp(-ε²n/(2B²))

Equivalently, with probability at least `1 - 2·exp(-ε²n/(2B²))`:

    risk(ERM(S)) < risk(i*) + 4B√(2log|H|/n) + 2ε

This is the Rademacher analogue of `ERMGeneralization.lean` (which uses
the Hoeffding route). The two routes give complementary guarantees with
different constants and sample-size dependence.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter ProbabilityTheory Real Finset
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap)
open FormalSLT.Rademacher.UniformDeviation
  (uniformDeviation_highProb_finiteClass)
open FormalSLT.Risk
open FormalSLT.ERM

noncomputable section

namespace FormalSLT.Rademacher.ERMGeneralization

variable {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-- **Rademacher-route ERM excess-risk tail bound (comparator form).**

For a finite hypothesis class `ι` with `|ι| > 1`, uniformly `B`-bounded
measurable loss, an iid sample `S ~ μⁿ`, and any exact empirical-risk
minimizer `hhat(S)`:

    P(risk(i*) + 4B√(2log|H|/n) + 2ε ≤ risk(hhat(S))) ≤ 2·exp(-ε²n/(2B²))

where `i*` is any fixed comparator (not necessarily optimal).

The proof chains:
1. **Subset inclusion**: if `risk(hhat(S)) ≥ risk(i*) + 4B√(...) + 2ε`, then
   by the deterministic ERM bound, `uniformDeviation(S) ≥ 2B√(...) + ε`.
2. **Uniform deviation tail**: `P(uniformDeviation ≥ 2B√(...) + ε) ≤ 2·exp(...)`. -/
theorem rademacher_erm_comparator_tail {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | risk μ ℓ i_star
              + 4 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + 2 * ε
            ≤ risk μ ℓ (hhat S)}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  set t := 2 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ)) + ε
  -- Subset inclusion: ERM bad event ⊆ uniform deviation bad event.
  have h_subset :
      {S : Fin n → Z | risk μ ℓ i_star + 4 * B *
            Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n) + 2 * ε
          ≤ risk μ ℓ (hhat S)}
        ⊆ {S | t ≤ uniformDeviation μ ℓ S} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    -- Deterministic ERM bound: risk(hhat S) ≤ risk(i*) + 2·uniformDeviation(S)
    have h_det := erm_excessRisk_le_two_uniformDeviation (μ := μ) (ℓ := ℓ)
      (z := S) (î := hhat S) (i_star := i_star) (hERM S)
    -- From hS and h_det: 4B√(...) + 2ε ≤ 2·uniformDeviation(S)
    -- So: 2B√(...) + ε ≤ uniformDeviation(S)
    linarith
  -- The uniform deviation tail bound.
  have h_ud := uniformDeviation_highProb_finiteClass (μ := μ) (n := n)
    hB hℓ_meas hℓ_bdd hn hCard hε
  -- Chain via monotonicity.
  simp only [piMeasure] at h_subset h_ud ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  calc μn.real {S | risk μ ℓ i_star + 4 * B *
          Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n) + 2 * ε
        ≤ risk μ ℓ (hhat S)}
      ≤ μn.real {S | t ≤ uniformDeviation μ ℓ S} :=
        measureReal_mono h_subset (measure_ne_top μn _)
    _ ≤ 2 * Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := h_ud

/-- **Rademacher-route ERM excess-risk tail bound (oracle form).**

Specializes the comparator-form bound to the population-risk minimizer
`i_star` (via the hypothesis `hOracle : ∀ i, risk i_star ≤ risk i`), making
the conclusion a genuine excess-risk statement:

    P(risk(hhat(S)) - risk(i*) ≥ 4B√(2log|H|/n) + 2ε) ≤ 2·exp(-ε²n/(2B²))

This is the main ERM learning guarantee for finite hypothesis classes
via the Rademacher/Massart route. -/
theorem rademacher_erm_excessRisk_tail {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    (hOracle : ∀ i : ι, risk μ ℓ i_star ≤ risk μ ℓ i)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 4 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + 2 * ε
            ≤ risk μ ℓ (hhat S) - risk μ ℓ i_star}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  -- The oracle hypothesis witnesses that risk(hhat S) - risk(i*) ≥ 0.
  have _hExcessNonneg : ∀ S : Fin n → Z,
      0 ≤ risk μ ℓ (hhat S) - risk μ ℓ i_star := by
    intro S; linarith [hOracle (hhat S)]
  -- The event sets are equal by a linear rearrangement.
  have h_set_eq :
      {S : Fin n → Z |
        4 * B * Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n) + 2 * ε
          ≤ risk μ ℓ (hhat S) - risk μ ℓ i_star}
      = {S | risk μ ℓ i_star +
            4 * B * Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n) + 2 * ε
          ≤ risk μ ℓ (hhat S)} := by
    ext S
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [h_set_eq]
  exact rademacher_erm_comparator_tail hB hℓ_meas hℓ_bdd hn hCard hhat hERM i_star hε

end FormalSLT.Rademacher.ERMGeneralization
