import FormalSLT.Rademacher.MetricEntropyGeneralization
import FormalSLT.Rademacher.HighProbability

/-!
# High-probability metric-entropy generalization bridge

This module composes the finite metric-entropy mean bridge with FormalSLT's
sharp high-probability Rademacher theorem. If the same deterministic Dudley
budget controls the empirical Rademacher complexity for almost every iid
sample, then

`P(genGap S >= 2 * uniformDudleyBudget + ε) <= exp (-ε^2 * n / (2 * B^2))`.

Expanding `uniformDudleyBudget` gives the explicit metric-entropy threshold
with constant `8`. The theorem remains finite-class and uses the explicit
sample-dependent net conditions from `MetricEntropyGeneralization`; it is not
a full continuous Dudley theorem.

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Rademacher.MetricEntropyHighProbability

open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.GhostSample (piMeasure genGap)
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)
open FormalSLT.Rademacher (empiricalRademacher_integrable)
open FormalSLT.Rademacher.HighProbability (genGap_highProb_rademacher)
open FormalSLT.Rademacher.MetricEntropyGeneralization
  (SampleDudleySideConditions expected_empiricalRademacher_le_dudley_uniform
    uniformDudleyBudget)

noncomputable section

universe u

variable {n : ℕ} {ι : Type u} {Z : Type*}
variable [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
variable [Nonempty Z] [StandardBorelSpace Z]

/-- **High-probability generalization bound from a uniform Dudley budget.**

The almost-everywhere Dudley certificate bounds the expected empirical
Rademacher complexity by `uniformDudleyBudget`. The existing sharp
high-probability Rademacher theorem controls the event above twice that
expectation. Raising its deterministic threshold to twice the Dudley budget
can only shrink the bad event. -/
theorem genGap_highProb_uniformDudleyBudget
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : (Fin n → Z) → ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ)
    (t₀ : (Fin n → Z) → ι)
    (hside :
      ∀ᵐ S ∂(piMeasure μ n),
        SampleDudleySideConditions ℓ S (N S) m (t₀ S)
          radiusScale coveringNumberAtRadius)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S : Fin n → Z |
          2 * uniformDudleyBudget n m radiusScale coveringNumberAtRadius + ε
            ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * (n : ℝ) / (2 * B ^ 2)) := by
  have hrad_int :
      Integrable (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
        (piMeasure μ n) :=
    empiricalRademacher_integrable μ ℓ hB.le hℓ_meas hℓ_bdd hn
  have hrad :
      ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n)
        ≤ uniformDudleyBudget n m radiusScale coveringNumberAtRadius :=
    expected_empiricalRademacher_le_dudley_uniform
      μ ℓ hrad_int N m radiusScale coveringNumberAtRadius t₀ hside
  have hbase :=
    genGap_highProb_rademacher (μ := μ) (ℓ := ℓ)
      hB hℓ_meas hℓ_bdd hn hε
  have hsubset :
      {S : Fin n → Z |
          2 * uniformDudleyBudget n m radiusScale coveringNumberAtRadius + ε
            ≤ genGap μ ℓ S} ⊆
        {S : Fin n → Z |
          2 * ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n) + ε
            ≤ genGap μ ℓ S} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    nlinarith [hrad]
  exact (measureReal_mono hsubset).trans hbase

/-- **Explicit high-probability metric-entropy generalization bound.**

This is `genGap_highProb_uniformDudleyBudget` with the deterministic budget
expanded. The constant `8` is the Dudley constant `4` multiplied by the
symmetrization factor `2`. -/
theorem metricEntropy_generalization_highProb
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : (Fin n → Z) → ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ)
    (t₀ : (Fin n → Z) → ι)
    (hside :
      ∀ᵐ S ∂(piMeasure μ n),
        SampleDudleySideConditions ℓ S (N S) m (t₀ S)
          radiusScale coveringNumberAtRadius)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S : Fin n → Z |
          8 * Real.sqrt (2 / (n : ℝ)) *
              (∫ η in
                (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
                Real.sqrt (Real.log (coveringNumberAtRadius η : ℝ))) + ε
            ≤ genGap μ ℓ S}
      ≤ Real.exp (-ε ^ 2 * (n : ℝ) / (2 * B ^ 2)) := by
  have h := genGap_highProb_uniformDudleyBudget
    μ ℓ hB hℓ_meas hℓ_bdd hn N m radiusScale
      coveringNumberAtRadius t₀ hside hε
  have hbudget :
      2 * uniformDudleyBudget n m radiusScale coveringNumberAtRadius =
        8 * Real.sqrt (2 / (n : ℝ)) *
          (∫ η in
            (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            Real.sqrt (Real.log (coveringNumberAtRadius η : ℝ))) := by
    simp [uniformDudleyBudget]
    ring
  rwa [hbudget] at h

/-- The explicit sharp tail factor is genuinely below one for the concrete
choice `n = B = ε = 1`. This witnesses that the confidence term in the public
high-probability theorem is nontrivial. -/
theorem metricEntropy_highProb_tail_nontrivial :
    Real.exp (-((1 : ℝ) ^ 2) * (1 : ℝ) / (2 * (1 : ℝ) ^ 2)) < 1 := by
  rw [Real.exp_lt_one_iff]
  norm_num

end

end FormalSLT.Rademacher.MetricEntropyHighProbability
