import Mathlib.Probability.StrongLaw

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace FormalSLT.Probability.LawOfLargeNumbers

noncomputable section

/--
Strong law of large numbers for integrable identically distributed variables.

This is a claim-facing wrapper around mathlib's `strong_law_ae`. Mathlib proves
the theorem under pairwise independence plus identical distribution, which
covers the usual i.i.d. textbook scope while making the formal assumptions
explicit.
Claim-facing wrapper for theorempath.com evidence entry `claim:law-of-large-numbers::strong-law-of-large-numbers`.
-/
theorem strongLawAverageTendstoAlmostSure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hIntegrable : Integrable (X 0) μ)
    (hIndependent : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X))
    (hIdentDistrib : ∀ n, IdentDistrib (X n) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
        atTop
        (nhds μ[X 0]) :=
  strong_law_ae X hIntegrable hIndependent hIdentDistrib

/--
Weak law of large numbers, phrased as convergence in measure/probability.

This wrapper reuses the strong-law mathlib theorem and the standard
`tendstoInMeasure_of_tendsto_ae` bridge: almost-sure convergence on a
probability space implies convergence in measure, i.e. convergence in
probability. The formal statement keeps the same pairwise-independence and
identical-distribution assumptions as mathlib's strong law.
Claim-facing wrapper for theorempath.com evidence entry `claim:law-of-large-numbers::weak-law-of-large-numbers`.
-/
theorem weakLawAverageTendstoInMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hIntegrable : Integrable (X 0) μ)
    (hIndependent : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X))
    (hIdentDistrib : ∀ n, IdentDistrib (X n) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) (ω : Ω) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
      atTop
      (fun _ => μ[X 0]) := by
  have hMeas : ∀ i, AEStronglyMeasurable (X i) μ := fun i =>
    (hIdentDistrib i).aestronglyMeasurable_iff.2 hIntegrable.1
  have hAverage :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun (ω : Ω) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
          μ := fun n => by
    have hSum :
        AEStronglyMeasurable
          (fun (ω : Ω) => ∑ i ∈ Finset.range n, X i ω)
          μ :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ => hMeas i
    have h := AEStronglyMeasurable.const_smul hSum ((n : ℝ)⁻¹)
    change AEStronglyMeasurable
      (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) μ at h
    exact h
  exact tendstoInMeasure_of_tendsto_ae hAverage
    (strongLawAverageTendstoAlmostSure hIntegrable hIndependent hIdentDistrib)

end

end FormalSLT.Probability.LawOfLargeNumbers
