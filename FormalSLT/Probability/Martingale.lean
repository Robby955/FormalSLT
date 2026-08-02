import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace FormalSLT.Probability.Martingale

noncomputable section

/--
Doob's weak maximal inequality for nonnegative submartingales.

This wraps mathlib's `MeasureTheory.maximal_ineq`. The governed page claim
also states the Lp maximal inequality, so this declaration is a scoped proof
artifact rather than an exact verification of the whole Doob maximal claim.
Claim-facing wrapper for theorempath.com evidence entry `claim:martingale-theory::doob-weak-maximal-inequality`.
-/
theorem doobWeakMaximalInequality
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hsub : MeasureTheory.Submartingale X 𝒢 μ)
    (hnonneg : 0 ≤ X) {ε : ℝ≥0} (n : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => X k ω} ≤
      ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => X k ω},
          X n ω ∂μ) :=
  MeasureTheory.maximal_ineq hsub hnonneg n

end

end FormalSLT.Probability.Martingale
