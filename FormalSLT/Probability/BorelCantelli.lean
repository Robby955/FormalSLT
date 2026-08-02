import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.BorelCantelli

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace FormalSLT.Probability.BorelCantelli

/--
Borel-Cantelli lemma, limsup-measure-zero form.

This is a claim-facing thin wrapper around mathlib's
`MeasureTheory.measure_limsup_atTop_eq_zero`. The statement matches the
TheoremPath claim's "$A_n$ infinitely often has probability zero" formulation
by representing "infinitely often" as `Filter.limsup A Filter.atTop`.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::borel-cantelli-first`.
-/
theorem borelCantelliFirstLimsupMeasureZero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Set Ω}
    (hSummable : (∑' n, μ (A n)) ≠ ∞) :
    μ (Filter.limsup A Filter.atTop) = 0 :=
  MeasureTheory.measure_limsup_atTop_eq_zero hSummable

/--
Borel-Cantelli lemma, eventually-not-in form.

This companion wrapper captures the prose consequence: almost every outcome
belongs to finitely many of the events.
-/
theorem borelCantelliFirstEventuallyNotMem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Set Ω}
    (hSummable : (∑' n, μ (A n)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ A n :=
  MeasureTheory.ae_eventually_notMem hSummable

/--
Second Borel-Cantelli lemma, independent-events limsup-measure-one form.

Scope note: mathlib states this wrapper with `iIndepSet`, which is stronger
than the governed claim's pairwise-independence wording. The manifest marks
this as scoped support until the pairwise version is formalized.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::borel-cantelli-second`.
-/
theorem borelCantelliSecondIndependentLimsupMeasureOne
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℕ → Set Ω}
    (hMeasurable : ∀ n, MeasurableSet (A n))
    (hIndependent : iIndepSet A μ)
    (hDivergent : (∑' n, μ (A n)) = ∞) :
    μ (Filter.limsup A Filter.atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one hMeasurable hIndependent hDivergent

end FormalSLT.Probability.BorelCantelli
