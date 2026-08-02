import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.MeasureSpace

open Filter MeasureTheory

namespace FormalSLT.Probability.KolmogorovAxioms

/--
Basic identities for probability measures.

This claim-facing wrapper captures the basic reusable consequences on the
`kolmogorov-probability-axioms` page: the empty set has measure zero, the
sample space has total mass one, and probability is monotone under inclusion.
The empty-set and monotonicity facts come from the measure structure; total mass one comes
from `IsProbabilityMeasure`.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-basic-identities`.
-/
theorem probabilityMeasureBasicIdentities
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ ∅ = 0 ∧ μ Set.univ = 1 ∧
      ∀ {A B : Set Ω}, A ⊆ B → μ A ≤ μ B := by
  refine ⟨measure_empty, measure_univ, ?_⟩
  intro A B hAB
  exact measure_mono hAB

/--
Finite additivity for disjoint events in a probability space.

This is the exact existing-measure consequence used on the page. It does not
construct a probability measure from a raw finitely additive set function.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-finite-additivity`.
-/
theorem probabilityMeasureFiniteAdditivity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} (hB : MeasurableSet B) (hdisj : Disjoint A B) :
    μ (A ∪ B) = μ A + μ B :=
  measure_union hdisj hB

/--
Countable additivity for pairwise disjoint measurable events.

This wraps the countable-additivity theorem carried by mathlib's `Measure`
structure. The reverse construction from raw axioms is a separate theorem.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-countable-additivity`.
-/
theorem probabilityMeasureCountableAdditivity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) :=
  μ.m_iUnion hA hdisj

/--
Complement rule for probability measures.

The statement is scoped to measurable events. The finite-measure side
condition required by mathlib is automatic for probability measures.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-complement-rule`.
-/
theorem probabilityMeasureComplementRule
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  simpa [measure_univ] using measure_compl (μ := μ) hA (measure_ne_top μ A)

/--
Finite union bound for probability measures.

This is the finite-family version used in later learning-theory arguments:
the probability of a finite union is at most the sum of the event
probabilities. It does not require disjointness.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-finite-union-bound`.
-/
theorem probabilityMeasureFiniteUnionBound
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ι) (A : ι → Set Ω) :
    μ (⋃ i ∈ I, A i) ≤ ∑ i ∈ I, μ (A i) :=
  measure_biUnion_finset_le I A

/--
Countable union bound for probability measures.

This is the countable subadditivity form used by Borel-Cantelli and
probability tail-event arguments. It does not require the events to be
disjoint.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-countable-union-bound`.
-/
theorem probabilityMeasureCountableUnionBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) :
    μ (⋃ n, A n) ≤ ∑' n, μ (A n) :=
  measure_iUnion_le A

/--
Continuity from below for probability measures.

This claim-facing wrapper captures the exact monotone sequence scope: if
events increase, their probabilities tend to the probability of the countable
union.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-continuity-from-below`.
-/
theorem probabilityMeasureContinuityFromBelow
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : ℕ → Set Ω} (hA : Monotone A) :
    Tendsto (fun n : ℕ => μ (A n)) atTop (nhds (μ (⋃ n, A n))) :=
  tendsto_measure_iUnion_atTop hA

/--
Continuity from above for probability measures.

The measure-theoretic theorem requires the sets to be null-measurable and one
set to have finite measure. Event measurability supplies null measurability;
the probability-measure instance supplies finite measure.
Claim-facing wrapper for theorempath.com evidence entry `claim:kolmogorov-probability-axioms::probability-measure-continuity-from-above`.
-/
theorem probabilityMeasureContinuityFromAbove
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B : ℕ → Set Ω} (hB : Antitone B) (hB_meas : ∀ n, NullMeasurableSet (B n) μ) :
    Tendsto (fun n : ℕ => μ (B n)) atTop (nhds (μ (⋂ n, B n))) :=
  tendsto_measure_iInter_atTop hB_meas hB ⟨0, measure_ne_top μ (B 0)⟩

end FormalSLT.Probability.KolmogorovAxioms
