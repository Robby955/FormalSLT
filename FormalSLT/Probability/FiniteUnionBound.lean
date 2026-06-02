import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic

open scoped BigOperators ENNReal
open MeasureTheory

namespace FormalSLT.Probability.FiniteUnionBound
noncomputable section

/-
Finite union-bound seed.

This file proves the finite cardinality skeleton behind the probabilistic
union bound: the size of a finite union is bounded by the sum of the sizes of
the sets being unioned. It also proves the finite weighted probability
specialization: the mass of a finite union is bounded by the sum of the event
masses. It is intentionally not a countable Borel-Cantelli proof.
-/

/--
Finite cardinality union bound.

Scope note: this proves a finite-set counting inequality. It is a formal
ingredient for later probability-space work, not the full Borel-Cantelli
lemma on the topic page.
-/
def finiteUnionCardBoundStatement : Prop :=
  ∀ {Ω ι : Type*} [DecidableEq Ω] (s : Finset ι) (events : ι → Finset Ω),
    (s.biUnion events).card ≤ ∑ i ∈ s, (events i).card

/-- Canonical Lean declaration for the finite union-bound statement seed. -/
def finiteUnionBound : Prop :=
  finiteUnionCardBoundStatement.{0, 0}

/--
Proof of the finite cardinality union-bound seed.

This proves only the finite-set counting specialization above; it is not the
full measure-theoretic Borel-Cantelli page theorem.
-/
theorem finiteUnionCardBound_proof :
    finiteUnionCardBoundStatement := by
  intro Ω ι _ s events
  exact Finset.card_biUnion_le

def finiteEventMass {Ω : Type*} [DecidableEq Ω] (support : Finset Ω) (w : Ω → ℝ)
    (event : Finset Ω) : ℝ :=
  ∑ ω ∈ support, if ω ∈ event then w ω else 0

def finiteUnionEventMass {Ω ι : Type*} [DecidableEq Ω] (support : Finset Ω)
    (w : Ω → ℝ) (events : ι → Finset Ω) (s : Finset ι) : ℝ :=
  finiteEventMass support w (s.biUnion events)

def finiteEventMassSum {Ω ι : Type*} [DecidableEq Ω] (support : Finset Ω)
    (w : Ω → ℝ) (events : ι → Finset Ω) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, finiteEventMass support w (events i)

/--
Finite weighted probability union bound.

Scope note: this proves a finite-support event-mass inequality under
nonnegative weights. It is closer to a probability union bound than the
cardinality skeleton, but it is still not a countable probability-space
Borel-Cantelli theorem.
-/
def finiteProbabilityUnionBoundStatement : Prop :=
  ∀ {Ω ι : Type*} [DecidableEq Ω] (support : Finset Ω) (w : Ω → ℝ)
      (events : ι → Finset Ω) (s : Finset ι),
    (∀ ω, 0 ≤ w ω) →
    finiteUnionEventMass support w events s ≤ finiteEventMassSum support w events s

/-- Canonical Lean declaration for the finite weighted union-bound seed. -/
def finiteProbabilityUnionBound : Prop :=
  finiteProbabilityUnionBoundStatement.{0, 0}

/--
Proof of the finite weighted probability union-bound seed.

The proof is pointwise: every outcome's union indicator is bounded by the sum
of its finite event indicators, then summed against nonnegative weights.
-/
theorem finiteProbabilityUnionBound_proof :
    finiteProbabilityUnionBoundStatement := by
  intro Ω ι _ support w events s hw
  unfold finiteUnionEventMass finiteEventMassSum finiteEventMass
  calc
    (∑ ω ∈ support, if ω ∈ s.biUnion events then w ω else 0)
        ≤ ∑ ω ∈ support, ∑ i ∈ s, if ω ∈ events i then w ω else 0 := by
          apply Finset.sum_le_sum
          intro ω _hω
          by_cases hUnion : ω ∈ s.biUnion events
          · have hExists : ∃ i ∈ s, ω ∈ events i := by
              simpa [Finset.mem_biUnion] using hUnion
            rcases hExists with ⟨i, hi, hEvent⟩
            have hNonneg :
                ∀ j ∈ s, 0 ≤ (if ω ∈ events j then w ω else 0) := by
              intro j _hj
              by_cases hjEvent : ω ∈ events j
              · simp [hjEvent, hw ω]
              · simp [hjEvent]
            have hSingle :
                (if ω ∈ events i then w ω else 0)
                  ≤ ∑ j ∈ s, if ω ∈ events j then w ω else 0 :=
              Finset.single_le_sum hNonneg hi
            calc
              (if ω ∈ s.biUnion events then w ω else 0) = w ω := by
                simp [hUnion]
              _ ≤ ∑ j ∈ s, if ω ∈ events j then w ω else 0 := by
                simpa [hEvent] using hSingle
          · have hNonneg :
                0 ≤ ∑ i ∈ s, if ω ∈ events i then w ω else 0 := by
              apply Finset.sum_nonneg
              intro i _hi
              by_cases hEvent : ω ∈ events i
              · simp [hEvent, hw ω]
              · simp [hEvent]
            simpa [hUnion] using hNonneg
    _ = ∑ i ∈ s, ∑ ω ∈ support, if ω ∈ events i then w ω else 0 := by
      rw [Finset.sum_comm]

/--
Finite measure-theoretic union bound.

This is a thin wrapper around mathlib's finite-index subadditivity theorem.
-/
theorem finiteMeasureUnionBound
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    (events : ι → Set Ω) :
    μ (⋃ i, events i) ≤ ∑ i, μ (events i) :=
  MeasureTheory.measure_iUnion_fintype_le μ events

/--
Finite measure union bound with a supplied per-event budget sequence.

This is the finite budget-allocation form: if event `i` has mass at most
`budget i`, and the finite budget sum is bounded by `α`, then the union has
mass at most `α`.
-/
theorem finiteMeasureUnionBound_budget
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    (events : ι → Set Ω) (budget : ι → ℝ≥0∞) {α : ℝ≥0∞}
    (hbudget : ∀ i, μ (events i) ≤ budget i)
    (hsum : ∑ i, budget i ≤ α) :
    μ (⋃ i, events i) ≤ α := by
  calc
    μ (⋃ i, events i) ≤ ∑ i, μ (events i) :=
      finiteMeasureUnionBound events
    _ ≤ ∑ i, budget i := by
      exact Finset.sum_le_sum (by intro i _hi; exact hbudget i)
    _ ≤ α := hsum

/--
Finite measure union bound with a common per-event budget.

This is the finite-class skeleton used by anytime-valid arguments: if every
event in a finite family has measure at most `β`, then the union has measure at
most the number of events times `β`.
-/
theorem finiteMeasureUnionBound_const
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    (events : ι → Set Ω) {β : ℝ≥0∞}
    (hβ : ∀ i, μ (events i) ≤ β) :
    μ (⋃ i, events i) ≤ (Fintype.card ι : ℝ≥0∞) * β := by
  calc
    μ (⋃ i, events i) ≤ ∑ i, μ (events i) :=
      finiteMeasureUnionBound events
    _ ≤ ∑ _i : ι, β := by
      exact Finset.sum_le_sum (by intro i _hi; exact hβ i)
    _ = (Fintype.card ι : ℝ≥0∞) * β := by
      simp

/--
Finite measure union bound with an equal split of a total budget.

The hypotheses keep the arithmetic explicit: `inv_card` is a chosen reciprocal
for the finite index count and `hbudget` records that the count times the
per-event budget is bounded by the desired total budget.
-/
theorem finiteMeasureUnionBound_equalBudget
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    (events : ι → Set Ω) {α inv_card : ℝ≥0∞}
    (hbudget : (Fintype.card ι : ℝ≥0∞) * inv_card ≤ α)
    (hα : ∀ i, μ (events i) ≤ inv_card) :
    μ (⋃ i, events i) ≤ α := by
  calc
    μ (⋃ i, events i) ≤ (Fintype.card ι : ℝ≥0∞) * inv_card :=
      finiteMeasureUnionBound_const events hα
    _ ≤ α := hbudget

/--
Finite measure union bound with the total budget split equally across a
nonempty finite index type.
-/
theorem finiteMeasureUnionBound_cardInv
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι] [Nonempty ι]
    (events : ι → Set Ω) {α : ℝ≥0∞}
    (hα : ∀ i, μ (events i) ≤ α * (Fintype.card ι : ℝ≥0∞)⁻¹) :
    μ (⋃ i, events i) ≤ α := by
  have hcard_ne_zero : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hcard_ne_top : (Fintype.card ι : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  calc
    μ (⋃ i, events i)
        ≤ (Fintype.card ι : ℝ≥0∞) * (α * (Fintype.card ι : ℝ≥0∞)⁻¹) :=
      finiteMeasureUnionBound_const events hα
    _ = α := by
      rw [mul_comm (Fintype.card ι : ℝ≥0∞) (α * (Fintype.card ι : ℝ≥0∞)⁻¹),
        ENNReal.inv_mul_cancel_right hcard_ne_zero hcard_ne_top]

/--
Countable measure-theoretic union bound.

This is a thin wrapper around mathlib's countable subadditivity theorem.
-/
theorem countableMeasureUnionBound
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Countable ι]
    (events : ι → Set Ω) :
    μ (⋃ i, events i) ≤ ∑' i, μ (events i) :=
  MeasureTheory.measure_iUnion_le events

end

end FormalSLT.Probability.FiniteUnionBound
