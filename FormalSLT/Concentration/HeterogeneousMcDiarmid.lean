/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Concentration.SharpMcDiarmid

/-!
# Sharp McDiarmid over heterogeneous product laws

This module exposes the public bounded-differences API for independent,
non-identically-distributed coordinates. The law family is
`μ : Fin n → Measure Z`, so the ambient product is `Measure.pi μ`.

The exponent is unchanged from the homogeneous statement:

`exp (-2 * ε^2 / ∑ k, (c k)^2)`.

The coordinate widths `c k` come from `HasBoundedDifferences f c`, a
measure-free predicate on `f`, so changing the coordinate laws changes
the product measure but not the bounded-differences geometry.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.Concentration

noncomputable section

/-- Sharp McDiarmid bounded-differences inequality over a heterogeneous
independent product `Measure.pi μ`.

Each coordinate has its own probability law `μ k`. The coordinates remain
independent through the product measure, but they need not be identically
distributed. -/
theorem mcdiarmid_of_hasBoundedDifferences_sharp_hetero
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Fin n → Measure Z} [∀ k, IsProbabilityMeasure (μ k)]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi μ))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
        {S | ∫ s, f s ∂(Measure.pi μ) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) :=
  FormalSLT.Azuma.ExposureMartingale.hasBoundedDifferences_tail_sharp
    (μ := μ) hbdd hf hfi hc hε

/-- Lower-tail form of heterogeneous sharp McDiarmid. -/
theorem mcdiarmid_of_hasBoundedDifferences_sharp_hetero_lower
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Fin n → Measure Z} [∀ k, IsProbabilityMeasure (μ k)]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi μ))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
        {S | f S + ε ≤ ∫ s, f s ∂(Measure.pi μ)}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
  set μn : Measure (Fin n → Z) := Measure.pi μ with hμn
  have hupper := mcdiarmid_of_hasBoundedDifferences_sharp_hetero
    (μ := μ) (f := fun S : Fin n → Z => -f S) (c := c)
    hbdd.neg hf.neg hfi.neg hc hε
  change μn.real {S | ∫ s, -f s ∂μn + ε ≤ -f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) at hupper
  have hset :
      {S : Fin n → Z | ∫ s, -f s ∂μn + ε ≤ -f S}
        = {S | f S + ε ≤ ∫ s, f s ∂μn} := by
    ext S
    simp only [Set.mem_setOf_eq, integral_neg]
    constructor <;> intro h <;> linarith
  rw [hset] at hupper
  exact hupper

/-- Two-sided heterogeneous sharp McDiarmid bound. -/
theorem mcdiarmid_twoSided_of_hasBoundedDifferences_sharp_hetero
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Fin n → Measure Z} [∀ k, IsProbabilityMeasure (μ k)]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi μ))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
        {S | ε ≤ |f S - ∫ s, f s ∂(Measure.pi μ)|}
      ≤ 2 * Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
  set μn : Measure (Fin n → Z) := Measure.pi μ with hμn
  set I : ℝ := ∫ s, f s ∂μn with hI
  set upper : Set (Fin n → Z) := {S | I + ε ≤ f S} with hupper_set
  set lower : Set (Fin n → Z) := {S | f S + ε ≤ I} with hlower_set
  set target : Set (Fin n → Z) := {S | ε ≤ |f S - I|} with htarget_set
  have hupper_tail : μn.real upper
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
    have h := mcdiarmid_of_hasBoundedDifferences_sharp_hetero
      (μ := μ) (f := f) (c := c) hbdd hf hfi hc hε
    change μn.real upper ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2)
    change μn.real {S | I + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) at h
    simpa [upper] using h
  have hlower_tail : μn.real lower
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
    have h := mcdiarmid_of_hasBoundedDifferences_sharp_hetero_lower
      (μ := μ) (f := f) (c := c) hbdd hf hfi hc hε
    change μn.real lower ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2)
    change μn.real {S | f S + ε ≤ I}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) at h
    simpa [lower] using h
  have hsubset : target ⊆ upper ∪ lower := by
    intro S hS
    simp only [target, upper, lower, Set.mem_setOf_eq, Set.mem_union] at hS ⊢
    by_cases hnonneg : 0 ≤ f S - I
    · have habs : |f S - I| = f S - I := abs_of_nonneg hnonneg
      rw [habs] at hS
      left
      linarith
    · have hnonpos : f S - I ≤ 0 := le_of_not_ge hnonneg
      have habs : |f S - I| = -(f S - I) := abs_of_nonpos hnonpos
      rw [habs] at hS
      right
      linarith
  have htarget_le_union : μn.real target ≤ μn.real (upper ∪ lower) :=
    measureReal_mono hsubset
  have hunion_le : μn.real (upper ∪ lower) ≤ μn.real upper + μn.real lower :=
    measureReal_union_le upper lower
  calc
    μn.real target ≤ μn.real (upper ∪ lower) := htarget_le_union
    _ ≤ μn.real upper + μn.real lower := hunion_le
    _ ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2)
          + Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) :=
        add_le_add hupper_tail hlower_tail
    _ = 2 * Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
        ring

/-- Homogeneous recovery: the old sharp McDiarmid upper-tail statement follows
from the heterogeneous product theorem by taking `μ := fun _ => ν`. -/
theorem mcdiarmid_of_hasBoundedDifferences_sharp_of_hetero
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {ν : Measure Z} [IsProbabilityMeasure ν]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => ν)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => ν)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => ν)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) :=
  mcdiarmid_of_hasBoundedDifferences_sharp_hetero
    (μ := fun _ : Fin n => ν) hbdd hf hfi hc hε

end

end FormalSLT.Concentration
