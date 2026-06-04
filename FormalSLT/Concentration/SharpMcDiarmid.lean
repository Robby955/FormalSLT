/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Moments.SubGaussian
import FormalSLT.Azuma.GenGapTail

/-!
# Sharp bounded-differences (McDiarmid) inequality

The *sharp* McDiarmid bound carries the constant `2` in the exponent,
`exp (-2 t^2 / ∑ c_i^2)`, four times tighter than the Azuma constant
`exp (-t^2 / (2 ∑ c_i^2))`. The factor of `4` comes from the per-increment
sub-Gaussian variance proxy: the sharp proxy is `(c_i / 2)^2` (range `c_i`),
whereas the Azuma proxy is `c_i^2` (a symmetric bound `|Δ_i| ≤ c_i`, range
`2 c_i`).

Relationship to the existing development. `FormalSLT/Azuma/` proves both the
Azuma-constant bounded-differences inequality
(`FormalSLT.Azuma.ExposureMartingale.hasBoundedDifferences_tail_azuma`) and the
sharp McDiarmid-constant version
(`FormalSLT.Azuma.ExposureMartingale.hasBoundedDifferences_tail_sharp`). The
sharp route feeds the exposure-martingale increments into mathlib's conditional
Azuma-Hoeffding engine
`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` with the
per-increment proxy `(‖c_k‖₊ / 2)^2`, obtained from the conditional range-width
kernel theorem in `FormalSLT.Azuma.ExposureMartingale`.

What this file adds:

* `mcdiarmid_additive_independent` - the sharp constant `2` for the *additive,
  independent* case. For a sum of independent variables each supported in
  `[a_i, b_i]`, the per-coordinate range is directly `b_i - a_i` (no conditioning
  is needed), so the sharp proxy `((b_i - a_i)/2)^2` is available from mathlib's
  `hasSubgaussianMGF_of_mem_Icc`, and the bound is sharp. The general
  exposure-martingale theorem above does *not* give this constant.
* `mcdiarmid_of_hasBoundedDifferences_sharp` - the general product-measure
  bounded-differences theorem with the sharp McDiarmid constant.
* `mcdiarmid_of_hasBoundedDifferences_sharp_lower` - the matching lower-tail
  theorem, obtained by applying the upper-tail theorem to `-f`.
* `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` - the two-sided textbook
  bounded-differences theorem for `|f - E[f]|` over an iid product measure.
* `sharp_mcdiarmid_of_doob_increments` - an abstract reduction recording that
  *given* Doob increments that are conditionally sub-Gaussian with the sharp
  proxy `(c_i / 2)^2`, the sharp tail bound follows from the same engine. It
  pinpoints the exact hypothesis a sharpened general theorem must supply.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace FormalSLT.Concentration

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sharp McDiarmid, abstract reduction form.**

Let `g` be a centered statistic that decomposes as the sum of a Doob martingale
difference sequence `Y` adapted to a filtration `ℱ`, where each increment is
conditionally sub-Gaussian with the *sharp* variance proxy `(c i / 2) ^ 2`
(the proxy of an increment of conditional range `c i`). Then `g` satisfies the
sharp upper-tail bound

  `μ {ω | t ≤ g ω} ≤ exp (-2 t^2 / ∑ c_i^2)`.

The sharp constant `2` is produced by mathlib's conditional Azuma-Hoeffding
engine when fed the proxies `(c_i / 2) ^ 2`; this lemma performs that reduction
and the exponent bookkeeping. It records exactly the hypothesis a sharpened
general theorem must establish: the existing
`FormalSLT.Azuma.ExposureMartingale.exposureIncrement_hasCondSubgaussianMGF`
supplies its increments with the Azuma proxy `‖c_k‖₊^2`, not `(c_k / 2)^2`, which
is why the assembled `hasBoundedDifferences_tail_azuma` lands at the Azuma
constant. See `docs/SharpMcDiarmid.md`. -/
theorem sharp_mcdiarmid_of_doob_increments
    [StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} (n : ℕ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) ((c 0 / 2) ^ 2) μ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) ((c (i + 1) / 2) ^ 2) μ)
    {g : Ω → ℝ} (hg : ∀ ω, g ω = ∑ i ∈ Finset.range n, Y i ω)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ g ω}
      ≤ Real.exp (-2 * t ^ 2 / ∑ i ∈ Finset.range n, ((c i : ℝ)) ^ 2) := by
  have hengine := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (μ := μ) (ℱ := ℱ) (Y := Y) (cY := fun i => (c i / 2) ^ 2)
    h_adapted h0 n h_subG ht
  have hset : {ω | t ≤ g ω} = {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} := by
    ext ω; simp only [Set.mem_setOf_eq, hg ω]
  rw [hset]
  refine hengine.trans (le_of_eq ?_)
  congr 1
  have hsum : ((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0) : ℝ)
      = (∑ i ∈ Finset.range n, ((c i : ℝ)) ^ 2) / 4 := by
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

/-- **Sharp McDiarmid bounded-differences inequality over a product measure.**

If `f : (Fin n → Z) → ℝ` changes by at most `c k` when coordinate `k` is
altered, with nonnegative widths `c k`, then its upper tail under the iid product
measure satisfies the sharp McDiarmid bound

  `μⁿ {S | E[f] + ε ≤ f S} ≤ exp (-2 * ε^2 / ∑ k, c k ^ 2)`.

The proof is routed through the exposure martingale and the checked conditional
range-width theorem for its increments. -/
theorem mcdiarmid_of_hasBoundedDifferences_sharp
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) :=
  FormalSLT.Azuma.ExposureMartingale.hasBoundedDifferences_tail_sharp
    hbdd hf hfi hc hε

/-- Lower-tail form of the sharp product-measure bounded-differences theorem.

This is the upper-tail theorem applied to `-f`; the bounded-differences widths
are unchanged by negation. -/
theorem mcdiarmid_of_hasBoundedDifferences_sharp_lower
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | f S + ε ≤ ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ))}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  have hupper := mcdiarmid_of_hasBoundedDifferences_sharp
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

/-- Two-sided sharp McDiarmid bounded-differences inequality.

For an arbitrary function on an iid product space whose coordinate sensitivity
is bounded by `c k`, the centered absolute deviation has the textbook
Boucheron-Lugosi-Massart/McDiarmid tail

`P(|f(S) - E[f]| >= ε) <= 2 * exp(-2 * ε^2 / sum_k c_k^2)`.

The proof combines the sharp upper-tail wrapper with the lower-tail wrapper
above and applies the finite union bound for the two events. -/
theorem mcdiarmid_twoSided_of_hasBoundedDifferences_sharp
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ε ≤ |f S - ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ))|}
      ≤ 2 * Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  set I : ℝ := ∫ s, f s ∂μn with hI
  set upper : Set (Fin n → Z) := {S | I + ε ≤ f S} with hupper_set
  set lower : Set (Fin n → Z) := {S | f S + ε ≤ I} with hlower_set
  set target : Set (Fin n → Z) := {S | ε ≤ |f S - I|} with htarget_set
  have hupper_tail : μn.real upper
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
    have h := mcdiarmid_of_hasBoundedDifferences_sharp
      (μ := μ) (f := f) (c := c) hbdd hf hfi hc hε
    change μn.real upper ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2)
    change μn.real {S | I + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) at h
    simpa [upper] using h
  have hlower_tail : μn.real lower
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
    have h := mcdiarmid_of_hasBoundedDifferences_sharp_lower
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

/-- **McDiarmid bounded-differences inequality, additive independent case.**

For an *additive* statistic `∑ i ∈ s, X i` of independent random variables with
each `X i` supported almost surely in `[a i, b i]`, McDiarmid's bounded-
differences inequality coincides with Hoeffding's inequality for sums of
independent sub-Gaussian variables: the bounded difference in coordinate `i` is
exactly `b i - a i`, and the centered statistic obeys the sharp tail bound
`exp (-2 t^2 / ∑ (b_i - a_i)^2)`.

This is the special case exercised by the standard test instances (`c_i = 1`,
`c_i = 1/n`). The genuinely non-additive bounded-differences case (arbitrary `f`
over a product measure) is proved by
`mcdiarmid_of_hasBoundedDifferences_sharp`, using the exposure-martingale
kernel route. -/
theorem mcdiarmid_additive_independent
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ} {a b : ι → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hab : ∀ i, a i ≤ b i)
    (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {s : Finset ι} {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)}
      ≤ Real.exp (-2 * t ^ 2 / ∑ i ∈ s, (b i - a i) ^ 2) := by
  set c : ι → ℝ≥0 := fun i => (‖b i - a i‖₊ / 2) ^ 2 with hc
  have hZsub : ∀ i ∈ s, HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (c i) μ := by
    intro i _
    simpa using hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable (hX i)
  have hZindep : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ := by
    have h := hindep.comp (fun i => fun x : ℝ => x - ∫ x, X i x ∂μ)
      (fun i => measurable_id.sub_const _)
    simpa [Function.comp] using h
  have hengine := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hZindep (c := c) (s := s) hZsub ht
  refine hengine.trans (le_of_eq ?_)
  congr 1
  have hcoe : ∀ i, ((‖b i - a i‖₊ : ℝ)) = b i - a i := fun i => by
    simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hab i))]
  have hsum : ((∑ i ∈ s, c i : ℝ≥0) : ℝ) = (∑ i ∈ s, (b i - a i) ^ 2) / 4 := by
    rw [hc]
    push_cast [hcoe]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

end

end FormalSLT.Concentration
