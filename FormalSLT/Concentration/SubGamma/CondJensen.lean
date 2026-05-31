/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional Jensen inequality (specialization to ℝ-valued bounded RVs)

**Mathlib status:** the general conditional Jensen for convex
lower-semicontinuous functions on a Banach space already lives in
`Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen` as
`ConvexOn.map_condExp_le_univ` (Yongxi Lin, Thomas Zhu 2026).

We do **not** reprove it. This module pins down the exact ℝ-valued
specialization the extractor needs (`φ ∘ X` integrable when `|X| ≤ b`
and `φ` is continuous on `[-b, b]`), so the downstream proof has a
single named lemma to invoke rather than threading the universal form.

If the specialization turns out to be a one-line corollary, this module
should be inlined into `Extractor.lean` rather than kept as a separate
file.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Conditional Jensen for an ℝ-valued, bounded random variable and a
convex `φ` continuous on the image.**

The convex function `φ` need only be `ConvexOn ℝ Set.univ φ` and
lower-semicontinuous for the mathlib lemma; we state the specialization
the extractor needs (one-dimensional case, real values).
-/
theorem condJensen_real
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    {X : Ω → ℝ} {φ : ℝ → ℝ}
    (hφ_cvx : ConvexOn ℝ Set.univ φ)
    (hφ_lsc : LowerSemicontinuous φ)
    (hX_int : Integrable X μ)
    (hφX_int : Integrable (fun ω => φ (X ω)) μ) :
    (fun ω => φ (μ[X | m] ω)) ≤ᵐ[μ] μ[fun ω => φ (X ω) | m] := by
  -- Direct corollary of mathlib's `ConvexOn.map_condExp_le_univ` specialised
  -- to `E = ℝ`. The two sides are definitionally `φ ∘ μ[X | m]` and
  -- `μ[φ ∘ X | m]`, so the universal form applies verbatim.
  exact hφ_cvx.map_condExp_le_univ hm hφ_lsc hX_int hφX_int

end FormalSLT.Concentration.SubGamma
