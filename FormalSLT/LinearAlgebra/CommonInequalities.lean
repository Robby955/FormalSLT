import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory

namespace FormalSLT.LinearAlgebra.CommonInequalities

noncomputable section

/--
Cauchy-Schwarz inequality for real inner product spaces.

This is the exact claim-facing wrapper for the core inequality on the
`common-inequalities` page. Equality cases, finite-sum forms, and probability
forms are useful corollaries, but they are intentionally not bundled into this
declaration.
Claim-facing wrapper for theorempath.com evidence entry `claim:common-inequalities::cauchy-schwarz-inequality`.
-/
theorem cauchySchwarzRealInner
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := by
  exact abs_real_inner_le_norm u v

/--
Jensen's inequality for averages with respect to a finite nonzero measure.

This is the integral-average version of the convex Jensen claim. The statement
makes the formal side conditions explicit: the convex function is continuous on
a closed convex domain, the random variable lands in that domain almost
everywhere, and both sides are integrable.
Claim-facing wrapper for theorempath.com evidence entry `claim:common-inequalities::jensen-inequality`.
-/
theorem jensenIntegralAverageConvex
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {s : Set E} {f : α → E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s)
    (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  hg.map_average_le hgc hsc hfs hfi hgi

/--
Jensen's inequality for expectations under a probability measure.

This is the probability-expectation statement closest to the textbook display
`g (E[X]) ≤ E[g(X)]`, with mathlib's measurability, domain, continuity, and
integrability side conditions made explicit.
-/
theorem jensenProbabilityIntegralConvex
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Set E} {X : Ω → E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s)
    (hsc : IsClosed s)
    (hXs : ∀ᵐ ω ∂P, X ω ∈ s)
    (hXi : Integrable X P)
    (hgi : Integrable (g ∘ X) P) :
    g (∫ ω, X ω ∂P) ≤ ∫ ω, g (X ω) ∂P :=
  hg.map_integral_le hgc hsc hXs hXi hgi

/--
Jensen's inequality for concave functions under a probability measure.

This records the reversed inequality for the concave variant stated on the
public common-inequalities page.
-/
theorem jensenProbabilityIntegralConcave
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Set E} {X : Ω → E} {g : E → ℝ}
    (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s)
    (hsc : IsClosed s)
    (hXs : ∀ᵐ ω ∂P, X ω ∈ s)
    (hXi : Integrable X P)
    (hgi : Integrable (g ∘ X) P) :
    (∫ ω, g (X ω) ∂P) ≤ g (∫ ω, X ω ∂P) :=
  hg.le_map_integral hgc hsc hXs hXi hgi

/--
Finite weighted Jensen inequality for convex functions.

This is the finite weighted form shown on the public page: nonnegative weights
whose finite sum is one give a convex combination before and after applying
the convex function.
-/
theorem jensenFiniteWeightedConvex
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {g : E → ℝ} {t : Finset ι} {w : ι → ℝ} {x : ι → E}
    (hg : ConvexOn ℝ s g)
    (hwNonneg : ∀ i ∈ t, 0 ≤ w i)
    (hwSum : ∑ i ∈ t, w i = 1)
    (hx : ∀ i ∈ t, x i ∈ s) :
    g (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • g (x i) :=
  hg.map_sum_le hwNonneg hwSum hx

/--
Finite weighted Jensen inequality for concave functions.

This is the finite weighted reversed inequality for concave functions.
-/
theorem jensenFiniteWeightedConcave
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {g : E → ℝ} {t : Finset ι} {w : ι → ℝ} {x : ι → E}
    (hg : ConcaveOn ℝ s g)
    (hwNonneg : ∀ i ∈ t, 0 ≤ w i)
    (hwSum : ∑ i ∈ t, w i = 1)
    (hx : ∀ i ∈ t, x i ∈ s) :
    (∑ i ∈ t, w i • g (x i)) ≤ g (∑ i ∈ t, w i • x i) :=
  hg.le_map_sum hwNonneg hwSum hx

end

end FormalSLT.LinearAlgebra.CommonInequalities
