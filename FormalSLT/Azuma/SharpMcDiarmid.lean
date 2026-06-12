/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.ExposureIncrementCondMGF
import FormalSLT.Azuma.GenGapTail
import FormalSLT.Concentration.SharpMcDiarmid
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Sharp McDiarmid route through the exposure martingale

This module exposes the q049 surface API for the sharp McDiarmid constant.
The load-bearing proof already lives in the exposure-martingale development:

* `condExpKernel_product_decomposition` is the public kernel-support form of
  the finite-product decomposition. It says that, for the product measure
  `mu^{⊗n}`, a sample drawn from the `condExpKernel` of the prefix
  σ-algebra keeps the conditioned prefix coordinates almost surely.
* `sharp_mcdiarmid_increment_subGaussian_mgf` packages the kth increment as a
  conditional sub-Gaussian random variable with proxy `(c_k / 2)^2`.
* `sharp_mcdiarmid_inequality_iid_const_width` lifts the sharp increment
  through the existing FormalSLT exposure martingale and mathlib's
  conditional Azuma-Hoeffding engine.

Sources cited for this lane: McDiarmid 1989,
Boucheron-Lugosi-Massart 2013 §6, Bousquet-Elisseeff 2002.

## Candidate mathlib4 PR statement

The natural reusable mathlib theorem is stronger than the support statement
formalized below. A candidate PR would state, for finite `n`, standard Borel
coordinate space `Z`, product probability measure `mu^{⊗n}`, and the prefix
projection

```
prefix k : (Fin n -> Z) -> ({i : Fin n // (i : Nat) < k} -> Z),
```

that the disintegration kernel of

```
(Measure.pi (fun _ : Fin n => mu)).map (fun s => (prefix k s, s))
```

is almost everywhere equal, with respect to the first marginal, to the kernel
that samples a point by taking a Dirac mass on the observed prefix and an
independent product measure on the tail, then recombines the two parts through
`MeasurableEquiv.piEquivPiSubtypeProd`. In words:

```
Measure.condKernel (map (fun s => (prefix k s, s)) mu^n)
  =ᵐ[map prefix mu^n]
  delta_observed_prefix ⊗ mu^tail
```

The current mathlib API supplies `Measure.condKernel`,
`Measure.condKernel_compProd`, and the uniqueness theorem
`Measure.eq_condKernel_of_measure_eq_compProd`, but it does not expose a
ready-to-use finite-product prefix/tail conditional-kernel lemma. FormalSLT
therefore works around that missing lemma with
`compProd_trim_condExpKernel`: the proof identifies the joint law of a prefix
state and a draw from its conditional kernel with the diagonal joint law, then
deduces the a.e. prefix-agreement support property used by the sharp
McDiarmid increment.

Step-by-step proof outline for the theorem below:

1. Put `mu^n := Measure.pi (fun _ : Fin n => mu)` and
   `m := coordinateSubAlgebra n Z k`.
2. Prove that coordinate evaluation is measurable from the prefix
   σ-algebra whenever the coordinate lies in the prefix.
3. Use those coordinate measurability facts to show that the set of pairs
   `(S, T)` agreeing on all prefix coordinates is measurable in
   `m.prod MeasurableSpace.pi`.
4. The diagonal map `S |-> (S, S)` lands in that agreement set everywhere.
5. Rewrite the joint law
   `(mu^n.trim (coordinateSubAlgebra_le_pi k)) ⊗ₘ condExpKernel mu^n m`
   using `compProd_trim_condExpKernel`.
6. Apply `Measure.ae_ae_of_ae_compProd` to turn the joint a.e. statement into
   the fiberwise `condExpKernel` statement.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory Filter ProbabilityTheory Real
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)

noncomputable section

namespace FormalSLT.Azuma.ExposureMartingale

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

private lemma q049_measurable_eval_coordinateSubAlgebra
    (k : Fin (n + 1)) (i : Fin n) (hi : (i : ℕ) < (k : ℕ)) :
    @Measurable (Fin n → Z) Z (coordinateSubAlgebra n Z k) _ (fun S => S i) := by
  rw [measurable_iff_comap_le]
  unfold coordinateSubAlgebra
  exact le_iSup₂ (f := fun (j : Fin n) (_ : (j : ℕ) < (k : ℕ)) =>
    (inferInstance : MeasurableSpace Z).comap
      (fun s : Fin n → Z => s j)) i hi

private lemma q049_measurableSet_pair_agree_prefix
    [MeasurableEq Z] (k : Fin (n + 1)) :
    @MeasurableSet ((Fin n → Z) × (Fin n → Z))
      ((coordinateSubAlgebra n Z k).prod MeasurableSpace.pi)
      {p | ∀ i : Fin n, (i : ℕ) < (k : ℕ) → p.2 i = p.1 i} := by
  rw [Set.setOf_forall]
  refine MeasurableSet.iInter (fun i : Fin n => ?_)
  by_cases hi : (i : ℕ) < (k : ℕ)
  · have hfst : @Measurable ((Fin n → Z) × (Fin n → Z)) Z
        ((coordinateSubAlgebra n Z k).prod MeasurableSpace.pi) _
        (fun p => p.1 i) :=
      (q049_measurable_eval_coordinateSubAlgebra k i hi).comp measurable_fst
    have hsnd : @Measurable ((Fin n → Z) × (Fin n → Z)) Z
        ((coordinateSubAlgebra n Z k).prod MeasurableSpace.pi) _
        (fun p => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    simpa [hi] using hsnd.eq hfst
  · simp [hi]

/-- Conditional product-measure kernel decomposition, in the support form used
by the sharp McDiarmid proof.

For the homogeneous finite product measure `mu^{⊗n}` and the prefix
σ-algebra `coordinateSubAlgebra n Z k`, the conditional-expectation kernel
keeps the revealed prefix fixed: for almost every conditioning state `S`, a
draw `T` from

```
condExpKernel (Measure.pi (fun _ : Fin n => mu))
  (coordinateSubAlgebra n Z k) S
```

agrees with `S` on every coordinate `i < k`.

This is the formally checked piece of the decomposition
`delta_{S_<k} ⊗ mu^{⊗tail}` needed by the sharp McDiarmid increment. The
module docstring records the stronger `Measure.condKernel` equality that would
be the clean mathlib4 PR. -/
theorem condExpKernel_product_decomposition
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ] (k : Fin (n + 1)) :
    ∀ᵐ S ∂((Measure.pi (fun _ : Fin n => μ)).trim (coordinateSubAlgebra_le_pi k)),
      ∀ᵐ T ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
          (coordinateSubAlgebra n Z k) S),
        ∀ i : Fin n, (i : ℕ) < (k : ℕ) → T i = S i := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  have hm : coordinateSubAlgebra n Z k ≤ MeasurableSpace.pi :=
    coordinateSubAlgebra_le_pi k
  letI : MeasurableSpace ((Fin n → Z) × (Fin n → Z)) :=
    (coordinateSubAlgebra n Z k).prod MeasurableSpace.pi
  have hmeas : MeasurableSet
      {p : (Fin n → Z) × (Fin n → Z) |
        ∀ i : Fin n, (i : ℕ) < (k : ℕ) → p.2 i = p.1 i} := by
    exact q049_measurableSet_pair_agree_prefix k
  have hdiag : ∀ᵐ p ∂Measure.map (fun S : Fin n → Z => (S, S)) μn,
      ∀ i : Fin n, (i : ℕ) < (k : ℕ) → p.2 i = p.1 i := by
    have hmap : Measurable (fun S : Fin n → Z => (S, S)) :=
      Measurable.prodMk (measurable_id'' hm) measurable_id
    rw [ae_map_iff hmap.aemeasurable hmeas]
    exact Filter.Eventually.of_forall (fun S i _ => rfl)
  have hjoint : ∀ᵐ p ∂((μn.trim hm) ⊗ₘ condExpKernel μn (coordinateSubAlgebra n Z k)),
      ∀ i : Fin n, (i : ℕ) < (k : ℕ) → p.2 i = p.1 i := by
    rw [compProd_trim_condExpKernel hm]
    exact hdiag
  simpa [μn] using Measure.ae_ae_of_ae_compProd hjoint

/-- Sharp conditional sub-Gaussian MGF for the kth exposure-martingale
increment.

This is the q049 per-increment McDiarmid step. The sharp proxy is
`(‖c k‖₊ / 2)^2`, corresponding to a conditional range of width `c k` on the
prefix fiber, instead of the Azuma proxy `‖c k‖₊^2` obtained from the symmetric
bound `|Delta_k| <= c k`. The proof route is the one described by
Boucheron-Lugosi-Massart 2013 §6. -/
theorem sharp_mcdiarmid_increment_subGaussian_mgf
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (k : Fin n) (hck : 0 ≤ c k) :
    HasCondSubgaussianMGF
      (m := coordinateSubAlgebra n Z k.castSucc)
      (coordinateSubAlgebra_le_pi k.castSucc)
      (exposureIncrement μ f k) ((‖c k‖₊ / 2 : ℝ≥0) ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have _hkernel :=
    condExpKernel_product_decomposition (μ := μ) (k := k.castSucc)
  exact exposureIncrement_hasCondSubgaussianMGF_sharp
    (μ := μ) hbdd hf hfi k hck

/-- Constant-width sharp McDiarmid inequality over a homogeneous iid product
measure.

If `f : (Fin n -> Z) -> R` has bounded differences with constant coordinate
width `c`, then

```
mu^n {S | E[f] + ε <= f S}
  <= exp (-2 * ε^2 / (n * c^2)).
```

This is the constant-width specialization of
`hasBoundedDifferences_tail_sharp`, assembled from the sharp conditional MGF
above through the existing FormalSLT exposure-martingale machinery. With
coordinate width `c / n`, the exponent rewrites to the usual sample-mean form
`-2 * ε^2 * n / c^2`. -/
theorem sharp_mcdiarmid_inequality_iid_const_width
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbdd : HasBoundedDifferences f (fun _ : Fin n => c))
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) := by
  have hSharp := hasBoundedDifferences_tail_sharp
    (μ := μ) hbdd hf hfi (fun _ => hc) hε
  have h_sum_real :
      (∑ _k : Fin n, c ^ 2) = (n : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp_eq :
      -2 * ε ^ 2 / (∑ _k : Fin n, c ^ 2)
        = -2 * ε ^ 2 / ((n : ℝ) * c ^ 2) := by
    rw [h_sum_real]
  rw [hexp_eq] at hSharp
  exact hSharp

end FormalSLT.Azuma.ExposureMartingale

