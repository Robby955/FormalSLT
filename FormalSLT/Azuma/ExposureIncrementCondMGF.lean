/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.ExposureIncrementHoeffding
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional sub-Gaussian MGF for the exposure-martingale increments

Stage B2c-3 part 3 of `docs/plans/mcdiarmid-rademacher-plan.md`.

Combines the conditional mean-zero property and a.e. range bound from
B2c-3 part 2 (`exposureIncrement_condExp_eq_zero_ae`,
`abs_exposureIncrement_le_ae`) into a `HasCondSubgaussianMGF` object
on the prefix-only σ-algebra `coordinateSubAlgebra n Z k.castSucc`,
in the exact shape mathlib's Azuma-Hoeffding theorem
`measure_sum_ge_le_of_hasCondSubgaussianMGF` consumes.

## Constant choice (Azuma, not sharp McDiarmid)

The parameter is `‖c k‖₊²`, obtained by feeding the a.e. absolute
bound `|Δ_k| ≤ c k` into mathlib's
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` per fiber with the
symmetric interval `[-c k, c k]`. The resulting tail bound after
Azuma-Hoeffding has the form
  `P(M_n - M_0 ≥ t)  ≤  exp(-t² / (2 ∑ c_k²))`,
i.e. the **Azuma constant**, weaker by a factor of 4 in the exponent
than the sharp McDiarmid bound `exp(-2t² / ∑ c_k²)`.

The sharper McDiarmid constant would require a *conditional
range-width* statement of the form
  `Δ_k(S) ∈ [a_k(S_{<k}), a_k(S_{<k}) + c k]`  for every prefix `S_{<k}`,
which in turn requires identifying `condExpKernel μⁿ (coordinateSubAlgebra n Z k.castSucc) ω'`
with the product measure `δ_{S_{<k}} ⊗ μ ⊗ μ^(n-k-1)` (i.e. a
conditional product-measure decomposition). Mathlib does not yet have
the decomposition lemma in usable form: `condExpKernel` of a product
measure relative to a coordinate sub-σ-algebra is not characterised as
a product kernel anywhere I can find. Until that is in place, the
analytic core stays at the Azuma constant. **This is documented
deliberately, not silently degraded** -- downstream PRs that want the
sharp constant must either land the kernel decomposition lemma in
mathlib or build it as a private internal lemma here.

## Imports rationale

- `ExposureIncrementHoeffding` brings `exposureIncrement_condExp_eq_zero_ae`
  and `abs_exposureIncrement_le_ae`.
- `Probability.Moments.SubGaussian` brings `Kernel.HasSubgaussianMGF`,
  `HasCondSubgaussianMGF`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
  `integrable_exp_mul_of_mem_Icc`.
- `Probability.Kernel.Condexp` brings `condExpKernel`,
  `condExpKernel_comp_trim`, `condExp_ae_eq_trim_integral_condExpKernel`.

`[StandardBorelSpace Z]` and `[Nonempty Z]` are kept as local hypotheses
on this theorem, not module-wide assumptions, so unrelated downstream
code does not pay for them.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory Filter ProbabilityTheory Real
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)

noncomputable section

namespace FormalSLT.Azuma.ExposureMartingale

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-- Hoeffding's symmetric-interval parameter `(‖2c‖₊ / 2)² = ‖c‖₊²`. -/
private lemma hoeffding_param_eq_sq {c : ℝ} :
    ((‖c - (-c)‖₊ / 2 : ℝ≥0)) ^ 2 = ‖c‖₊ ^ 2 := by
  have h1 : c - (-c) = c * 2 := by ring
  rw [h1, nnnorm_mul]
  have h2 : ‖(2 : ℝ)‖₊ = 2 := by
    have : ‖(2 : ℝ)‖ = 2 := by norm_num
    exact NNReal.eq this
  rw [h2, mul_div_assoc, div_self (by norm_num : (2 : ℝ≥0) ≠ 0), mul_one]

/-- The kth exposure-martingale increment has a conditionally
sub-Gaussian moment-generating function with parameter `‖c k‖₊²`,
with respect to the prefix-only σ-algebra
`coordinateSubAlgebra n Z k.castSucc` and the product measure `μⁿ`.

This is the **Azuma**, not McDiarmid, constant; see the module
docstring for the precise gap and the missing kernel-decomposition
lemma that blocks the sharper bound.

Proof sketch.
* `abs_exposureIncrement_le_ae` gives `|Δ_k| ≤ c k` a.e. `μⁿ`,
  hence `Δ_k ∈ [-c k, c k]` a.e. `μⁿ`. Lifted to fibers via
  `condExpKernel_comp_trim` and `Measure.ae_ae_of_ae_comp` it gives
  the per-fiber a.e. interval bound on `condExpKernel μⁿ m ω'`.
* `exposureIncrement_condExp_eq_zero_ae` gives `μⁿ[Δ_k|m] =ᵐ[μⁿ] 0`.
  Both sides are `m`-strongly-measurable so the equality descends to
  `μⁿ.trim hm` via `ae_eq_trim_of_stronglyMeasurable`. Combined with
  `condExp_ae_eq_trim_integral_condExpKernel`, this gives
  `∫ Δ_k d(condExpKernel μⁿ m ω') = 0` for `μⁿ.trim hm`-a.e. `ω'`.
* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` applied per
  fiber yields the kernel-MGF bound, with parameter
  `(‖2 c k‖₊ / 2)² = ‖c k‖₊²` (`hoeffding_param_eq_sq`).
* `integrable_exp_mul_of_mem_Icc` plus `condExpKernel_comp_trim` gives
  the global integrability field of `Kernel.HasSubgaussianMGF`. -/
theorem exposureIncrement_hasCondSubgaussianMGF
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (k : Fin n) (hck : 0 ≤ c k) :
    HasCondSubgaussianMGF
      (m := coordinateSubAlgebra n Z k.castSucc)
      (coordinateSubAlgebra_le_pi k.castSucc)
      (exposureIncrement μ f k) (‖c k‖₊ ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  -- Local hypothesis: prefix σ-algebra ≤ full σ-algebra (used several times).
  have hm :
      coordinateSubAlgebra n Z k.castSucc
        ≤ (MeasurableSpace.pi : MeasurableSpace (Fin n → Z)) :=
    coordinateSubAlgebra_le_pi k.castSucc
  -- Δ_k as a strongly measurable function on the full σ-algebra.
  have hΔm : StronglyMeasurable (exposureIncrement μ f k) := by
    show StronglyMeasurable (fun S =>
      exposureMartingale μ f k.succ S - exposureMartingale μ f k.castSucc S)
    refine StronglyMeasurable.sub ?_ ?_
    · exact stronglyMeasurable_condExp.mono (coordinateSubAlgebra_le_pi _)
    · exact stronglyMeasurable_condExp.mono (coordinateSubAlgebra_le_pi _)
  have hΔi : Integrable (exposureIncrement μ f k)
      (Measure.pi (fun _ : Fin n => μ)) := by
    show Integrable (fun S =>
      exposureMartingale μ f k.succ S - exposureMartingale μ f k.castSucc S) _
    exact integrable_condExp.sub integrable_condExp
  -- Step 1: a.e. interval bound on μⁿ.
  have h_bnd : ∀ᵐ S ∂(Measure.pi (fun _ : Fin n => μ)),
      exposureIncrement μ f k S ∈ Set.Icc (-c k) (c k) := by
    have h := abs_exposureIncrement_le_ae (μ := μ) hbdd hf hfi k hck
    filter_upwards [h] with S hS
    exact ⟨neg_le_of_abs_le hS, le_of_abs_le hS⟩
  -- Step 2: per-fiber a.e. interval bound (lift to the kernel).
  have h_bnd_fib : ∀ᵐ ω' ∂((Measure.pi (fun _ : Fin n => μ)).trim hm),
      ∀ᵐ ω ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
              (coordinateSubAlgebra n Z k.castSucc) ω'),
        exposureIncrement μ f k ω ∈ Set.Icc (-c k) (c k) := by
    have h_eq : Measure.pi (fun _ : Fin n => μ)
        = condExpKernel (Measure.pi (fun _ : Fin n => μ))
            (coordinateSubAlgebra n Z k.castSucc)
          ∘ₘ (Measure.pi (fun _ : Fin n => μ)).trim hm :=
      (condExpKernel_comp_trim hm).symm
    have h := h_bnd
    rw [h_eq] at h
    exact Measure.ae_ae_of_ae_comp h
  -- Step 3: per-fiber integral = 0.
  have h_zero : ∀ᵐ ω' ∂((Measure.pi (fun _ : Fin n => μ)).trim hm),
      ∫ ω, exposureIncrement μ f k ω
        ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
            (coordinateSubAlgebra n Z k.castSucc) ω') = 0 := by
    -- μⁿ[Δ_k | m] =ᵐ[μⁿ] 0  (existing).
    have h0 := exposureIncrement_condExp_eq_zero_ae (μ := μ) f k
    -- Both sides are `m`-strongly-measurable, so the equality descends to
    -- `μⁿ.trim hm`.
    have h0' :
        (Measure.pi (fun _ : Fin n => μ))[
            exposureIncrement μ f k | coordinateSubAlgebra n Z k.castSucc]
          =ᵐ[(Measure.pi (fun _ : Fin n => μ)).trim hm] 0 := by
      exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
        stronglyMeasurable_condExp stronglyMeasurable_const h0
    -- Kernel-integral form of conditional expectation, μⁿ.trim hm-a.e.
    have h1 :
        (Measure.pi (fun _ : Fin n => μ))[
            exposureIncrement μ f k | coordinateSubAlgebra n Z k.castSucc]
          =ᵐ[(Measure.pi (fun _ : Fin n => μ)).trim hm]
          fun ω' => ∫ ω, exposureIncrement μ f k ω
            ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
                (coordinateSubAlgebra n Z k.castSucc) ω') :=
      condExp_ae_eq_trim_integral_condExpKernel hm hΔi
    filter_upwards [h0', h1] with ω' h0_ω' h1_ω'
    have hcombine := h1_ω'.symm.trans h0_ω'
    simpa using hcombine
  -- Step 4: assemble Kernel.HasSubgaussianMGF.
  show Kernel.HasSubgaussianMGF (exposureIncrement μ f k) (‖c k‖₊ ^ 2)
    (condExpKernel (Measure.pi (fun _ : Fin n => μ))
      (coordinateSubAlgebra n Z k.castSucc))
    ((Measure.pi (fun _ : Fin n => μ)).trim hm)
  refine
    { integrable_exp_mul := ?_
      mgf_le := ?_ }
  · -- κ ∘ₘ ν = μⁿ via condExpKernel_comp_trim.
    intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hΔm.aemeasurable h_bnd
  · -- mgf_le: per-fiber Hoeffding.
    filter_upwards [h_bnd_fib, h_zero] with ω' h_bnd_ω' h_zero_ω' t
    -- The kernel value at ω' is a probability measure (Markov kernel).
    haveI : IsProbabilityMeasure
        (condExpKernel (Measure.pi (fun _ : Fin n => μ))
          (coordinateSubAlgebra n Z k.castSucc) ω') := inferInstance
    -- Hoeffding's lemma fiberwise.
    have h_mgf :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := condExpKernel (Measure.pi (fun _ : Fin n => μ))
                (coordinateSubAlgebra n Z k.castSucc) ω')
        hΔm.aemeasurable h_bnd_ω' h_zero_ω'
    have hbound := h_mgf.mgf_le t
    -- Rewrite Hoeffding's parameter `(‖c k - (-c k)‖₊ / 2)²` as `‖c k‖₊²`.
    have hparam_real :
        (((‖c k - (-c k)‖₊ / 2 : ℝ≥0)) ^ 2 : ℝ)
          = ((‖c k‖₊ : ℝ≥0) ^ 2 : ℝ) := by
      exact_mod_cast hoeffding_param_eq_sq (c := c k)
    calc mgf (exposureIncrement μ f k)
            (condExpKernel (Measure.pi (fun _ : Fin n => μ))
              (coordinateSubAlgebra n Z k.castSucc) ω') t
        ≤ Real.exp (((‖c k - (-c k)‖₊ / 2 : ℝ≥0) ^ 2 : ℝ) * t ^ 2 / 2) := hbound
      _ = Real.exp (((‖c k‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
            rw [hparam_real]; push_cast; ring_nf

end FormalSLT.Azuma.ExposureMartingale
