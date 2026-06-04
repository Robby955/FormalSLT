/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.ExposureIncrementHoeffding
import Mathlib.MeasureTheory.Function.EssSup
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

## Constant choices

The parameter is `‖c k‖₊²`, obtained by feeding the a.e. absolute
bound `|Δ_k| ≤ c k` into mathlib's
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` per fiber with the
symmetric interval `[-c k, c k]`. The resulting tail bound after
Azuma-Hoeffding has the form
  `P(M_n - M_0 ≥ t)  ≤  exp(-t² / (2 ∑ c_k²))`,
i.e. the **Azuma constant**, weaker by a factor of 4 in the exponent
than the sharp McDiarmid bound `exp(-2t² / ∑ c_k²)`.

The theorem `exposureIncrement_hasCondSubgaussianMGF_sharp` sharpens
the per-increment proxy to `(‖c k‖₊ / 2)²`. It uses the conditional
range-width bridge `exposureIncrement_condRange_width` plus an
`essInf` interval argument: an a.e. pairwise diameter bound on a
conditional fiber puts the increment in an a.e. interval of width
`c k`. The downstream summed McDiarmid tail theorem is a separate
assembly step.

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

private lemma ae_mem_Icc_essInf_add_of_ae_pairwise_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {C : ℝ} (hwidth : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, |X x - X y| ≤ C) :
    ∀ᵐ x ∂ν, X x ∈ Set.Icc (essInf X ν) (essInf X ν + C) := by
  have hν_univ : ν Set.univ ≠ 0 := by
    rw [measure_univ]
    norm_num
  obtain ⟨x0, _hx0_mem, hx0⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := ν) (s := Set.univ) hν_univ (by simpa using hwidth)
  have h_upper_ae : ∀ᵐ y ∂ν, X y ≤ X x0 + C := by
    filter_upwards [hx0] with y hy
    have hy' : |X y - X x0| ≤ C := by
      simpa [abs_sub_comm] using hy
    have hle : X y - X x0 ≤ C := (abs_le.mp hy').2
    linarith
  have h_lower_ae : ∀ᵐ y ∂ν, X x0 - C ≤ X y := by
    filter_upwards [hx0] with y hy
    have hle : X x0 - X y ≤ C := (abs_le.mp hy).2
    linarith
  have hbddBelow : IsBoundedUnder (· ≥ ·) (ae ν) X :=
    ⟨X x0 - C, eventually_map.2 h_lower_ae⟩
  have hcobddBelow : IsCoboundedUnder (· ≥ ·) (ae ν) X := by
    exact IsBounded.isCobounded_ge
      (⟨X x0 + C, eventually_map.2 h_upper_ae⟩ :
        IsBoundedUnder (· ≤ ·) (ae ν) X)
  have h_low : ∀ᵐ y ∂ν, essInf X ν ≤ X y :=
    ae_essInf_le (μ := ν) (f := X) hbddBelow
  have h_high : ∀ᵐ y ∂ν, X y ≤ essInf X ν + C := by
    filter_upwards [hwidth] with y hy
    have hy_le : X y - C ≤ essInf X ν := by
      dsimp [essInf]
      exact Filter.le_liminf_of_le hcobddBelow <| by
        filter_upwards [hy] with z hz
        have hle : X y - X z ≤ C := (abs_le.mp hz).2
        linarith
    linarith
  filter_upwards [h_low, h_high] with y hlow hhigh
  exact ⟨hlow, hhigh⟩

/-! ### Conditional-kernel support on prefix fibers

For the sharp McDiarmid constant, the key kernel-level fact is that the
conditional expectation kernel for the prefix σ-algebra is almost surely
supported on samples with the same revealed prefix. This follows from
`compProd_trim_condExpKernel`: the joint measure of a prefix-state and a
sample drawn from its conditional kernel is the diagonal measure when tested
against sets measurable in the prefix/full product σ-algebra. -/

private lemma measurable_eval_coordinateSubAlgebra
    (k : Fin (n + 1)) (i : Fin n) (hi : (i : ℕ) < (k : ℕ)) :
    @Measurable (Fin n → Z) Z (coordinateSubAlgebra n Z k) _ (fun S => S i) := by
  rw [measurable_iff_comap_le]
  unfold coordinateSubAlgebra
  exact le_iSup₂ (f := fun (j : Fin n) (_ : (j : ℕ) < (k : ℕ)) =>
    (inferInstance : MeasurableSpace Z).comap
      (fun s : Fin n → Z => s j)) i hi

private lemma measurableSet_pair_agree_prefix
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
      (measurable_eval_coordinateSubAlgebra k i hi).comp measurable_fst
    have hsnd : @Measurable ((Fin n → Z) × (Fin n → Z)) Z
        ((coordinateSubAlgebra n Z k).prod MeasurableSpace.pi) _
        (fun p => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    simpa [hi] using hsnd.eq hfst
  · simp [hi]

private lemma condExpKernel_ae_agree_prefix
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
    exact measurableSet_pair_agree_prefix k
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

/-- Conditional range-width bridge for the exposure-martingale increment.

For almost every prefix state `S`, two samples drawn from the conditional
kernel over the prefix σ-algebra have `k`th exposure increments whose
difference is bounded by the coordinate sensitivity `c k`. This is the
kernel-level width-`c_k` statement needed before applying a sharp conditional
Hoeffding lemma; it is stronger than the existing symmetric bound
`|Δ_k| ≤ c k`, but does not yet package the result as
`HasCondSubgaussianMGF` with proxy `(c k / 2)^2`. -/
theorem exposureIncrement_condRange_width
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (k : Fin n) (hck : 0 ≤ c k) :
    ∀ᵐ S ∂((Measure.pi (fun _ : Fin n => μ)).trim (coordinateSubAlgebra_le_pi k.castSucc)),
      ∀ᵐ T ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
          (coordinateSubAlgebra n Z k.castSucc) S),
        ∀ᵐ T' ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
            (coordinateSubAlgebra n Z k.castSucc) S),
          |exposureIncrement μ f k T - exposureIncrement μ f k T'| ≤ c k := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  have hm : coordinateSubAlgebra n Z k.castSucc ≤ MeasurableSpace.pi :=
    coordinateSubAlgebra_le_pi k.castSucc
  have hprefix :
      ∀ᵐ S ∂(μn.trim hm),
        ∀ᵐ T ∂(condExpKernel μn (coordinateSubAlgebra n Z k.castSucc) S),
          ∀ i : Fin n, (i : ℕ) < (k : ℕ) → T i = S i := by
    simpa [μn] using
      (condExpKernel_ae_agree_prefix (μ := μ) (k := k.castSucc))
  have h_eq_partial :
      ∀ᵐ T ∂μn,
        exposureIncrement μ f k T =
          partialIntegral μ k.succ f T - partialIntegral μ k.castSucc f T :=
    exposureIncrement_eq_partialIntegral_diff_ae (μ := μ) k hf hfi
  have h_eq_kernel :
      ∀ᵐ S ∂(μn.trim hm),
        ∀ᵐ T ∂(condExpKernel μn (coordinateSubAlgebra n Z k.castSucc) S),
          exposureIncrement μ f k T =
            partialIntegral μ k.succ f T - partialIntegral μ k.castSucc f T := by
    have h_comp :
        ∀ᵐ T ∂(condExpKernel μn (coordinateSubAlgebra n Z k.castSucc) ∘ₘ μn.trim hm),
          exposureIncrement μ f k T =
            partialIntegral μ k.succ f T - partialIntegral μ k.castSucc f T := by
      rw [condExpKernel_comp_trim hm]
      exact h_eq_partial
    exact Measure.ae_ae_of_ae_comp h_comp
  filter_upwards [hprefix, h_eq_kernel] with S hprefix_S heq_S
  filter_upwards [hprefix_S, heq_S] with T hprefix_T heq_T
  filter_upwards [hprefix_S, heq_S] with T' hprefix_T' heq_T'
  have hprefix_TT' : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → T i = T' i := by
    intro i hi
    rw [hprefix_T i hi, hprefix_T' i hi]
  have h_width :=
    abs_partialIntegral_step_sub_step_le_of_agree_prefix
      (μ := μ) hbdd hf k hck T T' hprefix_TT'
  rw [heq_T, heq_T']
  exact h_width

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

/-- The kth exposure-martingale increment has a conditionally
sub-Gaussian moment-generating function with the sharp one-step
Hoeffding proxy `(‖c k‖₊ / 2)²`.

The proof combines two kernel-level facts. First,
`exposureIncrement_condRange_width` gives an a.e. pairwise diameter
bound of width `c k` on each conditional prefix fiber. Second,
`exposureIncrement_condExp_eq_zero_ae` gives mean zero on the same
fibers. An `essInf` interval argument converts the pairwise diameter
bound into an a.e. fiber interval of width `c k`, so Hoeffding's lemma
applies fiberwise with proxy `(‖c k‖₊ / 2)²`.

This is the load-bearing per-increment result for the sharp McDiarmid
constant; the summed tail theorem is a downstream assembly step. -/
theorem exposureIncrement_hasCondSubgaussianMGF_sharp
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
  have hm :
      coordinateSubAlgebra n Z k.castSucc
        ≤ (MeasurableSpace.pi : MeasurableSpace (Fin n → Z)) :=
    coordinateSubAlgebra_le_pi k.castSucc
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
  have h_bnd : ∀ᵐ S ∂(Measure.pi (fun _ : Fin n => μ)),
      exposureIncrement μ f k S ∈ Set.Icc (-c k) (c k) := by
    have h := abs_exposureIncrement_le_ae (μ := μ) hbdd hf hfi k hck
    filter_upwards [h] with S hS
    exact ⟨neg_le_of_abs_le hS, le_of_abs_le hS⟩
  have h_width :
      ∀ᵐ S ∂((Measure.pi (fun _ : Fin n => μ)).trim hm),
        ∀ᵐ T ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
            (coordinateSubAlgebra n Z k.castSucc) S),
          ∀ᵐ T' ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
              (coordinateSubAlgebra n Z k.castSucc) S),
            |exposureIncrement μ f k T - exposureIncrement μ f k T'| ≤ c k :=
    exposureIncrement_condRange_width (μ := μ) hbdd hf hfi k hck
  have h_zero : ∀ᵐ ω' ∂((Measure.pi (fun _ : Fin n => μ)).trim hm),
      ∫ ω, exposureIncrement μ f k ω
        ∂(condExpKernel (Measure.pi (fun _ : Fin n => μ))
            (coordinateSubAlgebra n Z k.castSucc) ω') = 0 := by
    have h0 := exposureIncrement_condExp_eq_zero_ae (μ := μ) f k
    have h0' :
        (Measure.pi (fun _ : Fin n => μ))[
            exposureIncrement μ f k | coordinateSubAlgebra n Z k.castSucc]
          =ᵐ[(Measure.pi (fun _ : Fin n => μ)).trim hm] 0 := by
      exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
        stronglyMeasurable_condExp stronglyMeasurable_const h0
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
  show Kernel.HasSubgaussianMGF (exposureIncrement μ f k)
    ((‖c k‖₊ / 2 : ℝ≥0) ^ 2)
    (condExpKernel (Measure.pi (fun _ : Fin n => μ))
      (coordinateSubAlgebra n Z k.castSucc))
    ((Measure.pi (fun _ : Fin n => μ)).trim hm)
  refine
    { integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hΔm.aemeasurable h_bnd
  · filter_upwards [h_width, h_zero] with ω' h_width_ω' h_zero_ω' t
    let κω : Measure (Fin n → Z) :=
      condExpKernel (Measure.pi (fun _ : Fin n => μ))
        (coordinateSubAlgebra n Z k.castSucc) ω'
    haveI : IsProbabilityMeasure κω := by
      dsimp [κω]
      infer_instance
    have h_Icc : ∀ᵐ ω ∂κω,
        exposureIncrement μ f k ω ∈
          Set.Icc (essInf (exposureIncrement μ f k) κω)
            (essInf (exposureIncrement μ f k) κω + c k) :=
      ae_mem_Icc_essInf_add_of_ae_pairwise_abs_sub_le
        (ν := κω) (X := exposureIncrement μ f k) h_width_ω'
    have h_mgf :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := κω) hΔm.aemeasurable h_Icc (by simpa [κω] using h_zero_ω')
    have hbound := h_mgf.mgf_le t
    have hdiff :
        (essInf (exposureIncrement μ f k) κω + c k)
            - essInf (exposureIncrement μ f k) κω = c k := by
      ring
    have hparam_real :
        ((((‖(essInf (exposureIncrement μ f k) κω + c k)
              - essInf (exposureIncrement μ f k) κω‖₊ / 2 : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ)
          = ((((‖c k‖₊ / 2 : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ) := by
      rw [hdiff]
    calc mgf (exposureIncrement μ f k) κω t
        ≤ Real.exp (((((‖(essInf (exposureIncrement μ f k) κω + c k)
              - essInf (exposureIncrement μ f k) κω‖₊ / 2 : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ)
            * t ^ 2 / 2) := hbound
      _ = Real.exp (((((‖c k‖₊ / 2 : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
            rw [hparam_real]

end FormalSLT.Azuma.ExposureMartingale
