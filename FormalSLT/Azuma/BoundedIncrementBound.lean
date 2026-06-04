import FormalSLT.Azuma.BoundedDiffMartingale
import FormalSLT.Azuma.BoundedDiffsAzumaInput
import FormalSLT.Azuma.HasBoundedDifferences

/-!
# Exposure-martingale increment bound from `HasBoundedDifferences`

Stage B sub-PR 2c-3 (part 1) of `docs/plans/mcdiarmid-rademacher-plan.md`.

Building on the conditional-expectation identification
`partialIntegral_eq_condExp_ae` from sub-PR 2c-2, this module ships
the **algebraic / a.e. core** of the bridge from sub-PR 2c-2 to the
Azuma-Hoeffding consumer expected by mathlib's
`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`.

## Contents (all closed; no `sorry`, no `admit`, no custom `axiom`)

* `exposureMartingale_eq_partialIntegral_ae` bridge identity:
  `M_k =ᵐ partialIntegral μ k f`. Direct corollary of
  `partialIntegral_eq_condExp_ae`.
* `exposureIncrement_eq_partialIntegral_diff_ae` increment
  representation: `D_k =ᵐ partialIntegral_{k.succ} - partialIntegral_{k.castSucc}`.
* `splice_succ_eq_update_castSucc` pointwise structural identity:
  `splice k.succ S T = Function.update (splice k.castSucc S T) k (S k)`.
  The single-coordinate "reveal" step.
* `abs_partialIntegral_step_le` the bounded-increment range bound:
  for `f : (Fin n → Z) → ℝ` with `HasBoundedDifferences f c`,
  `|partialIntegral μ k.succ f S - partialIntegral μ k.castSucc f S| ≤ c k`
  pointwise. The analytic input that the conditional Hoeffding lemma
  (deferred) will turn into a sub-Gaussian MGF bound.

## Deliberately deferred to follow-on sub-PR(s)

* Conditional sub-Gaussian MGF for `D_k` w.r.t. the coordinate
  filtration, in the form mathlib's `HasCondSubgaussianMGF` consumes.
  This requires `[StandardBorelSpace Z]` (mathlib's `condExpKernel`
  Martingale section opens with that hypothesis), and the conditional
  Hoeffding lift through `condExpKernel μ m` + `μ.trim hm` of
  mathlib's unconditional `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.
  No conditional Hoeffding exists in mathlib at present.
* Filtration index adapter `Fin (n+1) → ℕ` so mathlib's
  `Filtration ℕ`-indexed Azuma-Hoeffding can apply.
* McDiarmid concentration / `genGap` specialization (Stage B3).
* High-probability Rademacher generalization bound (Stage C, the first
  public flagship).

## Constraints respected

* No `sorry`, no `admit`, no custom `axiom`.
* No concentration claim, no high-probability claim, no McDiarmid
  claim, no Massart claim, no VC/PAC claim.
* No manifest entry. No `/lean` dashboard update.
* `[StandardBorelSpace Z]` is **not** used in this module.
-/

namespace FormalSLT.Azuma.ExposureMartingale

open MeasureTheory Filter
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-! ### Step 1: Exposure martingale equals the partial integral, a.e. -/

/-- The exposure martingale equals the partial-integral candidate, almost
everywhere. Direct corollary of `partialIntegral_eq_condExp_ae`
(sub-PR 2c-2) combined with the definition of the exposure martingale
as `μⁿ[f | coordinateSubAlgebra n Z k]`. -/
theorem exposureMartingale_eq_partialIntegral_ae
    [Nonempty Z] [IsProbabilityMeasure μ]
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    exposureMartingale μ f k
      =ᵐ[Measure.pi (fun _ : Fin n => μ)] partialIntegral μ k f :=
  (partialIntegral_eq_condExp_ae k hf hfi).symm

/-! ### Step 2: Increment representation -/

/-- The exposure-martingale increment expressed as the difference of two
partial integrals at consecutive prefix lengths. -/
theorem exposureIncrement_eq_partialIntegral_diff_ae
    [Nonempty Z] [IsProbabilityMeasure μ]
    (k : Fin n) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    exposureIncrement μ f k
      =ᵐ[Measure.pi (fun _ : Fin n => μ)]
        fun S => partialIntegral μ k.succ f S - partialIntegral μ k.castSucc f S := by
  have h_succ := exposureMartingale_eq_partialIntegral_ae k.succ hf hfi
  have h_castSucc := exposureMartingale_eq_partialIntegral_ae k.castSucc hf hfi
  unfold exposureIncrement
  filter_upwards [h_succ, h_castSucc] with S hS_succ hS_castSucc
  rw [hS_succ, hS_castSucc]

/-! ### Step 3: Bounded-increment range bound

The structural identity
`splice k.succ S T = Function.update (splice k.castSucc S T) k (S k)`
expresses the increment as a single-coordinate update at index `k`.
Combined with `HasBoundedDifferences f c`, this yields a pointwise
range bound `|partialIntegral_{k.succ} - partialIntegral_{k.castSucc}| ≤ c k`. -/

/-- Single-coordinate "reveal" identity for `splice`:
`splice k.succ S T` and `splice k.castSucc S T` differ exactly at
coordinate `k`, where the former takes the prefix value `S k` and the
latter takes the tail value `T k`. -/
lemma splice_succ_eq_update_castSucc
    (k : Fin n) (S T : Fin n → Z) :
    splice k.succ S T = Function.update (splice k.castSucc S T) k (S k) := by
  funext j
  by_cases hj_eq : j = k
  · subst hj_eq
    rw [Function.update_self]
    unfold splice
    have h_lt : (j : ℕ) < (j.succ : ℕ) := by rw [Fin.val_succ]; omega
    rw [if_pos h_lt]
  · rw [Function.update_of_ne hj_eq]
    unfold splice
    have hj_ne_k : (j : ℕ) ≠ (k : ℕ) := fun h => hj_eq (Fin.ext h)
    by_cases hjk : (j : ℕ) < (k : ℕ)
    · have hjk_succ : (j : ℕ) < (k.succ : ℕ) := by
        rw [Fin.val_succ]; omega
      have hjk_cast : (j : ℕ) < (k.castSucc : ℕ) := by
        rw [Fin.val_castSucc]; exact hjk
      rw [if_pos hjk_succ, if_pos hjk_cast]
    · have hjk_gt : (k : ℕ) < (j : ℕ) := by
        have : (k : ℕ) ≤ (j : ℕ) := Nat.not_lt.mp hjk
        omega
      have hjk_succ : ¬ ((j : ℕ) < (k.succ : ℕ)) := by
        rw [Fin.val_succ]; omega
      have hjk_cast : ¬ ((j : ℕ) < (k.castSucc : ℕ)) := by
        rw [Fin.val_castSucc]; omega
      rw [if_neg hjk_succ, if_neg hjk_cast]

/-! Pointwise integrand-difference bound.

For each fixed `S` and any `T`, the integrand difference
`f(splice k.succ S T) - f(splice k.castSucc S T)` is bounded in absolute
value by `c k`. Direct application of `HasBoundedDifferences` after the
`splice_succ_eq_update_castSucc` rewrite. -/
private lemma abs_integrand_diff_le
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (S : Fin n → Z) (k : Fin n) (T : Fin n → Z) :
    |f (splice k.succ S T) - f (splice k.castSucc S T)| ≤ c k := by
  rw [splice_succ_eq_update_castSucc]
  rw [abs_sub_comm]
  exact hbdd (splice k.castSucc S T) k (S k)

/-- If two prefixes agree before coordinate `k`, then the two `k.succ`
spliced integrands differ by at most the bounded-differences width `c k`.

This is the pointwise integrand-level form of the range-width argument
needed for the sharp McDiarmid constant: after conditioning on the prefix
before `k`, changing the free coordinate `k` can move the integrand by at
most `c k`. -/
private lemma abs_integrand_succ_sub_succ_le_of_agree_prefix
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (S S' : Fin n → Z) (k : Fin n) (T : Fin n → Z)
    (hprefix : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = S' i) :
    |f (splice k.succ S T) - f (splice k.succ S' T)| ≤ c k := by
  refine FormalSLT.Azuma.BoundedDifferences.HasBoundedDifferences.sub_le_of_agree_off
    hbdd ?_
  intro i hi_ne
  unfold splice
  by_cases hi_succ : (i : ℕ) < (k.succ : ℕ)
  · have hi_lt_k : (i : ℕ) < (k : ℕ) := by
      rw [Fin.val_succ] at hi_succ
      have hne_val : (i : ℕ) ≠ (k : ℕ) := fun h => hi_ne (Fin.ext h)
      omega
    rw [if_pos hi_succ, if_pos hi_succ]
    exact hprefix i hi_lt_k
  · rw [if_neg hi_succ, if_neg hi_succ]

/-! Measurability helper for the integrand at fixed `S`.

`T ↦ f(splice k S T)` is strongly measurable as a composition of
`f` (strongly measurable) with `T ↦ splice k S T` (measurable, since
each coordinate is either a constant `S i` or `T i`). -/
private lemma stronglyMeasurable_splice_partial
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f) (S : Fin n → Z) :
    StronglyMeasurable (fun T : Fin n → Z => f (splice k S T)) := by
  apply hf.comp_measurable
  refine measurable_pi_iff.mpr (fun i => ?_)
  show Measurable (fun T : Fin n → Z =>
    if (i : ℕ) < (k : ℕ) then S i else T i)
  by_cases hi : (i : ℕ) < (k : ℕ)
  · simp only [hi, if_true]; exact measurable_const
  · simp only [hi, if_false]; exact measurable_pi_apply i

/-! Integrability of the inner integrand at fixed `S`.

For each fixed `S`, integrability of `T ↦ f(splice k.succ S T)` is
inherited from `T ↦ f(splice k.castSucc S T)` modulo a single-coordinate
update at index `k`. The bounded-difference hypothesis bounds the gap
in absolute value, so integrability of one form follows from
integrability of the other. -/
private lemma integrable_splice_succ_of_castSucc
    [IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ))]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f) (k : Fin n) (S : Fin n → Z)
    (hint_cast : Integrable (fun T => f (splice k.castSucc S T))
      (Measure.pi (fun _ : Fin n => μ))) :
    Integrable (fun T => f (splice k.succ S T))
      (Measure.pi (fun _ : Fin n => μ)) := by
  -- ‖f(splice k.succ S T)‖ ≤ ‖f(splice k.castSucc S T)‖ + c k by triangle inequality.
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ)
  have h_meas : StronglyMeasurable (fun T => f (splice k.succ S T)) :=
    stronglyMeasurable_splice_partial k.succ hf S
  -- Build the dominating function g(T) = ‖f(splice k.castSucc S T)‖ + c k.
  have hint_norm : Integrable (fun T => ‖f (splice k.castSucc S T)‖) μn :=
    hint_cast.norm
  have hint_g : Integrable (fun T => ‖f (splice k.castSucc S T)‖ + c k) μn :=
    hint_norm.add (integrable_const (c k))
  refine hint_g.mono' h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun T => ?_)
  -- Goal: ‖f(splice k.succ S T)‖ ≤ ‖f(splice k.castSucc S T)‖ + c k.
  have h_diff : |f (splice k.succ S T) - f (splice k.castSucc S T)| ≤ c k :=
    abs_integrand_diff_le hbdd S k T
  -- Triangle inequality: |a| = |(a - b) + b| ≤ |a - b| + |b|.
  have h_tri : |f (splice k.succ S T)|
      ≤ |f (splice k.succ S T) - f (splice k.castSucc S T)|
        + |f (splice k.castSucc S T)| := by
    have h_id : f (splice k.succ S T) - f (splice k.castSucc S T)
        + f (splice k.castSucc S T) = f (splice k.succ S T) := by ring
    calc |f (splice k.succ S T)|
        = |(f (splice k.succ S T) - f (splice k.castSucc S T))
            + f (splice k.castSucc S T)| := by rw [h_id]
      _ ≤ |f (splice k.succ S T) - f (splice k.castSucc S T)|
            + |f (splice k.castSucc S T)| := abs_add_le _ _
  show ‖f (splice k.succ S T)‖ ≤ ‖f (splice k.castSucc S T)‖ + c k
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  linarith

/-! Pointwise bounded-increment range bound.

For each fixed `S`, the partial-integral increment is bounded in
absolute value by `c k`. The bound holds for **all** `S` (not only
a.e.): if the inner integrand fails integrability at some `S`, both
partial integrals default to `0`, the difference is `0`, and the bound
holds trivially provided `c k ≥ 0`.

The hypothesis `0 ≤ c k` is needed to handle the non-integrable
fallback case; under bounded differences with non-negative widths
(the only case used in McDiarmid) it is automatic. -/
set_option linter.unusedVariables false in
theorem abs_partialIntegral_step_le
    [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (k : Fin n) (hck : 0 ≤ c k) (S : Fin n → Z) :
    |partialIntegral μ k.succ f S - partialIntegral μ k.castSucc f S| ≤ c k := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  -- Integrability of the inner integrand at `S` is the issue.
  by_cases hint_cast :
      Integrable (fun T => f (splice k.castSucc S T)) μn
  · -- Both inner integrands are integrable.
    have hint_succ : Integrable (fun T => f (splice k.succ S T)) μn :=
      integrable_splice_succ_of_castSucc hbdd hf k S hint_cast
    -- Rewrite the difference as a single integral.
    unfold partialIntegral
    rw [show
        ∫ T, f (splice k.succ S T) ∂μn
          - ∫ T, f (splice k.castSucc S T) ∂μn
        = ∫ T, (f (splice k.succ S T) - f (splice k.castSucc S T)) ∂μn from
      (integral_sub hint_succ hint_cast).symm]
    -- Triangle inequality: |∫ g| ≤ ∫ |g| ≤ ∫ c k = c k.
    refine (abs_integral_le_integral_abs).trans ?_
    have h_pointwise : ∀ T,
        |f (splice k.succ S T) - f (splice k.castSucc S T)| ≤ c k :=
      fun T => abs_integrand_diff_le hbdd S k T
    have h_const : ∫ _T : Fin n → Z, c k ∂μn = c k := by
      rw [integral_const]
      simp
    rw [← h_const]
    refine integral_mono_ae ?_ (integrable_const (c k)) ?_
    · -- Integrability of |f1 - f2|.
      exact (hint_succ.sub hint_cast).abs
    · exact Filter.Eventually.of_forall h_pointwise
  · -- The inner integrand at `S` is not integrable.  Both
    -- `partialIntegral` values default to `0` by `integral_undef`,
    -- since the splice change is a single-coordinate update and
    -- preserves integrability (proved above).  Hence the partial
    -- integral at `k.succ` is also `0`, and the difference is `0`.
    have hint_succ_neg : ¬ Integrable (fun T => f (splice k.succ S T)) μn := by
      intro hint_succ
      apply hint_cast
      -- Symmetric trick: ‖f(splice k.cast S T)‖ ≤ ‖f(splice k.succ S T)‖ + c k.
      have h_meas : StronglyMeasurable
          (fun T => f (splice k.castSucc S T)) :=
        stronglyMeasurable_splice_partial k.castSucc hf S
      have hint_norm : Integrable (fun T => ‖f (splice k.succ S T)‖) μn :=
        hint_succ.norm
      have hint_g : Integrable (fun T => ‖f (splice k.succ S T)‖ + c k) μn :=
        hint_norm.add (integrable_const (c k))
      refine hint_g.mono' h_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun T => ?_)
      have h_diff : |f (splice k.castSucc S T) - f (splice k.succ S T)| ≤ c k := by
        rw [abs_sub_comm]; exact abs_integrand_diff_le hbdd S k T
      have h_tri : |f (splice k.castSucc S T)|
          ≤ |f (splice k.castSucc S T) - f (splice k.succ S T)|
            + |f (splice k.succ S T)| := by
        have h_id : f (splice k.castSucc S T) - f (splice k.succ S T)
            + f (splice k.succ S T) = f (splice k.castSucc S T) := by ring
        calc |f (splice k.castSucc S T)|
            = |(f (splice k.castSucc S T) - f (splice k.succ S T))
                + f (splice k.succ S T)| := by rw [h_id]
          _ ≤ |f (splice k.castSucc S T) - f (splice k.succ S T)|
                + |f (splice k.succ S T)| := abs_add_le _ _
      show ‖f (splice k.castSucc S T)‖ ≤ ‖f (splice k.succ S T)‖ + c k
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      linarith
    unfold partialIntegral
    rw [integral_undef hint_succ_neg, integral_undef hint_cast, sub_zero]
    -- Goal: |0| ≤ c k.
    rw [abs_zero]
    exact hck

/-! ### Pointwise range-width form for the explicit increments

The previous theorem gives a symmetric absolute bound
`|P_{k+1}(S) - P_k(S)| ≤ c k`. For the sharp McDiarmid constant, the
needed geometry is stronger: once the prefix before `k` is fixed, the
explicit increment `P_{k+1} - P_k` has range width at most `c k` as the
`k`th coordinate varies. The following two lemmas isolate that pointwise
partial-integral statement before any conditional-kernel lift. -/

/-- If two samples agree on the prefix before `k`, then their `k.succ`
partial integrals differ by at most the coordinate width `c k`. -/
theorem abs_partialIntegral_succ_sub_succ_le_of_agree_prefix
    [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (k : Fin n) (hck : 0 ≤ c k) (S S' : Fin n → Z)
    (hprefix : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = S' i) :
    |partialIntegral μ k.succ f S - partialIntegral μ k.succ f S'| ≤ c k := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  by_cases hint :
      Integrable (fun T => f (splice k.succ S T)) μn
  · have hint' : Integrable (fun T => f (splice k.succ S' T)) μn := by
      have h_meas : StronglyMeasurable (fun T => f (splice k.succ S' T)) :=
        stronglyMeasurable_splice_partial k.succ hf S'
      have hint_norm : Integrable (fun T => ‖f (splice k.succ S T)‖) μn :=
        hint.norm
      have hint_g : Integrable (fun T => ‖f (splice k.succ S T)‖ + c k) μn :=
        hint_norm.add (integrable_const (c k))
      refine hint_g.mono' h_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun T => ?_)
      have h_diff :
          |f (splice k.succ S' T) - f (splice k.succ S T)| ≤ c k := by
        rw [abs_sub_comm]
        exact abs_integrand_succ_sub_succ_le_of_agree_prefix hbdd S S' k T hprefix
      have h_tri : |f (splice k.succ S' T)|
          ≤ |f (splice k.succ S' T) - f (splice k.succ S T)|
            + |f (splice k.succ S T)| := by
        have h_id : f (splice k.succ S' T) - f (splice k.succ S T)
            + f (splice k.succ S T) = f (splice k.succ S' T) := by ring
        calc |f (splice k.succ S' T)|
            = |(f (splice k.succ S' T) - f (splice k.succ S T))
                + f (splice k.succ S T)| := by rw [h_id]
          _ ≤ |f (splice k.succ S' T) - f (splice k.succ S T)|
                + |f (splice k.succ S T)| := abs_add_le _ _
      show ‖f (splice k.succ S' T)‖ ≤ ‖f (splice k.succ S T)‖ + c k
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      linarith
    unfold partialIntegral
    rw [show
        ∫ T, f (splice k.succ S T) ∂μn
          - ∫ T, f (splice k.succ S' T) ∂μn
        = ∫ T, (f (splice k.succ S T) - f (splice k.succ S' T)) ∂μn from
      (integral_sub hint hint').symm]
    refine (abs_integral_le_integral_abs).trans ?_
    have h_pointwise : ∀ T,
        |f (splice k.succ S T) - f (splice k.succ S' T)| ≤ c k :=
      fun T => abs_integrand_succ_sub_succ_le_of_agree_prefix hbdd S S' k T hprefix
    have h_const : ∫ _T : Fin n → Z, c k ∂μn = c k := by
      rw [integral_const]
      simp
    rw [← h_const]
    refine integral_mono_ae ?_ (integrable_const (c k)) ?_
    · exact (hint.sub hint').abs
    · exact Filter.Eventually.of_forall h_pointwise
  · have hint'_neg : ¬ Integrable (fun T => f (splice k.succ S' T)) μn := by
      intro hint'
      apply hint
      have h_meas : StronglyMeasurable (fun T => f (splice k.succ S T)) :=
        stronglyMeasurable_splice_partial k.succ hf S
      have hint_norm : Integrable (fun T => ‖f (splice k.succ S' T)‖) μn :=
        hint'.norm
      have hint_g : Integrable (fun T => ‖f (splice k.succ S' T)‖ + c k) μn :=
        hint_norm.add (integrable_const (c k))
      refine hint_g.mono' h_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun T => ?_)
      have h_diff :
          |f (splice k.succ S T) - f (splice k.succ S' T)| ≤ c k :=
        abs_integrand_succ_sub_succ_le_of_agree_prefix hbdd S S' k T hprefix
      have h_tri : |f (splice k.succ S T)|
          ≤ |f (splice k.succ S T) - f (splice k.succ S' T)|
            + |f (splice k.succ S' T)| := by
        have h_id : f (splice k.succ S T) - f (splice k.succ S' T)
            + f (splice k.succ S' T) = f (splice k.succ S T) := by ring
        calc |f (splice k.succ S T)|
            = |(f (splice k.succ S T) - f (splice k.succ S' T))
                + f (splice k.succ S' T)| := by rw [h_id]
          _ ≤ |f (splice k.succ S T) - f (splice k.succ S' T)|
                + |f (splice k.succ S' T)| := abs_add_le _ _
      show ‖f (splice k.succ S T)‖ ≤ ‖f (splice k.succ S' T)‖ + c k
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      linarith
    unfold partialIntegral
    rw [integral_undef hint, integral_undef hint'_neg, sub_zero]
    rw [abs_zero]
    exact hck

/-- Pointwise range-width form for the explicit partial-integral
increment `P_{k+1} - P_k`: fixing the prefix before `k`, the increment's
range as the `k`th coordinate varies has width at most `c k`. -/
theorem abs_partialIntegral_step_sub_step_le_of_agree_prefix
    [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (k : Fin n) (hck : 0 ≤ c k) (S S' : Fin n → Z)
    (hprefix : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = S' i) :
    |(partialIntegral μ k.succ f S - partialIntegral μ k.castSucc f S)
        - (partialIntegral μ k.succ f S' - partialIntegral μ k.castSucc f S')|
      ≤ c k := by
  have h_cast :
      partialIntegral μ k.castSucc f S = partialIntegral μ k.castSucc f S' :=
    partialIntegral_eq_of_agree_prefix (μ := μ) k.castSucc f S S' hprefix
  have h_succ :=
    abs_partialIntegral_succ_sub_succ_le_of_agree_prefix (μ := μ)
      hbdd hf k hck S S' hprefix
  convert h_succ using 1
  rw [h_cast]
  ring_nf

end FormalSLT.Azuma.ExposureMartingale
