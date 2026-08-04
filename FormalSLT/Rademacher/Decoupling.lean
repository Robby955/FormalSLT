import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import FormalSLT.Risk
import FormalSLT.Rademacher.FiniteSample
import FormalSLT.Rademacher.FiniteSampleSymmetrization
import FormalSLT.Rademacher.ProbabilityBridge
import FormalSLT.GhostSample

/-!
# Rademacher decoupling (Stage 2 of finite-sample symmetrization)

Builds on:

* Stage 1 (`FiniteSampleGhostSampleReplacement`) — provides the
  `decoupledGap` quantity and the expected ghost-sample replacement
  inequality.
* Combinatorial factor-two identity (`FiniteSampleSymmetrization`) —
  provides `finiteSampleSymmetrizationFactorTwo`, a purely
  combinatorial bound on sums over sign vectors.
* Probability bridge (`RademacherProbabilityBridge`) — connects the
  combinatorial sum form of the empirical Rademacher complexity to its
  Bochner-integral form against the uniform sign PMF.

What this module provides (all closed, no `sorry`, no `admit`):

* `decoupledGap_eq_sup_diff` — Lemma 1: pointwise rewrite of
  `decoupledGap ℓ S S'` as a sup over `i` of the `(1/n)`-scaled
  difference of losses on the two samples.
* `signedDecoupledGap` — the σ-weighted version of `decoupledGap`,
  with each coordinate's contribution multiplied by `signOfBool (σ k)`.
* `swapBy` — the per-coordinate "swap or not" map on
  `(Fin n → Z) × (Fin n → Z)` controlled by a sign vector `σ`.
* `swapBy_involutive`, `measurable_swapBy` — basic structural lemmas.
* `decoupledGap_swapBy_eq_signedDecoupledGap` — pointwise identity
  recasting `decoupledGap ∘ swapBy σ` as `signedDecoupledGap σ`.
* `expected_decoupledGap_eq_expected_signedDecoupledGap` — Lemma 2:
  for each sign vector `σ`, the expected `decoupledGap` over the iid
  product `(piMeasure μ n).prod (piMeasure μ n)` equals the expected
  `signedDecoupledGap σ`. Proof: the swap is measure-preserving on the
  iid product (per-coordinate swap of `μ.prod μ` is symmetric).
* `finiteSampleSymmetrizationFactorTwo_div_n` — Lemma 3a: `(1/n)`-
  rescaled version of the existing combinatorial factor-two bound.
* `expected_decoupledGap_le_two_expected_empiricalRademacherComplexity`
  — Stage 2 final theorem.

Out of scope for this module (deferred):

* High-probability uniform-deviation bound (no McDiarmid, no sub-Gaussian).
* VC dimension / generic PAC.
* Contraction lemma; uncountable hypothesis classes; separability.
* No manifest entry. The Stage 3 module
  (`FiniteSampleRademacherSymmetrization`, future PR) combines Stage 1
  and Stage 2 into the recognizable expected symmetrization theorem and
  becomes manifest-eligible.
-/

namespace FormalSLT.Rademacher.Decoupling

open MeasureTheory PMF Finset
open scoped BigOperators ENNReal
open FormalSLT.GhostSample
  (decoupledGap piMeasure)
open FormalSLT.Rademacher.FiniteSample
  (signOfBool empiricalRademacherComplexity signOfBool_neg signOfBool_sq
   abs_signOfBool)
open FormalSLT.Rademacher.FiniteSampleSymmetrization
  (signedEmpiricalSum finiteSampleSymmetrizationFactorTwo)
open FormalSLT.Rademacher.ProbabilityBridge
  (uniformSignPMF supSignedEmpiricalMean signedEmpiricalMean
   empiricalRademacherComplexity_eq_integral
   uniform_average_eq_finset_sum)

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]
variable {n : ℕ}

/-! ### Lemma 1: decoupledGap as a sup of (1/n)-scaled difference sums -/

/-- **Algebraic rewrite of `decoupledGap`.** The supremum-of-empirical-risk-
differences is the supremum-of-`(1/n)`-scaled-coordinate-difference-sums.
Pure algebra; no measure theory. -/
lemma decoupledGap_eq_sup_diff
    [MeasurableSpace Z] (ℓ : ι → Z → ℝ) (S S' : Fin n → Z) :
    decoupledGap ℓ S S'
      = (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, (ℓ i (S' k) - ℓ i (S k))) := by
  unfold decoupledGap Risk.empiricalRisk
  refine Finset.sup'_congr _ rfl (fun i _ => ?_)
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-! ### σ-weighted decoupled gap and the per-coordinate swap -/

/-- The σ-weighted version of `decoupledGap`: each coordinate's
contribution to the difference is multiplied by `signOfBool (σ k)`.
For the all-`true` σ, this reduces to the original `decoupledGap` (up to
the algebraic rewrite of Lemma 1). -/
noncomputable def signedDecoupledGap
    (ℓ : ι → Z → ℝ) (σ : Fin n → Bool) (S S' : Fin n → Z) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => (n : ℝ)⁻¹ *
      ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k)))

/-- Per-coordinate "swap or not" map on `(Fin n → Z) × (Fin n → Z)`
controlled by a sign vector `σ`. At coordinate `k`:

* `σ k = true`  → keep `(S_k, S'_k)` as is.
* `σ k = false` → swap to `(S'_k, S_k)`.

The map fixes coordinates where `σ k = true` and swaps the two samples'
entries at coordinates where `σ k = false`. -/
def swapBy (σ : Fin n → Bool) :
    (Fin n → Z) × (Fin n → Z) → (Fin n → Z) × (Fin n → Z) :=
  fun p =>
    (fun k => if σ k = true then p.1 k else p.2 k,
     fun k => if σ k = true then p.2 k else p.1 k)

@[simp] lemma swapBy_fst (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z))
    (k : Fin n) :
    (swapBy σ p).1 k = if σ k = true then p.1 k else p.2 k := rfl

@[simp] lemma swapBy_snd (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z))
    (k : Fin n) :
    (swapBy σ p).2 k = if σ k = true then p.2 k else p.1 k := rfl

/-- The per-coordinate swap is involutive: `swapBy σ ∘ swapBy σ = id`. -/
lemma swapBy_involutive (σ : Fin n → Bool) :
    Function.Involutive (swapBy σ : (Fin n → Z) × (Fin n → Z) →
      (Fin n → Z) × (Fin n → Z)) := by
  intro p
  ext k <;> by_cases hσ : σ k = true <;> simp [swapBy, hσ]

/-- Measurability of `swapBy σ` viewed as a self-map of the product
space `(Fin n → Z) × (Fin n → Z)`. -/
lemma measurable_swapBy [MeasurableSpace Z] (σ : Fin n → Bool) :
    Measurable
      (swapBy σ : (Fin n → Z) × (Fin n → Z) →
        (Fin n → Z) × (Fin n → Z)) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_lambda _ (fun k => ?_)
    by_cases hσ : σ k = true
    · change Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        if σ k = true then p.1 k else p.2 k)
      simp only [if_pos hσ]
      fun_prop
    · change Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        if σ k = true then p.1 k else p.2 k)
      simp only [if_neg hσ]
      fun_prop
  · refine measurable_pi_lambda _ (fun k => ?_)
    by_cases hσ : σ k = true
    · change Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        if σ k = true then p.2 k else p.1 k)
      simp only [if_pos hσ]
      fun_prop
    · change Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        if σ k = true then p.2 k else p.1 k)
      simp only [if_neg hσ]
      fun_prop

/-- **Pointwise swap identity.** For any sample pair `(S, S')` and any
sign vector `σ`, evaluating `decoupledGap` at the σ-swapped pair gives
the σ-weighted decoupled gap on the original pair. Pure algebra: the
factor `signOfBool (σ k)` records whether the k-th coordinate was kept
(`+1`) or swapped (`-1`). -/
lemma decoupledGap_swapBy_eq_signedDecoupledGap
    [MeasurableSpace Z] (ℓ : ι → Z → ℝ) (σ : Fin n → Bool)
    (S S' : Fin n → Z) :
    decoupledGap ℓ (swapBy σ (S, S')).1 (swapBy σ (S, S')).2
      = signedDecoupledGap ℓ σ S S' := by
  rw [decoupledGap_eq_sup_diff]
  unfold signedDecoupledGap
  refine Finset.sup'_congr _ rfl (fun i _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Case-split on `σ k`. Each branch reduces to a small algebraic identity.
  cases hσ : σ k <;>
    (simp [swapBy_fst, swapBy_snd, hσ, signOfBool]; try ring)

/-! ### Lemma 3: rescaled combinatorial factor-two identity -/

/-- Pull a non-negative scalar out of `Finset.sup'`. Specialization of
`Finset.mul₀_sup'` to `ℝ`. -/
private lemma mul_inv_n_sup' (g : ι → ℝ) :
    (n : ℝ)⁻¹ *
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty g =
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * g i) := by
  have h_n_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg n)
  exact Finset.mul₀_sup' h_n_nonneg g (Finset.univ : Finset ι)
    Finset.univ_nonempty

/-- **Lemma 3a: `(1/n)`-rescaled factor-two combinatorial bound.**

Multiply the existing `finiteSampleSymmetrizationFactorTwo` bound — a
purely combinatorial inequality on sums over sign vectors — through by
`(2^n)⁻¹ * (n : ℝ)⁻¹` to get the rescaled form that matches the
`(1/n)`-scaled signed empirical means appearing in the empirical
Rademacher complexity.

Concretely:

`(2^n)⁻¹ ∑_σ sup_i (1/n) (signedEmpiricalSum ℓ z' σ i
                          - signedEmpiricalSum ℓ z σ i)`
` ≤ (2^n)⁻¹ ∑_σ sup_i (1/n) signedEmpiricalSum ℓ z' σ i`
` + (2^n)⁻¹ ∑_σ sup_i (1/n) signedEmpiricalSum ℓ z σ i`. -/
theorem finiteSampleSymmetrizationFactorTwo_div_n
    (ℓ : ι → Z → ℝ) (z z' : Fin n → Z) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ *
            (signedEmpiricalSum ℓ z' σ i - signedEmpiricalSum ℓ z σ i)) ≤
      (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z' σ i)) +
        (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i)) := by
  -- Combinatorial factor-two on sums of sup' (no `(1/n)`), with z and z'
  -- swapped so the difference is z'-side minus z-side.
  have h_combo := finiteSampleSymmetrizationFactorTwo (ι := ι) (n := n) ℓ z' z
  -- Re-express each `sup'` of an `(1/n)`-scaled function via `mul_inv_n_sup'`.
  have h_lhs :
      ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ *
              (signedEmpiricalSum ℓ z' σ i - signedEmpiricalSum ℓ z σ i)) =
        (n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => signedEmpiricalSum ℓ z' σ i -
                      signedEmpiricalSum ℓ z σ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    exact (mul_inv_n_sup'
      (fun i => signedEmpiricalSum ℓ z' σ i -
                signedEmpiricalSum ℓ z σ i)).symm
  have h_rhs1 :
      ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z' σ i) =
        (n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => signedEmpiricalSum ℓ z' σ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    exact (mul_inv_n_sup' (fun i => signedEmpiricalSum ℓ z' σ i)).symm
  have h_rhs2 :
      ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i) =
        (n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => signedEmpiricalSum ℓ z σ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    exact (mul_inv_n_sup' (fun i => signedEmpiricalSum ℓ z σ i)).symm
  -- Substitute and reduce to multiplying the combinatorial bound by
  -- `(2^n)⁻¹ * (n)⁻¹`, both ≥ 0.
  rw [h_lhs, h_rhs1, h_rhs2]
  have h_two_pow_nonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have h_n_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg n)
  have h_factor_nonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ * (n : ℝ)⁻¹ :=
    mul_nonneg h_two_pow_nonneg h_n_nonneg
  -- Multiply the combinatorial bound through by `(2^n)⁻¹ * (n)⁻¹`.
  have := mul_le_mul_of_nonneg_left h_combo h_factor_nonneg
  -- Match the goal shape via algebra.
  ring_nf
  ring_nf at this
  linarith

/-! ### Lemma 2: σ-swap is measure-preserving on the iid product -/

/-- Per-coordinate swap on `Fin n → Z × Z`. At coordinate `k`, keep the
pair `p k` if `σ k = true`, else swap to `Prod.swap (p k)`. This is the
"arrow form" companion of `swapBy`: under the identification
`(Fin n → Z × Z) ≃ᵐ (Fin n → Z) × (Fin n → Z)`, it corresponds to
`swapBy σ`. -/
private def coordSwap (σ : Fin n → Bool) :
    (Fin n → Z × Z) → (Fin n → Z × Z) :=
  fun p k => if σ k = true then p k else Prod.swap (p k)

/-- Per-coordinate `coordSwap` rewritten as a per-coordinate map family,
ready for `measurePreserving_pi`. -/
private lemma coordSwap_eq_pi (σ : Fin n → Bool) :
    (coordSwap σ : (Fin n → Z × Z) → (Fin n → Z × Z)) =
      fun a (k : Fin n) =>
        (if σ k = true then (id : Z × Z → Z × Z) else Prod.swap) (a k) := by
  funext p k
  simp only [coordSwap]
  by_cases hσ : σ k = true
  · simp [hσ]
  · simp [hσ]

/-- Per-coordinate map (`id` or `Prod.swap`) is measure-preserving on
`μ.prod μ`. -/
private lemma measurePreserving_coordSwap_coord
    [MeasurableSpace Z] (μ : Measure Z) [SigmaFinite μ]
    (σ : Fin n → Bool) (k : Fin n) :
    MeasurePreserving
      (if σ k = true then (id : Z × Z → Z × Z) else Prod.swap)
      (μ.prod μ) (μ.prod μ) := by
  by_cases hσ : σ k = true
  · simp [hσ]
    exact MeasurePreserving.id (μ.prod μ)
  · simp [hσ]
    exact Measure.measurePreserving_swap

/-- The per-coordinate swap is measure-preserving on the symmetric iid
product `Pi (μ.prod μ)`. -/
private lemma measurePreserving_coordSwap
    [MeasurableSpace Z] (μ : Measure Z) [SigmaFinite μ]
    (σ : Fin n → Bool) :
    MeasurePreserving (coordSwap σ : (Fin n → Z × Z) → (Fin n → Z × Z))
      (Measure.pi (fun _ : Fin n => μ.prod μ))
      (Measure.pi (fun _ : Fin n => μ.prod μ)) := by
  rw [coordSwap_eq_pi]
  exact measurePreserving_pi _ _
    (fun k => measurePreserving_coordSwap_coord μ σ k)

/-- Factoring `swapBy` through the measurable equivalence
`(Fin n → Z × Z) ≃ᵐ (Fin n → Z) × (Fin n → Z)`: the per-coordinate-swap
on `Fin n → Z × Z` becomes `swapBy σ` after pre/post-composition with
the equivalence. -/
private lemma swapBy_eq_arrow_coordSwap [MeasurableSpace Z]
    (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z)) :
    swapBy σ p =
      (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))
        (coordSwap σ
          ((MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)).symm p)) := by
  -- Both sides are pairs of functions on `Fin n`; check componentwise.
  ext k <;> by_cases hσ : σ k = true <;>
    simp [swapBy, coordSwap, hσ,
          MeasurableEquiv.arrowProdEquivProdArrow,
          Equiv.arrowProdEquivProdArrow, Prod.swap]

/-- **`swapBy σ` is measure-preserving on the iid product.** Combines
`measurePreserving_arrowProdEquivProdArrow` (and its symm) with
`measurePreserving_coordSwap`. -/
lemma measurePreserving_swapBy [MeasurableSpace Z]
    (μ : Measure Z) [SigmaFinite μ] (σ : Fin n → Bool) :
    MeasurePreserving
      (swapBy σ : (Fin n → Z) × (Fin n → Z) → (Fin n → Z) × (Fin n → Z))
      ((piMeasure μ n).prod (piMeasure μ n))
      ((piMeasure μ n).prod (piMeasure μ n)) := by
  -- Forward and inverse directions of the arrow ↔ pair-of-arrow equivalence.
  have h_arrow := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n)
    (fun _ : Fin n => μ) (fun _ : Fin n => μ)
  have h_arrow_symm : MeasurePreserving
      ((MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)).symm)
      ((piMeasure μ n).prod (piMeasure μ n))
      (Measure.pi (fun _ : Fin n => μ.prod μ)) := by
    -- Symm of the equivalence; piMeasure unfolds to Measure.pi.
    have := h_arrow.symm
      (e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))
    -- Rewrite goal/hypothesis to expose `piMeasure`.
    unfold piMeasure
    exact this
  -- coordSwap is measure-preserving on Pi (μ.prod μ).
  have h_coord := measurePreserving_coordSwap (μ := μ) σ
  -- Forward arrow direction back.
  have h_arrow_fwd : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))
      (Measure.pi (fun _ : Fin n => μ.prod μ))
      ((piMeasure μ n).prod (piMeasure μ n)) := by
    unfold piMeasure
    exact h_arrow
  -- Compose: swapBy σ = arrow ∘ coordSwap σ ∘ arrow.symm.
  have h_comp : MeasurePreserving
      ((MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))
        ∘ (coordSwap σ : (Fin n → Z × Z) → _)
        ∘ (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)).symm)
      ((piMeasure μ n).prod (piMeasure μ n))
      ((piMeasure μ n).prod (piMeasure μ n) : Measure _) :=
    h_arrow_fwd.comp (h_coord.comp h_arrow_symm)
  -- Pointwise equality `swapBy σ = arrow ∘ coordSwap σ ∘ arrow.symm`.
  have h_eq :
      (swapBy σ : (Fin n → Z) × (Fin n → Z) → (Fin n → Z) × (Fin n → Z))
        = (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))
          ∘ (coordSwap σ : (Fin n → Z × Z) → _)
          ∘ (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)).symm := by
    funext p
    exact swapBy_eq_arrow_coordSwap σ p
  rw [h_eq]
  exact h_comp

/-- The σ-swap as a measurable equivalence (its inverse is itself). -/
def swapByEquiv [MeasurableSpace Z] (σ : Fin n → Bool) :
    (Fin n → Z) × (Fin n → Z) ≃ᵐ (Fin n → Z) × (Fin n → Z) where
  toFun := swapBy σ
  invFun := swapBy σ
  left_inv := swapBy_involutive σ
  right_inv := swapBy_involutive σ
  measurable_toFun := measurable_swapBy σ
  measurable_invFun := measurable_swapBy σ

/-- **Lemma 2: expected `decoupledGap` equals expected `signedDecoupledGap σ`.**
For each sign vector `σ`, integrating `decoupledGap` against the iid
product measure equals integrating the σ-weighted version. The integral
is invariant because `swapBy σ` is measure-preserving on the symmetric
product, and `decoupledGap ∘ swapBy σ` equals `signedDecoupledGap σ` by
`decoupledGap_swapBy_eq_signedDecoupledGap`. -/
theorem expected_decoupledGap_eq_expected_signedDecoupledGap
    [MeasurableSpace Z] (μ : Measure Z) [SigmaFinite μ]
    (ℓ : ι → Z → ℝ) (σ : Fin n → Bool) :
    ∫ p, decoupledGap ℓ p.1 p.2 ∂((piMeasure μ n).prod (piMeasure μ n))
      = ∫ p, signedDecoupledGap ℓ σ p.1 p.2
          ∂((piMeasure μ n).prod (piMeasure μ n)) := by
  -- Step 1: invariance under swapBy σ.
  have h_inv :
      ∫ p, decoupledGap ℓ p.1 p.2
            ∂((piMeasure μ n).prod (piMeasure μ n))
        = ∫ p, decoupledGap ℓ (swapBy σ p).1 (swapBy σ p).2
            ∂((piMeasure μ n).prod (piMeasure μ n)) := by
    have h_mp := measurePreserving_swapBy (μ := μ) σ
    -- Apply `MeasurePreserving.integral_comp` with the measurable
    -- embedding furnished by `swapByEquiv σ`.
    have h_emb : MeasurableEmbedding
        (swapBy σ : (Fin n → Z) × (Fin n → Z) →
          (Fin n → Z) × (Fin n → Z)) :=
      (swapByEquiv σ).measurableEmbedding
    have := h_mp.integral_comp h_emb
              (fun p : (Fin n → Z) × (Fin n → Z) => decoupledGap ℓ p.1 p.2)
    exact this.symm
  -- Step 2: pointwise rewrite via the swap identity.
  rw [h_inv]
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  -- The integrand on the LHS is `decoupledGap ℓ (swapBy σ p).1 (swapBy σ p).2`,
  -- which by the pointwise identity equals `signedDecoupledGap ℓ σ p.1 p.2`.
  exact decoupledGap_swapBy_eq_signedDecoupledGap ℓ σ p.1 p.2

/-! ### Lemma 3b: pointwise factor-two restated in terms of
`signedDecoupledGap` and `empiricalRademacherComplexity`. -/

/-- **Pointwise factor-two for `signedDecoupledGap` and
`empiricalRademacherComplexity`.** Specialization of Lemma 3a
(`finiteSampleSymmetrizationFactorTwo_div_n`) recognizing the standard
named quantities: the σ-average of `signedDecoupledGap ℓ σ S S'` is
bounded by the sum of the empirical Rademacher complexities of `S'`
and `S`. -/
theorem signedDecoupledGap_avg_le_two_empiricalRademacher
    (ℓ : ι → Z → ℝ) (S S' : Fin n → Z) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ S S'
      ≤ empiricalRademacherComplexity ℓ S' +
        empiricalRademacherComplexity ℓ S := by
  -- Pointwise rewrite: each `signedDecoupledGap ℓ σ S S'` matches the
  -- LHS sup of Lemma 3a, after distributing `(1/n) * (… - …)`.
  have h_lhs_eq : ∀ σ : Fin n → Bool,
      signedDecoupledGap ℓ σ S S' =
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ *
            (signedEmpiricalSum ℓ S' σ i - signedEmpiricalSum ℓ S σ i)) := by
    intro σ
    unfold signedDecoupledGap signedEmpiricalSum
    refine Finset.sup'_congr _ rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine congrArg ((n : ℝ)⁻¹ * ·) ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  -- Rewrite RHS using `empiricalRademacherComplexity` definition unfolded
  -- to the `signedEmpiricalSum`-flavored form Lemma 3a uses.
  have h_rhs_S' : empiricalRademacherComplexity ℓ S' =
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ S' σ i) := rfl
  have h_rhs_S : empiricalRademacherComplexity ℓ S =
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ S σ i) := rfl
  rw [h_rhs_S', h_rhs_S]
  -- Rewrite LHS using `h_lhs_eq` so it matches Lemma 3a's LHS.
  have h_lhs_sum :
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ S S' =
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty
          (fun i => (n : ℝ)⁻¹ *
            (signedEmpiricalSum ℓ S' σ i - signedEmpiricalSum ℓ S σ i)) := by
    congr 1
    exact Finset.sum_congr rfl (fun σ _ => h_lhs_eq σ)
  rw [h_lhs_sum]
  exact finiteSampleSymmetrizationFactorTwo_div_n (ι := ι) (n := n) ℓ S S'

/-! ### Boundedness and measurability helpers for the final theorem -/

omit [Fintype ι] [Nonempty ι] in
/-- Bound `|signedEmpiricalSum ℓ z σ i| ≤ n * B` when `|ℓ i z| ≤ B`. -/
private lemma abs_signedEmpiricalSum_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (z : Fin n → Z) (σ : Fin n → Bool) (i : ι) :
    |signedEmpiricalSum ℓ z σ i| ≤ (n : ℝ) * B := by
  unfold signedEmpiricalSum
  calc |∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)|
      ≤ ∑ k : Fin n, |signOfBool (σ k) * ℓ i (z k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |signOfBool (σ k)| * |ℓ i (z k)| := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact abs_mul _ _
    _ = ∑ k : Fin n, |ℓ i (z k)| := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [abs_signOfBool, one_mul]
    _ ≤ ∑ _k : Fin n, B := Finset.sum_le_sum (fun k _ => hℓ_bdd i (z k))
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Boundedness of `empiricalRademacherComplexity` by `B`. -/
lemma abs_empiricalRademacherComplexity_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (_hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) (z : Fin n → Z) :
    |empiricalRademacherComplexity ℓ z| ≤ B := by
  -- Step: show inner `sup_i (1/n) signedEmpiricalSum ℓ z σ i` ∈ [-B, B] for each σ.
  -- Then `|∑_σ inner_σ| ≤ 2^n * B`, and `(2^n)⁻¹ · 2^n · B = B`.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have h_inner_le : ∀ σ : Fin n → Bool,
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i) ≤ B := by
    intro σ
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    have h_abs := abs_signedEmpiricalSum_le (n := n) hℓ_bdd z σ i
    have h1 : (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i ≤
              (n : ℝ)⁻¹ * |signedEmpiricalSum ℓ z σ i| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hn_pos.le)
    have h2 : (n : ℝ)⁻¹ * |signedEmpiricalSum ℓ z σ i| ≤
              (n : ℝ)⁻¹ * ((n : ℝ) * B) :=
      mul_le_mul_of_nonneg_left h_abs (inv_nonneg.mpr hn_pos.le)
    have h3 : (n : ℝ)⁻¹ * ((n : ℝ) * B) = B := by field_simp
    linarith
  have h_inner_ge : ∀ σ : Fin n → Bool,
      -B ≤
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i) := by
    intro σ
    have h_le_sup :
        (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i₀ ≤
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i) :=
      Finset.le_sup' (f := fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i)
        (s := (Finset.univ : Finset ι)) (Finset.mem_univ i₀)
    have h_abs := abs_signedEmpiricalSum_le (n := n) hℓ_bdd z σ i₀
    have h1 : -((n : ℝ) * B) ≤ signedEmpiricalSum ℓ z σ i₀ := by
      linarith [abs_le.mp h_abs]
    have h2 : (n : ℝ)⁻¹ * (-((n : ℝ) * B)) ≤
              (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i₀ :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn_pos.le)
    have h3 : (n : ℝ)⁻¹ * (-((n : ℝ) * B)) = -B := by field_simp
    linarith
  -- Sum over σ: 2^n terms each in [-B, B], so |∑_σ| ≤ 2^n * B.
  have h_sum_abs :
      |∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i)|
        ≤ ((2 : ℝ) ^ n) * B := by
    have h_card_real : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = (2 : ℝ) ^ n := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      push_cast
      rfl
    calc |∑ σ : Fin n → Bool,
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty
            (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i)|
        ≤ ∑ σ : Fin n → Bool,
            |(Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => (n : ℝ)⁻¹ * signedEmpiricalSum ℓ z σ i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Fin n → Bool, B :=
          Finset.sum_le_sum (fun σ _ => abs_le.mpr ⟨h_inner_ge σ, h_inner_le σ⟩)
      _ = ((2 : ℝ) ^ n) * B := by
          rw [Finset.sum_const, nsmul_eq_mul, h_card_real]
  -- Now |empRC| = (2^n)⁻¹ * |∑_σ ...| ≤ (2^n)⁻¹ * 2^n * B = B.
  unfold empiricalRademacherComplexity
  rw [abs_mul, abs_inv, abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)]
  have h_two_pow_pos : (0 : ℝ) < (2 : ℝ) ^ n :=
    pow_pos (by norm_num : (0 : ℝ) < 2) n
  calc ((2 : ℝ) ^ n)⁻¹ * |∑ σ : Fin n → Bool, _|
      ≤ ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * B) :=
        mul_le_mul_of_nonneg_left h_sum_abs (inv_nonneg.mpr h_two_pow_pos.le)
    _ = B := by field_simp

/-- Boundedness of `signedDecoupledGap` by `2 * B`. -/
private lemma abs_signedDecoupledGap_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (_hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) (σ : Fin n → Bool) (S S' : Fin n → Z) :
    |signedDecoupledGap ℓ σ S S'| ≤ 2 * B := by
  -- Each inner term `(n)⁻¹ * ∑_k σ_k (ℓ_i S'_k - ℓ_i S_k)` is bounded by 2B.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have h_each_abs : ∀ i : ι,
      |(n : ℝ)⁻¹ *
        ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))| ≤ 2 * B := by
    intro i
    rw [abs_mul, abs_inv, abs_of_nonneg hn_pos.le]
    have h_sum_abs :
        |∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))|
          ≤ (n : ℝ) * (2 * B) := by
      calc |∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))|
          ≤ ∑ k : Fin n, |signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ℓ i (S' k) - ℓ i (S k)| := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [abs_mul, abs_signOfBool, one_mul]
        _ ≤ ∑ _k : Fin n, 2 * B :=
            Finset.sum_le_sum (fun k _ => by
              have h1 := hℓ_bdd i (S' k)
              have h2 := hℓ_bdd i (S k)
              have := abs_sub (ℓ i (S' k)) (ℓ i (S k))
              linarith)
        _ = (n : ℝ) * (2 * B) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h_le : (n : ℝ)⁻¹ *
        |∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))|
          ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (2 * B)) :=
      mul_le_mul_of_nonneg_left h_sum_abs (inv_nonneg.mpr hn_pos.le)
    have h_eq : (n : ℝ)⁻¹ * ((n : ℝ) * (2 * B)) = 2 * B := by field_simp
    linarith
  -- Apply the bound on each i to bound the sup'.
  unfold signedDecoupledGap
  have h_le : (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => (n : ℝ)⁻¹ *
        ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))) ≤ 2 * B := by
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    linarith [abs_le.mp (h_each_abs i)]
  have h_ge : -(2 * B) ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => (n : ℝ)⁻¹ *
        ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))) := by
    have h_le_sup :
        (n : ℝ)⁻¹ *
          ∑ k : Fin n, signOfBool (σ k) * (ℓ i₀ (S' k) - ℓ i₀ (S k))
          ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => (n : ℝ)⁻¹ *
                ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k))) :=
      Finset.le_sup' (f := fun i => (n : ℝ)⁻¹ *
        ∑ k : Fin n, signOfBool (σ k) * (ℓ i (S' k) - ℓ i (S k)))
        (s := (Finset.univ : Finset ι)) (Finset.mem_univ i₀)
    linarith [abs_le.mp (h_each_abs i₀)]
  rw [abs_le]
  exact ⟨h_ge, h_le⟩

/-- Joint measurability of `signedDecoupledGap ℓ σ p.1 p.2` as a function
of `p : (Fin n → Z) × (Fin n → Z)`, for any fixed sign vector `σ`. -/
private lemma measurable_signedDecoupledGap
    [MeasurableSpace Z] {ℓ : ι → Z → ℝ}
    (hℓ_meas : ∀ i, Measurable (ℓ i)) (σ : Fin n → Bool) :
    Measurable
      (fun p : (Fin n → Z) × (Fin n → Z) =>
        signedDecoupledGap ℓ σ p.1 p.2) := by
  -- Each per-`i` inner integrand is jointly measurable in p.
  have h_each : ∀ i : ι,
      Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        (n : ℝ)⁻¹ *
          ∑ k : Fin n, signOfBool (σ k) * (ℓ i (p.2 k) - ℓ i (p.1 k))) := by
    intro i
    refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.const_mul ?_ (signOfBool (σ k))
    refine Measurable.sub ?_ ?_
    · exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_snd)
    · exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_fst)
  -- Bridge sup'-of-functions to the pointwise form.
  have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
    (f := fun i (p : (Fin n → Z) × (Fin n → Z)) =>
      (n : ℝ)⁻¹ *
        ∑ k : Fin n, signOfBool (σ k) * (ℓ i (p.2 k) - ℓ i (p.1 k)))
    Finset.univ_nonempty (fun i _ => h_each i)
  convert h_pi using 1
  ext p
  unfold signedDecoupledGap
  simp [Finset.sup'_apply]

/-- Measurability of `empiricalRademacherComplexity ℓ z` as a function of
`z`. -/
lemma measurable_empiricalRademacherComplexity
    [MeasurableSpace Z] {ℓ : ι → Z → ℝ}
    (hℓ_meas : ∀ i, Measurable (ℓ i)) :
    Measurable
      (fun z : Fin n → Z => empiricalRademacherComplexity ℓ z) := by
  unfold empiricalRademacherComplexity
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  -- Each per-σ sup' is measurable in z.
  have h_each : ∀ i : ι,
      Measurable (fun z : Fin n → Z =>
        (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)) := by
    intro i
    refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.const_mul ?_ (signOfBool (σ k))
    exact (hℓ_meas i).comp (measurable_pi_apply k)
  have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
    (f := fun i (z : Fin n → Z) =>
      (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
    Finset.univ_nonempty (fun i _ => h_each i)
  convert h_pi using 1
  ext z
  simp [Finset.sup'_apply]

/-- Bounded measurable function is integrable on a finite measure (a
local re-statement to avoid private import). -/
private lemma integrable_of_bounded_meas {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} {B : ℝ} (hf_meas : Measurable f) (hf_bdd : ∀ a, |f a| ≤ B) :
    Integrable f ν := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := B) ?_
  refine Filter.Eventually.of_forall (fun a => ?_)
  exact (Real.norm_eq_abs (f a)) ▸ hf_bdd a

/-! ### Stage 2 final theorem -/

/-- **Stage 2 final theorem: expected decoupled gap ≤ 2 × expected
empirical Rademacher complexity.**

For a finite, nonempty hypothesis class with bounded measurable
real-valued losses against an iid sample of size `n ≥ 1` from a
probability measure `μ`, the expected supremum of the ghost-sample-
minus-sample empirical-risk gap is bounded by twice the expected
empirical Rademacher complexity of the loss class on a single sample.

This is the symmetrization step of statistical learning theory in
expectation, finite hypothesis-class, finite-sample, bounded-loss
form. No high-probability rearrangement, no McDiarmid, no contraction
lemma, no VC. -/
theorem expected_decoupledGap_le_two_expected_empiricalRademacherComplexity
    [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) :
    ∫ p, decoupledGap ℓ p.1 p.2 ∂((piMeasure μ n).prod (piMeasure μ n))
      ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by
  -- Set up product probability measure (so SigmaFinite is automatic).
  haveI : IsProbabilityMeasure (piMeasure μ n) := by
    unfold piMeasure; infer_instance
  haveI : SigmaFinite (piMeasure μ n) := by infer_instance
  haveI : IsProbabilityMeasure
      ((piMeasure μ n).prod (piMeasure μ n)) := by infer_instance
  -- Integrability bookkeeping. Use bounded-measurable on the finite measure.
  -- LHS integrand integrability.
  have h_decoupled_meas :
      Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        decoupledGap ℓ p.1 p.2) := by
    -- Build measurability via `Finset.measurable_sup'` (mirrors Stage 1).
    have h_each : ∀ i : ι,
        Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
          Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i) := by
      intro i
      refine Measurable.sub ?_ ?_
      · unfold Risk.empiricalRisk
        refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
        refine Finset.measurable_sum _ (fun k _ => ?_)
        exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_snd)
      · unfold Risk.empiricalRisk
        refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
        refine Finset.measurable_sum _ (fun k _ => ?_)
        exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_fst)
    have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
      (f := fun i (p : (Fin n → Z) × (Fin n → Z)) =>
        Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i)
      Finset.univ_nonempty (fun i _ => h_each i)
    convert h_pi using 1
    ext p
    unfold decoupledGap
    simp [Finset.sup'_apply]
  -- Boundedness of decoupledGap (replicates Stage 1's `abs_decoupledGap_le`).
  have h_decoupled_bdd : ∀ p : (Fin n → Z) × (Fin n → Z),
      |decoupledGap ℓ p.1 p.2| ≤ 2 * B := by
    intro p
    have h_each_le_2B : ∀ i : ι,
        Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i ≤ 2 * B := by
      intro i
      unfold Risk.empiricalRisk
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h_S2 : (n : ℝ)⁻¹ * ∑ k, ℓ i (p.2 k) ≤ B := by
        have h_abs : |∑ k : Fin n, ℓ i (p.2 k)| ≤ (n : ℝ) * B := by
          calc |∑ k : Fin n, ℓ i (p.2 k)|
              ≤ ∑ k : Fin n, |ℓ i (p.2 k)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, B :=
                Finset.sum_le_sum (fun k _ => hℓ_bdd i (p.2 k))
            _ = (n : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
        have := mul_le_mul_of_nonneg_left
          (le_abs_self (∑ k : Fin n, ℓ i (p.2 k))) (inv_nonneg.mpr hn_pos.le)
        have h2 := mul_le_mul_of_nonneg_left h_abs (inv_nonneg.mpr hn_pos.le)
        have h3 : (n : ℝ)⁻¹ * ((n : ℝ) * B) = B := by field_simp
        linarith
      have h_S1 : -B ≤ (n : ℝ)⁻¹ * ∑ k, ℓ i (p.1 k) := by
        have h_abs : |∑ k : Fin n, ℓ i (p.1 k)| ≤ (n : ℝ) * B := by
          calc |∑ k : Fin n, ℓ i (p.1 k)|
              ≤ ∑ k : Fin n, |ℓ i (p.1 k)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, B :=
                Finset.sum_le_sum (fun k _ => hℓ_bdd i (p.1 k))
            _ = (n : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
        have h1 : -((n : ℝ) * B) ≤ ∑ k : Fin n, ℓ i (p.1 k) := by
          linarith [abs_le.mp h_abs]
        have h2 : (n : ℝ)⁻¹ * (-((n : ℝ) * B))
                  ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ i (p.1 k) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn_pos.le)
        have h3 : (n : ℝ)⁻¹ * (-((n : ℝ) * B)) = -B := by field_simp
        linarith
      linarith
    have h_each_ge_neg_2B : ∀ i : ι,
        -(2 * B) ≤ Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i := by
      intro i
      unfold Risk.empiricalRisk
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h_S2_ge : -B ≤ (n : ℝ)⁻¹ * ∑ k, ℓ i (p.2 k) := by
        have h_abs : |∑ k : Fin n, ℓ i (p.2 k)| ≤ (n : ℝ) * B := by
          calc |∑ k : Fin n, ℓ i (p.2 k)|
              ≤ ∑ k : Fin n, |ℓ i (p.2 k)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, B :=
                Finset.sum_le_sum (fun k _ => hℓ_bdd i (p.2 k))
            _ = (n : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
        have h1 : -((n : ℝ) * B) ≤ ∑ k : Fin n, ℓ i (p.2 k) := by
          linarith [abs_le.mp h_abs]
        have h2 : (n : ℝ)⁻¹ * (-((n : ℝ) * B))
                  ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ i (p.2 k) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn_pos.le)
        have h3 : (n : ℝ)⁻¹ * (-((n : ℝ) * B)) = -B := by field_simp
        linarith
      have h_S1_le : (n : ℝ)⁻¹ * ∑ k, ℓ i (p.1 k) ≤ B := by
        have h_abs : |∑ k : Fin n, ℓ i (p.1 k)| ≤ (n : ℝ) * B := by
          calc |∑ k : Fin n, ℓ i (p.1 k)|
              ≤ ∑ k : Fin n, |ℓ i (p.1 k)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, B :=
                Finset.sum_le_sum (fun k _ => hℓ_bdd i (p.1 k))
            _ = (n : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
        have := mul_le_mul_of_nonneg_left
          (le_abs_self (∑ k : Fin n, ℓ i (p.1 k))) (inv_nonneg.mpr hn_pos.le)
        have h2 := mul_le_mul_of_nonneg_left h_abs (inv_nonneg.mpr hn_pos.le)
        have h3 : (n : ℝ)⁻¹ * ((n : ℝ) * B) = B := by field_simp
        linarith
      linarith
    have h_le : decoupledGap ℓ p.1 p.2 ≤ 2 * B := by
      unfold decoupledGap
      exact Finset.sup'_le _ _ (fun i _ => h_each_le_2B i)
    have h_ge : -(2 * B) ≤ decoupledGap ℓ p.1 p.2 := by
      unfold decoupledGap
      obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
      have h_le_sup :
          Risk.empiricalRisk p.2 ℓ i₀ - Risk.empiricalRisk p.1 ℓ i₀
            ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty
                (fun i => Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i) :=
        Finset.le_sup'
          (f := fun j => Risk.empiricalRisk p.2 ℓ j - Risk.empiricalRisk p.1 ℓ j)
          (s := (Finset.univ : Finset ι)) (Finset.mem_univ i₀)
      linarith [h_each_ge_neg_2B i₀]
    rw [abs_le]
    exact ⟨h_ge, h_le⟩
  have h_decoupled_int :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        decoupledGap ℓ p.1 p.2) ((piMeasure μ n).prod (piMeasure μ n)) :=
    integrable_of_bounded_meas (B := 2 * B) _ h_decoupled_meas h_decoupled_bdd
  -- Integrability of `signedDecoupledGap σ` for each σ.
  have h_signed_int : ∀ σ : Fin n → Bool,
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        signedDecoupledGap ℓ σ p.1 p.2)
        ((piMeasure μ n).prod (piMeasure μ n)) := by
    intro σ
    refine integrable_of_bounded_meas (B := 2 * B) _
      (measurable_signedDecoupledGap hℓ_meas σ) ?_
    intro p
    exact abs_signedDecoupledGap_le hB hℓ_bdd hn σ p.1 p.2
  -- Integrability of `empiricalRademacherComplexity ℓ z` over `piMeasure μ n`.
  have h_empRC_int :
      Integrable (fun z : Fin n → Z => empiricalRademacherComplexity ℓ z)
        (piMeasure μ n) := by
    refine integrable_of_bounded_meas (B := B) _
      (measurable_empiricalRademacherComplexity hℓ_meas) ?_
    intro z
    exact abs_empiricalRademacherComplexity_le hB hℓ_bdd hn z
  -- Integrability of `empiricalRademacherComplexity ℓ p.1` and `p.2`
  -- on the product (composition with measurable projections).
  have h_empRC_int_left :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        empiricalRademacherComplexity ℓ p.1)
        ((piMeasure μ n).prod (piMeasure μ n)) := by
    refine integrable_of_bounded_meas (B := B) _
      ((measurable_empiricalRademacherComplexity hℓ_meas).comp measurable_fst)
      ?_
    intro p
    exact abs_empiricalRademacherComplexity_le hB hℓ_bdd hn p.1
  have h_empRC_int_right :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        empiricalRademacherComplexity ℓ p.2)
        ((piMeasure μ n).prod (piMeasure μ n)) := by
    refine integrable_of_bounded_meas (B := B) _
      ((measurable_empiricalRademacherComplexity hℓ_meas).comp measurable_snd)
      ?_
    intro p
    exact abs_empiricalRademacherComplexity_le hB hℓ_bdd hn p.2
  -- Step A: σ-averaging trick — `∫ decoupledGap = ∫ avg-of-signed`.
  set ν : Measure ((Fin n → Z) × (Fin n → Z)) :=
    (piMeasure μ n).prod (piMeasure μ n) with hν_def
  have h_two_pow_ne : ((2 : ℝ) ^ n) ≠ 0 := by
    exact ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) n)
  have h_card_real : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = (2 : ℝ) ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rfl
  have h_avg :
      ∫ p, decoupledGap ℓ p.1 p.2 ∂ν =
        ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          ∫ p, signedDecoupledGap ℓ σ p.1 p.2 ∂ν := by
    -- Each ∫ signedDecoupledGap σ = ∫ decoupledGap by Lemma 2.
    have h_each : ∀ σ : Fin n → Bool,
        ∫ p, signedDecoupledGap ℓ σ p.1 p.2 ∂ν =
          ∫ p, decoupledGap ℓ p.1 p.2 ∂ν := by
      intro σ
      symm
      exact expected_decoupledGap_eq_expected_signedDecoupledGap μ ℓ σ
    rw [Finset.sum_congr rfl (fun σ _ => h_each σ)]
    rw [Finset.sum_const, nsmul_eq_mul, h_card_real]
    field_simp
  -- Step B: pull (2^n)⁻¹ * ∑_σ inside the integral.
  have h_avg_inside :
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          ∫ p, signedDecoupledGap ℓ σ p.1 p.2 ∂ν =
        ∫ p, ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ p.1 p.2 ∂ν := by
    rw [← integral_finsetSum (Finset.univ : Finset (Fin n → Bool))
        (fun σ _ => h_signed_int σ)]
    rw [integral_const_mul]
  -- Step C: Lemma 3b pointwise + integral_mono.
  have h_pointwise : ∀ p : (Fin n → Z) × (Fin n → Z),
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ p.1 p.2
        ≤ empiricalRademacherComplexity ℓ p.2 +
          empiricalRademacherComplexity ℓ p.1 := by
    intro p
    exact signedDecoupledGap_avg_le_two_empiricalRademacher ℓ p.1 p.2
  -- Need integrability of the LHS (avg of signedDecoupledGap).
  have h_avg_int :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ p.1 p.2) ν := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum (Finset.univ : Finset (Fin n → Bool))
      (fun σ _ => h_signed_int σ)
  have h_rhs_int :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        empiricalRademacherComplexity ℓ p.2 +
          empiricalRademacherComplexity ℓ p.1) ν :=
    Integrable.add h_empRC_int_right h_empRC_int_left
  have h_int_le :
      ∫ p, ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ p.1 p.2 ∂ν
        ≤ ∫ p, empiricalRademacherComplexity ℓ p.2 +
              empiricalRademacherComplexity ℓ p.1 ∂ν :=
    integral_mono h_avg_int h_rhs_int h_pointwise
  -- Step D: split the RHS integral.
  have h_split :
      ∫ p, empiricalRademacherComplexity ℓ p.2 +
            empiricalRademacherComplexity ℓ p.1 ∂ν =
        (∫ p, empiricalRademacherComplexity ℓ p.2 ∂ν) +
          ∫ p, empiricalRademacherComplexity ℓ p.1 ∂ν :=
    integral_add h_empRC_int_right h_empRC_int_left
  -- Step E: marginalize each: integrating a function of `p.1` against
  -- the prod measure equals integrating against the left marginal.
  -- Use `integral_prod` (Fubini) — for an integrable function depending
  -- only on one coordinate, the inner integral is constant.
  have h_marg_left :
      ∫ p, empiricalRademacherComplexity ℓ p.1 ∂ν =
        ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by
    rw [hν_def]
    rw [MeasureTheory.integral_prod _ h_empRC_int_left]
    -- Inner integral over p.2 is constant since the integrand depends only on p.1.
    simp [integral_const]
  have h_marg_right :
      ∫ p, empiricalRademacherComplexity ℓ p.2 ∂ν =
        ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by
    rw [hν_def]
    rw [MeasureTheory.integral_prod _ h_empRC_int_right]
    -- Now inner integral is over p.2, depends only on p.2; outer constant.
    simp
  -- Combine all steps.
  rw [h_avg, h_avg_inside]
  calc ∫ p, ((2 : ℝ) ^ n)⁻¹ *
        ∑ σ : Fin n → Bool, signedDecoupledGap ℓ σ p.1 p.2 ∂ν
      ≤ ∫ p, empiricalRademacherComplexity ℓ p.2 +
            empiricalRademacherComplexity ℓ p.1 ∂ν := h_int_le
    _ = (∫ p, empiricalRademacherComplexity ℓ p.2 ∂ν) +
          ∫ p, empiricalRademacherComplexity ℓ p.1 ∂ν := h_split
    _ = (∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n)) +
          ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by
            rw [h_marg_left, h_marg_right]
    _ = 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by ring

end FormalSLT.Rademacher.Decoupling
