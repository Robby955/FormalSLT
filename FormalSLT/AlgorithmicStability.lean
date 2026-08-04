/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.HasBoundedDifferences
import FormalSLT.Risk
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Algorithmic stability and generalization

Formalizes the **uniform stability** framework of Bousquet-Elisseeff
(2002). An algorithm `A : (Fin n → Z) → ι` has uniform stability `β`
if replacing any single training point changes the loss of the selected
hypothesis on any test point by at most `β`.

## What is proved (all closed, no sorry)

* `UniformStability A ℓ β`: the stability predicate.
* `trainingLoss_hasBoundedDifferences`: stability + bounded loss
  imply bounded differences with constant `β + 2B/n` for the training
  loss. This can be fed to bounded-differences concentration tails.
* `stability_genGap_hasBoundedDifferences`: the generalization gap
  `R(A(S)) - trainingLoss(A,S)` has bounded differences with constant
  `2β + 2B/n`. It feeds into the sharp McDiarmid stability wrappers.
* `expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap` :
  finite expected-gap adapter: under finite sample weights and a
  finite coordinate-swap identity, uniform stability gives expected gap `≤ β`.
* `expectedFiniteStabilityGap_le_uniformStability_finiteProduct` :
  finite iid product-weight specialization: the coordinate-swap identity is
  proved by an explicit finite reindexing argument.
* `abs_expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct` :
  finite iid two-sided expected generalization-gap bound:
  `|E_S[R(A(S)) - Rhat_S(A(S))]| ≤ β`.
* `abs_expectedStabilityGap_le_uniformStability_piMeasure` :
  measure-theoretic iid two-sided expected generalization-gap bound over
  `Measure.pi`, with explicit integrability assumptions on the selected
  losses induced by the algorithm.
* `abs_expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss` :
  finite-class bounded-loss adapter that discharges those integrability
  assumptions from measurability of `A` and the per-hypothesis losses.
-/

namespace FormalSLT.AlgorithmicStability

open FormalSLT.Risk
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)
open MeasureTheory
open scoped BigOperators

variable {ι Z : Type*} [Fintype ι]

/-! ### Uniform stability predicate -/

/-- An algorithm `A` has **uniform stability** `β` if replacing any
single training example changes the selected hypothesis's loss on any
test point by at most `β` in absolute value. -/
def UniformStability {n : ℕ}
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) (β : ℝ) : Prop :=
  ∀ (S : Fin n → Z) (k : Fin n) (z' : Z) (z : Z),
    |ℓ (A S) z - ℓ (A (Function.update S k z')) z| ≤ β

omit [Fintype ι] in
/-- Negating the loss preserves uniform stability with the same `β`. -/
lemma uniformStability_neg {n : ℕ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β) :
    UniformStability A (fun i z => -ℓ i z) β := by
  intro S k z' z
  have h := hstab S k z' z
  have h_eq :
      -ℓ (A S) z - -ℓ (A (Function.update S k z')) z =
        -(ℓ (A S) z - ℓ (A (Function.update S k z')) z) := by
    ring
  rw [h_eq, abs_neg]
  exact h

/-! ### Training loss -/

/-- Training loss: empirical risk of the algorithm-selected hypothesis
on the training data. `trainingLoss A ℓ S = (1/n) ∑_k ℓ(A(S), S(k))` -/
noncomputable def trainingLoss {n : ℕ}
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) (S : Fin n → Z) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ (A S) (S k)

/-! ### Measure-theoretic coordinate swap -/

omit [Fintype ι] in
/-- Swap sample coordinate `k` with an auxiliary fresh draw.

This is the measure-theoretic analogue of `finiteCoordinateSwapEquiv`: a pair
`(S, z)` is sent to `(Function.update S k z, S k)`. Under the iid product
measure `μⁿ × μ`, this map preserves measure. -/
def sampleCoordinateSwap {n : ℕ} (k : Fin n) :
    ((Fin n → Z) × Z) → ((Fin n → Z) × Z) :=
  fun P => (Function.update P.1 k P.2, P.1 k)

omit [Fintype ι] in
/-- The sample-coordinate swap is its own inverse. -/
lemma sampleCoordinateSwap_involutive {n : ℕ} (k : Fin n) :
    Function.Involutive (sampleCoordinateSwap (Z := Z) k) := by
  intro P
  rcases P with ⟨S, z⟩
  apply Prod.ext
  · funext j
    by_cases hj : j = k
    · subst j
      simp [sampleCoordinateSwap]
    · simp [sampleCoordinateSwap]
  · simp [sampleCoordinateSwap]

omit [Fintype ι] in
/-- Measurability of the sample-coordinate swap. -/
lemma measurable_sampleCoordinateSwap [MeasurableSpace Z] {n : ℕ} (k : Fin n) :
    Measurable (sampleCoordinateSwap (Z := Z) k) := by
  refine Measurable.prod ?_ ?_
  · rw [measurable_pi_iff]
    intro j
    by_cases hj : j = k
    · subst j
      simpa [sampleCoordinateSwap] using
        (measurable_snd : Measurable (fun P : (Fin n → Z) × Z => P.2))
    · simp only [sampleCoordinateSwap, Function.update_of_ne hj]
      fun_prop
  · simp only [sampleCoordinateSwap]
    fun_prop

omit [Fintype ι] in
/-- The sample-coordinate swap as a measurable equivalence. -/
def sampleCoordinateSwapEquiv [MeasurableSpace Z] {n : ℕ} (k : Fin n) :
    ((Fin n → Z) × Z) ≃ᵐ ((Fin n → Z) × Z) where
  toFun := sampleCoordinateSwap (Z := Z) k
  invFun := sampleCoordinateSwap (Z := Z) k
  left_inv := sampleCoordinateSwap_involutive (Z := Z) k
  right_inv := sampleCoordinateSwap_involutive (Z := Z) k
  measurable_toFun := measurable_sampleCoordinateSwap (Z := Z) k
  measurable_invFun := measurable_sampleCoordinateSwap (Z := Z) k

omit [Fintype ι] in
private abbrev optionCoordinateSwap {n : ℕ} (k : Fin n) :
    Option (Fin n) ≃ Option (Fin n) :=
  Equiv.swap none (some k)

omit [Fintype ι] in
private lemma piOptionEquivProd_apply_fst [MeasurableSpace Z] {n : ℕ}
    (f : Option (Fin n) → Z) (j : Fin n) :
    ((MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) => Z)) f).1 j = f (some j) := by
  change ((Equiv.piOptionEquivProd
    (β := fun _ : Option (Fin n) => Z)) f).2 j = f (some j)
  rfl

omit [Fintype ι] in
private lemma piOptionEquivProd_apply_snd [MeasurableSpace Z] {n : ℕ}
    (f : Option (Fin n) → Z) :
    ((MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) => Z)) f).2 = f none := by
  change ((Equiv.piOptionEquivProd
    (β := fun _ : Option (Fin n) => Z)) f).1 = f none
  rfl

omit [Fintype ι] in
private lemma piOptionEquivProd_symm_apply_none [MeasurableSpace Z] {n : ℕ}
    (S : Fin n → Z) (z : Z) :
    ((MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) => Z)).symm (S, z)) none = z := by
  change ((Equiv.piOptionEquivProd
    (β := fun _ : Option (Fin n) => Z)).symm (z, S)) none = z
  rfl

omit [Fintype ι] in
private lemma piOptionEquivProd_symm_apply_some [MeasurableSpace Z] {n : ℕ}
    (S : Fin n → Z) (z : Z) (j : Fin n) :
    ((MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) => Z)).symm (S, z)) (some j) = S j := by
  change ((Equiv.piOptionEquivProd
    (β := fun _ : Option (Fin n) => Z)).symm (z, S)) (some j) = S j
  rfl

omit [Fintype ι] in
private lemma sampleCoordinateSwap_eq_piOption [MeasurableSpace Z] {n : ℕ} (k : Fin n) :
    sampleCoordinateSwap (Z := Z) k =
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Z)) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin n) => Z)
          (optionCoordinateSwap k)) ∘
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Z)).symm := by
  funext P
  rcases P with ⟨S, z⟩
  apply Prod.ext
  · funext j
    dsimp [sampleCoordinateSwap]
    rw [piOptionEquivProd_apply_fst]
    by_cases hj : j = k
    · subst j
      rw [Function.update_self]
      calc
        z = ((MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => Z)).symm (S, z)) none :=
            (piOptionEquivProd_symm_apply_none S z).symm
        _ = ((MeasurableEquiv.piCongrLeft (fun _ : Option (Fin n) => Z)
                (optionCoordinateSwap k))
              ((MeasurableEquiv.piOptionEquivProd
                (fun _ : Option (Fin n) => Z)).symm (S, z))) (some k) := by
            have happ := (MeasurableEquiv.piCongrLeft_apply_apply
              (e := optionCoordinateSwap k)
              (β := fun _ : Option (Fin n) => Z)
              ((MeasurableEquiv.piOptionEquivProd
                (fun _ : Option (Fin n) => Z)).symm (S, z))
              none).symm
            simpa [optionCoordinateSwap] using happ
    · rw [Function.update_of_ne hj]
      have hswap : optionCoordinateSwap k (some j) = some j := by
        exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hj])
      calc
        S j = ((MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => Z)).symm (S, z)) (some j) :=
            (piOptionEquivProd_symm_apply_some S z j).symm
        _ = ((MeasurableEquiv.piCongrLeft (fun _ : Option (Fin n) => Z)
                (optionCoordinateSwap k))
              ((MeasurableEquiv.piOptionEquivProd
                (fun _ : Option (Fin n) => Z)).symm (S, z))) (some j) := by
            have happ := (MeasurableEquiv.piCongrLeft_apply_apply
              (e := optionCoordinateSwap k)
              (β := fun _ : Option (Fin n) => Z)
              ((MeasurableEquiv.piOptionEquivProd
                (fun _ : Option (Fin n) => Z)).symm (S, z))
              (some j)).symm
            simpa [hswap] using happ
  · dsimp [sampleCoordinateSwap]
    rw [piOptionEquivProd_apply_snd]
    calc
      S k = ((MeasurableEquiv.piOptionEquivProd
            (fun _ : Option (Fin n) => Z)).symm (S, z)) (some k) :=
          (piOptionEquivProd_symm_apply_some S z k).symm
      _ = ((MeasurableEquiv.piCongrLeft (fun _ : Option (Fin n) => Z)
              (optionCoordinateSwap k))
            ((MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => Z)).symm (S, z))) none := by
          have happ := (MeasurableEquiv.piCongrLeft_apply_apply
            (e := optionCoordinateSwap k)
            (β := fun _ : Option (Fin n) => Z)
            ((MeasurableEquiv.piOptionEquivProd
              (fun _ : Option (Fin n) => Z)).symm (S, z))
            (some k)).symm
          simpa [optionCoordinateSwap] using happ

omit [Fintype ι] in
/-- The sample-coordinate swap preserves the iid product measure `μⁿ × μ`.

Equivalently, replacing the `k`th coordinate by a fresh draw and carrying the
old coordinate as the auxiliary draw is just a finite coordinate permutation
of the product index set `Option (Fin n)`. -/
theorem measurePreserving_sampleCoordinateSwap [MeasurableSpace Z]
    (μ : Measure Z) [SigmaFinite μ] {n : ℕ} (k : Fin n) :
    MeasurePreserving (sampleCoordinateSwap (Z := Z) k)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  let eProd := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Z)
  let eSwap := MeasurableEquiv.piCongrLeft (fun _ : Option (Fin n) => Z)
    (optionCoordinateSwap k)
  have h_prod_to_pi : MeasurePreserving eProd.symm
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)
      (Measure.pi (fun _ : Option (Fin n) => μ)) := by
    refine ⟨eProd.symm.measurable, ?_⟩
    simpa [eProd] using
      (Measure.pi_map_piOptionEquivProd
        (μ := fun _ : Option (Fin n) => μ))
  have h_pi_to_prod : MeasurePreserving eProd
      (Measure.pi (fun _ : Option (Fin n) => μ))
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
    exact h_prod_to_pi.symm (e := eProd.symm)
  have h_reindex : MeasurePreserving eSwap
      (Measure.pi (fun _ : Option (Fin n) => μ))
      (Measure.pi (fun _ : Option (Fin n) => μ)) := by
    simpa [eSwap, optionCoordinateSwap] using
      (measurePreserving_piCongrLeft
        (μ := fun _ : Option (Fin n) => μ)
        (α := fun _ : Option (Fin n) => Z)
        (f := optionCoordinateSwap k))
  have h_comp : MeasurePreserving (eProd ∘ eSwap ∘ eProd.symm)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) :=
    h_pi_to_prod.comp (h_reindex.comp h_prod_to_pi)
  rw [sampleCoordinateSwap_eq_piOption (Z := Z) k]
  exact h_comp

omit [Fintype ι] in
/-- Integral invariance under the sample-coordinate swap. -/
theorem integral_sampleCoordinateSwap [MeasurableSpace Z]
    (μ : Measure Z) [SigmaFinite μ] {n : ℕ} (k : Fin n)
    (G : ((Fin n → Z) × Z) → ℝ) :
    ∫ P, G (sampleCoordinateSwap (Z := Z) k P)
        ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)
      = ∫ P, G P ∂((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  exact (measurePreserving_sampleCoordinateSwap (Z := Z) μ k).integral_comp
    (sampleCoordinateSwapEquiv (Z := Z) k).measurableEmbedding G

omit [Fintype ι] in
/-- Coordinate-swap integral identity in the update notation used by stability.

This is the measure-theoretic replacement for the finite sum reindexing used
by `finiteProductSampleWeight_coordinateSwapIdentity`. -/
theorem integral_update_eq_integral_coordinate [MeasurableSpace Z]
    (μ : Measure Z) [SigmaFinite μ] {n : ℕ} (k : Fin n)
    (G : (Fin n → Z) → Z → ℝ) :
    ∫ P : (Fin n → Z) × Z, G (Function.update P.1 k P.2) P.2
        ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)
      =
    ∫ P : (Fin n → Z) × Z, G P.1 (P.1 k)
        ∂((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  have h := integral_sampleCoordinateSwap (Z := Z) μ k
    (fun P : (Fin n → Z) × Z => G P.1 (P.1 k))
  simpa [sampleCoordinateSwap, Function.update_self] using h

omit [Fintype ι] in
/-- Measure-theoretic iid expected uniform-stability bound.

This is the iid product-measure lift of the finite coordinate-swap expected
gap argument. It is deliberately scoped to a finite sample `Fin n`, scalar
real-valued losses, an arbitrary data space with probability law `μ`, and
explicit integrability hypotheses for the selected-loss functions induced by
the learning algorithm `A`.

The proof is the Bousquet-Elisseeff coordinate-swap argument:
Fubini rewrites selected population risk as an integral over `μⁿ × μ`, uniform
stability compares it to the coordinate-replaced sample, and
`integral_update_eq_integral_coordinate` swaps the fresh draw back into the
training coordinate. -/
theorem expectedStabilityGap_le_uniformStability_piMeasure
    [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (h_loss_int : Integrable
      (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ))
    (h_update_int : ∀ k : Fin n, Integrable
      (fun P : (Fin n → Z) × Z => ℓ (A (Function.update P.1 k P.2)) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ))
    (h_coord_int : ∀ k : Fin n, Integrable
      (fun S : Fin n → Z => ℓ (A S) (S k))
      (Measure.pi (fun _ : Fin n => μ))) :
    ∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β := by
  let μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ)
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  have hrisk_eq :
      (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn) =
        ∫ P : (Fin n → Z) × Z, ℓ (A P.1) P.2
          ∂((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
    unfold risk μn
    exact integral_integral (μ := Measure.pi (fun _ : Fin n => μ)) (ν := μ)
      (f := fun S z => ℓ (A S) z) h_loss_int
  have hcoord_bound : ∀ k : Fin n,
      (∫ P : (Fin n → Z) × Z, ℓ (A P.1) P.2
          ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)) ≤
        (∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) + β := by
    intro k
    have hpoint : (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2) ≤
        (fun P : (Fin n → Z) × Z => ℓ (A (Function.update P.1 k P.2)) P.2 + β) := by
      intro P
      have h := hstab P.1 k P.2 P.2
      linarith [(abs_le.mp h).2]
    have hmono :
        (∫ P : (Fin n → Z) × Z, ℓ (A P.1) P.2
          ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)) ≤
          ∫ P : (Fin n → Z) × Z,
            (ℓ (A (Function.update P.1 k P.2)) P.2 + β)
            ∂((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
      exact integral_mono h_loss_int ((h_update_int k).add (integrable_const β)) hpoint
    have hright_eq :
        (∫ P : (Fin n → Z) × Z,
            (ℓ (A (Function.update P.1 k P.2)) P.2 + β)
              ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)) =
          (∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) + β := by
      calc
        (∫ P : (Fin n → Z) × Z,
            (ℓ (A (Function.update P.1 k P.2)) P.2 + β)
              ∂((Measure.pi (fun _ : Fin n => μ)).prod μ))
            = (∫ P : (Fin n → Z) × Z,
                ℓ (A (Function.update P.1 k P.2)) P.2
                  ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)) + β := by
                rw [integral_add (h_update_int k) (integrable_const β)]
                simp
        _ = (∫ P : (Fin n → Z) × Z, ℓ (A P.1) (P.1 k)
                ∂((Measure.pi (fun _ : Fin n => μ)).prod μ)) + β := by
                rw [integral_update_eq_integral_coordinate (Z := Z) μ k
                  (fun S z => ℓ (A S) z)]
        _ = (∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) + β := by
                congr 1
                simpa [μn] using (integral_fun_fst
                  (μ := Measure.pi (fun _ : Fin n => μ)) (ν := μ)
                  (f := fun S : Fin n → Z => ℓ (A S) (S k)))
    linarith
  have hrisk_repeat :
      (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn) =
        (n : ℝ)⁻¹ * ∑ _k : Fin n,
          (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn_real_ne]
  have havg :
      (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn) ≤
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          ((∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) + β) := by
    rw [hrisk_repeat]
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro k _hk
      rw [hrisk_eq]
      exact hcoord_bound k
    · exact inv_nonneg.mpr hn_real_pos.le
  have htrain_eq :
      (∫ S : Fin n → Z, trainingLoss A ℓ S ∂μn) =
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          ∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn := by
    unfold trainingLoss
    rw [integral_const_mul]
    congr 1
    simpa using
      (integral_finsetSum (μ := μn) (s := (Finset.univ : Finset (Fin n)))
        (f := fun k S => ℓ (A S) (S k))
        (by intro k _hk; exact h_coord_int k))
  have hselected_le :
      (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn) ≤
        (∫ S : Fin n → Z, trainingLoss A ℓ S ∂μn) + β := by
    calc
      (∫ S : Fin n → Z, risk μ ℓ (A S) ∂μn)
          ≤ (n : ℝ)⁻¹ * ∑ k : Fin n,
            ((∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) + β) := havg
      _ = (n : ℝ)⁻¹ *
            ((∑ k : Fin n, ∫ S : Fin n → Z, ℓ (A S) (S k) ∂μn) +
              ∑ _k : Fin n, β) := by rw [Finset.sum_add_distrib]
      _ = (∫ S : Fin n → Z, trainingLoss A ℓ S ∂μn) + β := by
            rw [mul_add, ← htrain_eq]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp [hn_real_ne]
  have hrisk_int : Integrable (fun S : Fin n → Z => risk μ ℓ (A S)) μn := by
    unfold risk μn
    exact h_loss_int.integral_prod_left
  have htrain_int : Integrable (fun S : Fin n → Z => trainingLoss A ℓ S) μn := by
    unfold trainingLoss
    exact (integrable_finsetSum (μ := μn) (s := (Finset.univ : Finset (Fin n)))
      (f := fun k S => ℓ (A S) (S k))
      (by intro k _hk; exact h_coord_int k)).const_mul _
  rw [integral_sub hrisk_int htrain_int]
  linarith

/-! ### Stability implies bounded differences -/

omit [Fintype ι] in
/-- Stability + bounded loss ⟹ bounded differences for training loss.
The width is `β + 2B/n`: stability contributes β (all terms shift), and
the evaluation-point change at coordinate k contributes 2B/n. -/
theorem trainingLoss_hasBoundedDifferences {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    HasBoundedDifferences (trainingLoss A ℓ) (fun _ : Fin n => β + 2 * B / ↑n) := by
  intro S k z'
  set S' := Function.update S k z'
  show |trainingLoss A ℓ S - trainingLoss A ℓ S'| ≤ β + 2 * B / ↑n
  unfold trainingLoss
  have hn_pos : (0 : ℝ) < ↑n := by exact_mod_cast hn
  -- Key: express difference as n⁻¹ * ∑ per-coordinate differences
  have h_sum_eq : ∑ j : Fin n, (ℓ (A S) (S j) - ℓ (A S') (S' j))
      = ∑ j : Fin n, ℓ (A S) (S j) - ∑ j : Fin n, ℓ (A S') (S' j) :=
    Finset.sum_sub_distrib (fun j => ℓ (A S) (S j)) (fun j => ℓ (A S') (S' j))
  have h_rewrite : (↑n)⁻¹ * ∑ j, ℓ (A S) (S j) - (↑n)⁻¹ * ∑ j, ℓ (A S') (S' j)
      = (↑n)⁻¹ * ∑ j : Fin n, (ℓ (A S) (S j) - ℓ (A S') (S' j)) := by
    rw [← mul_sub, ← h_sum_eq]
  rw [h_rewrite, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg (n := n))]
  -- Split the sum at coordinate k
  have h_split :
      ∑ j : Fin n, (ℓ (A S) (S j) - ℓ (A S') (S' j))
        = (ℓ (A S) (S k) - ℓ (A S') (S' k))
          + ∑ j ∈ Finset.univ.erase k, (ℓ (A S) (S j) - ℓ (A S') (S' j)) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)).symm
  -- Bound at k: ≤ β + 2B (stability + bounded loss)
  have h_k : |ℓ (A S) (S k) - ℓ (A S') (S' k)| ≤ β + 2 * B := by
    have hSk : S' k = z' := Function.update_self k z' S
    rw [hSk]
    have h_stab_part : |ℓ (A S) z' - ℓ (A S') z'| ≤ β := hstab S k z' z'
    have h_loss_part : |ℓ (A S) (S k) - ℓ (A S) z'| ≤ 2 * B := by
      have ha := hℓ_bdd (A S) (S k)
      have hb := hℓ_bdd (A S) z'
      have h1 : ℓ (A S) (S k) - ℓ (A S) z' ≤ 2 * B := by linarith [abs_le.mp ha, abs_le.mp hb]
      have h2 : -(2 * B) ≤ ℓ (A S) (S k) - ℓ (A S) z' := by linarith [abs_le.mp ha, abs_le.mp hb]
      exact abs_le.mpr ⟨h2, h1⟩
    -- Triangle: |a - c| = |(a - b) + (b - c)| ≤ |a - b| + |b - c|
    have h_tri : |ℓ (A S) (S k) - ℓ (A S') z'|
        ≤ |ℓ (A S) (S k) - ℓ (A S) z'| + |ℓ (A S) z' - ℓ (A S') z'| := by
      have h_id : ℓ (A S) (S k) - ℓ (A S') z'
          = (ℓ (A S) (S k) - ℓ (A S) z') + (ℓ (A S) z' - ℓ (A S') z') := by ring
      calc |ℓ (A S) (S k) - ℓ (A S') z'|
          = |(ℓ (A S) (S k) - ℓ (A S) z') + (ℓ (A S) z' - ℓ (A S') z')| := by rw [h_id]
        _ ≤ |ℓ (A S) (S k) - ℓ (A S) z'| + |ℓ (A S) z' - ℓ (A S') z'| := abs_add_le _ _
    linarith
  -- Bound off-k terms: each ≤ β (only hypothesis changes, test point unchanged)
  have h_off_k : ∀ j ∈ Finset.univ.erase k,
      |ℓ (A S) (S j) - ℓ (A S') (S' j)| ≤ β := by
    intro j hj
    have hSj : S' j = S j := by
      show (Function.update S k z') j = S j
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) z' S
    rw [hSj]; exact hstab S k z' (S j)
  -- Sum over off-k: ≤ (n-1)β
  have h_card : (Finset.univ.erase k : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have h_off_sum : |∑ j ∈ Finset.univ.erase k, (ℓ (A S) (S j) - ℓ (A S') (S' j))|
      ≤ (↑(n - 1) : ℝ) * β :=
    calc |∑ j ∈ Finset.univ.erase k, (ℓ (A S) (S j) - ℓ (A S') (S' j))|
        ≤ ∑ j ∈ Finset.univ.erase k, |ℓ (A S) (S j) - ℓ (A S') (S' j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, β := Finset.sum_le_sum h_off_k
      _ = (↑(n - 1) : ℝ) * β := by rw [Finset.sum_const, h_card, nsmul_eq_mul]
  -- Total bound: |sum| ≤ (β+2B) + (n-1)β = n(β + 2B/n)
  have h_total : |∑ j : Fin n, (ℓ (A S) (S j) - ℓ (A S') (S' j))|
      ≤ ↑n * (β + 2 * B / ↑n) := by
    rw [h_split]
    have h1 : |(ℓ (A S) (S k) - ℓ (A S') (S' k))
        + ∑ j ∈ Finset.univ.erase k, (ℓ (A S) (S j) - ℓ (A S') (S' j))|
        ≤ |ℓ (A S) (S k) - ℓ (A S') (S' k)|
          + |∑ j ∈ Finset.univ.erase k, (ℓ (A S) (S j) - ℓ (A S') (S' j))| :=
      abs_add_le _ _
    have h_arith : (β + 2 * B) + (↑(n - 1) : ℝ) * β = ↑n * (β + 2 * B / ↑n) := by
      rw [Nat.cast_sub (Nat.one_le_of_lt hn)]; field_simp; ring
    linarith
  -- Conclude: n⁻¹ * |sum| ≤ β + 2B/n
  calc (↑n)⁻¹ * |∑ j : Fin n, (ℓ (A S) (S j) - ℓ (A S') (S' j))|
      ≤ (↑n)⁻¹ * (↑n * (β + 2 * B / ↑n)) :=
        mul_le_mul_of_nonneg_left h_total (inv_nonneg.mpr hn_pos.le)
    _ = β + 2 * B / ↑n := by field_simp

/-! ### Generalization gap bounded differences -/

omit [Fintype ι] in
/-- The generalization gap `R(A(S)) - trainingLoss(A,S)` has bounded
differences with constant `2β + 2B/n`. The risk integral changes by
at most β (integrate the pointwise stability bound), and the training
loss changes by at most β + 2B/n. -/
theorem stability_genGap_hasBoundedDifferences
    [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hstab : UniformStability A ℓ β)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hℓ_int : ∀ i, Integrable (ℓ i) μ) :
    HasBoundedDifferences
      (fun S : Fin n → Z => ∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      (fun _ : Fin n => 2 * β + 2 * B / ↑n) := by
  intro S k z'
  set S' := Function.update S k z'
  show |(∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      - (∫ z, ℓ (A S') z ∂μ - trainingLoss A ℓ S')| ≤ 2 * β + 2 * B / ↑n
  -- Rearrange
  have h_eq : (∫ z, ℓ (A S) z ∂μ - trainingLoss A ℓ S)
      - (∫ z, ℓ (A S') z ∂μ - trainingLoss A ℓ S')
      = (∫ z, ℓ (A S) z ∂μ - ∫ z, ℓ (A S') z ∂μ)
        - (trainingLoss A ℓ S - trainingLoss A ℓ S') := by ring
  rw [h_eq]
  -- Bound |R(A(S)) - R(A(S'))| ≤ β via integral of stability
  have h_risk : |∫ z, ℓ (A S) z ∂μ - ∫ z, ℓ (A S') z ∂μ| ≤ β := by
    rw [← integral_sub (hℓ_int (A S)) (hℓ_int (A S'))]
    have h_norm := norm_integral_le_integral_norm
      (μ := μ) (f := fun z => ℓ (A S) z - ℓ (A S') z)
    have h_int_le : ∫ z, ‖ℓ (A S) z - ℓ (A S') z‖ ∂μ ≤ β := by
      have h_pw : ∀ z, ‖ℓ (A S) z - ℓ (A S') z‖ ≤ β := fun z => by
        rw [Real.norm_eq_abs]; exact hstab S k z' z
      calc ∫ z, ‖ℓ (A S) z - ℓ (A S') z‖ ∂μ
          ≤ ∫ _z, β ∂μ :=
            integral_mono_ae
              ((hℓ_int (A S)).sub (hℓ_int (A S'))).norm
              (integrable_const β)
              (Filter.Eventually.of_forall h_pw)
        _ = β := by rw [integral_const, probReal_univ, one_smul]
    rw [Real.norm_eq_abs] at h_norm
    linarith
  -- Bound |T(S) - T(S')| ≤ β + 2B/n (from trainingLoss_hasBoundedDifferences)
  have h_train : |trainingLoss A ℓ S - trainingLoss A ℓ S'| ≤ β + 2 * B / ↑n :=
    trainingLoss_hasBoundedDifferences hn hstab hℓ_bdd S k z'
  -- Triangle: |a - b| ≤ |a| + |b|
  have h_tri : |(∫ z, ℓ (A S) z ∂μ - ∫ z, ℓ (A S') z ∂μ)
      - (trainingLoss A ℓ S - trainingLoss A ℓ S')|
      ≤ |∫ z, ℓ (A S) z ∂μ - ∫ z, ℓ (A S') z ∂μ|
        + |trainingLoss A ℓ S - trainingLoss A ℓ S'| := by
    set a := ∫ z, ℓ (A S) z ∂μ - ∫ z, ℓ (A S') z ∂μ
    set b := trainingLoss A ℓ S - trainingLoss A ℓ S'
    have h_id : a - b = a + (-b) := sub_eq_add_neg a b
    calc |a - b| = |a + (-b)| := by rw [h_id]
      _ ≤ |a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg]
  linarith

/-! ### Finite expected stability adapter -/

omit [Fintype ι] in
/-- Finite population risk under an explicit finite probability mass function.

This is a finite-domain adapter for the expected-stability theorem below. It
does not replace the measure-theoretic `risk`; it makes the coordinate-swap
bookkeeping explicit while the full product-measure kernel decomposition is
developed separately. -/
noncomputable def finitePopulationRisk [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) : ℝ :=
  ∑ z : Z, p z * ℓ i z

omit [Fintype ι] in
/-- Finite expectation over samples with explicit sample weights. -/
noncomputable def finiteSampleExpectation {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (F : (Fin n → Z) → ℝ) : ℝ :=
  ∑ S : Fin n → Z, sampleWeight S * F S

omit [Fintype ι] in
/-- Expected risk of the hypothesis selected by `A` under finite sample
weights and a finite data distribution. -/
noncomputable def expectedFiniteSelectedRisk {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) : ℝ :=
  finiteSampleExpectation sampleWeight
    (fun S => finitePopulationRisk p ℓ (A S))

omit [Fintype ι] in
/-- Expected empirical training loss of the hypothesis selected by `A` under
finite sample weights. -/
noncomputable def expectedFiniteTrainingLoss {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) : ℝ :=
  finiteSampleExpectation sampleWeight (fun S => trainingLoss A ℓ S)

omit [Fintype ι] in
/-- Expected finite generalization gap for an algorithm-selected hypothesis.

This is `E_S[R(A(S))] - E_S[Rhat(A(S), S)]` with all expectations expanded as
finite weighted sums. -/
noncomputable def expectedFiniteStabilityGap {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) : ℝ :=
  expectedFiniteSelectedRisk sampleWeight p A ℓ -
    expectedFiniteTrainingLoss sampleWeight A ℓ

omit [Fintype ι] in
/-- Pointwise finite generalization gap for an algorithm-selected hypothesis.

For a realized sample `S`, this is
`R(A(S)) - Rhat_S(A(S))` with both risks expanded as finite sums. -/
noncomputable def finiteStabilityGeneralizationGap {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ)
    (S : Fin n → Z) : ℝ :=
  finitePopulationRisk p ℓ (A S) - trainingLoss A ℓ S

omit [Fintype ι] in
/-- Finite expectation of the pointwise algorithmic-stability generalization gap.

This is the literal finite `E_S[R(A(S)) - Rhat_S(A(S))]` form. -/
noncomputable def expectedFiniteGeneralizationGap {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) : ℝ :=
  finiteSampleExpectation sampleWeight (finiteStabilityGeneralizationGap p A ℓ)

omit [Fintype ι] in
/-- The pointwise-gap expectation agrees with selected risk minus expected
training loss in the finite setting. -/
theorem expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap
    {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) :
    expectedFiniteGeneralizationGap sampleWeight p A ℓ =
      expectedFiniteStabilityGap sampleWeight p A ℓ := by
  classical
  unfold expectedFiniteGeneralizationGap finiteStabilityGeneralizationGap
    expectedFiniteStabilityGap expectedFiniteSelectedRisk expectedFiniteTrainingLoss
    finiteSampleExpectation
  calc
    (∑ S : Fin n → Z,
        sampleWeight S *
          (finitePopulationRisk p ℓ (A S) - trainingLoss A ℓ S))
        =
      ∑ S : Fin n → Z,
        (sampleWeight S * finitePopulationRisk p ℓ (A S) -
          sampleWeight S * trainingLoss A ℓ S) := by
        apply Finset.sum_congr rfl
        intro S _hS
        ring
    _ =
      (∑ S : Fin n → Z, sampleWeight S * finitePopulationRisk p ℓ (A S)) -
        ∑ S : Fin n → Z, sampleWeight S * trainingLoss A ℓ S := by
        rw [Finset.sum_sub_distrib]

omit [Fintype ι] in
private lemma finite_weighted_sum_neg {α : Type*} [Fintype α]
    (w : α → ℝ) (F : α → ℝ) :
    (∑ x : α, w x * (-F x)) = -∑ x : α, w x * F x := by
  calc
    (∑ x : α, w x * (-F x))
        = ∑ x : α, -(w x * F x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = -∑ x : α, w x * F x := by
          rw [Finset.sum_neg_distrib]

omit [Fintype ι] in
/-- Finite population risk changes sign when the loss is negated. -/
lemma finitePopulationRisk_neg [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (i : ι) :
    finitePopulationRisk p (fun i z => -ℓ i z) i =
      -finitePopulationRisk p ℓ i := by
  unfold finitePopulationRisk
  calc
    (∑ z : Z, p z * -ℓ i z)
        = ∑ z : Z, -(p z * ℓ i z) := by
          apply Finset.sum_congr rfl
          intro z _hz
          ring
    _ = -∑ z : Z, p z * ℓ i z := by
          rw [Finset.sum_neg_distrib]

omit [Fintype ι] in
/-- Training loss changes sign when the loss is negated. -/
lemma trainingLoss_neg {n : ℕ}
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) (S : Fin n → Z) :
    trainingLoss A (fun i z => -ℓ i z) S =
      -trainingLoss A ℓ S := by
  unfold trainingLoss
  rw [Finset.sum_neg_distrib]
  ring

omit [Fintype ι] in
/-- Population risk changes sign when the loss is negated. -/
lemma risk_neg [MeasurableSpace Z]
    (μ : Measure Z) (ℓ : ι → Z → ℝ) (i : ι) :
    risk μ (fun i z => -ℓ i z) i = -risk μ ℓ i := by
  unfold risk
  rw [integral_neg]

omit [Fintype ι] in
/-- Measure-theoretic iid two-sided expected uniform-stability bound.

This is the absolute-value wrapper around
`expectedStabilityGap_le_uniformStability_piMeasure`, obtained by applying the
one-sided theorem to the negated loss. It bounds the absolute value of the
expected gap, not the expectation of the pointwise absolute gap. -/
theorem abs_expectedStabilityGap_le_uniformStability_piMeasure
    [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (h_loss_int : Integrable
      (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ))
    (h_update_int : ∀ k : Fin n, Integrable
      (fun P : (Fin n → Z) × Z => ℓ (A (Function.update P.1 k P.2)) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ))
    (h_coord_int : ∀ k : Fin n, Integrable
      (fun S : Fin n → Z => ℓ (A S) (S k))
      (Measure.pi (fun _ : Fin n => μ))) :
    |∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
        ∂(Measure.pi (fun _ : Fin n => μ))| ≤ β := by
  have hupper := expectedStabilityGap_le_uniformStability_piMeasure (ι := ι) (Z := Z)
    μ hn hstab h_loss_int h_update_int h_coord_int
  have hneg_upper :
      ∫ S : Fin n → Z,
          (risk μ (fun i z => -ℓ i z) (A S) -
            trainingLoss A (fun i z => -ℓ i z) S)
          ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β :=
    expectedStabilityGap_le_uniformStability_piMeasure (ι := ι) (Z := Z)
      μ hn (uniformStability_neg hstab) h_loss_int.neg
      (fun k => (h_update_int k).neg) (fun k => (h_coord_int k).neg)
  have hneg_eq :
      (∫ S : Fin n → Z,
          (risk μ (fun i z => -ℓ i z) (A S) -
            trainingLoss A (fun i z => -ℓ i z) S)
          ∂(Measure.pi (fun _ : Fin n => μ))) =
        -∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
          ∂(Measure.pi (fun _ : Fin n => μ)) := by
    calc
      (∫ S : Fin n → Z,
          (risk μ (fun i z => -ℓ i z) (A S) -
            trainingLoss A (fun i z => -ℓ i z) S)
          ∂(Measure.pi (fun _ : Fin n => μ)))
          = ∫ S : Fin n → Z, -(risk μ ℓ (A S) - trainingLoss A ℓ S)
              ∂(Measure.pi (fun _ : Fin n => μ)) := by
              apply integral_congr_ae
              refine Filter.Eventually.of_forall ?_
              intro S
              change risk μ (fun i z => -ℓ i z) (A S) -
                  trainingLoss A (fun i z => -ℓ i z) S =
                -(risk μ ℓ (A S) - trainingLoss A ℓ S)
              rw [risk_neg, trainingLoss_neg]
              ring
      _ = -∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
          ∂(Measure.pi (fun _ : Fin n => μ)) := by
          rw [integral_neg]
  rw [hneg_eq] at hneg_upper
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- A finite hypothesis-indexed scalar loss is jointly measurable when each
hypothesis loss is measurable and the finite index type has measurable
singletons.

This is a finite-class measurability adapter. It is not a measurability theorem
for arbitrary hypothesis spaces or arbitrary stochastic kernels. -/
lemma finiteClass_loss_measurable
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (ℓ : ι → Z → ℝ) (hℓ_meas : ∀ i, Measurable (ℓ i)) :
    Measurable (fun P : ι × Z => ℓ P.1 P.2) := by
  classical
  let F : ι → ι × Z → ℝ :=
    fun i => ({P : ι × Z | P.1 = i}).indicator (fun P => ℓ i P.2)
  have hF : ∀ i, Measurable (F i) := by
    intro i
    exact ((hℓ_meas i).comp
      (measurable_snd : Measurable (fun P : ι × Z => P.2))).indicator
      ((MeasurableSingletonClass.measurableSet_singleton i).preimage
        (measurable_fst : Measurable (fun P : ι × Z => P.1)))
  have hsum : Measurable (fun P : ι × Z => ∑ i : ι, F i P) := by
    exact Finset.measurable_sum Finset.univ (by intro i _hi; exact hF i)
  convert hsum using 1
  funext P
  dsimp [F]
  rw [Finset.sum_eq_single P.1]
  · simp
  · intro i _hi hne
    have hnot : P.1 ≠ i := Ne.symm hne
    simp [Set.indicator, hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ P.1)).elim

/-- Integrability of the algorithm-selected loss under `μⁿ × μ`, from finite
hypothesis class measurability and a uniform bounded-loss assumption.

This adapter is for finite-sample, finite-class, scalar-valued stability
theorems. It does not remove the need to prove the learning algorithm
`A : (Fin n → Z) → ι` is measurable. -/
theorem boundedLoss_selectedLoss_integrable
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {B : ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    Integrable (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  have hℓ_joint : Measurable (fun P : ι × Z => ℓ P.1 P.2) :=
    finiteClass_loss_measurable ℓ hℓ_meas
  have hpair : Measurable (fun P : (Fin n → Z) × Z => (A P.1, P.2)) :=
    Measurable.prod (hA.comp measurable_fst) measurable_snd
  have hselected : Measurable (fun P : (Fin n → Z) × Z => ℓ (A P.1) P.2) :=
    hℓ_joint.comp hpair
  refine Integrable.of_bound hselected.aestronglyMeasurable B ?_
  exact Filter.Eventually.of_forall (by
    intro P
    simpa [Real.norm_eq_abs] using hℓ_bdd (A P.1) P.2)

/-- Integrability of the coordinate-updated selected loss under `μⁿ × μ`.

This is the bounded-loss adapter for the fresh-sample term
`ℓ (A (Function.update S k z')) z'` used by the measure-theoretic stability
coordinate-swap proof. -/
theorem boundedLoss_updateSelectedLoss_integrable
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (k : Fin n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {B : ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    Integrable
      (fun P : (Fin n → Z) × Z => ℓ (A (Function.update P.1 k P.2)) P.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ) := by
  have hℓ_joint : Measurable (fun P : ι × Z => ℓ P.1 P.2) :=
    finiteClass_loss_measurable ℓ hℓ_meas
  have hupdate : Measurable
      (fun P : (Fin n → Z) × Z => Function.update P.1 k P.2) := by
    exact measurable_fst.comp (measurable_sampleCoordinateSwap (Z := Z) k)
  have hpair : Measurable
      (fun P : (Fin n → Z) × Z => (A (Function.update P.1 k P.2), P.2)) :=
    Measurable.prod (hA.comp hupdate) measurable_snd
  have hselected : Measurable
      (fun P : (Fin n → Z) × Z => ℓ (A (Function.update P.1 k P.2)) P.2) :=
    hℓ_joint.comp hpair
  refine Integrable.of_bound hselected.aestronglyMeasurable B ?_
  exact Filter.Eventually.of_forall (by
    intro P
    simpa [Real.norm_eq_abs] using hℓ_bdd (A (Function.update P.1 k P.2)) P.2)

/-- Integrability of each empirical coordinate loss under `μⁿ`.

This is the bounded-loss adapter for the terms
`S ↦ ℓ (A S) (S k)` in the training-loss integral. -/
theorem boundedLoss_coordinateSelectedLoss_integrable
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (k : Fin n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {B : ℝ}
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    Integrable (fun S : Fin n → Z => ℓ (A S) (S k))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hℓ_joint : Measurable (fun P : ι × Z => ℓ P.1 P.2) :=
    finiteClass_loss_measurable ℓ hℓ_meas
  have hpair : Measurable (fun S : Fin n → Z => (A S, S k)) :=
    Measurable.prod hA (measurable_pi_apply k)
  have hselected : Measurable (fun S : Fin n → Z => ℓ (A S) (S k)) :=
    hℓ_joint.comp hpair
  refine Integrable.of_bound hselected.aestronglyMeasurable B ?_
  exact Filter.Eventually.of_forall (by
    intro S
    simpa [Real.norm_eq_abs] using hℓ_bdd (A S) (S k))

/-- Measure-theoretic iid expected uniform-stability bound with bounded-loss
integrability discharged automatically.

This is the finite-class bounded-loss wrapper around
`expectedStabilityGap_le_uniformStability_piMeasure`. It assumes a finite
hypothesis index type, measurable algorithm `A`, measurable scalar losses
`ℓ i`, and a uniform pointwise bound `|ℓ i z| ≤ B`; it is not an infinite-class
or kernel-measurability theorem. -/
theorem expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hstab : UniformStability A ℓ β)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    ∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
        ∂(Measure.pi (fun _ : Fin n => μ)) ≤ β := by
  exact expectedStabilityGap_le_uniformStability_piMeasure (ι := ι) (Z := Z)
    μ hn hstab
    (boundedLoss_selectedLoss_integrable (ι := ι) (Z := Z)
      μ hA hℓ_meas hℓ_bdd)
    (fun k => boundedLoss_updateSelectedLoss_integrable (ι := ι) (Z := Z)
      μ k hA hℓ_meas hℓ_bdd)
    (fun k => boundedLoss_coordinateSelectedLoss_integrable (ι := ι) (Z := Z)
      μ k hA hℓ_meas hℓ_bdd)

/-- Two-sided measure-theoretic iid expected uniform-stability bound with
bounded-loss integrability discharged automatically.

This bounds the absolute value of the expected generalization gap for a finite
hypothesis class and measurable bounded scalar losses. It is not a
high-probability stability theorem and does not cover arbitrary infinite
hypothesis spaces. -/
theorem abs_expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β B : ℝ}
    (hstab : UniformStability A ℓ β)
    (hA : Measurable A)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) :
    |∫ S : Fin n → Z, (risk μ ℓ (A S) - trainingLoss A ℓ S)
        ∂(Measure.pi (fun _ : Fin n => μ))| ≤ β := by
  exact abs_expectedStabilityGap_le_uniformStability_piMeasure (ι := ι) (Z := Z)
    μ hn hstab
    (boundedLoss_selectedLoss_integrable (ι := ι) (Z := Z)
      μ hA hℓ_meas hℓ_bdd)
    (fun k => boundedLoss_updateSelectedLoss_integrable (ι := ι) (Z := Z)
      μ k hA hℓ_meas hℓ_bdd)
    (fun k => boundedLoss_coordinateSelectedLoss_integrable (ι := ι) (Z := Z)
      μ k hA hℓ_meas hℓ_bdd)

omit [Fintype ι] in
/-- Expected selected finite risk changes sign when the loss is negated. -/
lemma expectedFiniteSelectedRisk_neg {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) :
    expectedFiniteSelectedRisk sampleWeight p A (fun i z => -ℓ i z) =
      -expectedFiniteSelectedRisk sampleWeight p A ℓ := by
  unfold expectedFiniteSelectedRisk finiteSampleExpectation
  calc
    (∑ S : Fin n → Z,
        sampleWeight S * finitePopulationRisk p (fun i z => -ℓ i z) (A S))
        =
      ∑ S : Fin n → Z,
        sampleWeight S * (-finitePopulationRisk p ℓ (A S)) := by
        apply Finset.sum_congr rfl
        intro S _hS
        rw [finitePopulationRisk_neg]
    _ = -∑ S : Fin n → Z,
          sampleWeight S * finitePopulationRisk p ℓ (A S) := by
          exact finite_weighted_sum_neg sampleWeight
            (fun S : Fin n → Z => finitePopulationRisk p ℓ (A S))

omit [Fintype ι] in
/-- Expected finite training loss changes sign when the loss is negated. -/
lemma expectedFiniteTrainingLoss_neg {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) :
    expectedFiniteTrainingLoss sampleWeight A (fun i z => -ℓ i z) =
      -expectedFiniteTrainingLoss sampleWeight A ℓ := by
  unfold expectedFiniteTrainingLoss finiteSampleExpectation
  calc
    (∑ S : Fin n → Z,
        sampleWeight S * trainingLoss A (fun i z => -ℓ i z) S)
        =
      ∑ S : Fin n → Z, sampleWeight S * (-trainingLoss A ℓ S) := by
        apply Finset.sum_congr rfl
        intro S _hS
        rw [trainingLoss_neg]
    _ = -∑ S : Fin n → Z, sampleWeight S * trainingLoss A ℓ S := by
          exact finite_weighted_sum_neg sampleWeight
            (fun S : Fin n → Z => trainingLoss A ℓ S)

omit [Fintype ι] in
/-- Expected finite stability gap changes sign when the loss is negated. -/
lemma expectedFiniteStabilityGap_neg {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) :
    expectedFiniteStabilityGap sampleWeight p A (fun i z => -ℓ i z) =
      -expectedFiniteStabilityGap sampleWeight p A ℓ := by
  unfold expectedFiniteStabilityGap
  rw [expectedFiniteSelectedRisk_neg, expectedFiniteTrainingLoss_neg]
  ring

omit [Fintype ι] in
/-- Pointwise finite stability generalization gap changes sign when the loss
is negated. -/
lemma finiteStabilityGeneralizationGap_neg {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ)
    (S : Fin n → Z) :
    finiteStabilityGeneralizationGap p A (fun i z => -ℓ i z) S =
      -finiteStabilityGeneralizationGap p A ℓ S := by
  unfold finiteStabilityGeneralizationGap
  rw [finitePopulationRisk_neg, trainingLoss_neg]
  ring

omit [Fintype ι] in
/-- Expected finite pointwise generalization gap changes sign when the loss is
negated. -/
lemma expectedFiniteGeneralizationGap_neg {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ)
    (A : (Fin n → Z) → ι) (ℓ : ι → Z → ℝ) :
    expectedFiniteGeneralizationGap sampleWeight p A (fun i z => -ℓ i z) =
      -expectedFiniteGeneralizationGap sampleWeight p A ℓ := by
  unfold expectedFiniteGeneralizationGap finiteSampleExpectation
  calc
    (∑ S : Fin n → Z,
        sampleWeight S *
          finiteStabilityGeneralizationGap p A (fun i z => -ℓ i z) S)
        =
      ∑ S : Fin n → Z,
        sampleWeight S * (-finiteStabilityGeneralizationGap p A ℓ S) := by
        apply Finset.sum_congr rfl
        intro S _hS
        rw [finiteStabilityGeneralizationGap_neg]
    _ = -∑ S : Fin n → Z,
          sampleWeight S * finiteStabilityGeneralizationGap p A ℓ S := by
          exact finite_weighted_sum_neg sampleWeight
            (fun S : Fin n → Z => finiteStabilityGeneralizationGap p A ℓ S)

omit [Fintype ι] in
/-- Finite coordinate-swap identity for replacing coordinate `k` with an
independent draw from `p`.

For iid product weights this is the finite-sum analogue of the product-measure
coordinate-swap symmetry. It is kept as an explicit hypothesis here so the
expected-stability proof can be closed without hiding the product-kernel
infrastructure still needed for the measure-theoretic theorem. -/
def FiniteCoordinateSwapIdentity {n : ℕ} [Fintype Z]
    (sampleWeight : (Fin n → Z) → ℝ) (p : Z → ℝ) : Prop :=
  ∀ (k : Fin n) (G : (Fin n → Z) → Z → ℝ),
    (∑ S : Fin n → Z,
        sampleWeight S * ∑ z : Z, p z * G (Function.update S k z) z) =
      ∑ S : Fin n → Z, sampleWeight S * G S (S k)

omit [Fintype ι] in
/-- Finite iid product sample weight induced by a finite data mass function.

For a sample `S : Fin n → Z`, this is `∏ k, p (S k)`. The definition is
purely finite and is used to close the coordinate-swap symmetry needed by the
finite expected-stability adapter. -/
noncomputable def finiteProductSampleWeight {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (S : Fin n → Z) : ℝ :=
  ∏ k : Fin n, p (S k)

omit [Fintype ι] in
/-- Finite iid product sample weights are nonnegative when the base mass
function is nonnegative. -/
lemma finiteProductSampleWeight_nonneg {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp_nonneg : ∀ z, 0 ≤ p z) :
    ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S := by
  intro S
  unfold finiteProductSampleWeight
  exact Finset.prod_nonneg (fun k _hk => hp_nonneg (S k))

omit [Fintype ι] in
/-- Finite iid product sample weights sum to one when the base mass function
sums to one. -/
lemma finiteProductSampleWeight_sum_eq_one {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp_sum : ∑ z : Z, p z = 1) :
    ∑ S : Fin n → Z, finiteProductSampleWeight p S = 1 := by
  unfold finiteProductSampleWeight
  calc
    (∑ S : Fin n → Z, ∏ k : Fin n, p (S k))
        = ∏ _k : Fin n, ∑ z : Z, p z := by
          exact (Fintype.prod_sum (f := fun _k : Fin n => p)).symm
    _ = 1 := by simp [hp_sum]

omit [Fintype ι] in
/-- Replacing coordinate `k` in a finite iid product weight and multiplying by
the old coordinate mass equals the original weight times the replacement mass.

This is the algebraic core of the finite coordinate-swap proof. -/
lemma finiteProductSampleWeight_update_mul {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (S : Fin n → Z) (k : Fin n) (z : Z) :
    finiteProductSampleWeight p (Function.update S k z) * p (S k) =
      finiteProductSampleWeight p S * p z := by
  classical
  unfold finiteProductSampleWeight
  have h_update :
      (∏ j : Fin n, p ((Function.update S k z) j)) =
        p z * ∏ j ∈ ({k}ᶜ : Finset (Fin n)), p (S j) := by
    rw [Fintype.prod_eq_mul_prod_compl k]
    rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ k := by simpa using hj
    rw [Function.update_of_ne hne]
  have h_original :
      (∏ j : Fin n, p (S j)) =
        p (S k) * ∏ j ∈ ({k}ᶜ : Finset (Fin n)), p (S j) := by
    rw [Fintype.prod_eq_mul_prod_compl k]
  rw [h_update, h_original]
  ring

omit [Fintype ι] in
/-- Involutive reindexing for finite coordinate swaps.

The pair `(S, z)` is sent to `(Function.update S k z, S k)`: the replacement
sample becomes the visible sample, and the old coordinate becomes the auxiliary
summation variable. -/
def finiteCoordinateSwapEquiv {n : ℕ} (k : Fin n) :
    ((Fin n → Z) × Z) ≃ ((Fin n → Z) × Z) where
  toFun P := (Function.update P.1 k P.2, P.1 k)
  invFun P := (Function.update P.1 k P.2, P.1 k)
  left_inv := by
    intro P
    rcases P with ⟨S, z⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = k
      · subst j
        simp [Function.update_self]
      · simp [Function.update_of_ne hj]
    · simp [Function.update_self]
  right_inv := by
    intro P
    rcases P with ⟨S, z⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = k
      · subst j
        simp [Function.update_self]
      · simp [Function.update_of_ne hj]
    · simp [Function.update_self]

omit [Fintype ι] in
/-- Finite iid product sample weights satisfy the coordinate-swap identity.

This is a finite-domain theorem: finite data domain, finite samples, and all
expectations expanded as finite sums. It removes the explicit coordinate-swap
hypothesis from the finite expected-stability adapter for iid product weights.
The measure-theoretic analogue is `integral_update_eq_integral_coordinate`. -/
theorem finiteProductSampleWeight_coordinateSwapIdentity {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (hp_sum : ∑ z : Z, p z = 1) :
    FiniteCoordinateSwapIdentity (finiteProductSampleWeight (n := n) p) p := by
  classical
  intro k G
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S * ∑ z : Z, p z * G (Function.update S k z) z)
        =
      ∑ S : Fin n → Z, ∑ z : Z,
        finiteProductSampleWeight p S * (p z * G (Function.update S k z) z) := by
          apply Finset.sum_congr rfl
          intro S _hS
          rw [Finset.mul_sum]
    _ =
      ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p P.1 * (p P.2 * G (Function.update P.1 k P.2) P.2) := by
          exact (Fintype.sum_prod_type'
            (fun S : Fin n → Z => fun z : Z =>
              finiteProductSampleWeight p S * (p z * G (Function.update S k z) z))).symm
    _ =
      ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p (Function.update P.1 k P.2) *
          (p (P.1 k) * G P.1 (P.1 k)) := by
          refine Fintype.sum_equiv (finiteCoordinateSwapEquiv (Z := Z) k) _ _ ?_
          intro P
          rcases P with ⟨S, z⟩
          simp [finiteCoordinateSwapEquiv, Function.update_self]
    _ =
      ∑ P : (Fin n → Z) × Z,
        finiteProductSampleWeight p P.1 * p P.2 * G P.1 (P.1 k) := by
          apply Finset.sum_congr rfl
          intro P _hP
          rw [← mul_assoc, finiteProductSampleWeight_update_mul]
    _ =
      ∑ S : Fin n → Z, ∑ z : Z,
        finiteProductSampleWeight p S * p z * G S (S k) := by
          exact Fintype.sum_prod_type'
            (fun S : Fin n → Z => fun z : Z =>
              finiteProductSampleWeight p S * p z * G S (S k))
    _ =
      ∑ S : Fin n → Z, finiteProductSampleWeight p S * G S (S k) := by
          apply Finset.sum_congr rfl
          intro S _hS
          calc
            (∑ z : Z, finiteProductSampleWeight p S * p z * G S (S k))
                = (finiteProductSampleWeight p S * G S (S k)) * ∑ z : Z, p z := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro z _hz
                  ring
            _ = finiteProductSampleWeight p S * G S (S k) := by
                  rw [hp_sum, mul_one]

omit [Fintype ι] in
/-- One-coordinate finite expected stability bound.

The selected finite population risk is bounded by the coordinate-`k`
expected training contribution plus `β`, provided the sample weights satisfy
the finite coordinate-swap identity. -/
lemma expectedFiniteSelectedRisk_le_coordinateTraining_add_beta
    {n : ℕ} [Fintype Z]
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p)
    (k : Fin n) :
    expectedFiniteSelectedRisk sampleWeight p A ℓ ≤
      (∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) + β := by
  classical
  have hpoint : ∀ (S : Fin n → Z) (z : Z),
      ℓ (A S) z ≤ ℓ (A (Function.update S k z)) z + β := by
    intro S z
    have h := hstab S k z z
    linarith [(abs_le.mp h).2]
  have hinner : ∀ S : Fin n → Z,
      (∑ z : Z, p z * ℓ (A S) z) ≤
        ∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β) := by
    intro S
    apply Finset.sum_le_sum
    intro z _hz
    exact mul_le_mul_of_nonneg_left (hpoint S z) (hp_nonneg z)
  have hsum_le :
      (∑ S : Fin n → Z, sampleWeight S * ∑ z : Z, p z * ℓ (A S) z) ≤
        ∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β) := by
    apply Finset.sum_le_sum
    intro S _hS
    exact mul_le_mul_of_nonneg_left (hinner S) (hw_nonneg S)
  have hinner_eq : ∀ S : Fin n → Z,
      (∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β)) =
        (∑ z : Z, p z * ℓ (A (Function.update S k z)) z) + β := by
    intro S
    calc
      (∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β))
          = ∑ z : Z, (p z * ℓ (A (Function.update S k z)) z + p z * β) := by
            apply Finset.sum_congr rfl
            intro z _hz
            ring
      _ = (∑ z : Z, p z * ℓ (A (Function.update S k z)) z) +
            ∑ z : Z, p z * β := by
            rw [Finset.sum_add_distrib]
      _ = (∑ z : Z, p z * ℓ (A (Function.update S k z)) z) + β := by
            rw [← Finset.sum_mul, hp_sum, one_mul]
  have houter_eq :
      (∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β)) =
        (∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * ℓ (A (Function.update S k z)) z) + β := by
    calc
      (∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β))
          =
        ∑ S : Fin n → Z,
          sampleWeight S *
            ((∑ z : Z, p z * ℓ (A (Function.update S k z)) z) + β) := by
            apply Finset.sum_congr rfl
            intro S _hS
            rw [hinner_eq S]
      _ =
        ∑ S : Fin n → Z,
          (sampleWeight S *
            (∑ z : Z, p z * ℓ (A (Function.update S k z)) z) +
              sampleWeight S * β) := by
            apply Finset.sum_congr rfl
            intro S _hS
            ring
      _ =
        (∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * ℓ (A (Function.update S k z)) z) +
          ∑ S : Fin n → Z, sampleWeight S * β := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * ℓ (A (Function.update S k z)) z) + β := by
            rw [← Finset.sum_mul, hw_sum, one_mul]
  calc
    expectedFiniteSelectedRisk sampleWeight p A ℓ
        = ∑ S : Fin n → Z, sampleWeight S * ∑ z : Z, p z * ℓ (A S) z := by
            rfl
    _ ≤ ∑ S : Fin n → Z,
          sampleWeight S *
            ∑ z : Z, p z * (ℓ (A (Function.update S k z)) z + β) := hsum_le
    _ = (∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) + β := by
          rw [houter_eq]
          exact congrArg (fun x => x + β)
            (hswap k (fun S z => ℓ (A S) z))

omit [Fintype ι] in
/-- Finite expected uniform-stability bound, conditional on the finite
coordinate-swap identity.

If replacing one coordinate changes the selected loss by at most `β`, then the
expected finite generalization gap of the algorithm-selected hypothesis is at
most `β`. This closes the finite-sum adapter; the measure-theoretic iid lift is
`expectedStabilityGap_le_uniformStability_piMeasure`. -/
theorem expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    expectedFiniteStabilityGap sampleWeight p A ℓ ≤ β := by
  classical
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  have hselected_repeat :
      expectedFiniteSelectedRisk sampleWeight p A ℓ =
        (n : ℝ)⁻¹ *
          ∑ _k : Fin n, expectedFiniteSelectedRisk sampleWeight p A ℓ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn_real_ne]
  have hcoord : ∀ k : Fin n,
      expectedFiniteSelectedRisk sampleWeight p A ℓ ≤
        (∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) + β :=
    expectedFiniteSelectedRisk_le_coordinateTraining_add_beta hstab
      hp_nonneg hp_sum hw_nonneg hw_sum hswap
  have havg :
      expectedFiniteSelectedRisk sampleWeight p A ℓ ≤
        (n : ℝ)⁻¹ *
          ∑ k : Fin n,
            ((∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) + β) := by
    rw [hselected_repeat]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k _hk => hcoord k))
      (inv_nonneg.mpr hn_real_pos.le)
  have htrain_eq :
      (n : ℝ)⁻¹ *
          ∑ k : Fin n, (∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) =
        expectedFiniteTrainingLoss sampleWeight A ℓ := by
    unfold expectedFiniteTrainingLoss finiteSampleExpectation trainingLoss
    rw [Finset.mul_sum]
    calc
      (∑ k : Fin n,
          (n : ℝ)⁻¹ * ∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k))
          =
        ∑ k : Fin n, ∑ S : Fin n → Z,
          (n : ℝ)⁻¹ * (sampleWeight S * ℓ (A S) (S k)) := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.mul_sum]
      _ =
        ∑ S : Fin n → Z, ∑ k : Fin n,
          (n : ℝ)⁻¹ * (sampleWeight S * ℓ (A S) (S k)) := by
            rw [Finset.sum_comm]
      _ =
        ∑ S : Fin n → Z,
          sampleWeight S * ((n : ℝ)⁻¹ * ∑ k : Fin n, ℓ (A S) (S k)) := by
            apply Finset.sum_congr rfl
            intro S _hS
            calc
              (∑ k : Fin n,
                  (n : ℝ)⁻¹ * (sampleWeight S * ℓ (A S) (S k)))
                  =
                ∑ k : Fin n, sampleWeight S * ((n : ℝ)⁻¹ * ℓ (A S) (S k)) := by
                  apply Finset.sum_congr rfl
                  intro k _hk
                  ring
              _ = sampleWeight S * ∑ k : Fin n,
                    ((n : ℝ)⁻¹ * ℓ (A S) (S k)) := by
                  rw [Finset.mul_sum]
              _ = sampleWeight S *
                    ((n : ℝ)⁻¹ * ∑ k : Fin n, ℓ (A S) (S k)) := by
                  calc
                    sampleWeight S * ∑ k : Fin n,
                        ((n : ℝ)⁻¹ * ℓ (A S) (S k))
                        =
                      ∑ k : Fin n,
                        (sampleWeight S * (n : ℝ)⁻¹) * ℓ (A S) (S k) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro k _hk
                        ring
                    _ = (sampleWeight S * (n : ℝ)⁻¹) *
                          ∑ k : Fin n, ℓ (A S) (S k) := by
                        rw [Finset.mul_sum]
                    _ = sampleWeight S *
                          ((n : ℝ)⁻¹ * ∑ k : Fin n, ℓ (A S) (S k)) := by
                        ring
  have hbeta_sum :
      (n : ℝ)⁻¹ * (∑ _k : Fin n, β) = β := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn_real_ne]
  have hselected_le :
      expectedFiniteSelectedRisk sampleWeight p A ℓ ≤
        expectedFiniteTrainingLoss sampleWeight A ℓ + β := by
    calc
      expectedFiniteSelectedRisk sampleWeight p A ℓ
          ≤ (n : ℝ)⁻¹ *
              ∑ k : Fin n,
                ((∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) + β) := havg
      _ =
          (n : ℝ)⁻¹ *
              (∑ k : Fin n, (∑ S : Fin n → Z, sampleWeight S * ℓ (A S) (S k)) +
                ∑ _k : Fin n, β) := by
            rw [Finset.sum_add_distrib]
      _ =
          expectedFiniteTrainingLoss sampleWeight A ℓ + β := by
            rw [mul_add, htrain_eq, hbeta_sum]
  unfold expectedFiniteStabilityGap
  linarith

omit [Fintype ι] in
/-- Finite iid expected uniform-stability bound.

If the finite data law `p` is a probability mass function and replacing one
coordinate changes the selected loss by at most `β`, then the expected finite
generalization gap under iid finite product sample weights is at most `β`.

This theorem closes the finite iid coordinate-swap specialization. It does not
replace the measure-theoretic iid theorem
`expectedStabilityGap_le_uniformStability_piMeasure`, which works over
`Measure.pi` with explicit integrability hypotheses. -/
theorem expectedFiniteStabilityGap_le_uniformStability_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    expectedFiniteStabilityGap (finiteProductSampleWeight p) p A ℓ ≤ β :=
  expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
    hn hstab hp_nonneg hp_sum
    (finiteProductSampleWeight_nonneg hp_nonneg)
    (finiteProductSampleWeight_sum_eq_one hp_sum)
    (finiteProductSampleWeight_coordinateSwapIdentity p hp_sum)

omit [Fintype ι] in
/-- Finite lower expected uniform-stability bound, conditional on the finite
coordinate-swap identity.

This is the lower half of the two-sided finite expected-gap statement. It is
obtained by applying the one-sided finite expected-stability theorem to the
negated loss. -/
theorem neg_beta_le_expectedFiniteStabilityGap_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    -β ≤ expectedFiniteStabilityGap sampleWeight p A ℓ := by
  have hneg_upper :
      expectedFiniteStabilityGap sampleWeight p A (fun i z => -ℓ i z) ≤ β :=
    expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
      hn (uniformStability_neg hstab)
      hp_nonneg hp_sum hw_nonneg hw_sum hswap
  rw [expectedFiniteStabilityGap_neg] at hneg_upper
  linarith

omit [Fintype ι] in
/-- Finite two-sided expected uniform-stability bound, conditional on the
finite coordinate-swap identity.

This is a finite-domain theorem: finite data domain, finite sample, explicit
finite sample weights, and a finite coordinate-swap identity. It bounds the
absolute value of the expected gap, not the expectation of the pointwise
absolute gap. -/
theorem abs_expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    |expectedFiniteStabilityGap sampleWeight p A ℓ| ≤ β := by
  exact abs_le.mpr
    ⟨neg_beta_le_expectedFiniteStabilityGap_of_coordinateSwap
        hn hstab hp_nonneg hp_sum hw_nonneg hw_sum hswap,
      expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
        hn hstab hp_nonneg hp_sum hw_nonneg hw_sum hswap⟩

omit [Fintype ι] in
/-- Finite iid lower expected uniform-stability bound.

The sample weights are the explicit finite iid product weights
`∏ k, p (S k)`. -/
theorem neg_beta_le_expectedFiniteStabilityGap_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    -β ≤ expectedFiniteStabilityGap (finiteProductSampleWeight p) p A ℓ :=
  neg_beta_le_expectedFiniteStabilityGap_of_coordinateSwap
    hn hstab hp_nonneg hp_sum
    (finiteProductSampleWeight_nonneg hp_nonneg)
    (finiteProductSampleWeight_sum_eq_one hp_sum)
    (finiteProductSampleWeight_coordinateSwapIdentity p hp_sum)

omit [Fintype ι] in
/-- Finite iid two-sided expected uniform-stability bound.

This bounds the absolute value of the expected finite stability gap under
explicit finite iid product weights. It is not a measure-theoretic product
space theorem. -/
theorem abs_expectedFiniteStabilityGap_le_uniformStability_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    |expectedFiniteStabilityGap (finiteProductSampleWeight p) p A ℓ| ≤ β := by
  exact abs_le.mpr
    ⟨neg_beta_le_expectedFiniteStabilityGap_finiteProduct
        hn hstab hp_nonneg hp_sum,
      expectedFiniteStabilityGap_le_uniformStability_finiteProduct
        hn hstab hp_nonneg hp_sum⟩

omit [Fintype ι] in
/-- Finite expected generalization-gap bound, conditional on the finite
coordinate-swap identity.

This is the literal `E_S[R(A(S)) - Rhat_S(A(S))] ≤ β` wrapper around
`expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap`. It remains
finite-domain and assumes the finite coordinate-swap identity explicitly. -/
theorem expectedFiniteGeneralizationGap_le_uniformStability_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    expectedFiniteGeneralizationGap sampleWeight p A ℓ ≤ β := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
    hn hstab hp_nonneg hp_sum hw_nonneg hw_sum hswap

omit [Fintype ι] in
/-- Finite iid expected generalization-gap bound for uniformly stable
algorithms.

If the finite data law `p` is a probability mass function and replacing one
training coordinate changes the selected loss by at most `β`, then

`E_S[R(A(S)) - Rhat_S(A(S))] ≤ β`

under the finite iid product sample weights `∏ k, p (S k)`.

This is a finite-domain theorem, scoped to finite data domains and explicit
iid product weights rather than arbitrary measurable sample spaces. -/
theorem expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    expectedFiniteGeneralizationGap (finiteProductSampleWeight p) p A ℓ ≤ β := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact expectedFiniteStabilityGap_le_uniformStability_finiteProduct
    hn hstab hp_nonneg hp_sum

omit [Fintype ι] in
/-- Finite lower expected generalization-gap bound, conditional on the finite
coordinate-swap identity.

This is the lower half of the two-sided literal finite
`E_S[R(A(S)) - Rhat_S(A(S))]` statement. -/
theorem neg_beta_le_expectedFiniteGeneralizationGap_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    -β ≤ expectedFiniteGeneralizationGap sampleWeight p A ℓ := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact neg_beta_le_expectedFiniteStabilityGap_of_coordinateSwap
    hn hstab hp_nonneg hp_sum hw_nonneg hw_sum hswap

omit [Fintype ι] in
/-- Finite iid lower expected generalization-gap bound. -/
theorem neg_beta_le_expectedFiniteGeneralizationGap_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    -β ≤
      expectedFiniteGeneralizationGap
        (finiteProductSampleWeight p) p A ℓ := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact neg_beta_le_expectedFiniteStabilityGap_finiteProduct
    hn hstab hp_nonneg hp_sum

omit [Fintype ι] in
/-- Finite two-sided expected generalization-gap bound, conditional on the
finite coordinate-swap identity.

This is the literal finite
`|E_S[R(A(S)) - Rhat_S(A(S))]| ≤ β` statement. It bounds the absolute value of
the expectation, not the expectation of the pointwise absolute gap. -/
theorem abs_expectedFiniteGeneralizationGap_le_uniformStability_of_coordinateSwap
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {sampleWeight : (Fin n → Z) → ℝ} {p : Z → ℝ}
    {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1)
    (hw_nonneg : ∀ S, 0 ≤ sampleWeight S)
    (hw_sum : ∑ S : Fin n → Z, sampleWeight S = 1)
    (hswap : FiniteCoordinateSwapIdentity sampleWeight p) :
    |expectedFiniteGeneralizationGap sampleWeight p A ℓ| ≤ β := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact abs_expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap
    hn hstab hp_nonneg hp_sum hw_nonneg hw_sum hswap

omit [Fintype ι] in
/-- Finite iid two-sided expected generalization-gap bound.

For a finite data law `p` and explicit finite iid product sample weights, a
uniformly stable algorithm satisfies
`|E_S[R(A(S)) - Rhat_S(A(S))]| ≤ β`. This is still a finite-domain theorem,
complementing the measure-theoretic product-space wrapper
`abs_expectedStabilityGap_le_uniformStability_piMeasure`. -/
theorem abs_expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    {p : Z → ℝ} {A : (Fin n → Z) → ι} {ℓ : ι → Z → ℝ} {β : ℝ}
    (hstab : UniformStability A ℓ β)
    (hp_nonneg : ∀ z, 0 ≤ p z)
    (hp_sum : ∑ z : Z, p z = 1) :
    |expectedFiniteGeneralizationGap
      (finiteProductSampleWeight p) p A ℓ| ≤ β := by
  rw [expectedFiniteGeneralizationGap_eq_expectedFiniteStabilityGap]
  exact abs_expectedFiniteStabilityGap_le_uniformStability_finiteProduct
    hn hstab hp_nonneg hp_sum

end FormalSLT.AlgorithmicStability
