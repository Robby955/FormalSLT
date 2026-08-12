/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteExponentialTiltProduct
import FormalSLT.PACBayes.FiniteEmpiricalVariance
import FormalSLT.Probability.BernsteinMGF

/-!
# Finite bounded-loss exponential tilts

This module specializes the finite exponential tilt to the lower-tail score
`z ↦ -t * ell i z` for a loss in `[0, 1]`.  It proves the two deterministic
facts needed before the joint mean/empirical-variance MGF argument:

* the tilted PMF pointwise dominates `exp (-t)` times the base PMF; and
* its population variance is at least `exp (-t)` times the base variance.

The exact one-coordinate and finite-product change-of-measure identities are
specializations of the generic exponential-tilt results.  The module also
records the retained-affine-factor Bennett bound for the centered lower-tail
loss score.  It does not apply the empirical-variance MGF or prove a joint
normalized score.
-/

namespace FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteExponentialTilt
open FormalSLT.PACBayes.FiniteExponentialTiltProduct
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.Probability.BernsteinMGF

noncomputable section

variable {Z ι : Type*} [Fintype Z]

/-- Lower-tail loss score used for the finite exponential change of measure. -/
def boundedLossTiltScore (ell : ι → Z → ℝ) (i : ι) (t : ℝ) (z : Z) : ℝ :=
  -t * ell i z

/-- Partition sum of the lower-tail bounded-loss tilt. -/
def finiteBoundedLossTiltNormalizer
    (p : Z → ℝ) (ell : ι → Z → ℝ) (i : ι) (t : ℝ) : ℝ :=
  finiteExponentialTiltNormalizer p (boundedLossTiltScore ell i t)

/-- PMF obtained by tilting a finite base PMF by `exp (-t * ell i z)`. -/
def finiteBoundedLossTiltPMF
    (p : Z → ℝ) (ell : ι → Z → ℝ) (i : ι) (t : ℝ) : Z → ℝ :=
  finiteExponentialTiltPMF p (boundedLossTiltScore ell i t)

/-- A lower-tail loss tilt of any finite PMF is again a PMF. -/
theorem finiteBoundedLossTiltPMF_isPMF
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι) (t : ℝ) :
    IsPMF (finiteBoundedLossTiltPMF p ell i t) := by
  simpa [finiteBoundedLossTiltPMF] using
    finiteExponentialTiltPMF_isPMF hp (boundedLossTiltScore ell i t)

/-- Exact one-coordinate change of measure for the lower-tail loss tilt. -/
theorem finiteBoundedLossTilt_changeOfMeasure
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι) (t : ℝ)
    (g : Z → ℝ) :
    (∑ z, p z * Real.exp (-t * ell i z) * g z) =
      finiteBoundedLossTiltNormalizer p ell i t *
        ∑ z, finiteBoundedLossTiltPMF p ell i t z * g z := by
  simpa [boundedLossTiltScore, finiteBoundedLossTiltNormalizer,
    finiteBoundedLossTiltPMF] using
    finiteExponentialTilt_changeOfMeasure hp
      (boundedLossTiltScore ell i t) g

/-- Exact iid-product change of measure for the lower-tail loss tilt. -/
theorem finiteBoundedLossTiltProduct_changeOfMeasure
    {n : ℕ} {p : Z → ℝ} (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι) (t : ℝ) (g : (Fin n → Z) → ℝ) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (∑ k, -t * ell i (S k)) * g S) =
      finiteBoundedLossTiltNormalizer p ell i t ^ n *
        ∑ S : Fin n → Z,
          finiteProductSampleWeight (finiteBoundedLossTiltPMF p ell i t) S * g S := by
  simpa [boundedLossTiltScore, finiteBoundedLossTiltNormalizer,
    finiteBoundedLossTiltPMF] using
    finiteProductExponentialTilt_changeOfMeasure hp
      (boundedLossTiltScore ell i t) g

/-- The lower-tail bounded-loss partition sum is at most one. -/
theorem finiteBoundedLossTiltNormalizer_le_one
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    {t : ℝ} (ht : 0 ≤ t)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1) :
    finiteBoundedLossTiltNormalizer p ell i t ≤ 1 := by
  unfold finiteBoundedLossTiltNormalizer finiteExponentialTiltNormalizer
  calc
    (∑ z : Z, p z * Real.exp (boundedLossTiltScore ell i t z)) ≤
        ∑ z : Z, p z * 1 := by
      refine Finset.sum_le_sum (fun z _hz ↦ ?_)
      apply mul_le_mul_of_nonneg_left _ (hp.nonneg z)
      have hnonpos : boundedLossTiltScore ell i t z ≤ 0 := by
        unfold boundedLossTiltScore
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hell z).1
      simpa using (Real.exp_le_exp.mpr hnonpos)
    _ = 1 := by simp [hp.sum_one]

/-- The tilted PMF pointwise dominates `exp (-t)` times the base PMF. -/
theorem finiteBoundedLossTilt_exp_neg_mul_le
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    {t : ℝ} (ht : 0 ≤ t)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1) (z : Z) :
    Real.exp (-t) * p z ≤ finiteBoundedLossTiltPMF p ell i t z := by
  have hnormalizerPos : 0 < finiteBoundedLossTiltNormalizer p ell i t := by
    exact finiteExponentialTiltNormalizer_pos hp (boundedLossTiltScore ell i t)
  have hnormalizerLe : finiteBoundedLossTiltNormalizer p ell i t ≤ 1 :=
    finiteBoundedLossTiltNormalizer_le_one hp ell i ht hell
  have hscore : -t ≤ boundedLossTiltScore ell i t z := by
    unfold boundedLossTiltScore
    nlinarith [(hell z).2]
  unfold finiteBoundedLossTiltPMF
  apply (le_div_iff₀ hnormalizerPos).2
  calc
    Real.exp (-t) * p z * finiteBoundedLossTiltNormalizer p ell i t ≤
        Real.exp (-t) * p z * 1 := by
      exact mul_le_mul_of_nonneg_left hnormalizerLe
        (mul_nonneg (Real.exp_pos _).le (hp.nonneg z))
    _ = p z * Real.exp (-t) := by ring
    _ ≤ p z * Real.exp (boundedLossTiltScore ell i t z) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscore) (hp.nonneg z)

/-- Weighted squared error decomposes into population variance plus squared
distance from the population risk.  This is the finite-PMF minimization
identity used in the variance comparison. -/
theorem finiteWeightedSquaredError_eq_populationVariance_add_sq
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι) (a : ℝ) :
    (∑ z : Z, p z * (ell i z - a) ^ (2 : Nat)) =
      finitePopulationVariance p ell i +
        (finitePopulationRisk p ell i - a) ^ (2 : Nat) := by
  let R := finitePopulationRisk p ell i
  have hR : (∑ z : Z, p z * ell i z) = R := rfl
  rw [finitePopulationVariance_eq_secondMoment_sub_riskSq p hp ell i]
  change
    (∑ z : Z, p z * (ell i z - a) ^ (2 : Nat)) =
      ((∑ z : Z, p z * (ell i z) ^ (2 : Nat)) - R ^ (2 : Nat)) +
        (R - a) ^ (2 : Nat)
  calc
    (∑ z : Z, p z * (ell i z - a) ^ (2 : Nat)) =
        ∑ z : Z,
          (p z * (ell i z) ^ (2 : Nat) -
            2 * a * (p z * ell i z) + a ^ (2 : Nat) * p z) := by
      refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
      ring
    _ = (∑ z : Z, p z * (ell i z) ^ (2 : Nat)) -
          2 * a * (∑ z : Z, p z * ell i z) +
          a ^ (2 : Nat) * (∑ z : Z, p z) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ((∑ z : Z, p z * (ell i z) ^ (2 : Nat)) - R ^ (2 : Nat)) +
          (R - a) ^ (2 : Nat) := by
      rw [hR, hp.sum_one]
      ring

/-- The population risk minimizes finite-PMF weighted squared error. -/
theorem finitePopulationVariance_le_weightedSquaredError
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι) (a : ℝ) :
    finitePopulationVariance p ell i ≤
      ∑ z : Z, p z * (ell i z - a) ^ (2 : Nat) := by
  rw [finiteWeightedSquaredError_eq_populationVariance_add_sq p hp ell i a]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Tilting by `exp (-t * ell)` can reduce population variance by at most the
uniform factor `exp (-t)`. -/
theorem finitePopulationVariance_mul_exp_neg_le_tilted
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    {t : ℝ} (ht : 0 ≤ t)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1) :
    finitePopulationVariance p ell i * Real.exp (-t) ≤
      finitePopulationVariance (finiteBoundedLossTiltPMF p ell i t) ell i := by
  let q : Z → ℝ := finiteBoundedLossTiltPMF p ell i t
  let Rq : ℝ := finitePopulationRisk q ell i
  have hq : IsPMF q := finiteBoundedLossTiltPMF_isPMF hp ell i t
  have hmin : finitePopulationVariance p ell i ≤
      ∑ z : Z, p z * (ell i z - Rq) ^ (2 : Nat) :=
    finitePopulationVariance_le_weightedSquaredError p hp ell i Rq
  have hdom (z : Z) : Real.exp (-t) * p z ≤ q z := by
    exact finiteBoundedLossTilt_exp_neg_mul_le hp ell i ht hell z
  calc
    finitePopulationVariance p ell i * Real.exp (-t) ≤
        (∑ z : Z, p z * (ell i z - Rq) ^ (2 : Nat)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hmin (Real.exp_pos _).le
    _ = ∑ z : Z,
        (Real.exp (-t) * p z) * (ell i z - Rq) ^ (2 : Nat) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
      ring
    _ ≤ ∑ z : Z, q z * (ell i z - Rq) ^ (2 : Nat) := by
      exact Finset.sum_le_sum (fun z _hz ↦
        mul_le_mul_of_nonneg_right (hdom z) (sq_nonneg _))
    _ = finitePopulationVariance q ell i := by
      simpa [Rq] using
        finiteWeightedSquaredError_eq_populationVariance_add_sq
          q hq ell i (finitePopulationRisk q ell i)

/-- Retained-affine-factor Bennett bound for the centered lower-tail loss
score.  This is the one-coordinate normalizer estimate used by the next joint
MGF slice. -/
theorem finiteBoundedLoss_centeredBennettNormalizer_le
    {p : Z → ℝ} (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    {t : ℝ} (ht : 0 ≤ t)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1) :
    (∑ z : Z, p z *
        Real.exp (t * (finitePopulationRisk p ell i - ell i z))) ≤
      1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i := by
  have hcenter :
      (∑ z : Z, p z * (finitePopulationRisk p ell i - ell i z)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
    simp [finitePopulationRisk]
  have hbound (z : Z) : finitePopulationRisk p ell i - ell i z ≤ 1 := by
    have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell i hell
    exact (sub_le_self _ (hell z).1).trans hR.2
  have hsecond :
      (∑ z : Z,
          p z * (finitePopulationRisk p ell i - ell i z) ^ (2 : Nat)) =
        finitePopulationVariance p ell i := by
    unfold finitePopulationVariance
    refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
    ring
  simpa using
    (bennett_mgf_le_one_add p
      (fun z : Z ↦ finitePopulationRisk p ell i - ell i z)
      (b := 1) (v := finitePopulationVariance p ell i) (lam := t)
      (by norm_num) ht hp.nonneg hp.sum_one hcenter hbound hsecond.le)

end

end FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt
