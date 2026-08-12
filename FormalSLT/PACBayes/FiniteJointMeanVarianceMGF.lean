/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt
import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF

/-!
# Fixed-n joint mean and empirical-variance exponential moments

This module combines the lower-tail mean score with the Bessel empirical-
variance score for one fixed hypothesis and one fixed sample size.  The proof
tilts the finite data PMF by `exp (-t * ell i z)`, applies the existing
Tolstikhin--Seldin empirical-variance MGF under the tilted PMF, and transports
the resulting variance term back using
`exp (-t) * V_p <= V_{q_t}`.

The endpoint is a per-hypothesis expectation bound.  There is no prior
mixture, Markov step, Donsker--Varadhan argument, tilt catalog, confidence
event, or post-data optimization in this module.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVarianceMGF

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt

noncomputable section

variable {Z ι : Type*}

/-- Linear-minus-quadratic variance coefficient left after applying the
Tolstikhin--Seldin Bessel empirical-variance MGF. -/
def finiteJointMeanVarianceKappa (n : ℕ) (eta : ℝ) : ℝ :=
  eta * (n : ℝ) -
    eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) /
      (2 * ((n : ℝ) - 1))

/-- The joint variance coefficient is nonnegative throughout the exact range
`eta * n <= 2 * (n - 1)`. -/
theorem finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le
    {n : ℕ} {eta : ℝ} (hn : 2 ≤ n) (heta : 0 ≤ eta)
    (heta_upper : eta * (n : ℝ) ≤ 2 * ((n : ℝ) - 1)) :
    0 ≤ finiteJointMeanVarianceKappa n eta := by
  have hnPredPos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    linarith
  have hdenPos : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by positivity
  have hetaN : 0 ≤ eta * (n : ℝ) :=
    mul_nonneg heta (Nat.cast_nonneg n)
  have hgap : 0 ≤ 2 * ((n : ℝ) - 1) - eta * (n : ℝ) := by
    linarith
  have hfactor :
      finiteJointMeanVarianceKappa n eta =
        (eta * (n : ℝ)) *
            (2 * ((n : ℝ) - 1) - eta * (n : ℝ)) /
          (2 * ((n : ℝ) - 1)) := by
    unfold finiteJointMeanVarianceKappa
    field_simp [ne_of_gt hdenPos]
  rw [hfactor]
  exact div_nonneg (mul_nonneg hetaN hgap) hdenPos.le

/-- Under the lower-tail tilted PMF, the negative Bessel empirical-variance
moment is bounded by the population variance with coefficient `kappa`. -/
theorem finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight (finiteBoundedLossTiltPMF p ell i t) S *
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
      Real.exp
        (-finiteJointMeanVarianceKappa n eta *
          finitePopulationVariance (finiteBoundedLossTiltPMF p ell i t) ell i) := by
  let q : Z → ℝ := finiteBoundedLossTiltPMF p ell i t
  let Vq : ℝ := finitePopulationVariance q ell i
  let penalty : ℝ :=
    eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) * Vq /
      (2 * ((n : ℝ) - 1))
  have hq : IsPMF q := finiteBoundedLossTiltPMF_isPMF hp ell i t
  have hmgf :=
    finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
      hn q hq ell i hell heta
  have hfactor :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight q S *
            Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) =
        Real.exp (-eta * (n : ℝ) * Vq) *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp
                (eta * (n : ℝ) *
                  (Vq - finiteEmpiricalVariance ell i S)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _hS ↦ ?_)
    calc
      finiteProductSampleWeight q S *
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) =
        finiteProductSampleWeight q S *
          (Real.exp (-eta * (n : ℝ) * Vq) *
            Real.exp
              (eta * (n : ℝ) *
                (Vq - finiteEmpiricalVariance ell i S))) := by
          rw [← Real.exp_add]
          congr 2
          ring
      _ = Real.exp (-eta * (n : ℝ) * Vq) *
          (finiteProductSampleWeight q S *
            Real.exp
              (eta * (n : ℝ) *
                (Vq - finiteEmpiricalVariance ell i S))) := by ring
  change
    (∑ S : Fin n → Z,
        finiteProductSampleWeight q S *
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
      Real.exp (-finiteJointMeanVarianceKappa n eta * Vq)
  rw [hfactor]
  change
    (∑ S : Fin n → Z,
        finiteProductSampleWeight q S *
          Real.exp
            (eta * (n : ℝ) *
              (Vq - finiteEmpiricalVariance ell i S))) ≤
      Real.exp penalty at hmgf
  calc
    Real.exp (-eta * (n : ℝ) * Vq) *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp
                (eta * (n : ℝ) *
                  (Vq - finiteEmpiricalVariance ell i S))) ≤
        Real.exp (-eta * (n : ℝ) * Vq) * Real.exp penalty :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-finiteJointMeanVarianceKappa n eta * Vq) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [penalty]
      unfold finiteJointMeanVarianceKappa
      ring

/-- Unnormalized fixed-n joint MGF for the lower-tail mean score and Bessel
empirical variance.  The nonnegative `kappa` hypothesis is exactly what lets
the tilted population variance be replaced by `exp (-t) * V_p`. -/
theorem finiteJointMeanVarianceMGF_le
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} {t eta : ℝ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (t * (n : ℝ) *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
      (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i) ^ n *
        Real.exp
          (-Real.exp (-t) * finiteJointMeanVarianceKappa n eta *
            finitePopulationVariance p ell i) := by
  let q : Z → ℝ := finiteBoundedLossTiltPMF p ell i t
  let Vp : ℝ := finitePopulationVariance p ell i
  let Vq : ℝ := finitePopulationVariance q ell i
  let R : ℝ := finitePopulationRisk p ell i
  let N : ℝ := finiteBoundedLossTiltNormalizer p ell i t
  let A : ℝ := 1 + (Real.exp t - 1 - t) * Vp
  let K : ℝ := finiteJointMeanVarianceKappa n eta
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnRNe : (n : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hempirical (S : Fin n → Z) :
      (n : ℝ) * finiteEmpiricalRisk ell i S =
        ∑ k : Fin n, ell i (S k) := by
    unfold finiteEmpiricalRisk
    field_simp [hnRNe]
  have hscore (S : Fin n → Z) :
      t * (n : ℝ) * (R - finiteEmpiricalRisk ell i S) =
        t * (n : ℝ) * R +
          ∑ k : Fin n, boundedLossTiltScore ell i t (S k) := by
    simp only [boundedLossTiltScore]
    rw [← Finset.mul_sum]
    rw [← hempirical S]
    ring
  have hpoint (S : Fin n → Z) :
      Real.exp
          (t * (n : ℝ) * (R - finiteEmpiricalRisk ell i S) -
            eta * (n : ℝ) * finiteEmpiricalVariance ell i S) =
        Real.exp (t * (n : ℝ) * R) *
          Real.exp (∑ k : Fin n, boundedLossTiltScore ell i t (S k)) *
            Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hscore S]
    ring
  have hchange :=
    finiteBoundedLossTiltProduct_changeOfMeasure
      (n := n) hp ell i t
        (fun S : Fin n → Z ↦
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S))
  have hcenter :
      Real.exp (t * R) * N =
        ∑ z : Z, p z * Real.exp (t * (R - ell i z)) := by
    unfold N finiteBoundedLossTiltNormalizer
    unfold FormalSLT.PACBayes.FiniteExponentialTilt.finiteExponentialTiltNormalizer
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
    simp only [boundedLossTiltScore]
    calc
      Real.exp (t * R) * (p z * Real.exp (-t * ell i z)) =
          p z * (Real.exp (t * R) * Real.exp (-t * ell i z)) := by ring
      _ = p z * Real.exp (t * (R - ell i z)) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hexpPower :
      Real.exp (t * (n : ℝ) * R) * N ^ n =
        (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n := by
    calc
      Real.exp (t * (n : ℝ) * R) * N ^ n =
          Real.exp (t * R) ^ n * N ^ n := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      _ = (Real.exp (t * R) * N) ^ n := by rw [mul_pow]
      _ = (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n := by
        rw [hcenter]
  have hrawFactor :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) =
        (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
    change
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) *
                  (R - finiteEmpiricalRisk ell i S) -
                eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) = _
    calc
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) * (R - finiteEmpiricalRisk ell i S) -
                eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) =
          Real.exp (t * (n : ℝ) * R) *
            ∑ S : Fin n → Z,
              finiteProductSampleWeight p S *
                Real.exp (∑ k : Fin n, boundedLossTiltScore ell i t (S k)) *
                  Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _hS ↦ ?_)
        rw [hpoint S]
        ring
      _ = Real.exp (t * (n : ℝ) * R) *
          (N ^ n *
            ∑ S : Fin n → Z,
              finiteProductSampleWeight q S *
                Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) := by
        have hchange' :
            (∑ S : Fin n → Z,
                finiteProductSampleWeight p S *
                  Real.exp
                    (∑ k : Fin n, boundedLossTiltScore ell i t (S k)) *
                  Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) =
              N ^ n *
                ∑ S : Fin n → Z,
                  finiteProductSampleWeight q S *
                    Real.exp
                      (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
          simpa only [boundedLossTiltScore, N, q] using hchange
        rw [hchange']
      _ = (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
        rw [← mul_assoc, hexpPower]
  have hcenterBound :
      (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ≤ A := by
    exact finiteBoundedLoss_centeredBennettNormalizer_le hp ell i ht hell
  have hcenterNonneg :
      0 ≤ ∑ z : Z, p z * Real.exp (t * (R - ell i z)) :=
    Finset.sum_nonneg
      (fun z _hz ↦ mul_nonneg (hp.nonneg z) (Real.exp_pos _).le)
  have hcenterPow :
      (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n ≤ A ^ n :=
    pow_le_pow_left₀ hcenterNonneg hcenterBound n
  have hA_nonneg : 0 ≤ A := hcenterNonneg.trans hcenterBound
  have hqMoment :=
    finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le
      hn p hp ell i hell t heta
  change
    (∑ S : Fin n → Z,
        finiteProductSampleWeight q S *
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
      Real.exp (-K * Vq) at hqMoment
  have hqMomentNonneg :
      0 ≤ ∑ S : Fin n → Z,
        finiteProductSampleWeight q S *
          Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
    exact Finset.sum_nonneg (fun S _hS ↦
      mul_nonneg
        (Finset.prod_nonneg (fun k _hk ↦
          (finiteBoundedLossTiltPMF_isPMF hp ell i t).nonneg (S k)))
        (Real.exp_pos _).le)
  have hvariance : Vp * Real.exp (-t) ≤ Vq := by
    exact finitePopulationVariance_mul_exp_neg_le_tilted hp ell i ht hell
  have hvarianceScaled : K * (Vp * Real.exp (-t)) ≤ K * Vq :=
    mul_le_mul_of_nonneg_left hvariance hkappa
  have hvarianceExp :
      Real.exp (-K * Vq) ≤ Real.exp (-Real.exp (-t) * K * Vp) := by
    apply Real.exp_le_exp.mpr
    calc
      -K * Vq ≤ -(K * (Vp * Real.exp (-t))) := by
        simpa only [neg_mul] using neg_le_neg hvarianceScaled
      _ = -Real.exp (-t) * K * Vp := by ring
  rw [hrawFactor]
  change _ ≤ A ^ n * Real.exp (-Real.exp (-t) * K * Vp)
  calc
    (∑ z : Z, p z * Real.exp (t * (R - ell i z))) ^ n *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
        A ^ n *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight q S *
              Real.exp (-eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) :=
      mul_le_mul_of_nonneg_right hcenterPow hqMomentNonneg
    _ ≤ A ^ n * Real.exp (-K * Vq) :=
      mul_le_mul_of_nonneg_left hqMoment (pow_nonneg hA_nonneg n)
    _ ≤ A ^ n * Real.exp (-Real.exp (-t) * K * Vp) :=
      mul_le_mul_of_nonneg_left hvarianceExp (pow_nonneg hA_nonneg n)

/-- Normalized fixed-n joint score.  The exact retained Bennett factor appears
inside the logarithm, and the transported variance correction is added back
inside the exponent. -/
theorem finiteJointMeanVariance_normalizedMGF_le_one
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} {t eta : ℝ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (t * (n : ℝ) *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              eta * (n : ℝ) * finiteEmpiricalVariance ell i S -
              (n : ℝ) * Real.log
                (1 + (Real.exp t - 1 - t) *
                  finitePopulationVariance p ell i) +
              Real.exp (-t) * finiteJointMeanVarianceKappa n eta *
                finitePopulationVariance p ell i)) ≤ 1 := by
  let Vp : ℝ := finitePopulationVariance p ell i
  let A : ℝ := 1 + (Real.exp t - 1 - t) * Vp
  let C : ℝ := Real.exp (-t) * finiteJointMeanVarianceKappa n eta * Vp
  have hpsi : 0 ≤ Real.exp t - 1 - t := by
    linarith [Real.add_one_le_exp t]
  have hVp : 0 ≤ Vp := finitePopulationVariance_nonneg p hp ell i
  have hApos : 0 < A := by
    dsimp only [A]
    nlinarith [mul_nonneg hpsi hVp]
  have hraw :=
    finiteJointMeanVarianceMGF_le
      hn p hp ell i hell ht heta hkappa
  have hrawBound :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (t * (n : ℝ) *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
      A ^ n * Real.exp (-C) := by
    calc
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
          (1 + (Real.exp t - 1 - t) *
              finitePopulationVariance p ell i) ^ n *
            Real.exp
              (-Real.exp (-t) * finiteJointMeanVarianceKappa n eta *
                finitePopulationVariance p ell i) := hraw
      _ = A ^ n * Real.exp (-C) := by
        dsimp only [A, C, Vp]
        congr 2
        ring
  have hfactor :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                eta * (n : ℝ) * finiteEmpiricalVariance ell i S -
                (n : ℝ) * Real.log A + C)) =
        Real.exp (-(n : ℝ) * Real.log A + C) *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp
                (t * (n : ℝ) *
                    (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                  eta * (n : ℝ) * finiteEmpiricalVariance ell i S) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _hS ↦ ?_)
    calc
      finiteProductSampleWeight p S *
            Real.exp
              (t * (n : ℝ) *
                    (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                  eta * (n : ℝ) * finiteEmpiricalVariance ell i S -
                  (n : ℝ) * Real.log A + C) =
          finiteProductSampleWeight p S *
            (Real.exp (-(n : ℝ) * Real.log A + C) *
              Real.exp
                (t * (n : ℝ) *
                    (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                  eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(n : ℝ) * Real.log A + C) *
            (finiteProductSampleWeight p S *
              Real.exp
                (t * (n : ℝ) *
                    (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                  eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) := by
        ring
  have hApow : A ^ n = Real.exp ((n : ℝ) * Real.log A) := by
    rw [Real.exp_nat_mul, Real.exp_log hApos]
  change
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (t * (n : ℝ) *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              eta * (n : ℝ) * finiteEmpiricalVariance ell i S -
              (n : ℝ) * Real.log A + C)) ≤ 1
  rw [hfactor]
  calc
    Real.exp (-(n : ℝ) * Real.log A + C) *
          (∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp
                (t * (n : ℝ) *
                    (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                  eta * (n : ℝ) * finiteEmpiricalVariance ell i S)) ≤
        Real.exp (-(n : ℝ) * Real.log A + C) *
          (A ^ n * Real.exp (-C)) :=
      mul_le_mul_of_nonneg_left hrawBound (Real.exp_pos _).le
    _ = 1 := by
      rw [hApow, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      simp

end

end FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
