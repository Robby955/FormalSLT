/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteExponentialTilt
import FormalSLT.PACBayesFiniteProductMGF

/-!
# Finite-product exponential tilts

This module lifts the exact one-coordinate exponential-tilt identity to a
finite iid sample.  It proves the pointwise relation between the base and
tilted product weights and the resulting change-of-measure formula for an
arbitrary real-valued sample functional.

The scope is purely algebraic and finite.  There are no bounded-loss,
empirical-variance, joint-MGF, or PAC-Bayes confidence claims here.
-/

namespace FormalSLT.PACBayes.FiniteExponentialTiltProduct

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteExponentialTilt

noncomputable section

variable {Z : Type*} [Fintype Z]

/-- Pointwise relation between a base finite product weight and its
exponentially tilted product weight. -/
theorem finiteProductSampleWeight_mul_exp_sum_eq
    {n : ℕ} {p : Z → ℝ} (hp : IsPMF p) (score : Z → ℝ)
    (S : Fin n → Z) :
    finiteProductSampleWeight p S * Real.exp (∑ k, score (S k)) =
      finiteExponentialTiltNormalizer p score ^ n *
        finiteProductSampleWeight
          (finiteExponentialTiltPMF p score) S := by
  classical
  unfold finiteProductSampleWeight
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  calc
    (∏ k : Fin n, p (S k) * Real.exp (score (S k))) =
        ∏ k : Fin n,
          finiteExponentialTiltPMF p score (S k) *
            finiteExponentialTiltNormalizer p score := by
      refine Finset.prod_congr rfl (fun k _hk ↦ ?_)
      exact (finiteExponentialTiltPMF_mul_normalizer hp score (S k)).symm
    _ = (∏ k : Fin n, finiteExponentialTiltPMF p score (S k)) *
        ∏ _k : Fin n, finiteExponentialTiltNormalizer p score := by
      rw [Finset.prod_mul_distrib]
    _ = finiteExponentialTiltNormalizer p score ^ n *
        ∏ k : Fin n, finiteExponentialTiltPMF p score (S k) := by
      simp [Finset.prod_const, Fintype.card_fin, mul_comm]

/-- Exact finite-product change of measure under an exponential tilt, for an
arbitrary real-valued sample functional. -/
theorem finiteProductExponentialTilt_changeOfMeasure
    {n : ℕ} {p : Z → ℝ} (hp : IsPMF p) (score : Z → ℝ)
    (g : (Fin n → Z) → ℝ) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (∑ k, score (S k)) * g S) =
      finiteExponentialTiltNormalizer p score ^ n *
        ∑ S : Fin n → Z,
          finiteProductSampleWeight
              (finiteExponentialTiltPMF p score) S * g S := by
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (∑ k, score (S k)) * g S) =
      ∑ S : Fin n → Z,
        (finiteExponentialTiltNormalizer p score ^ n *
          finiteProductSampleWeight
            (finiteExponentialTiltPMF p score) S) * g S := by
      refine Finset.sum_congr rfl (fun S _hS ↦ ?_)
      rw [finiteProductSampleWeight_mul_exp_sum_eq hp score S]
    _ = finiteExponentialTiltNormalizer p score ^ n *
        ∑ S : Fin n → Z,
          finiteProductSampleWeight
              (finiteExponentialTiltPMF p score) S * g S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S _hS ↦ ?_)
      ring

end

end FormalSLT.PACBayes.FiniteExponentialTiltProduct
