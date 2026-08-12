/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayesKL

/-!
# Finite exponential tilts

This module normalizes an exponentially tilted finite probability mass
function.  The base PMF may have zero-mass atoms; full support is not required.

For a base PMF `p` and an arbitrary score `score`, it defines

`q(z) = p(z) * exp(score(z)) / sum_z p(z) * exp(score(z))`

and proves that `q` is a PMF together with the exact finite
change-of-measure identity.  This is the one-coordinate algebraic foundation;
it does not yet include product-sample identities, bounded-loss estimates, or
joint mean/variance exponential moments.
-/

namespace FormalSLT.PACBayes.FiniteExponentialTilt

open Finset Real BigOperators
open FormalSLT.PACBayesKL

noncomputable section

variable {Z : Type*} [Fintype Z]

/-- Normalizing constant for an exponential tilt of a finite weight function. -/
def finiteExponentialTiltNormalizer (p : Z → ℝ) (score : Z → ℝ) : ℝ :=
  ∑ z, p z * Real.exp (score z)

/-- Exponential tilt of a finite weight function, normalized by its partition sum. -/
def finiteExponentialTiltPMF (p : Z → ℝ) (score : Z → ℝ) (z : Z) : ℝ :=
  p z * Real.exp (score z) / finiteExponentialTiltNormalizer p score

/-- The exponential-tilt normalizer is positive for every finite PMF, even
when the base PMF does not have full support. -/
theorem finiteExponentialTiltNormalizer_pos
    {p : Z → ℝ} (hp : IsPMF p) (score : Z → ℝ) :
    0 < finiteExponentialTiltNormalizer p score := by
  have hpSumPos : 0 < ∑ z : Z, p z := by
    rw [hp.sum_one]
    exact zero_lt_one
  have hPositiveAtom : ∃ z ∈ (Finset.univ : Finset Z), 0 < p z :=
    (Finset.sum_pos_iff_of_nonneg (fun z _hz ↦ hp.nonneg z)).mp hpSumPos
  unfold finiteExponentialTiltNormalizer
  apply Finset.sum_pos'
  · intro z _hz
    exact mul_nonneg (hp.nonneg z) (Real.exp_pos _).le
  · rcases hPositiveAtom with ⟨z, hz, hpz⟩
    exact ⟨z, hz, mul_pos hpz (Real.exp_pos _)⟩

/-- Exponentially tilting a finite PMF produces another finite PMF. -/
theorem finiteExponentialTiltPMF_isPMF
    {p : Z → ℝ} (hp : IsPMF p) (score : Z → ℝ) :
    IsPMF (finiteExponentialTiltPMF p score) where
  nonneg z := by
    unfold finiteExponentialTiltPMF
    exact div_nonneg
      (mul_nonneg (hp.nonneg z) (Real.exp_pos _).le)
      (finiteExponentialTiltNormalizer_pos hp score).le
  sum_one := by
    unfold finiteExponentialTiltPMF
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (finiteExponentialTiltNormalizer_pos hp score))

/-- Pointwise cancellation of the positive exponential-tilt normalizer. -/
theorem finiteExponentialTiltPMF_mul_normalizer
    {p : Z → ℝ} (hp : IsPMF p) (score : Z → ℝ) (z : Z) :
    finiteExponentialTiltPMF p score z *
        finiteExponentialTiltNormalizer p score =
      p z * Real.exp (score z) := by
  unfold finiteExponentialTiltPMF
  exact div_mul_cancel₀ _
    (ne_of_gt (finiteExponentialTiltNormalizer_pos hp score))

/-- Exact one-coordinate finite change of measure under an exponential tilt. -/
theorem finiteExponentialTilt_changeOfMeasure
    {p : Z → ℝ} (hp : IsPMF p) (score g : Z → ℝ) :
    (∑ z, p z * Real.exp (score z) * g z) =
      finiteExponentialTiltNormalizer p score *
        ∑ z, finiteExponentialTiltPMF p score z * g z := by
  calc
    (∑ z, p z * Real.exp (score z) * g z) =
        ∑ z, (finiteExponentialTiltPMF p score z *
          finiteExponentialTiltNormalizer p score) * g z := by
      refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
      rw [finiteExponentialTiltPMF_mul_normalizer hp score z]
    _ = finiteExponentialTiltNormalizer p score *
        ∑ z, finiteExponentialTiltPMF p score z * g z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _hz ↦ ?_)
      ring

end

end FormalSLT.PACBayes.FiniteExponentialTilt
