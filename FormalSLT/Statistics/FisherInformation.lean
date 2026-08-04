/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Statistics.ClassicalEstimation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Finite Fisher-information layer

This module gives the finite parametric-statistics layer needed for the
Cramer-Rao inequality. A finite model is represented by a mass function
`pmf theta : Ω -> ℝ` and its parameter derivative `pmfDeriv theta : Ω -> ℝ`.
The score is `pmfDeriv / pmf`, Fisher information is `E[score^2]`, and the
regularity identities are named finite-sum lemmas:

* `score_mean_zero_of_finite_regular`: if the derivative mass sums to zero,
  the score is centered.
* `covariance_score_eq_deriv_mean`: if derivative commutes with the finite
  expectation of a fixed estimator, covariance with the score is that
  derivative.
* `covariance_cauchy_schwarz`: the Cramer-Rao step, proved from mathlib's
  finite Cauchy-Schwarz lemma.

The measure-theoretic dominated-differentiation-under-the-integral theorem is
not used here. Mathlib has parametric-integral differentiation lemmas, but the
StatLean v0.3 layer below is deliberately finite-sum based, matching the
classical-estimation layer in `ClassicalEstimation`.
-/

open scoped BigOperators
open Finset

namespace FormalSLT.Statistics
namespace FisherInformation

noncomputable section

open ClassicalEstimation

/-! ### Weighted moments -/

/-- Finite weighted variance `E[(X - E[X])^2]`. -/
def weightedVariance {Ω : Type*} [Fintype Ω] (w : Ω -> ℝ) (X : Ω -> ℝ) : ℝ :=
  ∑ x, w x * (X x - weightedExpectation w X) ^ 2

/-- Finite weighted covariance `E[(X - E[X])(Y - E[Y])]`. -/
def weightedCovariance {Ω : Type*} [Fintype Ω]
    (w : Ω -> ℝ) (X Y : Ω -> ℝ) : ℝ :=
  ∑ x, w x * (X x - weightedExpectation w X) * (Y x - weightedExpectation w Y)

/-- Weighted variance is nonnegative under nonnegative weights. -/
theorem weightedVariance_nonneg {Ω : Type*} [Fintype Ω]
    {w : Ω -> ℝ} (X : Ω -> ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ weightedVariance w X := by
  unfold weightedVariance
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)

/-- If a statistic is centered, its weighted variance is its weighted second moment. -/
theorem weightedVariance_eq_secondMoment_of_mean_zero {Ω : Type*} [Fintype Ω]
    {w : Ω -> ℝ} {X : Ω -> ℝ}
    (hmean : weightedExpectation w X = 0) :
    weightedVariance w X = weightedExpectation w (fun x => X x ^ 2) := by
  unfold weightedVariance
  rw [hmean]
  simp [weightedExpectation]

/-! ### Score and Fisher information -/

/-- Score function `s(theta; x) = d_theta pmf(theta, x) / pmf(theta, x)`. -/
def scoreFunction {Ω : Type*}
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (theta : ℝ) (x : Ω) : ℝ :=
  pmfDeriv theta x / pmf theta x

/-- Fisher information `I(theta) = E_theta[score(theta; X)^2]`. -/
def fisherInformation {Ω : Type*} [Fintype Ω]
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (theta : ℝ) : ℝ :=
  weightedExpectation (pmf theta) fun x => scoreFunction pmf pmfDeriv theta x ^ 2

/-- **Finite differentiation through a weighted expectation.**

For finite sample spaces, differentiating an expectation of a fixed statistic is
just differentiating each mass and summing the terms. -/
theorem hasDerivAt_weightedExpectation_param {Ω : Type*} [Fintype Ω]
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (T : Ω -> ℝ) (theta : ℝ)
    (hderiv : ∀ x, HasDerivAt (fun u => pmf u x) (pmfDeriv theta x) theta) :
    HasDerivAt
      (fun u => weightedExpectation (pmf u) T)
      (∑ x, pmfDeriv theta x * T x)
      theta := by
  change HasDerivAt (fun u => ∑ x, pmf u x * T x)
    (∑ x, pmfDeriv theta x * T x) theta
  have h := HasDerivAt.sum (u := (Finset.univ : Finset Ω)) fun x _ =>
    (hderiv x).mul_const (T x)
  have hfun : (∑ x : Ω, fun u => pmf u x * T x) =
      fun u => ∑ x : Ω, pmf u x * T x := by
    funext u
    rw [Fintype.sum_apply]
  rw [← hfun]
  exact h

/-- **Regularity: the finite score has mean zero.**

If `pmf * score` is the derivative mass and the derivative mass sums to zero,
then `E_theta[score] = 0`. -/
theorem score_mean_zero_of_finite_regular {Ω : Type*} [Fintype Ω]
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (theta : ℝ)
    (hscore :
      ∀ x, pmf theta x * scoreFunction pmf pmfDeriv theta x = pmfDeriv theta x)
    (hsum_deriv : ∑ x, pmfDeriv theta x = 0) :
    weightedExpectation (pmf theta) (scoreFunction pmf pmfDeriv theta) = 0 := by
  unfold weightedExpectation
  calc
    ∑ x, pmf theta x * scoreFunction pmf pmfDeriv theta x
        = ∑ x, pmfDeriv theta x := by
          exact Finset.sum_congr rfl fun x _ => hscore x
    _ = 0 := hsum_deriv

/-- **Covariance identity for a finite parametric model.**

If derivative commutes with the finite expectation of a fixed estimator `T`,
then `Cov_theta(T, score) = d/dtheta E_theta[T]`. -/
theorem covariance_score_eq_deriv_mean {Ω : Type*} [Fintype Ω]
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (T : Ω -> ℝ) (theta meanDeriv : ℝ)
    (hscore :
      ∀ x, pmf theta x * scoreFunction pmf pmfDeriv theta x = pmfDeriv theta x)
    (hscore_mean :
      weightedExpectation (pmf theta) (scoreFunction pmf pmfDeriv theta) = 0)
    (hmean_deriv : ∑ x, pmfDeriv theta x * T x = meanDeriv) :
    weightedCovariance (pmf theta) T (scoreFunction pmf pmfDeriv theta)
      = meanDeriv := by
  unfold weightedCovariance
  rw [hscore_mean]
  unfold weightedExpectation
  simp only [sub_zero]
  calc
    ∑ x,
        pmf theta x * (T x - ∑ y, pmf theta y * T y)
          * scoreFunction pmf pmfDeriv theta x
        =
      ∑ x,
        (T x - ∑ y, pmf theta y * T y)
          * (pmf theta x * scoreFunction pmf pmfDeriv theta x) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ = ∑ x, (T x - ∑ y, pmf theta y * T y) * pmfDeriv theta x := by
          exact Finset.sum_congr rfl fun x _ => by rw [hscore x]
    _ = ∑ x, T x * pmfDeriv theta x
          - (∑ y, pmf theta y * T y) * ∑ x, pmfDeriv theta x := by
          calc
            ∑ x, (T x - ∑ y, pmf theta y * T y) * pmfDeriv theta x
                = ∑ x, (T x * pmfDeriv theta x
                    - (∑ y, pmf theta y * T y) * pmfDeriv theta x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _hx
                  ring
            _ = ∑ x, T x * pmfDeriv theta x
                  - ∑ x, (∑ y, pmf theta y * T y) * pmfDeriv theta x := by
                  rw [Finset.sum_sub_distrib]
            _ = ∑ x, T x * pmfDeriv theta x
                  - (∑ y, pmf theta y * T y) * ∑ x, pmfDeriv theta x := by
                  rw [Finset.mul_sum]
    _ = ∑ x, pmfDeriv theta x * T x := by
          have hderiv_sum : ∑ x, pmfDeriv theta x = 0 := by
            calc
              ∑ x, pmfDeriv theta x
                  = ∑ x, pmf theta x * scoreFunction pmf pmfDeriv theta x := by
                  exact (Finset.sum_congr rfl fun x _ => (hscore x).symm)
              _ = 0 := hscore_mean
          rw [hderiv_sum]
          simp
          exact Finset.sum_congr rfl fun x _ => by ring
    _ = meanDeriv := hmean_deriv

/-- **Weighted finite Cauchy-Schwarz for covariance.**

For nonnegative finite weights,
`Cov(X,Y)^2 <= Var(X) * Var(Y)`. -/
theorem covariance_cauchy_schwarz {Ω : Type*} [Fintype Ω]
    {w : Ω -> ℝ} (X Y : Ω -> ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedCovariance w X Y ^ 2 ≤ weightedVariance w X * weightedVariance w Y := by
  let mx := weightedExpectation w X
  let my := weightedExpectation w Y
  have hcs :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset Ω))
      (r := fun x => w x * (X x - mx) * (Y x - my))
      (f := fun x => w x * (X x - mx) ^ 2)
      (g := fun x => w x * (Y x - my) ^ 2)
      (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
      (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
      (fun x _ => le_of_eq (by ring))
  simpa [weightedCovariance, weightedVariance, mx, my] using hcs

end

end FisherInformation
end FormalSLT.Statistics
