/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Statistics.FisherInformation

/-!
# Finite Cramer-Rao inequality

This module proves the one-parameter finite Cramer-Rao lower bound from the
Fisher-information layer. The theorem is stated with explicit regularity data:
nonnegative model weights, centered score, positive Fisher information, and the
unbiased-estimator covariance identity `Cov(T, score) = 1`.

The analytic content is the standard final step:

`1 = Cov(T, score)^2 <= Var(T) * I(theta)`,

then division by the positive Fisher information gives `1 / I(theta) <= Var(T)`.
-/

open scoped BigOperators

namespace FormalSLT.Statistics
namespace CramerRao

noncomputable section

open ClassicalEstimation
open FisherInformation

/-- **Finite one-parameter Cramer-Rao inequality.**

For a finite parametric model with centered score, positive Fisher information,
and an unbiased estimator whose derivative identity gives `Cov(T, score) = 1`,
the estimator variance is at least `1 / I(theta)`. -/
theorem cramerRao_unbiased {Ω : Type*} [Fintype Ω]
    (pmf pmfDeriv : ℝ -> Ω -> ℝ) (T : Ω -> ℝ) (theta I : ℝ)
    (hpmf_nonneg : ∀ x, 0 ≤ pmf theta x)
    (hscore_centered :
      weightedExpectation (pmf theta) (scoreFunction pmf pmfDeriv theta) = 0)
    (hfisher : fisherInformation pmf pmfDeriv theta = I)
    (hIpos : 0 < I)
    (hcov_identity :
      weightedCovariance (pmf theta) T (scoreFunction pmf pmfDeriv theta) = 1) :
    1 / I ≤ weightedVariance (pmf theta) T := by
  have hcs :=
    covariance_cauchy_schwarz
      (w := pmf theta) T (scoreFunction pmf pmfDeriv theta) hpmf_nonneg
  have hvar_score :
      weightedVariance (pmf theta) (scoreFunction pmf pmfDeriv theta) = I := by
    rw [weightedVariance_eq_secondMoment_of_mean_zero hscore_centered]
    exact hfisher
  have hmul : 1 ≤ weightedVariance (pmf theta) T * I := by
    rw [hcov_identity, hvar_score] at hcs
    norm_num at hcs
    exact hcs
  exact (div_le_iff₀ hIpos).2 hmul

/-! ### Concrete Bernoulli witness -/

/-- Bernoulli mass function on `Bool`, with parameter `p`. -/
def bernoulliWeights (p : ℝ) : Bool -> ℝ := fun b => if b then p else 1 - p

/-- Parameter derivative of the Bernoulli mass function. -/
def bernoulliWeightsDeriv (_p : ℝ) : Bool -> ℝ := fun b => if b then 1 else -1

/-- Bernoulli identity estimator, estimating the success probability. -/
def bernoulliIdentityEstimator : Bool -> ℝ := fun b => if b then 1 else 0

/-- Fisher information of the Bernoulli family in this finite model API. -/
def bernoulliFisherInformation (p : ℝ) : ℝ :=
  fisherInformation (fun u => bernoulliWeights u) bernoulliWeightsDeriv p

/-- The Bernoulli score relation `p(x) * score(x) = p'(x)` at `p = 1/2`. -/
theorem bernoulliHalf_score_relation :
    ∀ x,
      bernoulliWeights ((1 : ℝ) / 2) x *
          scoreFunction (fun u => bernoulliWeights u) bernoulliWeightsDeriv
            ((1 : ℝ) / 2) x
        = bernoulliWeightsDeriv ((1 : ℝ) / 2) x := by
  intro x
  cases x <;>
    norm_num [bernoulliWeights, bernoulliWeightsDeriv, scoreFunction]

/-- The Bernoulli score is centered at `p = 1/2`. -/
theorem bernoulliHalf_score_mean_zero :
    weightedExpectation (bernoulliWeights ((1 : ℝ) / 2))
        (scoreFunction (fun u => bernoulliWeights u) bernoulliWeightsDeriv
          ((1 : ℝ) / 2))
      = 0 := by
  exact score_mean_zero_of_finite_regular
    (pmf := fun u => bernoulliWeights u)
    (pmfDeriv := bernoulliWeightsDeriv)
    (theta := (1 : ℝ) / 2)
    bernoulliHalf_score_relation
    (by
      rw [Fintype.sum_bool]
      norm_num [bernoulliWeightsDeriv])

/-- At `p = 1/2`, Bernoulli Fisher information is `4`. -/
theorem bernoulliHalfFisherInformation :
    bernoulliFisherInformation ((1 : ℝ) / 2) = 4 := by
  norm_num [bernoulliFisherInformation, fisherInformation, weightedExpectation,
    scoreFunction, bernoulliWeights, bernoulliWeightsDeriv]

/-- At `p = 1/2`, the Bernoulli identity estimator has covariance `1` with the score. -/
theorem bernoulliHalf_covariance_identity :
    weightedCovariance (bernoulliWeights ((1 : ℝ) / 2)) bernoulliIdentityEstimator
        (scoreFunction (fun u => bernoulliWeights u) bernoulliWeightsDeriv
          ((1 : ℝ) / 2))
      = 1 := by
  norm_num [weightedCovariance, weightedExpectation, bernoulliWeights,
    bernoulliIdentityEstimator, scoreFunction, bernoulliWeightsDeriv]

/-- Concrete Cramer-Rao inequality for the Bernoulli identity estimator at `p = 1/2`. -/
theorem bernoulliHalfCramerRaoBound :
    1 / bernoulliFisherInformation ((1 : ℝ) / 2)
      ≤ weightedVariance (bernoulliWeights ((1 : ℝ) / 2)) bernoulliIdentityEstimator := by
  refine cramerRao_unbiased
    (pmf := fun u => bernoulliWeights u)
    (pmfDeriv := bernoulliWeightsDeriv)
    (T := bernoulliIdentityEstimator)
    (theta := (1 : ℝ) / 2)
    (I := bernoulliFisherInformation ((1 : ℝ) / 2))
    ?_ bernoulliHalf_score_mean_zero rfl ?_ bernoulliHalf_covariance_identity
  · intro x
    cases x <;> norm_num [bernoulliWeights]
  · rw [bernoulliHalfFisherInformation]
    norm_num

/-- Concrete sharp witness: at `p = 1/2`, the Bernoulli identity-estimator
variance equals the Cramer-Rao lower bound `1 / I = 1/4`. -/
theorem bernoulliHalfCramerRaoWitness :
    weightedVariance (bernoulliWeights ((1 : ℝ) / 2)) bernoulliIdentityEstimator
      = 1 / bernoulliFisherInformation ((1 : ℝ) / 2) := by
  rw [bernoulliHalfFisherInformation]
  norm_num [weightedVariance, weightedExpectation, bernoulliWeights,
    bernoulliIdentityEstimator]

end

end CramerRao
end FormalSLT.Statistics
