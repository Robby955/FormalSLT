/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteProductBernstein
import FormalSLT.PACBayesBernstein

/-!
# Prior-averaged Bernstein moments for indicator losses

This module averages the exact hypothesis-specific normalized product MGF from
`FormalSLT.PACBayes.FiniteProductBernstein` over an arbitrary finite prior.  It
discharges the expected-moment premise used by the abstract finite PAC-Bayes
Bernstein confidence theorem.

The variance proxy remains hypothesis-specific:
`R_i * (1 - R_i) / n`.  The theorem assumes only that the prior is a PMF; full
support is intentionally deferred to the later KL change-of-measure layer.

The result is finite, fixed-sample, fixed-tilt, and population-variance.  It is
not empirical Bernstein, time-uniform, continuous-hypothesis, or all-tilt.

Mathematical sources: Boucheron, Lugosi, and Massart (2013), *Concentration
Inequalities*, for the Bernstein MGF normalization; Tolstikhin and Seldin
(2013), "PAC-Bayes-Empirical-Bernstein Inequality," for the variance-sensitive
PAC-Bayes context.  The theorem here supplies the prior-moment premise for the
repository's finite PAC-Bayes adapter; it is not by itself a posterior bound.
-/

namespace FormalSLT.PACBayes.IndicatorBernsteinMoment

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein

noncomputable section

variable {ι Z : Type*}

/-- The Bernstein scale for an indicator average over `n` observations. -/
def indicatorBernsteinScale (n : ℕ) : ℝ :=
  1 / (3 * (n : ℝ))

/-- The exact population-variance proxy for hypothesis `i` at sample size `n`. -/
def indicatorBernsteinVarianceProxy [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (bad : ι → Z → Bool) (i : ι) : ℝ :=
  indicatorPopulationRisk p bad i * (1 - indicatorPopulationRisk p bad i) /
    (n : ℝ)

/-- The abstract Bernstein normalization equals the exact product-MGF budget. -/
theorem indicatorBernstein_normalization_eq_budget [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (bad : ι → Z → Bool) (i : ι)
    {lambda : ℝ} (hlambda_lt : lambda < 3 * (n : ℝ)) :
    lambda ^ (2 : Nat) * indicatorBernsteinVarianceProxy n p bad i /
        (2 * (1 - indicatorBernsteinScale n * lambda)) =
      indicatorBernsteinMGFBudget n lambda (indicatorPopulationRisk p bad i) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  have hthree_n_ne : (3 * (n : ℝ)) ≠ 0 := by positivity
  have hden : 1 - lambda / (3 * (n : ℝ)) ≠ 0 := by
    have hratio : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    linarith
  unfold indicatorBernsteinVarianceProxy indicatorBernsteinScale
    indicatorBernsteinMGFBudget
  field_simp

/--
The normalized Bernstein prior moment for an arbitrary finite indicator class
has expectation at most one under the finite i.i.d. product law.

Only PMF normalization of the prior is required here.  Full support enters the
subsequent PAC-Bayes KL theorem, not this moment calculation.
-/
theorem indicator_expectedPriorBernsteinExpMoment_le_one
    [Fintype ι] [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (π : ι → ℝ) (hπ : IsPMF π)
    (bad : ι → Z → Bool)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ)) :
    expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight (n := n) p)
        π lambda (indicatorBernsteinScale n)
        (indicatorPopulationRisk p bad)
        (fun S i => finiteEmpiricalRisk (indicatorLoss bad) i S)
        (indicatorBernsteinVarianceProxy n p bad) ≤
      1 := by
  unfold expectedPriorBernsteinExpMoment priorBernsteinExpMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (π i *
            Real.exp
              (lambda *
                    (indicatorPopulationRisk p bad i -
                      finiteEmpiricalRisk (indicatorLoss bad) i S) -
                lambda ^ (2 : Nat) * indicatorBernsteinVarianceProxy n p bad i /
                  (2 * (1 - indicatorBernsteinScale n * lambda))))) =
        ∑ i : ι, π i *
          ∑ S : Fin n → Z,
            finiteProductSampleWeight p S *
              Real.exp
                (lambda *
                      (indicatorPopulationRisk p bad i -
                        finiteEmpiricalRisk (indicatorLoss bad) i S) -
                  indicatorBernsteinMGFBudget n lambda
                    (indicatorPopulationRisk p bad i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _hS
      rw [indicatorBernstein_normalization_eq_budget hn p bad i hlambda_lt]
      ring
    _ ≤ ∑ i : ι, π i * 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (indicator_product_normalizedMGF_le_one
          hn p hp bad i hlambda hlambda_lt)
        (hπ.nonneg i)
    _ = 1 := by simp [hπ.sum_one]

end

end FormalSLT.PACBayes.IndicatorBernsteinMoment
