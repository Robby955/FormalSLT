/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
import FormalSLT.PACBayes.FiniteProductBernstein
import FormalSLT.PACBayesBernstein

/-!
# Finite PAC-Bayes empirical-variance confidence bounds

This module lifts the source-normalized finite empirical-variance MGF to a
fixed-tilt PAC-Bayes confidence theorem. For a finite hypothesis class, one
finite-product bad-sample set has mass at most `delta`; outside it, every
posterior, including a posterior selected after seeing the sample, satisfies a
bound on its posterior average of the per-hypothesis population variances.

The theorem is finite, iid, fixed-sample, and fixed-tilt. The posterior average
is taken after computing each hypothesis's variance; it is not the variance of
a posterior-averaged loss. This module does not optimize over a tilt grid and
does not provide a time-uniform result.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteProductBernstein

noncomputable section

variable {Z ι : Type*}

/-- Prior-average normalization of the empirical-variance exponential moment. -/
theorem finiteEmpiricalVariance_expectedPriorBernsteinExpMoment_le_one
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) :
    expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight p) prior (eta * (n : ℝ)) 0
        (finitePopulationVariance p ell)
        (fun (S : Fin n → Z) i => finiteEmpiricalVariance ell i S)
        (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1)) ≤ 1 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hpred : (n : ℝ) - 1 ≠ 0 := by linarith
  have hexp (i : ι) (S : Fin n → Z) :
      (eta * (n : ℝ)) *
            (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
          (eta * (n : ℝ)) ^ (2 : Nat) *
              (finitePopulationVariance p ell i / ((n : ℝ) - 1)) /
            (2 * (1 - 0 * (eta * (n : ℝ)))) =
        eta * (n : ℝ) *
            (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
          eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) *
              finitePopulationVariance p ell i /
            (2 * ((n : ℝ) - 1)) := by
    field_simp [hpred]
    ring
  unfold expectedPriorBernsteinExpMoment priorBernsteinExpMoment
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (∑ i : ι, prior i *
            Real.exp
              ((eta * (n : ℝ)) *
                  (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
                (eta * (n : ℝ)) ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / ((n : ℝ) - 1)) /
                  (2 * (1 - 0 * (eta * (n : ℝ))))))) =
      ∑ S : Fin n → Z, ∑ i : ι,
        finiteProductSampleWeight p S *
          (prior i *
            Real.exp
              ((eta * (n : ℝ)) *
                  (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
                (eta * (n : ℝ)) ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / ((n : ℝ) - 1)) /
                  (2 * (1 - 0 * (eta * (n : ℝ)))))) := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (prior i *
            Real.exp
              ((eta * (n : ℝ)) *
                  (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
                (eta * (n : ℝ)) ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / ((n : ℝ) - 1)) /
                  (2 * (1 - 0 * (eta * (n : ℝ)))))) := by
        rw [Finset.sum_comm]
    _ = ∑ i : ι, prior i *
        (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (eta * (n : ℝ) *
                  (finitePopulationVariance p ell i - finiteEmpiricalVariance ell i S) -
                eta ^ (2 : Nat) * (n : ℝ) ^ (2 : Nat) *
                  finitePopulationVariance p ell i /
                    (2 * ((n : ℝ) - 1)))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [hexp i S]
        ring
    _ ≤ ∑ i : ι, prior i * 1 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hprior.nonneg i)
      exact finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
        hn p hp ell i (hell i) heta
    _ = 1 := by simp [hprior.sum_one]

/-- Samples where some posterior violates the fixed-tilt variance bound. -/
def finiteEmpiricalVariancePACBayesBadSamples
    [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ)
    (ell : ι → Z → ℝ) (eta delta : ℝ) : Finset (Fin n → Z) :=
  finitePACBayesBernsteinFixedLambdaBadSamples
    prior (eta * (n : ℝ)) 0 delta
    (finitePopulationVariance p ell)
    (fun S i => finiteEmpiricalVariance ell i S)
    (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1))

/-- Outside the bad-sample set, every posterior satisfies the unrearranged
population-variance minus empirical-variance gap bound. -/
theorem finiteEmpiricalVariance_posteriorGap_le_of_not_mem
    [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ)
    (ell : ι → Z → ℝ) (eta delta : ℝ)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell eta delta)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorGeneralizationGap rho
        (finitePopulationVariance p ell)
        (fun i => finiteEmpiricalVariance ell i S) ≤
      (klDiv rho prior + Real.log (1 / delta)) / (eta * (n : ℝ)) +
        (eta * (n : ℝ)) * posteriorMarginVarianceProxy rho
          (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1)) / 2 := by
  classical
  by_contra hbound
  apply hS
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨rho, hrho, ?_⟩
  simpa only [zero_mul, sub_zero, mul_one] using lt_of_not_ge hbound

/-- The fixed-tilt empirical-variance PAC-Bayes bad set has product-law mass at
most `delta`. The same event is simultaneous over all finite posteriors. -/
theorem finiteEmpiricalVariancePACBayes_badEventMass_le_delta
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta delta : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) :
    (∑ S ∈ finiteEmpiricalVariancePACBayesBadSamples
        n p prior ell eta delta,
        finiteProductSampleWeight p S) ≤ delta := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hlambda : 0 < eta * (n : ℝ) := mul_pos heta hnR
  exact finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    (finiteProductSampleWeight_isPMF hp) hprior
    (eta * (n : ℝ)) 0 delta hlambda (by norm_num) hdelta
    (finitePopulationVariance p ell)
    (fun (S : Fin n → Z) i => finiteEmpiricalVariance ell i S)
    (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1))
    (finiteEmpiricalVariance_expectedPriorBernsteinExpMoment_le_one
      hn p hp hprior.toIsPMF ell hell heta.le)

/-- Rearranged PAC-Bayes upper bound for the posterior average of the
per-hypothesis population variances.

The strict tilt condition keeps the denominator positive. -/
theorem posteriorPopulationVariance_le_empiricalVariance_of_not_mem
    [Fintype Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ)
    (ell : ι → Z → ℝ)
    {eta delta : ℝ} (heta : 0 < eta)
    (heta_upper : eta * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell eta delta)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationVariance p ell) ≤
      (posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (klDiv rho prior + Real.log (1 / delta)) / (eta * (n : ℝ))) /
        (1 - eta * (n : ℝ) / (2 * ((n : ℝ) - 1))) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hpred : 0 < (n : ℝ) - 1 := by linarith
  have hdenom :
      0 < 1 - eta * (n : ℝ) / (2 * ((n : ℝ) - 1)) := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact heta_upper
  have hgap := finiteEmpiricalVariance_posteriorGap_le_of_not_mem
    n p prior ell eta delta S hS rho hrho
  have hproxy :
      posteriorMarginVarianceProxy rho
          (fun i => finitePopulationVariance p ell i / ((n : ℝ) - 1)) =
        posteriorAverage rho (finitePopulationVariance p ell) / ((n : ℝ) - 1) := by
    unfold posteriorMarginVarianceProxy posteriorAverage
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hgap' :
      posteriorAverage rho (finitePopulationVariance p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) ≤
        (klDiv rho prior + Real.log (1 / delta)) / (eta * (n : ℝ)) +
          eta * (n : ℝ) *
              posteriorAverage rho (finitePopulationVariance p ell) /
            (2 * ((n : ℝ) - 1)) := by
    rw [hproxy] at hgap
    unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hgap
    have hvarianceTerm :
        eta * (n : ℝ) *
              (posteriorAverage rho (finitePopulationVariance p ell) / ((n : ℝ) - 1)) / 2 =
          eta * (n : ℝ) * posteriorAverage rho (finitePopulationVariance p ell) /
            (2 * ((n : ℝ) - 1)) := by
      field_simp [ne_of_gt hpred]
    rw [hvarianceTerm] at hgap
    exact hgap
  rw [le_div_iff₀ hdenom]
  calc
    posteriorAverage rho (finitePopulationVariance p ell) *
          (1 - eta * (n : ℝ) / (2 * ((n : ℝ) - 1))) =
        posteriorAverage rho (finitePopulationVariance p ell) -
          eta * (n : ℝ) *
              posteriorAverage rho (finitePopulationVariance p ell) /
            (2 * ((n : ℝ) - 1)) := by ring
    _ ≤ posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (klDiv rho prior + Real.log (1 / delta)) / (eta * (n : ℝ)) := by
      linarith

end

end FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
