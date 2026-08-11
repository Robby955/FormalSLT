/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteBoundedLossBernstein
import FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes

/-!
# Finite PAC-Bayes empirical-Bernstein risk bound

This module combines two separately checked fixed-parameter events:

* the empirical-variance event bounds the posterior average of the population
  variances by the observable Bessel empirical variances; and
* the bounded-loss Bernstein event bounds the posterior population-risk gap
  using that posterior-averaged population variance.

The union event has finite-product mass at most `deltaVariance + deltaRisk`.
Outside it, every finite posterior satisfies the resulting observable risk
bound. No independence between the two events is assumed. The theorem is
finite, iid, fixed-sample, and fixed in both tilts; it does not authorize
post-sample optimization over a tilt grid or over all real tilts.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
open FormalSLT.PACBayes.FiniteBoundedLossBernstein

noncomputable section

variable {Z ι : Type*}

/-- Union of the empirical-variance and population-risk Bernstein bad sets. -/
def finiteEmpiricalBernsteinRiskBadSamples
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (eta lambda deltaVariance deltaRisk : ℝ) : Finset (Fin n → Z) :=
  finiteEmpiricalVariancePACBayesBadSamples
      n p prior ell eta deltaVariance ∪
    finiteBoundedLossBernsteinBadSamples
      n p prior ell lambda deltaRisk

/-- The combined fixed-parameter bad set has mass at most the sum of the two
declared failure budgets. No independence is used. -/
theorem finiteEmpiricalBernsteinRisk_badEventMass_le
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta lambda deltaVariance deltaRisk : ℝ}
    (heta : 0 < eta)
    (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ))
    (hdeltaVariance : 0 < deltaVariance)
    (hdeltaRisk : 0 < deltaRisk) :
    (∑ S ∈ finiteEmpiricalBernsteinRiskBadSamples
        n p prior ell eta lambda deltaVariance deltaRisk,
        finiteProductSampleWeight p S) ≤ deltaVariance + deltaRisk := by
  classical
  let varianceBad := finiteEmpiricalVariancePACBayesBadSamples
    n p prior ell eta deltaVariance
  let riskBad := finiteBoundedLossBernsteinBadSamples
    n p prior ell lambda deltaRisk
  have hvariance :
      (∑ S ∈ varianceBad, finiteProductSampleWeight p S) ≤ deltaVariance := by
    exact finiteEmpiricalVariancePACBayes_badEventMass_le_delta
      hn p hp hprior ell hell heta hdeltaVariance
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrisk :
      (∑ S ∈ riskBad, finiteProductSampleWeight p S) ≤ deltaRisk := by
    exact finiteBoundedLossBernstein_badEventMass_le_delta
      hnpos p hp hprior ell hell hlambda hlambda_lt hdeltaRisk
  have hnonneg (S : Fin n → Z) : 0 ≤ finiteProductSampleWeight p S :=
    (finiteProductSampleWeight_isPMF hp).nonneg S
  have hintersection :
      0 ≤ ∑ S ∈ varianceBad ∩ riskBad, finiteProductSampleWeight p S :=
    Finset.sum_nonneg (fun S _ => hnonneg S)
  have hunion :
      (∑ S ∈ varianceBad ∪ riskBad, finiteProductSampleWeight p S) +
          ∑ S ∈ varianceBad ∩ riskBad, finiteProductSampleWeight p S =
        (∑ S ∈ varianceBad, finiteProductSampleWeight p S) +
          ∑ S ∈ riskBad, finiteProductSampleWeight p S :=
    Finset.sum_union_inter
  have hunion_le :
      (∑ S ∈ varianceBad ∪ riskBad, finiteProductSampleWeight p S) ≤
        deltaVariance + deltaRisk := by
    linarith
  simpa [finiteEmpiricalBernsteinRiskBadSamples, varianceBad, riskBad] using hunion_le

/-- Fixed-parameter observable PAC-Bayes empirical-Bernstein risk bound.

The confidence costs retain separate variance and risk budgets. The same
sample-dependent posterior is valid in both inequalities because each good
event is already simultaneous over all finite posteriors. -/
theorem posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    {eta lambda deltaVariance deltaRisk : ℝ}
    (heta : 0 < eta)
    (heta_upper : eta * (n : ℝ) < 2 * ((n : ℝ) - 1))
    (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ))
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinRiskBadSamples
      n p prior ell eta lambda deltaVariance deltaRisk)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / deltaRisk)) / lambda +
        lambda *
            ((posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
                (klDiv rho prior + Real.log (1 / deltaVariance)) /
                  (eta * (n : ℝ))) /
              (1 - eta * (n : ℝ) / (2 * ((n : ℝ) - 1)))) /
          (2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ)))) := by
  classical
  have hnot :
      S ∉ finiteEmpiricalVariancePACBayesBadSamples
            n p prior ell eta deltaVariance ∪
          finiteBoundedLossBernsteinBadSamples
            n p prior ell lambda deltaRisk := by
    simpa [finiteEmpiricalBernsteinRiskBadSamples] using hS
  rw [Finset.mem_union, not_or] at hnot
  have hvariance :=
    posteriorPopulationVariance_le_empiricalVariance_of_not_mem
      hn p prior ell heta heta_upper S hnot.1 rho hrho
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrisk :=
    boundedLoss_posteriorRisk_le_populationVariance_of_not_mem
      hnpos p prior ell hlambda hlambda_lt S hnot.2 rho hrho
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hriskDen :
      0 < 2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ))) := by
    have hratio : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    positivity
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hvariance hlambda.le) hriskDen.le
  linarith

end

end FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk
