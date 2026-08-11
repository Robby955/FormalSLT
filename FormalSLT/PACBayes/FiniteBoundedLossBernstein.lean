/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVariance
import FormalSLT.PACBayes.FiniteProductBernstein
import FormalSLT.PACBayesBernstein
import FormalSLT.Probability.BernsteinMGF

/-!
# Finite bounded-loss PAC-Bayes Bernstein confidence

This module proves the population-variance Bernstein moment and confidence
event for arbitrary finite `[0,1]` losses. It complements the empirical-
variance confidence event: this file controls the population-risk deviation
using the population variance, while
`FiniteEmpiricalVariancePACBayes` controls that population variance by the
observable Bessel empirical variance.

The result is finite, iid, fixed-sample, and fixed-tilt. It is simultaneous
over every finite posterior on one good event, but it does not optimize over a
tilt catalog and does not yet combine the two confidence events.
-/

namespace FormalSLT.PACBayes.FiniteBoundedLossBernstein

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.Probability.BernsteinMGF

noncomputable section

variable {Z ι : Type*}

/-- The exact population-variance Bernstein budget for a sample average. -/
def boundedLossBernsteinMGFBudget [Fintype Z]
    (n : ℕ) (p : Z → ℝ) (ell : ι → Z → ℝ) (i : ι) (lambda : ℝ) : ℝ :=
  lambda ^ (2 : Nat) * finitePopulationVariance p ell i /
    (2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ))))

/-- The one-coordinate population-minus-loss deviation is centered. -/
theorem boundedLossDeviation_centered [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι) :
    (∑ z : Z, p z * (finitePopulationRisk p ell i - ell i z)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
  simp [finitePopulationRisk]

/-- The centered second moment is exactly the population loss variance. -/
theorem boundedLossDeviation_secondMoment_eq [Fintype Z]
    (p : Z → ℝ) (ell : ι → Z → ℝ) (i : ι) :
    (∑ z : Z,
        p z * (finitePopulationRisk p ell i - ell i z) ^ (2 : Nat)) =
      finitePopulationVariance p ell i := by
  unfold finitePopulationVariance
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

/-- One-coordinate sub-Gamma MGF for an arbitrary finite `[0,1]` loss. -/
theorem boundedLoss_oneCoordinateDeviationMGF_le [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ)) :
    oneCoordinateDeviationMGF (n := n) p ell i lambda ≤
      Real.exp
        ((lambda * (n : ℝ)⁻¹) ^ (2 : Nat) *
            finitePopulationVariance p ell i /
          (2 * (1 - (lambda * (n : ℝ)⁻¹) / 3))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have ht_nonneg : 0 ≤ lambda * (n : ℝ)⁻¹ :=
    mul_nonneg hlambda (inv_nonneg.mpr hnR.le)
  have ht_lt : lambda * (n : ℝ)⁻¹ < 3 := by
    rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ hnR]
    exact hlambda_lt
  have hbound :
      ∀ z : Z, finitePopulationRisk p ell i - ell i z ≤ 1 := by
    intro z
    have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell i hell
    have hR_le : finitePopulationRisk p ell i ≤ 1 := hR.2
    have hell_nonneg : 0 ≤ ell i z := (hell z).1
    linarith
  have hmgf :=
    bennett_mgf_subgamma p
      (fun z : Z => finitePopulationRisk p ell i - ell i z)
      (b := 1) (v := finitePopulationVariance p ell i)
      (lam := lambda * (n : ℝ)⁻¹)
      (by norm_num) ht_nonneg (by simpa using ht_lt)
      hp.nonneg hp.sum_one
      (boundedLossDeviation_centered p hp ell i)
      hbound
      (boundedLossDeviation_secondMoment_eq p ell i).le
  simpa [oneCoordinateDeviationMGF] using hmgf

/-- Product-sample MGF bound with the exact per-hypothesis population variance. -/
theorem boundedLoss_product_mgf_le [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ)) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
              (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S))) ≤
      Real.exp (boundedLossBernsteinMGFBudget n p ell i lambda) := by
  have hfactor :=
    finiteProduct_mgf_empiricalRiskDeviation_eq_pow
      (ι := ι) (Z := Z) hn p ell i lambda
  rw [hfactor]
  have hbase :=
    boundedLoss_oneCoordinateDeviationMGF_le
      hn p hp ell i hell hlambda hlambda_lt
  have hbase_nonneg :
      0 ≤ oneCoordinateDeviationMGF (n := n) p ell i lambda := by
    unfold oneCoordinateDeviationMGF
    exact Finset.sum_nonneg
      (fun z _ => mul_nonneg (hp.nonneg z) (Real.exp_pos _).le)
  have hpow := pow_le_pow_left₀ hbase_nonneg hbase n
  refine hpow.trans_eq ?_
  rw [← Real.exp_nat_mul]
  congr 1
  unfold boundedLossBernsteinMGFBudget
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hden : 1 - lambda / (3 * (n : ℝ)) ≠ 0 := by
    have : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    linarith
  field_simp

/-- The product MGF normalized by its population-variance budget is at most one. -/
theorem boundedLoss_product_normalizedMGF_le_one [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ)) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              boundedLossBernsteinMGFBudget n p ell i lambda)) ≤ 1 := by
  let budget := boundedLossBernsteinMGFBudget n p ell i lambda
  have hmgf :=
    boundedLoss_product_mgf_le hn p hp ell i hell hlambda.le hlambda_lt
  change (∑ S : Fin n → Z,
      finiteProductSampleWeight p S *
        Real.exp
          (lambda *
              (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
            budget)) ≤ 1
  change (∑ S : Fin n → Z,
      finiteProductSampleWeight p S *
        Real.exp
          (lambda *
            (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S))) ≤
      Real.exp budget at hmgf
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
              budget)) =
      Real.exp (-budget) *
        ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (lambda *
                (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [sub_eq_add_neg, Real.exp_add]
        ring
    _ ≤ Real.exp (-budget) * Real.exp budget :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The explicit product budget is the generic PAC-Bayes Bernstein normalizer
with scale `1/(3n)` and variance proxy `V/n`. -/
theorem boundedLossBernsteinMGFBudget_eq_generic [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (i : ι)
    {lambda : ℝ} (hlambda_lt : lambda < 3 * (n : ℝ)) :
    boundedLossBernsteinMGFBudget n p ell i lambda =
      lambda ^ (2 : Nat) *
          (finitePopulationVariance p ell i / (n : ℝ)) /
        (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hden : 1 - lambda / (3 * (n : ℝ)) ≠ 0 := by
    have : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    linarith
  unfold boundedLossBernsteinMGFBudget
  field_simp [hn_ne, hden]

/-- Prior-average normalization of the bounded-loss population-variance MGF. -/
theorem boundedLoss_expectedPriorBernsteinExpMoment_le_one
    [Fintype Z] [Fintype ι]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ)) :
    expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight p) prior lambda
        (1 / (3 * (n : ℝ)))
        (finitePopulationRisk p ell)
        (fun (S : Fin n → Z) i => finiteEmpiricalRisk ell i S)
        (fun i => finitePopulationVariance p ell i / (n : ℝ)) ≤ 1 := by
  unfold expectedPriorBernsteinExpMoment priorBernsteinExpMoment
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (∑ i : ι, prior i *
            Real.exp
              (lambda *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                lambda ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / (n : ℝ)) /
                  (2 * (1 - (1 / (3 * (n : ℝ))) * lambda))))) =
      ∑ S : Fin n → Z, ∑ i : ι,
        finiteProductSampleWeight p S *
          (prior i *
            Real.exp
              (lambda *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                lambda ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / (n : ℝ)) /
                  (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)))) := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          (prior i *
            Real.exp
              (lambda *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                lambda ^ (2 : Nat) *
                    (finitePopulationVariance p ell i / (n : ℝ)) /
                  (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)))) := by
        rw [Finset.sum_comm]
    _ = ∑ i : ι, prior i *
        (∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (lambda *
                  (finitePopulationRisk p ell i - finiteEmpiricalRisk ell i S) -
                boundedLossBernsteinMGFBudget n p ell i lambda)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [boundedLossBernsteinMGFBudget_eq_generic hn p ell i hlambda_lt]
        ring
    _ ≤ ∑ i : ι, prior i * 1 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hprior.nonneg i)
      exact boundedLoss_product_normalizedMGF_le_one
        hn p hp ell i (hell i) hlambda hlambda_lt
    _ = 1 := by simp [hprior.sum_one]

/-- Samples where some posterior violates the fixed-tilt bounded-loss
population-variance Bernstein bound. -/
def finiteBoundedLossBernsteinBadSamples
    [Fintype Z] [Fintype ι]
    (n : ℕ) (p : Z → ℝ) (prior : ι → ℝ)
    (ell : ι → Z → ℝ) (lambda delta : ℝ) : Finset (Fin n → Z) :=
  finitePACBayesBernsteinFixedLambdaBadSamples
    prior lambda (1 / (3 * (n : ℝ))) delta
    (finitePopulationRisk p ell)
    (fun S i => finiteEmpiricalRisk ell i S)
    (fun i => finitePopulationVariance p ell i / (n : ℝ))

/-- Outside the bounded-loss Bernstein bad set, every posterior satisfies the
population-risk deviation bound with its posterior-averaged population
variance. -/
theorem boundedLoss_posteriorRisk_le_populationVariance_of_not_mem
    [Fintype Z] [Fintype ι]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    {lambda delta : ℝ} (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ))
    (S : Fin n → Z)
    (hS : S ∉ finiteBoundedLossBernsteinBadSamples
      n p prior ell lambda delta)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / delta)) / lambda +
        lambda * posteriorAverage rho (finitePopulationVariance p ell) /
          (2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ)))) := by
  classical
  have hgap :
      posteriorGeneralizationGap rho
          (finitePopulationRisk p ell)
          (fun i => finiteEmpiricalRisk ell i S) ≤
        (klDiv rho prior + Real.log (1 / delta)) / lambda +
          lambda * posteriorMarginVarianceProxy rho
              (fun i => finitePopulationVariance p ell i / (n : ℝ)) /
            (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)) := by
    by_contra hbound
    apply hS
    simp only [finiteBoundedLossBernsteinBadSamples,
      finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨rho, hrho, lt_of_not_ge hbound⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hden : 1 - lambda / (3 * (n : ℝ)) ≠ 0 := by
    have : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    linarith
  have hproxy :
      posteriorMarginVarianceProxy rho
          (fun i => finitePopulationVariance p ell i / (n : ℝ)) =
        posteriorAverage rho (finitePopulationVariance p ell) / (n : ℝ) := by
    unfold posteriorMarginVarianceProxy posteriorAverage
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hproxy] at hgap
  have hvarianceTerm :
      lambda *
            (posteriorAverage rho (finitePopulationVariance p ell) / (n : ℝ)) /
          (2 * (1 - (1 / (3 * (n : ℝ))) * lambda)) =
        lambda * posteriorAverage rho (finitePopulationVariance p ell) /
          (2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ)))) := by
    field_simp [hn_ne, hden]
  rw [hvarianceTerm] at hgap
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hgap
  linarith

/-- The fixed-tilt bounded-loss Bernstein bad set has product-law mass at most
`delta`. The event is simultaneous over every finite posterior. -/
theorem finiteBoundedLossBernstein_badEventMass_le_delta
    [Fintype Z] [DecidableEq Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {lambda delta : ℝ} (hlambda : 0 < lambda)
    (hlambda_lt : lambda < 3 * (n : ℝ))
    (hdelta : 0 < delta) :
    (∑ S ∈ finiteBoundedLossBernsteinBadSamples
        n p prior ell lambda delta,
        finiteProductSampleWeight p S) ≤ delta := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hscale : (1 / (3 * (n : ℝ))) * lambda < 1 := by
    rw [one_div, inv_mul_eq_div, div_lt_one (by positivity)]
    exact hlambda_lt
  exact finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    (finiteProductSampleWeight_isPMF hp) hprior
    lambda (1 / (3 * (n : ℝ))) delta hlambda hscale hdelta
    (finitePopulationRisk p ell)
    (fun (S : Fin n → Z) i => finiteEmpiricalRisk ell i S)
    (fun i => finitePopulationVariance p ell i / (n : ℝ))
    (boundedLoss_expectedPriorBernsteinExpMoment_le_one
      hn p hp hprior.toIsPMF ell hell hlambda hlambda_lt)

end

end FormalSLT.PACBayes.FiniteBoundedLossBernstein
