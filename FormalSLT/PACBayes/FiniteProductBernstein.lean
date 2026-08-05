/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.IndicatorVariance
import FormalSLT.Probability.BernsteinMGF

/-!
# Finite-product Bernstein moments for indicator losses

This module tensorizes the exact indicator variance identity across a finite
i.i.d. product sample. For each fixed hypothesis, it proves a normalized MGF
bound with the hypothesis-specific variance `R * (1 - R)`.

The public parameter range is explicit: the sample size is positive and the
fixed tilt satisfies `0 ≤ lambda < 3n`. The result is finite, fixed-sample, and
fixed-tilt; it does not claim empirical-variance adaptation or optimization
over all real tilts.

Mathematical sources: Boucheron, Lugosi, and Massart (2013), *Concentration
Inequalities*, for the Bennett-to-Bernstein MGF route; Tolstikhin and Seldin
(2013), "PAC-Bayes-Empirical-Bernstein Inequality," for the variance-sensitive
PAC-Bayes context. This module proves the fixed-hypothesis finite-product MGF
brick, not the posterior change-of-measure conclusion.
-/

namespace FormalSLT.PACBayes.FiniteProductBernstein

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.Probability.BernsteinMGF

noncomputable section

variable {ι Z : Type*}

/-! ### Finite product probability mass -/

private theorem finiteProductSampleWeight_nonneg {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) (S : Fin n → Z) :
    0 ≤ finiteProductSampleWeight p S := by
  unfold finiteProductSampleWeight
  exact Finset.prod_nonneg (fun k _ => hp.nonneg (S k))

private theorem finiteProductSampleWeight_sum_eq_one {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    (∑ S : Fin n → Z, finiteProductSampleWeight p S) = 1 := by
  unfold finiteProductSampleWeight
  calc
    (∑ S : Fin n → Z, ∏ k : Fin n, p (S k)) =
        ∏ _k : Fin n, ∑ z : Z, p z :=
      (Fintype.prod_sum (f := fun _k : Fin n => p)).symm
    _ = 1 := by simp [hp.sum_one]

/-- Finite i.i.d. product weights form a PMF on finite samples. -/
theorem finiteProductSampleWeight_isPMF {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    IsPMF (finiteProductSampleWeight (n := n) p) :=
  ⟨finiteProductSampleWeight_nonneg hp,
    finiteProductSampleWeight_sum_eq_one hp⟩

/-! ### Hypothesis-specific Bernstein MGF -/

/-- The exact indicator Bernstein exponent for a product sample. -/
def indicatorBernsteinMGFBudget
    (n : ℕ) (lambda risk : ℝ) : ℝ :=
  lambda ^ (2 : Nat) * (risk * (1 - risk)) /
    (2 * (n : ℝ) * (1 - lambda / (3 * (n : ℝ))))

/-- One-coordinate sub-Gamma MGF for an arbitrary finite indicator loss. -/
theorem indicator_oneCoordinateDeviationMGF_le [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (hlambda_lt : lambda < 3 * (n : ℝ)) :
    oneCoordinateDeviationMGF (n := n) p (indicatorLoss bad) i lambda ≤
      Real.exp
        ((lambda * (n : ℝ)⁻¹) ^ (2 : Nat) *
            (indicatorPopulationRisk p bad i * (1 - indicatorPopulationRisk p bad i)) /
          (2 * (1 - (lambda * (n : ℝ)⁻¹) / 3))) := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have ht_nonneg : 0 ≤ lambda * (n : ℝ)⁻¹ :=
    mul_nonneg hlambda (inv_nonneg.mpr hn_real.le)
  have ht_lt : lambda * (n : ℝ)⁻¹ < 3 := by
    rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ hn_real]
    exact hlambda_lt
  have hbound :
      ∀ z : Z, indicatorPopulationRisk p bad i - indicatorLoss bad i z ≤ 1 := by
    intro z
    have hR := indicatorPopulationRisk_le_one p hp bad i
    have hL := indicatorLoss_nonneg bad i z
    linarith
  have hmgf :=
    bennett_mgf_subgamma p
      (fun z : Z => indicatorPopulationRisk p bad i - indicatorLoss bad i z)
      (b := 1)
      (v := indicatorPopulationRisk p bad i * (1 - indicatorPopulationRisk p bad i))
      (lam := lambda * (n : ℝ)⁻¹)
      (by norm_num) ht_nonneg (by simpa using ht_lt)
      hp.nonneg hp.sum_one
      (indicatorDeviation_centered p hp bad i)
      hbound
      (indicatorDeviation_secondMoment_eq p hp bad i).le
  simpa [oneCoordinateDeviationMGF, indicatorPopulationRisk] using hmgf

/-- Product-sample MGF bound with the exact hypothesis-specific indicator variance. -/
theorem indicator_product_mgf_le [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (hlambda_lt : lambda < 3 * (n : ℝ)) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
              (indicatorPopulationRisk p bad i -
                finiteEmpiricalRisk (indicatorLoss bad) i S))) ≤
      Real.exp
        (indicatorBernsteinMGFBudget n lambda (indicatorPopulationRisk p bad i)) := by
  have hfactor :=
    finiteProduct_mgf_empiricalRiskDeviation_eq_pow
      (ι := ι) (Z := Z) hn p (indicatorLoss bad) i lambda
  rw [show finitePopulationRisk p (indicatorLoss bad) i =
      indicatorPopulationRisk p bad i by rfl] at hfactor
  rw [hfactor]
  have hbase := indicator_oneCoordinateDeviationMGF_le hn p hp bad i hlambda hlambda_lt
  have hbase_nonneg :
      0 ≤ oneCoordinateDeviationMGF (n := n) p (indicatorLoss bad) i lambda := by
    unfold oneCoordinateDeviationMGF
    exact Finset.sum_nonneg
      (fun z _ => mul_nonneg (hp.nonneg z) (Real.exp_pos _).le)
  have hpow := pow_le_pow_left₀ hbase_nonneg hbase n
  refine hpow.trans_eq ?_
  rw [← Real.exp_nat_mul]
  congr 1
  unfold indicatorBernsteinMGFBudget
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  have hden : 1 - lambda / (3 * (n : ℝ)) ≠ 0 := by
    have : lambda / (3 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hlambda_lt
    linarith
  field_simp

/-- The hypothesis-specific product MGF normalized by its exact Bernstein budget is at most one. -/
theorem indicator_product_normalizedMGF_le_one [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι)
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambda_lt : lambda < 3 * (n : ℝ)) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
                (indicatorPopulationRisk p bad i -
                  finiteEmpiricalRisk (indicatorLoss bad) i S) -
              indicatorBernsteinMGFBudget n lambda (indicatorPopulationRisk p bad i))) ≤
      1 := by
  let budget := indicatorBernsteinMGFBudget n lambda (indicatorPopulationRisk p bad i)
  have hmgf := indicator_product_mgf_le hn p hp bad i hlambda.le hlambda_lt
  change (∑ S : Fin n → Z,
      finiteProductSampleWeight p S *
        Real.exp
          (lambda *
              (indicatorPopulationRisk p bad i -
                finiteEmpiricalRisk (indicatorLoss bad) i S) - budget)) ≤ 1
  change (∑ S : Fin n → Z,
      finiteProductSampleWeight p S *
        Real.exp
          (lambda *
            (indicatorPopulationRisk p bad i -
              finiteEmpiricalRisk (indicatorLoss bad) i S))) ≤ Real.exp budget at hmgf
  calc
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
                (indicatorPopulationRisk p bad i -
                  finiteEmpiricalRisk (indicatorLoss bad) i S) - budget)) =
      Real.exp (-budget) *
        ∑ S : Fin n → Z,
          finiteProductSampleWeight p S *
            Real.exp
              (lambda *
                (indicatorPopulationRisk p bad i -
                  finiteEmpiricalRisk (indicatorLoss bad) i S)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [sub_eq_add_neg, Real.exp_add]
        ring
    _ ≤ Real.exp (-budget) * Real.exp budget :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end

end FormalSLT.PACBayes.FiniteProductBernstein
