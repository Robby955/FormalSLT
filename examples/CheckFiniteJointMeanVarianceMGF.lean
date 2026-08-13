import FormalSLT.PACBayes.FiniteJointMeanVarianceMGF

/-!
# Fixed-n joint mean/empirical-variance MGF audit

The receipt uses a fair Boolean law, the nonconstant loss `0, 1`, sample size
two, and positive tilts `t = eta = 1/2`.  In this regime the joint variance
coefficient is exactly `1/2`, so the exponential-tilt variance correction is
genuinely active rather than a zero-tilt specialization.
-/

namespace FormalSLT.Examples.CheckFiniteJointMeanVarianceMGF

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF

noncomputable section

def fairBool (_z : Bool) : ℝ := 1 / 2

abbrev fairBoolPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def indicatorLoss (_i : Unit) (z : Bool) : ℝ := if z then 1 else 0

theorem indicatorLoss_mem_Icc (z : Bool) :
    indicatorLoss () z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z <;> simp [indicatorLoss]

theorem fairBool_populationVariance_eq_quarter :
    finitePopulationVariance fairBool indicatorLoss () = (1 : ℝ) / 4 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, fairBool, indicatorLoss]

theorem halfTilt_kappa_eq_half :
    finiteJointMeanVarianceKappa 2 ((1 : ℝ) / 2) = (1 : ℝ) / 2 := by
  norm_num [finiteJointMeanVarianceKappa]

theorem halfTilt_kappa_pos :
    0 < finiteJointMeanVarianceKappa 2 ((1 : ℝ) / 2) := by
  rw [halfTilt_kappa_eq_half]
  norm_num

example :
    (∑ S : Fin 2 → Bool,
        finiteProductSampleWeight fairBool S *
          Real.exp
            (((1 : ℝ) / 2) * 2 *
                (finitePopulationRisk fairBool indicatorLoss () -
                  finiteEmpiricalRisk indicatorLoss () S) -
              ((1 : ℝ) / 2) * 2 * finiteEmpiricalVariance indicatorLoss () S)) ≤
      (1 + (Real.exp ((1 : ℝ) / 2) - 1 - (1 : ℝ) / 2) *
          finitePopulationVariance fairBool indicatorLoss ()) ^ 2 *
        Real.exp
          (-Real.exp (-((1 : ℝ) / 2)) *
            finiteJointMeanVarianceKappa 2 ((1 : ℝ) / 2) *
              finitePopulationVariance fairBool indicatorLoss ()) := by
  exact finiteJointMeanVarianceMGF_le
    (n := 2) (t := (1 : ℝ) / 2) (eta := (1 : ℝ) / 2)
    (by norm_num) fairBool fairBoolPMF indicatorLoss () indicatorLoss_mem_Icc
    (by norm_num) (by norm_num)
    (finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le
      (n := 2) (eta := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num))

example :
    (∑ S : Fin 2 → Bool,
        finiteProductSampleWeight fairBool S *
          Real.exp
            (((1 : ℝ) / 2) * 2 *
                (finitePopulationRisk fairBool indicatorLoss () -
                  finiteEmpiricalRisk indicatorLoss () S) -
              ((1 : ℝ) / 2) * 2 * finiteEmpiricalVariance indicatorLoss () S -
              2 * Real.log
                (1 + (Real.exp ((1 : ℝ) / 2) - 1 - (1 : ℝ) / 2) *
                  finitePopulationVariance fairBool indicatorLoss ()) +
              Real.exp (-((1 : ℝ) / 2)) *
                finiteJointMeanVarianceKappa 2 ((1 : ℝ) / 2) *
                  finitePopulationVariance fairBool indicatorLoss ())) ≤ 1 := by
  exact finiteJointMeanVariance_normalizedMGF_le_one
    (n := 2) (t := (1 : ℝ) / 2) (eta := (1 : ℝ) / 2)
    (by norm_num) fairBool fairBoolPMF indicatorLoss () indicatorLoss_mem_Icc
    (by norm_num) (by norm_num)
    (finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le
      (n := 2) (eta := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num))

#check finiteJointMeanVarianceKappa
#check finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le
#check finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le
#check finiteJointMeanVarianceMGF_le
#check finiteJointMeanVariance_normalizedMGF_le_one
#check fairBool_populationVariance_eq_quarter
#check halfTilt_kappa_eq_half
#check halfTilt_kappa_pos

#print axioms finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le
#print axioms finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le
#print axioms finiteJointMeanVarianceMGF_le
#print axioms finiteJointMeanVariance_normalizedMGF_le_one
#print axioms fairBool_populationVariance_eq_quarter
#print axioms halfTilt_kappa_eq_half
#print axioms halfTilt_kappa_pos

end

end FormalSLT.Examples.CheckFiniteJointMeanVarianceMGF
