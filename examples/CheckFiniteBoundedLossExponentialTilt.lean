import FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt

/-!
# Bounded-loss exponential-tilt audit

The concrete receipt starts from a fair Boolean law, uses the nonconstant loss
`0, 1`, and tilts by `t = log 2`.  The resulting law is `(2/3, 1/3)`:
the partition sum is strictly below one, both pointwise domination inequalities
are strict, and the exact variances certify the nontrivial comparison
`(1/4) * exp (-log 2) = 1/8 < 2/9`.
-/

namespace FormalSLT.Examples.CheckFiniteBoundedLossExponentialTilt

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteExponentialTilt
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt

noncomputable section

def fairBool (_z : Bool) : ℝ := 1 / 2

abbrev fairBoolPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def unitLoss (_i : Unit) (z : Bool) : ℝ := if z then 1 else 0

theorem unitLoss_mem_Icc (z : Bool) :
    unitLoss () z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z <;> simp [unitLoss]

theorem exp_neg_log_two : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem tiltNormalizer_eq_three_fourths :
    finiteBoundedLossTiltNormalizer fairBool unitLoss () (Real.log 2) =
      (3 : ℝ) / 4 := by
  norm_num [finiteBoundedLossTiltNormalizer, finiteExponentialTiltNormalizer,
    boundedLossTiltScore, fairBool, unitLoss, exp_neg_log_two]

theorem tilted_false_eq_two_thirds :
    finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2) false =
      (2 : ℝ) / 3 := by
  change
    fairBool false * Real.exp (boundedLossTiltScore unitLoss () (Real.log 2) false) /
        finiteBoundedLossTiltNormalizer fairBool unitLoss () (Real.log 2) =
      (2 : ℝ) / 3
  rw [tiltNormalizer_eq_three_fourths]
  norm_num [boundedLossTiltScore, fairBool, unitLoss]

theorem tilted_true_eq_one_third :
    finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2) true =
      (1 : ℝ) / 3 := by
  change
    fairBool true * Real.exp (boundedLossTiltScore unitLoss () (Real.log 2) true) /
        finiteBoundedLossTiltNormalizer fairBool unitLoss () (Real.log 2) =
      (1 : ℝ) / 3
  rw [tiltNormalizer_eq_three_fourths]
  norm_num [boundedLossTiltScore, fairBool, unitLoss, exp_neg_log_two]

theorem tiltNormalizer_strictly_below_one :
    finiteBoundedLossTiltNormalizer fairBool unitLoss () (Real.log 2) < 1 := by
  rw [tiltNormalizer_eq_three_fourths]
  norm_num

theorem pointwise_domination_strict_false :
    Real.exp (-Real.log 2) * fairBool false <
      finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2) false := by
  rw [exp_neg_log_two, tilted_false_eq_two_thirds]
  norm_num [fairBool]

theorem pointwise_domination_strict_true :
    Real.exp (-Real.log 2) * fairBool true <
      finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2) true := by
  rw [exp_neg_log_two, tilted_true_eq_one_third]
  norm_num [fairBool]

theorem fairBool_variance_eq_quarter :
    finitePopulationVariance fairBool unitLoss () = (1 : ℝ) / 4 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, fairBool, unitLoss]

theorem tilted_variance_eq_two_ninths :
    finitePopulationVariance
        (finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2))
        unitLoss () = (2 : ℝ) / 9 := by
  norm_num [finitePopulationVariance, finitePopulationRisk,
    tilted_false_eq_two_thirds, tilted_true_eq_one_third, unitLoss]

theorem variance_comparison_is_strict :
    finitePopulationVariance fairBool unitLoss () * Real.exp (-Real.log 2) <
      finitePopulationVariance
        (finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2))
        unitLoss () := by
  rw [fairBool_variance_eq_quarter, exp_neg_log_two,
    tilted_variance_eq_two_ninths]
  norm_num

example :
    finitePopulationVariance fairBool unitLoss () * Real.exp (-Real.log 2) ≤
      finitePopulationVariance
        (finiteBoundedLossTiltPMF fairBool unitLoss () (Real.log 2))
        unitLoss () := by
  exact finitePopulationVariance_mul_exp_neg_le_tilted
    fairBoolPMF unitLoss () (Real.log_nonneg (by norm_num)) unitLoss_mem_Icc

#check boundedLossTiltScore
#check finiteBoundedLossTiltNormalizer
#check finiteBoundedLossTiltPMF
#check finiteBoundedLossTiltPMF_isPMF
#check finiteBoundedLossTilt_changeOfMeasure
#check finiteBoundedLossTiltProduct_changeOfMeasure
#check finiteBoundedLossTiltNormalizer_le_one
#check finiteBoundedLossTilt_exp_neg_mul_le
#check finiteWeightedSquaredError_eq_populationVariance_add_sq
#check finitePopulationVariance_le_weightedSquaredError
#check finitePopulationVariance_mul_exp_neg_le_tilted
#check finiteBoundedLoss_centeredBennettNormalizer_le
#check tiltNormalizer_eq_three_fourths
#check tilted_false_eq_two_thirds
#check tilted_true_eq_one_third
#check tiltNormalizer_strictly_below_one
#check pointwise_domination_strict_false
#check pointwise_domination_strict_true
#check fairBool_variance_eq_quarter
#check tilted_variance_eq_two_ninths
#check variance_comparison_is_strict

#print axioms finiteBoundedLossTiltPMF_isPMF
#print axioms finiteBoundedLossTilt_changeOfMeasure
#print axioms finiteBoundedLossTiltProduct_changeOfMeasure
#print axioms finiteBoundedLossTiltNormalizer_le_one
#print axioms finiteBoundedLossTilt_exp_neg_mul_le
#print axioms finiteWeightedSquaredError_eq_populationVariance_add_sq
#print axioms finitePopulationVariance_le_weightedSquaredError
#print axioms finitePopulationVariance_mul_exp_neg_le_tilted
#print axioms finiteBoundedLoss_centeredBennettNormalizer_le
#print axioms tiltNormalizer_eq_three_fourths
#print axioms tilted_false_eq_two_thirds
#print axioms tilted_true_eq_one_third
#print axioms tiltNormalizer_strictly_below_one
#print axioms pointwise_domination_strict_false
#print axioms pointwise_domination_strict_true
#print axioms fairBool_variance_eq_quarter
#print axioms tilted_variance_eq_two_ninths
#print axioms variance_comparison_is_strict

end

end FormalSLT.Examples.CheckFiniteBoundedLossExponentialTilt
