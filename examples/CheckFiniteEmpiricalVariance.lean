import FormalSLT.PACBayes.FiniteEmpiricalVariance

/-!
# Checks for finite empirical-variance foundations

The receipt uses three genuinely nonbinary loss levels, `0`, `1/2`, and `1`.
It checks the population variance, the Bessel empirical variance, and the
ordered-pair representation on the same `Fin 3` sample.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVariance

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance

noncomputable section

/-- Uniform law on a three-point data domain. -/
def triLaw : Fin 3 → ℝ := fun _ => (1 : ℝ) / 3

theorem triLaw_isPMF : IsPMF triLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    norm_num [triLaw]
  · simp [triLaw]

/-- Nonbinary bounded loss with levels `0`, `1/2`, and `1`. -/
def triLoss : Unit → Fin 3 → ℝ := fun _ z => (z.1 : ℝ) / 2

theorem triLoss_mem_Icc (z : Fin 3) : triLoss () z ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases z <;> norm_num [triLoss]

/-- The sample visits each of the three loss levels exactly once. -/
def triSample : Fin 3 → Fin 3 := fun k => k

theorem triPopulationRisk_eq_half :
    finitePopulationRisk triLaw triLoss () = (1 : ℝ) / 2 := by
  norm_num [finitePopulationRisk, triLaw, triLoss, Fin.sum_univ_succ]

theorem triPopulationVariance_eq_sixth :
    finitePopulationVariance triLaw triLoss () = (1 : ℝ) / 6 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, triLaw, triLoss,
    Fin.sum_univ_succ]

theorem triEmpiricalVariance_eq_quarter :
    finiteEmpiricalVariance triLoss () triSample = (1 : ℝ) / 4 := by
  norm_num [finiteEmpiricalVariance,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, triLoss, triSample, Fin.sum_univ_succ]

theorem triPairwiseEmpiricalVariance_eq_quarter :
    finitePairwiseEmpiricalVariance triLoss () triSample = (1 : ℝ) / 4 := by
  rw [← finiteEmpiricalVariance_eq_pairwise (by norm_num : 2 ≤ 3)]
  norm_num [finiteEmpiricalVariance,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, triLoss, triSample, Fin.sum_univ_succ]

theorem triEmpiricalVariance_le_half :
    finiteEmpiricalVariance triLoss () triSample ≤ (1 : ℝ) / 2 := by
  exact finiteEmpiricalVariance_le_half (by norm_num) triLoss () triSample triLoss_mem_Icc

theorem triEmpiricalVariance_le_riskFactor :
    finiteEmpiricalVariance triLoss () triSample ≤
      (3 : ℝ) / 2 * finiteEmpiricalRisk triLoss () triSample := by
  convert finiteEmpiricalVariance_le_card_div_pred_mul_empiricalRisk
    (by norm_num) triLoss () triSample triLoss_mem_Icc using 1
  all_goals norm_num

/-- The general finite-product theorem gives the correct expectation `1/6`
over all `3^3` samples, even though the displayed sample has variance `1/4`. -/
theorem triExpectedEmpiricalVariance_eq_sixth :
    (∑ S : Fin 3 → Fin 3,
        finiteProductSampleWeight triLaw S *
          finiteEmpiricalVariance triLoss () S) = (1 : ℝ) / 6 := by
  rw [finiteEmpiricalVariance_unbiased_finiteProduct
    (by norm_num : 2 ≤ 3) triLaw triLaw_isPMF triLoss ()]
  exact triPopulationVariance_eq_sixth

#check finitePopulationVariance
#check finiteEmpiricalVariance
#check orderedOffDiagonalSquaredDifference
#check finitePairwiseEmpiricalVariance
#check finitePopulationVariance_nonneg
#check finitePopulationVariance_eq_secondMoment_sub_riskSq
#check finitePopulationRisk_mem_Icc_of_bounded
#check finitePopulationVariance_le_quarter
#check finiteEmpiricalVariance_nonneg
#check orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum
#check finiteEmpiricalVariance_eq_pairwise
#check orderedOffDiagonalSquaredDifference_le
#check finiteEmpiricalVariance_le_card_div_pred_mul_empiricalRisk
#check finiteEmpiricalVariance_le_half
#check finiteProductSampleWeight_pairExpectation
#check finitePairVarianceKernelExpectation_eq_populationVariance
#check finiteProductSampleWeight_pairSquaredDifferenceExpectation_eq
#check finiteEmpiricalVariance_unbiased_finiteProduct
#check triLaw_isPMF
#check triLoss_mem_Icc
#check triPopulationRisk_eq_half
#check triPopulationVariance_eq_sixth
#check triEmpiricalVariance_eq_quarter
#check triPairwiseEmpiricalVariance_eq_quarter
#check triEmpiricalVariance_le_half
#check triEmpiricalVariance_le_riskFactor
#check triExpectedEmpiricalVariance_eq_sixth

#print axioms finitePopulationVariance_nonneg
#print axioms finitePopulationVariance_eq_secondMoment_sub_riskSq
#print axioms finitePopulationRisk_mem_Icc_of_bounded
#print axioms finitePopulationVariance_le_quarter
#print axioms finiteEmpiricalVariance_nonneg
#print axioms orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum
#print axioms finiteEmpiricalVariance_eq_pairwise
#print axioms orderedOffDiagonalSquaredDifference_le
#print axioms finiteEmpiricalVariance_le_card_div_pred_mul_empiricalRisk
#print axioms finiteEmpiricalVariance_le_half
#print axioms finiteProductSampleWeight_pairExpectation
#print axioms finitePairVarianceKernelExpectation_eq_populationVariance
#print axioms finiteProductSampleWeight_pairSquaredDifferenceExpectation_eq
#print axioms finiteEmpiricalVariance_unbiased_finiteProduct
#print axioms triLaw_isPMF
#print axioms triLoss_mem_Icc
#print axioms triPopulationRisk_eq_half
#print axioms triPopulationVariance_eq_sixth
#print axioms triEmpiricalVariance_eq_quarter
#print axioms triPairwiseEmpiricalVariance_eq_quarter
#print axioms triEmpiricalVariance_le_half
#print axioms triEmpiricalVariance_le_riskFactor
#print axioms triExpectedEmpiricalVariance_eq_sixth

end

end FormalSLT.Examples.CheckFiniteEmpiricalVariance
