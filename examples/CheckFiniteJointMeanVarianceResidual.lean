import FormalSLT.PACBayes.FiniteJointMeanVarianceResidual
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Receipt for the exact joint mean/variance residual envelope

This checker activates the nonzero endpoint branch with the concrete
predeclared parameters `n = 6`, `t = 1`, and `eta = 1 / 2`.  It proves that
the residual coefficient lies strictly below the endpoint threshold, evaluates
the corresponding `xi` formula, proves that this residual is positive, and
instantiates the exact-maximum theorem.
-/

namespace FormalSLT.Examples.CheckFiniteJointMeanVarianceResidual

open Real
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVarianceResidual

noncomputable section

/-- The concrete variance MGF coefficient is positive. -/
theorem receiptKappa_eq :
    finiteJointMeanVarianceKappa 6 ((1 : ℝ) / 2) = 21 / 10 := by
  norm_num [finiteJointMeanVarianceKappa]

/-- Closed form of the transported variance rate for the receipt. -/
theorem receiptRate_eq :
    finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2) =
      (7 / 20 : ℝ) * Real.exp (-1) := by
  unfold finiteJointMeanVarianceResidualRate
  rw [receiptKappa_eq]
  ring

/-- The concrete rate lies strictly below the endpoint threshold, so the
maximum is attained at population variance `1 / 4` and the residual is
genuinely nonzero. -/
theorem receiptRate_lt_quarterThreshold :
    finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2) <
      finiteJointMeanVariancePsi 1 /
        (1 + finiteJointMeanVariancePsi 1 / 4) := by
  have heLower : (5 : ℝ) / 2 < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have heUpper : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hnegMul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hnegUpper : Real.exp (-1) < (1 : ℝ) / 2 := by
    nlinarith [Real.exp_pos (-1)]
  let b := finiteJointMeanVariancePsi 1
  let r := finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2)
  have hbLower : (1 : ℝ) / 2 < b := by
    dsimp [b, finiteJointMeanVariancePsi]
    linarith
  have hbUpper : b < 1 := by
    dsimp [b, finiteJointMeanVariancePsi]
    linarith
  have hrNonneg : 0 ≤ r := by
    dsimp [r]
    apply finiteJointMeanVarianceResidualRate_nonneg
    rw [receiptKappa_eq]
    norm_num
  have hrUpper : r < (7 : ℝ) / 40 := by
    rw [show r = (7 / 20 : ℝ) * Real.exp (-1) by
      simpa [r] using receiptRate_eq]
    nlinarith
  have hyPos : 0 < 1 + b / 4 := by nlinarith
  have hyUpper : 1 + b / 4 < (5 : ℝ) / 4 := by nlinarith
  have hproduct : r * (1 + b / 4) < b := by
    have hrough : r * (1 + b / 4) < (7 : ℝ) / 32 := by
      nlinarith [mul_nonneg hrNonneg (le_of_lt hyPos)]
    nlinarith
  exact (lt_div_iff₀ hyPos).2 hproduct

/-- The rate is also strictly below the Bennett coefficient itself. -/
theorem receiptRate_lt_psi :
    finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2) <
      finiteJointMeanVariancePsi 1 := by
  have hthreshold := receiptRate_lt_quarterThreshold
  have hb := finiteJointMeanVariancePsi_nonneg 1
  have hy : 1 ≤ 1 + finiteJointMeanVariancePsi 1 / 4 := by nlinarith
  have hratioLe :
      finiteJointMeanVariancePsi 1 /
          (1 + finiteJointMeanVariancePsi 1 / 4) ≤
        finiteJointMeanVariancePsi 1 := by
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  exact lt_of_lt_of_le hthreshold hratioLe

/-- The checker reaches the nonzero endpoint branch of the exact formula. -/
theorem receiptXi_eq :
    finiteJointMeanVarianceXi 6 1 ((1 : ℝ) / 2) =
      Real.log (1 + finiteJointMeanVariancePsi 1 / 4) -
        finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2) / 4 :=
  finiteJointMeanVarianceXi_eq_quarter_of_lt_of_le
    receiptRate_lt_psi (le_of_lt receiptRate_lt_quarterThreshold)

/-- The selected nonzero residual branch is genuinely positive. -/
theorem receiptXi_pos :
    0 < finiteJointMeanVarianceXi 6 1 ((1 : ℝ) / 2) := by
  let b := finiteJointMeanVariancePsi 1
  let r := finiteJointMeanVarianceResidualRate 6 1 ((1 : ℝ) / 2)
  have hb : 0 ≤ b := by
    simpa [b] using finiteJointMeanVariancePsi_nonneg 1
  have hy : 0 < 1 + b / 4 := by nlinarith
  have hthreshold : r * (1 + b / 4) < b :=
    (lt_div_iff₀ hy).mp (by
      simpa [b, r] using receiptRate_lt_quarterThreshold)
  have hlogLower := Real.self_sub_one_le_mul_log (le_of_lt hy)
  have hpositive : r / 4 < Real.log (1 + b / 4) := by
    nlinarith
  rw [receiptXi_eq]
  simpa [b, r] using sub_pos.mpr hpositive

/-- The concrete `xi` is the exact maximum, not just an upper bound. -/
theorem receiptXi_isGreatest :
    IsGreatest
      (finiteJointMeanVarianceResidual 6 1 ((1 : ℝ) / 2) ''
        Set.Icc (0 : ℝ) (1 / 4 : ℝ))
      (finiteJointMeanVarianceXi 6 1 ((1 : ℝ) / 2)) := by
  apply finiteJointMeanVarianceXi_isGreatest
  rw [receiptKappa_eq]
  norm_num

#check finiteJointMeanVariancePsi
#check finiteJointMeanVarianceResidualRate
#check finiteJointMeanVarianceResidual
#check finiteJointMeanVarianceXi
#check finiteJointMeanVarianceResidual_le_xi
#check finiteJointMeanVarianceXi_attained
#check finiteJointMeanVarianceXi_isGreatest
#check finiteJointMeanVarianceXi_nonneg
#check posteriorAverage_finitePopulationVariance_mem_Icc
#check finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
#check finiteJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem
#check receiptXi_eq
#check receiptXi_pos
#check receiptXi_isGreatest

#print axioms finiteJointMeanVarianceResidual_le_xi
#print axioms finiteJointMeanVarianceXi_attained
#print axioms finiteJointMeanVarianceXi_isGreatest
#print axioms finiteJointMeanVarianceXi_nonneg
#print axioms posteriorAverage_finitePopulationVariance_mem_Icc
#print axioms finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
#print axioms finiteJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem
#print axioms receiptXi_pos
#print axioms receiptXi_isGreatest

end

end FormalSLT.Examples.CheckFiniteJointMeanVarianceResidual
