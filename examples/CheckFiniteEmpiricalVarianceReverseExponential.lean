import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseExponential
import Mathlib.Probability.Distributions.Uniform

/-!
# Checks for the reverse-Bessel exponential submartingale

This receipt instantiates the affine-score martingale and its nonnegative
exponential submartingale on four iid Bool observations.  On one explicit path,
the exponential changes from `exp (1 / 6)` to `exp (1 / 2)`, so the checked
process is not merely a constant-process instantiation.

The coefficient is fixed across reverse time.  This checker does not claim an
endpoint MGF bound, a maximal inequality, or a time-uniform PAC-Bayes theorem.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseExponential

open MeasureTheory
open FormalSLT.Statistics.ClassicalEstimation
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

noncomputable section

def boolLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance boolLaw_isProbabilityMeasure : IsProbabilityMeasure boolLaw := by
  unfold boolLaw
  infer_instance

def boolLoss : Bool → ℝ := fun b ↦ if b then 1 else 0

/-- A nonconstant explicit horizon-four path. -/
def twoFalseTwoTrue : Fin 4 → Bool := fun k ↦ decide (2 ≤ k.1)

theorem card_fin4_ge_two :
    (Finset.univ.filter (fun k : Fin 4 ↦ 2 ≤ k.1)).card = 2 := by
  decide

theorem reverseProcess_zero :
    reverseBesselProcess 4 (by norm_num) boolLoss 0 twoFalseTwoTrue =
      (1 : ℝ) / 3 := by
  change sampleVarianceBessel
    (fun k : Fin 4 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) =
      (1 : ℝ) / 3
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_four, card_fin4_ge_two]

theorem reverseProcess_two :
    reverseBesselProcess 4 (by norm_num) boolLoss 2 twoFalseTwoTrue = 0 := by
  change sampleVarianceBessel
    (fun k : Fin 2 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) = 0
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_two]

/-- The affine lower-tail score is a genuine martingale. -/
theorem boolIID_reverseBesselAffineScore_martingale :
    Martingale
      (reverseBesselAffineScore 4 (by norm_num) boolLoss ((1 : ℝ) / 2) 1 0)
      (reverseBesselFiltration (Z := Bool) 4)
      (Measure.pi (fun _ : Fin 4 ↦ boolLaw)) := by
  exact reverseBesselAffineScore_martingale boolLaw 4 (by norm_num) boolLoss
    ((1 : ℝ) / 2) 1 0

/-- Exponentiating the fixed affine score gives a nonnegative submartingale. -/
theorem boolIID_reverseBesselExponentialProcess_submartingale :
    Submartingale
      (reverseBesselExponentialProcess 4 (by norm_num) boolLoss
        ((1 : ℝ) / 2) 1 0)
      (reverseBesselFiltration (Z := Bool) 4)
      (Measure.pi (fun _ : Fin 4 ↦ boolLaw)) := by
  exact reverseBesselExponentialProcess_submartingale boolLaw 4 (by norm_num)
    boolLoss ((1 : ℝ) / 2) 1 0

theorem explicitPath_exponential_zero :
    reverseBesselExponentialProcess 4 (by norm_num) boolLoss
        ((1 : ℝ) / 2) 1 0 0 twoFalseTwoTrue = Real.exp ((1 : ℝ) / 6) := by
  rw [reverseBesselExponentialProcess, reverseBesselAffineScore,
    reverseProcess_zero]
  congr 1
  norm_num

theorem explicitPath_exponential_two :
    reverseBesselExponentialProcess 4 (by norm_num) boolLoss
        ((1 : ℝ) / 2) 1 0 2 twoFalseTwoTrue = Real.exp ((1 : ℝ) / 2) := by
  rw [reverseBesselExponentialProcess, reverseBesselAffineScore,
    reverseProcess_two]
  congr 1
  norm_num

theorem explicitPath_exponential_strictly_changes :
    reverseBesselExponentialProcess 4 (by norm_num) boolLoss
        ((1 : ℝ) / 2) 1 0 0 twoFalseTwoTrue <
      reverseBesselExponentialProcess 4 (by norm_num) boolLoss
        ((1 : ℝ) / 2) 1 0 2 twoFalseTwoTrue := by
  rw [explicitPath_exponential_zero, explicitPath_exponential_two]
  exact Real.exp_lt_exp.mpr (by norm_num)

#check reverseBesselAffineScore
#check reverseBesselAffineScore_martingale
#check reverseBesselExponentialProcess
#check reverseBesselExponentialProcess_submartingale
#check reverseBesselExponentialProcess_nonneg
#check boolIID_reverseBesselExponentialProcess_submartingale
#check explicitPath_exponential_strictly_changes

#print axioms reverseBesselAffineScore_martingale
#print axioms reverseBesselExponentialProcess_submartingale
#print axioms boolIID_reverseBesselExponentialProcess_submartingale
#print axioms explicitPath_exponential_strictly_changes

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseExponential
