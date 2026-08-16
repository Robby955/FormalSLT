import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseMartingale
import Mathlib.Probability.Distributions.Uniform

/-!
# Checks for the finite-horizon reverse Bessel martingale

This receipt instantiates the full martingale on a horizon-four iid Bool
product law.  It also evaluates one nonconstant path, on which the reverse
sample-size process has values `1/3, 1/3, 0, 0, ...`.

The checked surface is the martingale itself.  It does not claim a reverse
maximal inequality, an exponential process, or a time-uniform PAC-Bayes bound.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseMartingale

open MeasureTheory
open FormalSLT.Statistics.ClassicalEstimation
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

noncomputable section

def boolLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance boolLaw_isProbabilityMeasure : IsProbabilityMeasure boolLaw := by
  unfold boolLaw
  infer_instance

def boolLoss : Bool → ℝ := fun b ↦ if b then 1 else 0

theorem reversePrefixSize_four_schedule :
    reverseBesselPrefixSize 4 0 = 4 ∧
      reverseBesselPrefixSize 4 1 = 3 ∧
      reverseBesselPrefixSize 4 2 = 2 ∧
      reverseBesselPrefixSize 4 3 = 2 := by
  norm_num [reverseBesselPrefixSize]

/-- The complete reverse Bessel process on four iid Bool observations is a
martingale, including every pair of reverse times in mathlib's definition. -/
theorem boolIID_reverseBesselProcess_martingale :
    Martingale (reverseBesselProcess 4 (by norm_num) boolLoss)
      (reverseBesselFiltration (Z := Bool) 4)
      (Measure.pi (fun _ : Fin 4 ↦ boolLaw)) := by
  exact reverseBesselProcess_martingale boolLaw 4 (by norm_num) boolLoss

def twoFalseTwoTrue : Fin 4 → Bool := fun k ↦ decide (2 ≤ k.1)

theorem card_fin4_ge_two :
    (Finset.univ.filter (fun k : Fin 4 ↦ 2 ≤ k.1)).card = 2 := by
  decide

theorem card_fin3_ge_two :
    (Finset.univ.filter (fun k : Fin 3 ↦ 2 ≤ k.1)).card = 1 := by
  decide

theorem twoFalseTwoTrue_reverseProcess_zero :
    reverseBesselProcess 4 (by norm_num) boolLoss 0 twoFalseTwoTrue =
      (1 : ℝ) / 3 := by
  change sampleVarianceBessel
    (fun k : Fin 4 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) =
      (1 : ℝ) / 3
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_four, card_fin4_ge_two]

theorem twoFalseTwoTrue_reverseProcess_one :
    reverseBesselProcess 4 (by norm_num) boolLoss 1 twoFalseTwoTrue =
      (1 : ℝ) / 3 := by
  change sampleVarianceBessel
    (fun k : Fin 3 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) =
      (1 : ℝ) / 3
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_three, card_fin3_ge_two]

theorem twoFalseTwoTrue_reverseProcess_two :
    reverseBesselProcess 4 (by norm_num) boolLoss 2 twoFalseTwoTrue = 0 := by
  change sampleVarianceBessel
    (fun k : Fin 2 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) = 0
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_two]

theorem twoFalseTwoTrue_reverseProcess_three :
    reverseBesselProcess 4 (by norm_num) boolLoss 3 twoFalseTwoTrue = 0 := by
  change sampleVarianceBessel
    (fun k : Fin 2 ↦ boolLoss (twoFalseTwoTrue (Fin.castLE (by norm_num) k))) = 0
  norm_num [boolLoss, twoFalseTwoTrue, sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_two]

#check reverseBesselPrefixSize
#check reverseBesselFiltration
#check reverseBesselProcess
#check reverseBesselProcess_ae_eq_condExp_succ
#check reverseBesselProcess_martingale
#check boolIID_reverseBesselProcess_martingale

#print axioms reverseBesselProcess_ae_eq_condExp_succ
#print axioms reverseBesselProcess_martingale
#print axioms boolIID_reverseBesselProcess_martingale

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseMartingale
