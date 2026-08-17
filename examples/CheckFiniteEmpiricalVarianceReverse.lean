import FormalSLT
import Mathlib.Probability.Distributions.Uniform

/-!
# Checks for the reverse empirical-variance foundation

This receipt checks the nonconstant three-level leave-one-out identity, records
the exact `n = 1` failure excluded by the theorem, and instantiates the
load-bearing conditional-expectation step on a concrete iid Bool product law.

The checked surface is one reverse conditional-expectation step.  It is not an
all-times martingale, maximal inequality, exponential process, or PAC-Bayes
bound.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverse

open MeasureTheory
open FormalSLT.Statistics
open FormalSLT.Statistics.ClassicalEstimation
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

noncomputable section

/-- The genuinely nonconstant sample with values `0`, `1/2`, and `1`. -/
def triValues : Fin 3 → ℝ := fun k ↦ (k.1 : ℝ) / 2

theorem triValues_variance_eq_quarter :
    sampleVarianceBessel triValues = (1 : ℝ) / 4 := by
  norm_num [triValues, sampleVarianceBessel, sampleMean, Fin.sum_univ_succ]

theorem triValues_delete_zero_eq :
    eraseCoordinate (0 : Fin 3) triValues = ![(1 : ℝ) / 2, 1] := by
  funext k
  fin_cases k <;> norm_num [eraseCoordinate, triValues, Fin.succAbove]

theorem triValues_delete_one_eq :
    eraseCoordinate (1 : Fin 3) triValues = ![0, (1 : ℝ)] := by
  funext k
  fin_cases k <;> norm_num [eraseCoordinate, triValues, Fin.succAbove]

theorem triValues_delete_two_eq :
    eraseCoordinate (2 : Fin 3) triValues = ![0, (1 : ℝ) / 2] := by
  funext k
  fin_cases k <;> simp [eraseCoordinate, triValues, Fin.succAbove]

/-- The three leave-one-out variances are `1/8`, `1/2`, and `1/8`, whose
average is the original variance `1/4`. -/
theorem triValues_leaveOneOut_average_eq_quarter :
    (∑ r : Fin 3, sampleVarianceBessel (eraseCoordinate r triValues)) /
        (3 : ℝ) = (1 : ℝ) / 4 := by
  rw [Fin.sum_univ_three, triValues_delete_zero_eq, triValues_delete_one_eq,
    triValues_delete_two_eq]
  norm_num [sampleVarianceBessel, sampleMean, Fin.sum_univ_succ]

theorem triValues_leaveOneOut_identity :
    sampleVarianceBessel triValues =
      (∑ r : Fin 3, sampleVarianceBessel (eraseCoordinate r triValues)) /
        (3 : ℝ) := by
  rw [triValues_variance_eq_quarter, triValues_leaveOneOut_average_eq_quarter]

/-- With reduced size `n = 1`, all leave-one-out singleton variances are zero
under Lean's total division, while the original two-point Bessel variance is
`1/2`.  This witnesses why the theorem assumes `2 ≤ n`. -/
def twoValues : Fin 2 → ℝ := ![0, 1]

theorem leaveOneOut_identity_fails_at_n_one :
    sampleVarianceBessel twoValues ≠
      (∑ r : Fin 2, sampleVarianceBessel (eraseCoordinate r twoValues)) /
        (2 : ℝ) := by
  norm_num [twoValues, eraseCoordinate, sampleVarianceBessel, sampleMean,
    Fin.sum_univ_succ, Fin.succAbove]

/-- Uniform probability law on Bool for the concrete iid receipt. -/
def boolLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance boolLaw_isProbabilityMeasure : IsProbabilityMeasure boolLaw := by
  unfold boolLaw
  infer_instance

def boolLoss : Bool → ℝ := fun b ↦ if b then 1 else 0

/-- Concrete horizon-three iid instance of the load-bearing reverse
conditional-expectation step, from prefix size two to prefix size three. -/
theorem boolIID_prefixVariance_three_ae_eq_condExp_two :
    prefixBesselVariance (by norm_num : 3 ≤ 3) boolLoss =ᵐ[
        Measure.pi (fun _ : Fin 3 ↦ boolLaw)]
      condExp (prefixExchangeableSpace (Z := Bool) 3 3)
        (Measure.pi (fun _ : Fin 3 ↦ boolLaw))
        (prefixBesselVariance (by norm_num : 2 ≤ 3) boolLoss) := by
  exact prefixBesselVariance_ae_eq_condExp boolLaw
    (by norm_num : 2 ≤ 2) (by norm_num : 2 + 1 ≤ 3) boolLoss

#check eraseCoordinate
#check sampleVarianceBessel_eq_average_eraseCoordinate
#check exchangeableReverseFiltration
#check prefixBesselVariance_eq_average_horizonDeletion
#check prefixBesselVariance_ae_eq_condExp
#check triValues_leaveOneOut_identity
#check leaveOneOut_identity_fails_at_n_one
#check boolIID_prefixVariance_three_ae_eq_condExp_two

#print axioms sampleVarianceBessel_eq_average_eraseCoordinate
#print axioms exchangeableReverseFiltration
#print axioms prefixBesselVariance_eq_average_horizonDeletion
#print axioms prefixBesselVariance_ae_eq_condExp
#print axioms triValues_leaveOneOut_identity
#print axioms leaveOneOut_identity_fails_at_n_one
#print axioms boolIID_prefixVariance_three_ae_eq_condExp_two

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverse
