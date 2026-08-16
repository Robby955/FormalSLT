import FormalSLT.PACBayes.FinitePMFBridge
import Mathlib.Tactic

/-!
# Finite PMF and KL interoperability audit

Checks the public conversion from FormalSLT finite PMFs to mathlib `PMF`s,
the finite-sum/integral identity, and the exact KL identity under posterior
support inclusion in the prior. A disjoint-support example records why that
support condition cannot be dropped.
-/

namespace FormalSLT.Examples.CheckFinitePMFBridge

open Finset BigOperators MeasureTheory
open FormalSLT.PACBayesKL

noncomputable section

def posterior : Bool → ℝ
  | false => 3 / 4
  | true => 1 / 4

def prior : Bool → ℝ := fun _ => 1 / 2

theorem posterior_isPMF : IsPMF posterior := by
  constructor
  · intro i
    cases i <;> norm_num [posterior]
  · rw [Fintype.sum_bool]
    norm_num [posterior]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine { nonneg := ?_, sum_one := ?_, pos := ?_ }
  · intro i
    norm_num [prior]
  · rw [Fintype.sum_bool]
    norm_num [prior]
  · intro i
    norm_num [prior]

example : (posterior_isPMF.toPMF false).toReal = 3 / 4 := by
  norm_num [posterior]

example (g : Bool → ℝ) :
    (∫ i, g i ∂posterior_isPMF.toPMF.toMeasure) =
      ∑ i, posterior i * g i :=
  posterior_isPMF.integral_toPMF_eq_sum g

example :
    InformationTheory.klDiv posterior_isPMF.toPMF.toMeasure
        prior_isFullSupportPMF.toIsPMF.toPMF.toMeasure =
      ENNReal.ofReal (klDiv posterior prior) :=
  informationTheory_klDiv_toPMF_eq_of_fullSupport
    posterior_isPMF prior_isFullSupportPMF

/-! The totalized finite real sum is intentionally not identified with
mathlib KL when posterior support is not contained in prior support. -/

def leftPoint : Bool → ℝ
  | false => 1
  | true => 0

def rightPoint : Bool → ℝ
  | false => 0
  | true => 1

theorem leftPoint_isPMF : IsPMF leftPoint := by
  constructor
  · intro i
    cases i <;> norm_num [leftPoint]
  · rw [Fintype.sum_bool]
    norm_num [leftPoint]

theorem rightPoint_isPMF : IsPMF rightPoint := by
  constructor
  · intro i
    cases i <;> norm_num [rightPoint]
  · rw [Fintype.sum_bool]
    norm_num [rightPoint]

theorem leftPoint_not_absolutelyContinuous_rightPoint :
    ¬ leftPoint_isPMF.toPMF.toMeasure ≪ rightPoint_isPMF.toPMF.toMeasure := by
  intro hac
  have hzero := hac (s := ({false} : Set Bool)) (by
    rw [PMF.toMeasure_apply_singleton rightPoint_isPMF.toPMF false
      (MeasurableSet.singleton false)]
    simp [rightPoint])
  rw [PMF.toMeasure_apply_singleton leftPoint_isPMF.toPMF false
    (MeasurableSet.singleton false)] at hzero
  norm_num [leftPoint] at hzero

example : klDiv leftPoint rightPoint = 0 := by
  simp [klDiv, leftPoint, rightPoint]

example :
    InformationTheory.klDiv leftPoint_isPMF.toPMF.toMeasure
        rightPoint_isPMF.toPMF.toMeasure = ⊤ :=
  InformationTheory.klDiv_of_not_ac leftPoint_not_absolutelyContinuous_rightPoint

#check IsPMF.toPMF
#check IsPMF.toPMF_apply
#check IsPMF.toPMF_apply_toReal
#check IsPMF.integral_toPMF_eq_sum
#check integral_toPMF_eq_posteriorAverage
#check toPMF_toMeasure_absolutelyContinuous_of_support
#check toPMF_toMeasure_absolutelyContinuous_of_fullSupport
#check klDiv_nonneg_of_support
#check informationTheory_klDiv_toPMF_eq_of_support
#check toReal_informationTheory_klDiv_toPMF_eq_of_support
#check informationTheory_klDiv_toPMF_eq_of_fullSupport
#check toReal_informationTheory_klDiv_toPMF_eq_of_fullSupport

#print axioms IsPMF.integral_toPMF_eq_sum
#print axioms informationTheory_klDiv_toPMF_eq_of_support
#print axioms toReal_informationTheory_klDiv_toPMF_eq_of_support

end

end FormalSLT.Examples.CheckFinitePMFBridge
