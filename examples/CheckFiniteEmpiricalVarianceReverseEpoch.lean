import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseEpoch

/-!
# Checks for the finite reverse-Bessel epoch bound

For fair Bool data, horizon `N = 4`, endpoint `m = 3`, `eta = 2/3`, and the
path `false,false,false,true`, the reverse exponential moves from
`exp (-1/4)` at horizon size four to `exp (1/4)` at prefix size three.  The
second value exceeds the `5/4` threshold for `delta = 4/5`, so the crossing
event is genuinely nonempty.  The checked theorem bounds its product-law mass
by `4/5`.

This is a transparent process receipt, not a small-delta numerical confidence
certificate and not yet a PAC-Bayes risk bound.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseEpoch

open Finset BigOperators MeasureTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteProductMeasureBridge

noncomputable section

def fairBool (_ : Bool) : ℝ := (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def indicatorLoss (_ : Unit) (z : Bool) : ℝ := if z then 1 else 0

theorem indicatorLoss_mem_Icc (z : Bool) :
    indicatorLoss () z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z <;> norm_num [indicatorLoss]

theorem fairBool_populationVariance_eq_quarter :
    finitePopulationVariance fairBool indicatorLoss () = (1 : ℝ) / 4 := by
  norm_num [finitePopulationVariance, finitePopulationRisk,
    fairBool, indicatorLoss]

/-- Three zero losses followed by one unit loss. -/
def threeFalseOneTrue : Fin 4 → Bool := fun k ↦ decide (3 ≤ k.1)

theorem card_fin4_ge_three :
    (Finset.univ.filter (fun k : Fin 4 ↦ 3 ≤ k.1)).card = 1 := by
  decide

theorem reverseProcess_zero_eq_quarter :
    reverseBesselProcess 4 (by norm_num) (indicatorLoss ()) 0
      threeFalseOneTrue = (1 : ℝ) / 4 := by
  change FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
    (fun k : Fin 4 ↦ indicatorLoss ()
      (threeFalseOneTrue (Fin.castLE (by norm_num) k))) = (1 : ℝ) / 4
  norm_num [indicatorLoss, threeFalseOneTrue,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_four, card_fin4_ge_three]

theorem reverseProcess_one_eq_zero :
    reverseBesselProcess 4 (by norm_num) (indicatorLoss ()) 1
      threeFalseOneTrue = 0 := by
  change FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
    (fun k : Fin 3 ↦ indicatorLoss ()
      (threeFalseOneTrue (Fin.castLE (by norm_num) k))) = 0
  norm_num [indicatorLoss, threeFalseOneTrue,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, Fin.sum_univ_three]

theorem epochPenalty_eq_quarter :
    reverseBesselEpochPenalty 3 ((2 : ℝ) / 3) ((1 : ℝ) / 4) =
      (1 : ℝ) / 4 := by
  norm_num [reverseBesselEpochPenalty]

theorem explicitPath_exponential_zero :
    reverseBesselExponentialProcess 4 (by norm_num) (indicatorLoss ())
        (finitePopulationVariance fairBool indicatorLoss ())
        (((2 : ℝ) / 3) * 3)
        (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
          (finitePopulationVariance fairBool indicatorLoss ()))
        0 threeFalseOneTrue = Real.exp (-(1 : ℝ) / 4) := by
  rw [reverseBesselExponentialProcess, reverseBesselAffineScore,
    fairBool_populationVariance_eq_quarter, reverseProcess_zero_eq_quarter,
    epochPenalty_eq_quarter]
  congr 1
  norm_num

theorem explicitPath_exponential_one :
    reverseBesselExponentialProcess 4 (by norm_num) (indicatorLoss ())
        (finitePopulationVariance fairBool indicatorLoss ())
        (((2 : ℝ) / 3) * 3)
        (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
          (finitePopulationVariance fairBool indicatorLoss ()))
        1 threeFalseOneTrue = Real.exp ((1 : ℝ) / 4) := by
  rw [reverseBesselExponentialProcess, reverseBesselAffineScore,
    fairBool_populationVariance_eq_quarter, reverseProcess_one_eq_zero,
    epochPenalty_eq_quarter]
  congr 1
  norm_num

theorem explicitPath_mem_crossing :
    threeFalseOneTrue ∈
      {x | ((4 : ℝ) / 5)⁻¹ ≤
        (Finset.range (4 - 3 + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ reverseBesselExponentialProcess 4 (by norm_num)
            (indicatorLoss ())
            (finitePopulationVariance fairBool indicatorLoss ())
            (((2 : ℝ) / 3) * 3)
            (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
              (finitePopulationVariance fairBool indicatorLoss ()))
            k x)} := by
  have hthreshold : ((4 : ℝ) / 5)⁻¹ < Real.exp ((1 : ℝ) / 4) := by
    convert Real.add_one_lt_exp (show (1 : ℝ) / 4 ≠ 0 by norm_num) using 1
    norm_num
  have htime : 1 ∈ Finset.range (4 - 3 + 1) := by norm_num
  have hle := Finset.le_sup'
    (fun k ↦ reverseBesselExponentialProcess 4 (by norm_num)
      (indicatorLoss ())
      (finitePopulationVariance fairBool indicatorLoss ())
      (((2 : ℝ) / 3) * 3)
      (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
        (finitePopulationVariance fairBool indicatorLoss ()))
      k threeFalseOneTrue) htime
  rw [explicitPath_exponential_one] at hle
  exact hthreshold.le.trans hle

theorem explicit_crossing_nonempty :
    Set.Nonempty
      {x | ((4 : ℝ) / 5)⁻¹ ≤
        (Finset.range (4 - 3 + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ reverseBesselExponentialProcess 4 (by norm_num)
            (indicatorLoss ())
            (finitePopulationVariance fairBool indicatorLoss ())
            (((2 : ℝ) / 3) * 3)
            (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
              (finitePopulationVariance fairBool indicatorLoss ()))
            k x)} :=
  ⟨threeFalseOneTrue, explicitPath_mem_crossing⟩

theorem fairBool_epoch_crossing_mass_le_four_fifths :
    Measure.pi (fun _ : Fin 4 ↦ fairBool_isPMF.toPMF.toMeasure)
        {x | ((4 : ℝ) / 5)⁻¹ ≤
          (Finset.range (4 - 3 + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess 4 (by norm_num)
              (indicatorLoss ())
              (finitePopulationVariance fairBool indicatorLoss ())
              (((2 : ℝ) / 3) * 3)
              (reverseBesselEpochPenalty 3 ((2 : ℝ) / 3)
                (finitePopulationVariance fairBool indicatorLoss ()))
              k x)} ≤ ENNReal.ofReal ((4 : ℝ) / 5) := by
  exact reverseBesselEpoch_crossing_mass_le_delta
    4 3 (by norm_num) (by norm_num) fairBool fairBool_isPMF
      indicatorLoss () indicatorLoss_mem_Icc (by norm_num) (by norm_num)

#check measurePreserving_samplePrefix
#check productMeasure_eq_finiteProductSampleWeight_toMeasure
#check reverseBesselExponentialProcess_epoch_maximal_ineq
#check reverseBesselEpoch_endpoint_integral_le_one
#check reverseBesselEpoch_crossing_mass_le_delta
#check fairBool_epoch_crossing_mass_le_four_fifths
#check explicit_crossing_nonempty

#print axioms measurePreserving_samplePrefix
#print axioms productMeasure_eq_finiteProductSampleWeight_toMeasure
#print axioms reverseBesselExponentialProcess_epoch_maximal_ineq
#print axioms reverseBesselEpoch_endpoint_integral_le_one
#print axioms reverseBesselEpoch_crossing_mass_le_delta
#print axioms fairBool_epoch_crossing_mass_le_four_fifths
#print axioms explicit_crossing_nonempty

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceReverseEpoch
