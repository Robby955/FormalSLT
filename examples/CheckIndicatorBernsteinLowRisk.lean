import FormalSLT.PACBayes.IndicatorBernsteinLowRisk

/-!
# Concrete observable low-risk indicator certificate

The worked instance uses the two constant Boolean classifiers under the fair
Boolean law, the uniform prior/posterior, and a balanced sample of size `40`.
Every classifier has population and empirical error `1/2` on that sample, so
the sample is outside the fixed-tilt Bernstein exceptional set.  The observable
low-risk corollary then gives an evaluated upper certificate at most
`301/320 < 1` using only `log 2 <= 1`.
-/

namespace FormalSLT.Examples.CheckIndicatorBernsteinLowRisk

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.IndicatorBernsteinMoment
open FormalSLT.PACBayes.IndicatorBernsteinConfidence
open FormalSLT.PACBayes.IndicatorBernsteinLowRisk

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

def fairBool : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairBool_isPMF : IsPMF fairBool := by
  constructor <;> simp [fairBool]

def uniformBoolPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  constructor
  · constructor <;> simp [uniformBoolPrior]
  · intro i
    simp [uniformBoolPrior]

/-- The hypotheses are the constant-false and constant-true classifiers. -/
def disagreementBad : Bool → Bool → Bool := fun classifier label =>
  classifier != label

/-- Twenty false labels followed by twenty true labels. -/
def balanced40 : Fin 40 → Bool := fun j => decide (20 ≤ j.1)

theorem card_fin40_ge_twenty :
    (Finset.univ.filter (fun j : Fin 40 => 20 ≤ j.1)).card = 20 := by
  decide

theorem card_fin40_lt_twenty :
    (Finset.univ.filter (fun j : Fin 40 => j.1 < 20)).card = 20 := by
  decide

theorem classifier_populationRisk_eq_half (classifier : Bool) :
    indicatorPopulationRisk fairBool disagreementBad classifier = (1 : ℝ) / 2 := by
  cases classifier <;>
    norm_num [indicatorPopulationRisk, finitePopulationRisk, indicatorLoss,
      disagreementBad, fairBool]

theorem classifier_balanced40_empiricalRisk_eq_half (classifier : Bool) :
    finiteEmpiricalRisk (indicatorLoss disagreementBad) classifier balanced40 =
      (1 : ℝ) / 2 := by
  cases classifier <;>
    norm_num [finiteEmpiricalRisk, indicatorLoss, disagreementBad, balanced40]
  · rw [card_fin40_ge_twenty]
    norm_num
  · rw [card_fin40_lt_twenty]
    norm_num

theorem everyPosterior_balanced40_gap_eq_zero
    (ρ : Bool → ℝ) :
    posteriorGeneralizationGap ρ
        (indicatorPopulationRisk fairBool disagreementBad)
        (fun i => finiteEmpiricalRisk
          (indicatorLoss disagreementBad) i balanced40) = 0 := by
  rw [posteriorGeneralizationGap_eq_sum]
  simp [classifier_populationRisk_eq_half,
    classifier_balanced40_empiricalRisk_eq_half]

theorem everyPosterior_varianceProxy_eq_one_over_oneSixty
    (ρ : Bool → ℝ) (hρ : IsPMF ρ) :
    posteriorMarginVarianceProxy ρ
        (indicatorBernsteinVarianceProxy 40 fairBool disagreementBad) =
      (1 : ℝ) / 160 := by
  have hsum : ρ true + ρ false = 1 := by
    simpa using hρ.sum_one
  unfold posteriorMarginVarianceProxy indicatorBernsteinVarianceProxy
  simp_rw [classifier_populationRisk_eq_half]
  norm_num
  linarith

/-- The balanced sample is genuinely outside the parent fixed-tilt bad set. -/
theorem balanced40_not_mem_badSamples :
    balanced40 ∉ indicatorFinitePACBayesBernsteinBadSamples
      40 fairBool uniformBoolPrior disagreementBad
      (2 * (40 : ℝ) / 3) ((1 : ℝ) / 2) := by
  unfold indicatorFinitePACBayesBernsteinBadSamples
    finitePACBayesBernsteinFixedLambdaBadSamples
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
  intro ρ
  simp only [not_and]
  intro hρ
  rw [everyPosterior_balanced40_gap_eq_zero ρ,
    everyPosterior_varianceProxy_eq_one_over_oneSixty ρ hρ]
  have hkl : 0 ≤ klDiv ρ uniformBoolPrior :=
    klDiv_nonneg hρ uniformBoolPrior_isFullSupportPMF
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  norm_num [indicatorBernsteinScale]
  linarith

theorem uniformPosterior_populationRisk_eq_half :
    posteriorRisk uniformBoolPrior
        (indicatorPopulationRisk fairBool disagreementBad) = (1 : ℝ) / 2 := by
  unfold posteriorRisk posteriorAverage
  simp [uniformBoolPrior, classifier_populationRisk_eq_half]

theorem uniformPosterior_balanced40_empiricalRisk_eq_half :
    posteriorEmpiricalRisk uniformBoolPrior
        (fun i => finiteEmpiricalRisk
          (indicatorLoss disagreementBad) i balanced40) = (1 : ℝ) / 2 := by
  unfold posteriorEmpiricalRisk posteriorAverage
  simp [uniformBoolPrior, classifier_balanced40_empiricalRisk_eq_half]

theorem uniformPosterior_kl_self_eq_zero :
    klDiv uniformBoolPrior uniformBoolPrior = 0 := by
  simp [klDiv, uniformBoolPrior]

/-- The checked low-risk certificate is strictly below the trivial upper bound
one on a concrete good sample. -/
theorem uniformPosterior_balanced40_certificate_le_threeHundredOne_over_threeTwenty :
    posteriorRisk uniformBoolPrior
        (indicatorPopulationRisk fairBool disagreementBad) ≤
      (301 : ℝ) / 320 := by
  have hbound := indicator_posteriorRisk_le_twoThirds_of_not_mem
    (n := 40) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool uniformBoolPrior disagreementBad
    ((1 : ℝ) / 2) balanced40 balanced40_not_mem_badSamples
    uniformBoolPrior uniformBoolPrior_isFullSupportPMF.toIsPMF
  rw [uniformPosterior_balanced40_empiricalRisk_eq_half,
    uniformPosterior_kl_self_eq_zero] at hbound
  norm_num at hbound
  have hlog : Real.log 2 ≤ 1 := by
    have hraw := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hraw ⊢
    exact hraw
  have hrhs :
      (7 : ℝ) / 8 + 21 / 320 * Real.log 2 ≤ 301 / 320 := by
    linarith
  exact hbound.trans hrhs

theorem uniformPosterior_balanced40_certificate_lt_one :
    (301 : ℝ) / 320 < 1 := by norm_num

example :
    (∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        40 fairBool uniformBoolPrior disagreementBad
          (2 * (40 : ℝ) / 3) ((1 : ℝ) / 2),
        finiteProductSampleWeight fairBool S) ≤ (1 : ℝ) / 2 := by
  exact indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta
    (n := 40) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF
    uniformBoolPrior_isFullSupportPMF disagreementBad
    ((1 : ℝ) / 2) (by norm_num)

#check indicatorBernsteinVarianceProxy_le_risk_div
#check posteriorIndicatorBernsteinVarianceProxy_le_risk_div
#check posteriorIndicatorPopulationRisk_le_one
#check indicator_posteriorRisk_le_lowRisk_of_not_mem
#check indicator_posteriorRisk_le_twoThirds_of_not_mem
#check indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem
#check indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta
#check fairBool_isPMF
#check uniformBoolPrior_isFullSupportPMF
#check card_fin40_ge_twenty
#check card_fin40_lt_twenty
#check classifier_populationRisk_eq_half
#check classifier_balanced40_empiricalRisk_eq_half
#check everyPosterior_balanced40_gap_eq_zero
#check everyPosterior_varianceProxy_eq_one_over_oneSixty
#check balanced40_not_mem_badSamples
#check uniformPosterior_populationRisk_eq_half
#check uniformPosterior_balanced40_empiricalRisk_eq_half
#check uniformPosterior_kl_self_eq_zero
#check uniformPosterior_balanced40_certificate_le_threeHundredOne_over_threeTwenty
#check uniformPosterior_balanced40_certificate_lt_one
#print axioms indicatorBernsteinVarianceProxy_le_risk_div
#print axioms posteriorIndicatorBernsteinVarianceProxy_le_risk_div
#print axioms posteriorIndicatorPopulationRisk_le_one
#print axioms indicator_posteriorRisk_le_lowRisk_of_not_mem
#print axioms indicator_posteriorRisk_le_twoThirds_of_not_mem
#print axioms indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem
#print axioms indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta
#print axioms fairBool_isPMF
#print axioms uniformBoolPrior_isFullSupportPMF
#print axioms card_fin40_ge_twenty
#print axioms card_fin40_lt_twenty
#print axioms classifier_populationRisk_eq_half
#print axioms classifier_balanced40_empiricalRisk_eq_half
#print axioms everyPosterior_balanced40_gap_eq_zero
#print axioms everyPosterior_varianceProxy_eq_one_over_oneSixty
#print axioms balanced40_not_mem_badSamples
#print axioms uniformPosterior_populationRisk_eq_half
#print axioms uniformPosterior_balanced40_empiricalRisk_eq_half
#print axioms uniformPosterior_kl_self_eq_zero
#print axioms uniformPosterior_balanced40_certificate_le_threeHundredOne_over_threeTwenty
#print axioms uniformPosterior_balanced40_certificate_lt_one

end

end FormalSLT.Examples.CheckIndicatorBernsteinLowRisk
