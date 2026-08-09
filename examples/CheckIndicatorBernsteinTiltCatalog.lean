import FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog

/-!
# Finite weighted indicator-Bernstein tilt-catalog receipt

This checker instantiates four fixed tilts with unequal positive confidence
weights.  Under the fair Boolean law, a balanced sample of size `40`, and the
uniform prior/posterior, it verifies:

* the simultaneous catalog event has product-law mass at most `1/2`;
* the balanced sample lies outside every catalog entry;
* an empirical-risk selector chooses the second entry after seeing the sample;
* the selected observable risk certificate is at most `13/14 < 1`.

The selector is valid because the catalog event is simultaneous in both the
finite tilt index and posterior.
-/

namespace FormalSLT.Examples.CheckIndicatorBernsteinTiltCatalog

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.IndicatorBernsteinMoment
open FormalSLT.PACBayes.IndicatorBernsteinConfidence
open FormalSLT.PACBayes.IndicatorBernsteinLowRisk
open FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

abbrev TiltIndex := Fin 4

/-- Unequal catalog weights with total mass one. -/
def catalogWeight : TiltIndex → ℝ :=
  ![(1 : ℝ) / 2, 1 / 4, 1 / 8, 1 / 8]

/-- Four predetermined tilts, from most to least aggressive. -/
def catalogTilt (n : ℕ) : TiltIndex → ℝ :=
  ![2 * (n : ℝ) / 3, (n : ℝ) / 2, (n : ℝ) / 3, (n : ℝ) / 6]

theorem catalogWeight_pos (j : TiltIndex) : 0 < catalogWeight j := by
  fin_cases j <;> norm_num [catalogWeight]

theorem catalogWeight_sum_eq_one : ∑ j, catalogWeight j = 1 := by
  norm_num [catalogWeight, Fin.sum_univ_succ]

theorem half_mul_catalogWeight_lt_one (j : TiltIndex) :
    ((1 : ℝ) / 2) * catalogWeight j < 1 := by
  fin_cases j <;> norm_num [catalogWeight]

theorem catalogTilt_pos {n : ℕ} (hn : 0 < n) (j : TiltIndex) :
    0 < catalogTilt n j := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  fin_cases j <;> norm_num [catalogTilt] <;> positivity

theorem catalogTilt_lt_lowRisk {n : ℕ} (hn : 0 < n) (j : TiltIndex) :
    catalogTilt n j < 6 * (n : ℝ) / 5 := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  fin_cases j <;> norm_num [catalogTilt] <;> nlinarith

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

theorem everyPosterior_balanced40_gap_eq_zero (ρ : Bool → ℝ) :
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

/-- The balanced sample lies outside a fixed entry whenever its tilt and
confidence budget are in the admissible ranges used by this checker. -/
theorem balanced40_not_mem_badSamples_entry
    (lambda confidence : ℝ)
    (hlambda : 0 < lambda) (hlambda_lt : lambda < 3 * (40 : ℝ))
    (hconfidence : 0 < confidence) (hconfidence_lt : confidence < 1) :
    balanced40 ∉ indicatorFinitePACBayesBernsteinBadSamples
      40 fairBool uniformBoolPrior disagreementBad lambda confidence := by
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
  have hlog : 0 < Real.log (1 / confidence) :=
    Real.log_pos (one_lt_one_div hconfidence hconfidence_lt)
  have hden :
      0 < 2 * (1 - indicatorBernsteinScale 40 * lambda) := by
    norm_num [indicatorBernsteinScale]
    nlinarith
  have hcomplexity :
      0 < (klDiv ρ uniformBoolPrior + Real.log (1 / confidence)) / lambda :=
    div_pos (add_pos_of_nonneg_of_pos hkl hlog) hlambda
  have hvariance :
      0 < lambda * ((1 : ℝ) / 160) /
          (2 * (1 - indicatorBernsteinScale 40 * lambda)) := by
    exact div_pos (mul_pos hlambda (by norm_num)) hden
  linarith

/-- The balanced sample lies outside the single simultaneous catalog event. -/
theorem balanced40_not_mem_weightedCatalog :
    balanced40 ∉ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
      40 fairBool uniformBoolPrior disagreementBad
        (catalogTilt 40) catalogWeight ((1 : ℝ) / 2) := by
  rw [indicator_not_mem_weightedCatalog_iff]
  intro j
  exact balanced40_not_mem_badSamples_entry
    (catalogTilt 40 j) (((1 : ℝ) / 2) * catalogWeight j)
    (catalogTilt_pos (by norm_num) j)
    (by
      have h := catalogTilt_lt_lowRisk (n := 40) (by norm_num) j
      nlinarith)
    (mul_pos (by norm_num) (catalogWeight_pos j))
    (half_mul_catalogWeight_lt_one j)

/-- The four-entry catalog has total exceptional mass at most `1/2`. -/
theorem weightedCatalog_badEventMass_le_half :
    (∑ S ∈ indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
        40 fairBool uniformBoolPrior disagreementBad
          (catalogTilt 40) catalogWeight ((1 : ℝ) / 2),
        finiteProductSampleWeight fairBool S) ≤ (1 : ℝ) / 2 := by
  apply indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta
    (n := 40) (κ := TiltIndex) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF
    uniformBoolPrior_isFullSupportPMF disagreementBad
    (catalogTilt 40) catalogWeight ((1 : ℝ) / 2)
  · exact catalogTilt_pos (by norm_num)
  · intro j
    fin_cases j <;> norm_num [catalogTilt]
  · exact catalogWeight_pos
  · rw [catalogWeight_sum_eq_one]
  · norm_num

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

/-- Select a less aggressive tilt as the observed posterior empirical risk
increases. -/
noncomputable def empiricalTiltSelector
    (S : Fin 40 → Bool) (ρ : Bool → ℝ) : TiltIndex :=
  let rhat := posteriorEmpiricalRisk ρ
    (fun i => finiteEmpiricalRisk (indicatorLoss disagreementBad) i S)
  if rhat ≤ 1 / 8 then 0
  else if rhat ≤ 1 / 2 then 1
  else if rhat ≤ 3 / 4 then 2
  else 3

theorem empiricalTiltSelector_balanced40_uniform_eq_one :
    empiricalTiltSelector balanced40 uniformBoolPrior = 1 := by
  unfold empiricalTiltSelector
  rw [uniformPosterior_balanced40_empiricalRisk_eq_half]
  norm_num

/-- The data-dependent selected certificate is non-vacuous. -/
theorem uniformPosterior_balanced40_selected_certificate_le_thirteenFourteenths :
    posteriorRisk uniformBoolPrior
        (indicatorPopulationRisk fairBool disagreementBad) ≤ (13 : ℝ) / 14 := by
  have hbound :=
    indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem
      (n := 40) (κ := TiltIndex) (ι := Bool) (Z := Bool)
      (by norm_num) fairBool uniformBoolPrior disagreementBad
      (catalogTilt 40) catalogWeight ((1 : ℝ) / 2)
      (catalogTilt_pos (by norm_num))
      (catalogTilt_lt_lowRisk (by norm_num))
      empiricalTiltSelector balanced40 balanced40_not_mem_weightedCatalog
      uniformBoolPrior uniformBoolPrior_isFullSupportPMF.toIsPMF
  rw [empiricalTiltSelector_balanced40_uniform_eq_one,
    uniformPosterior_balanced40_empiricalRisk_eq_half,
    uniformPosterior_kl_self_eq_zero] at hbound
  norm_num [catalogTilt, catalogWeight] at hbound
  have hlog2 : Real.log 2 ≤ 1 := by
    have hraw :=
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hraw ⊢
    exact hraw
  have hlog8 : Real.log 8 ≤ 3 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 3 := by linarith
  linarith

theorem thirteenFourteenths_lt_one : (13 : ℝ) / 14 < 1 := by
  norm_num

#check indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples
#check indicator_mem_weightedCatalog_iff
#check indicator_not_mem_weightedCatalog_iff
#check indicatorFixedTiltBadSamples_subset_weightedCatalog
#check indicator_posteriorGeneralizationGap_le_weightedCatalog_of_not_mem
#check indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta
#check indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem
#check indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem
#check catalogWeight_pos
#check catalogWeight_sum_eq_one
#check half_mul_catalogWeight_lt_one
#check catalogTilt_pos
#check catalogTilt_lt_lowRisk
#check fairBool_isPMF
#check uniformBoolPrior_isFullSupportPMF
#check card_fin40_ge_twenty
#check card_fin40_lt_twenty
#check classifier_populationRisk_eq_half
#check classifier_balanced40_empiricalRisk_eq_half
#check everyPosterior_balanced40_gap_eq_zero
#check everyPosterior_varianceProxy_eq_one_over_oneSixty
#check balanced40_not_mem_badSamples_entry
#check balanced40_not_mem_weightedCatalog
#check weightedCatalog_badEventMass_le_half
#check uniformPosterior_populationRisk_eq_half
#check uniformPosterior_balanced40_empiricalRisk_eq_half
#check uniformPosterior_kl_self_eq_zero
#check empiricalTiltSelector_balanced40_uniform_eq_one
#check uniformPosterior_balanced40_selected_certificate_le_thirteenFourteenths
#check thirteenFourteenths_lt_one

#print axioms indicatorFixedTiltBadSamples_subset_weightedCatalog
#print axioms indicator_mem_weightedCatalog_iff
#print axioms indicator_not_mem_weightedCatalog_iff
#print axioms indicator_posteriorGeneralizationGap_le_weightedCatalog_of_not_mem
#print axioms indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta
#print axioms indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem
#print axioms indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem
#print axioms catalogWeight_pos
#print axioms catalogWeight_sum_eq_one
#print axioms half_mul_catalogWeight_lt_one
#print axioms catalogTilt_pos
#print axioms catalogTilt_lt_lowRisk
#print axioms fairBool_isPMF
#print axioms uniformBoolPrior_isFullSupportPMF
#print axioms card_fin40_ge_twenty
#print axioms card_fin40_lt_twenty
#print axioms classifier_populationRisk_eq_half
#print axioms classifier_balanced40_empiricalRisk_eq_half
#print axioms everyPosterior_balanced40_gap_eq_zero
#print axioms everyPosterior_varianceProxy_eq_one_over_oneSixty
#print axioms balanced40_not_mem_badSamples_entry
#print axioms balanced40_not_mem_weightedCatalog
#print axioms weightedCatalog_badEventMass_le_half
#print axioms uniformPosterior_populationRisk_eq_half
#print axioms uniformPosterior_balanced40_empiricalRisk_eq_half
#print axioms uniformPosterior_kl_self_eq_zero
#print axioms empiricalTiltSelector_balanced40_uniform_eq_one
#print axioms uniformPosterior_balanced40_selected_certificate_le_thirteenFourteenths
#print axioms thirteenFourteenths_lt_one

end


end FormalSLT.Examples.CheckIndicatorBernsteinTiltCatalog
