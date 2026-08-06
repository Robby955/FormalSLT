import FormalSLT.PACBayes.IndicatorBernsteinConfidence

/-!
# Concrete witness for finite indicator PAC-Bayes--Bernstein

This file exercises the full finite i.i.d. indicator theorem on two constant
Boolean classifiers under the fair Boolean law.  At sample size `20`, tilt `6`,
and confidence level `1/2`, the all-true sample is a genuine bad sample for the
point-mass posterior on the constant-true classifier.  Its product mass is
exactly `2⁻²⁰`, while the headline theorem bounds the whole bad-event mass by
`1/2`.

The receipt therefore checks more than elaboration: the bad set is nonempty,
has explicit positive mass, and is constrained by the proved confidence bound.
-/

namespace FormalSLT.Examples.CheckIIDIndicatorPACBayesBernstein

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.IndicatorVariance
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.IndicatorBernsteinMoment
open FormalSLT.PACBayes.IndicatorBernsteinConfidence

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

/-- The two hypotheses are the constant-false and constant-true classifiers. -/
def disagreementBad : Bool → Bool → Bool := fun classifier label =>
  classifier != label

/-- Point mass on the constant-true classifier. -/
def truePosterior : Bool → ℝ := fun classifier => if classifier then 1 else 0

theorem truePosterior_isPMF : IsPMF truePosterior := by
  constructor
  · intro classifier
    cases classifier <;> simp [truePosterior]
  · simp [truePosterior]

/-- The length-20 sample containing only `true` labels. -/
def allTrue20 : Fin 20 → Bool := fun _ => true

theorem true_populationRisk_eq_half :
    indicatorPopulationRisk fairBool disagreementBad true = (1 : ℝ) / 2 := by
  simp [indicatorPopulationRisk, finitePopulationRisk, indicatorLoss,
    disagreementBad, fairBool]

theorem true_allTrue20_empiricalRisk_eq_zero :
    finiteEmpiricalRisk (indicatorLoss disagreementBad) true allTrue20 = 0 := by
  simp [finiteEmpiricalRisk, indicatorLoss, disagreementBad, allTrue20]

theorem true_varianceProxy_eq_one_over_eighty :
    indicatorBernsteinVarianceProxy 20 fairBool disagreementBad true =
      (1 : ℝ) / 80 := by
  rw [indicatorBernsteinVarianceProxy, true_populationRisk_eq_half]
  norm_num

theorem truePosterior_kl_uniform_eq_log_two :
    klDiv truePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, truePosterior, uniformBoolPrior]

theorem truePosterior_gap_allTrue20_eq_half :
    posteriorGeneralizationGap truePosterior
        (indicatorPopulationRisk fairBool disagreementBad)
        (fun i => finiteEmpiricalRisk (indicatorLoss disagreementBad) i allTrue20) =
      (1 : ℝ) / 2 := by
  rw [posteriorGeneralizationGap_eq_sum]
  simp [truePosterior, true_populationRisk_eq_half,
    true_allTrue20_empiricalRisk_eq_zero]

theorem truePosterior_varianceProxy_eq_one_over_eighty :
    posteriorMarginVarianceProxy truePosterior
        (indicatorBernsteinVarianceProxy 20 fairBool disagreementBad) =
      (1 : ℝ) / 80 := by
  simp [posteriorMarginVarianceProxy, truePosterior,
    true_varianceProxy_eq_one_over_eighty]

/-- At the concrete parameters, the PAC-Bayes--Bernstein penalty is below `1/2`. -/
theorem truePosterior_penalty_lt_half :
    (klDiv truePosterior uniformBoolPrior + Real.log (1 / ((1 : ℝ) / 2))) / 6 +
        6 * posteriorMarginVarianceProxy truePosterior
          (indicatorBernsteinVarianceProxy 20 fairBool disagreementBad) /
            (2 * (1 - indicatorBernsteinScale 20 * 6)) <
      (1 : ℝ) / 2 := by
  rw [truePosterior_kl_uniform_eq_log_two,
    truePosterior_varianceProxy_eq_one_over_eighty]
  have hlog : Real.log 2 ≤ 1 := by
    have hraw := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hraw
    exact hraw
  norm_num [indicatorBernsteinScale]
  linarith

/-- The all-true sample is genuinely in the specialized bad-event set. -/
theorem allTrue20_mem_badSamples :
    allTrue20 ∈ indicatorFinitePACBayesBernsteinBadSamples
      20 fairBool uniformBoolPrior disagreementBad 6 ((1 : ℝ) / 2) := by
  unfold indicatorFinitePACBayesBernsteinBadSamples
    finitePACBayesBernsteinFixedLambdaBadSamples
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, truePosterior, truePosterior_isPMF, ?_⟩
  rw [truePosterior_gap_allTrue20_eq_half]
  exact truePosterior_penalty_lt_half

theorem indicatorBadSamples_nonempty :
    (indicatorFinitePACBayesBernsteinBadSamples
      20 fairBool uniformBoolPrior disagreementBad 6 ((1 : ℝ) / 2)).Nonempty :=
  ⟨allTrue20, allTrue20_mem_badSamples⟩

/-- The witness sample has exactly fair-product mass `2⁻²⁰`. -/
theorem allTrue20_productWeight_eq_twoPowNegTwenty :
    finiteProductSampleWeight fairBool allTrue20 = ((1 : ℝ) / 2) ^ (20 : ℕ) := by
  simp [finiteProductSampleWeight, fairBool]

/-- The nonempty bad event has mass at least the witness sample's mass. -/
theorem indicatorBadSamples_mass_ge_twoPowNegTwenty :
    ((1 : ℝ) / 2) ^ (20 : ℕ) ≤
      ∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
          20 fairBool uniformBoolPrior disagreementBad 6 ((1 : ℝ) / 2),
        finiteProductSampleWeight fairBool S := by
  rw [← allTrue20_productWeight_eq_twoPowNegTwenty]
  exact Finset.single_le_sum
    (fun S _ => (finiteProductSampleWeight_isPMF
      (n := 20) fairBool_isPMF).nonneg S)
    allTrue20_mem_badSamples

theorem indicatorBadSamples_mass_pos :
    0 < ∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        20 fairBool uniformBoolPrior disagreementBad 6 ((1 : ℝ) / 2),
      finiteProductSampleWeight fairBool S := by
  exact lt_of_lt_of_le (by positivity) indicatorBadSamples_mass_ge_twoPowNegTwenty

/-- The headline theorem supplies the matching upper confidence bound. -/
theorem indicatorBadSamples_mass_le_half :
    (∑ S ∈ indicatorFinitePACBayesBernsteinBadSamples
        20 fairBool uniformBoolPrior disagreementBad 6 ((1 : ℝ) / 2),
      finiteProductSampleWeight fairBool S) ≤ (1 : ℝ) / 2 := by
  exact indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
    (n := 20) (ι := Bool) (Z := Bool)
    (by norm_num) fairBool fairBool_isPMF
    uniformBoolPrior_isFullSupportPMF disagreementBad
    6 ((1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)

#check indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
#check allTrue20_mem_badSamples
#check indicatorBadSamples_nonempty
#check indicatorBadSamples_mass_ge_twoPowNegTwenty
#check indicatorBadSamples_mass_pos
#check indicatorBadSamples_mass_le_half
#print axioms allTrue20_mem_badSamples
#print axioms indicatorBadSamples_mass_ge_twoPowNegTwenty
#print axioms indicatorBadSamples_mass_pos
#print axioms indicatorBadSamples_mass_le_half

end

end FormalSLT.Examples.CheckIIDIndicatorPACBayesBernstein
