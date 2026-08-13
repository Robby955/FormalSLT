import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk

/-!
# Concrete finite empirical-Bernstein risk checker

A fair two-point law, nonconstant indicator loss, and one-hypothesis posterior
instantiate the two-event theorem at `n = 2`, `eta = 1/2`, `lambda = 1`, and
separate failure budgets `1/4`. The combined bad set has mass at most `1/2`,
so a good sample exists and the observable final risk inequality holds there.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalBernsteinRisk

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteBoundedLossBernstein
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk

noncomputable section

def dataLaw : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

def prior : Unit → ℝ := fun _ => 1

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  constructor
  · constructor
    · intro i
      norm_num [prior]
    · norm_num [prior]
  · intro i
    norm_num [prior]

def posterior : Unit → ℝ := prior

theorem posterior_isPMF : IsPMF posterior :=
  prior_isFullSupportPMF.toIsPMF

def loss (_ : Unit) (z : Bool) : ℝ := if z then 1 else 0

theorem loss_mem_Icc (i : Unit) (z : Bool) :
    loss i z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z <;> norm_num [loss]

def badSamples : Finset (Fin 2 → Bool) :=
  finiteEmpiricalBernsteinRiskBadSamples
    2 dataLaw prior loss (1 / 2) 1 (1 / 4) (1 / 4)

theorem badSamples_mass_le_half :
    (∑ S ∈ badSamples, finiteProductSampleWeight dataLaw S) ≤ (1 : ℝ) / 2 := by
  have hmass :=
    finiteEmpiricalBernsteinRisk_badEventMass_le
      (n := 2) (by norm_num) dataLaw dataLaw_isPMF
      prior_isFullSupportPMF loss loss_mem_Icc
      (eta := (1 : ℝ) / 2) (lambda := 1)
      (deltaVariance := (1 : ℝ) / 4) (deltaRisk := (1 : ℝ) / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hmass
  simpa [badSamples] using hmass

theorem goodSample_exists : ∃ S : Fin 2 → Bool, S ∉ badSamples := by
  by_contra hgood
  push Not at hgood
  have hbad : badSamples = Finset.univ := by
    ext S
    simp [hgood S]
  have htotal :
      (∑ S : Fin 2 → Bool, finiteProductSampleWeight dataLaw S) = 1 :=
    (finiteProductSampleWeight_isPMF (n := 2) dataLaw_isPMF).sum_one
  have hmass := badSamples_mass_le_half
  rw [hbad] at hmass
  norm_num [htotal] at hmass

theorem fairBool_empiricalBernsteinRisk_witness :
    ∃ S : Fin 2 → Bool,
      S ∉ badSamples ∧
        posteriorAverage posterior (finitePopulationRisk dataLaw loss) ≤
          posteriorAverage posterior (fun i => finiteEmpiricalRisk loss i S) +
            (klDiv posterior prior + Real.log (1 / ((1 : ℝ) / 4))) / 1 +
            1 *
                ((posteriorAverage posterior
                      (fun i => finiteEmpiricalVariance loss i S) +
                    (klDiv posterior prior + Real.log (1 / ((1 : ℝ) / 4))) /
                      (((1 : ℝ) / 2) * 2)) /
                  (1 - ((1 : ℝ) / 2) * 2 / (2 * (2 - 1)))) /
              (2 * 2 * (1 - 1 / (3 * 2))) := by
  rcases goodSample_exists with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem
    (n := 2) (by norm_num) dataLaw prior loss
    (eta := (1 : ℝ) / 2) (lambda := 1)
    (deltaVariance := (1 : ℝ) / 4) (deltaRisk := (1 : ℝ) / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    S hS posterior posterior_isPMF

#check finiteEmpiricalBernsteinRisk_badEventMass_le
#check posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem
#check boundedLossDeviation_centered
#check boundedLossDeviation_secondMoment_eq
#check boundedLoss_oneCoordinateDeviationMGF_le
#check boundedLoss_product_mgf_le
#check boundedLoss_product_normalizedMGF_le_one
#check boundedLossBernsteinMGFBudget_eq_generic
#check boundedLoss_expectedPriorBernsteinExpMoment_le_one
#check boundedLoss_posteriorRisk_le_populationVariance_of_not_mem
#check finiteBoundedLossBernstein_badEventMass_le_delta

#print axioms finiteEmpiricalBernsteinRisk_badEventMass_le
#print axioms posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem
#print axioms boundedLossDeviation_centered
#print axioms boundedLossDeviation_secondMoment_eq
#print axioms boundedLoss_oneCoordinateDeviationMGF_le
#print axioms boundedLoss_product_mgf_le
#print axioms boundedLoss_product_normalizedMGF_le_one
#print axioms boundedLossBernsteinMGFBudget_eq_generic
#print axioms boundedLoss_expectedPriorBernsteinExpMoment_le_one
#print axioms boundedLoss_posteriorRisk_le_populationVariance_of_not_mem
#print axioms finiteBoundedLossBernstein_badEventMass_le_delta
#print axioms fairBool_empiricalBernsteinRisk_witness

end

end FormalSLT.Examples.CheckFiniteEmpiricalBernsteinRisk
