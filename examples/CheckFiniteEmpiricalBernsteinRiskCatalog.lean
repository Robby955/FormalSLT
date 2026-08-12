import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog

/-!
# Concrete finite empirical-Bernstein catalog checker

A fair two-point law, nonconstant indicator loss, and two-entry variance and
risk catalogs instantiate the weighted-catalog theorem at `n = 2`. Both
catalogs use weights `1/2, 1/2`; the variance tilts are `1/2, 1/4`, and the
risk tilts are `1, 2`. The combined bad set has mass at most `1/2`, so a good
sample exists. The two selectors genuinely inspect different sample
coordinates before the final observable risk inequality is instantiated.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalBernsteinRiskCatalog

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog

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

def etaCatalog (j : Fin 2) : ℝ := if j = 0 then 1 / 2 else 1 / 4

def lambdaCatalog (k : Fin 2) : ℝ := if k = 0 then 1 else 2

def varianceWeight (_j : Fin 2) : ℝ := 1 / 2

def riskWeight (_k : Fin 2) : ℝ := 1 / 2

theorem etaCatalog_pos (j : Fin 2) : 0 < etaCatalog j := by
  fin_cases j <;> norm_num [etaCatalog]

theorem etaCatalog_upper (j : Fin 2) :
    etaCatalog j * (2 : ℝ) < 2 * ((2 : ℝ) - 1) := by
  fin_cases j <;> norm_num [etaCatalog]

theorem lambdaCatalog_pos (k : Fin 2) : 0 < lambdaCatalog k := by
  fin_cases k <;> norm_num [lambdaCatalog]

theorem lambdaCatalog_lt (k : Fin 2) : lambdaCatalog k < 3 * (2 : ℝ) := by
  fin_cases k <;> norm_num [lambdaCatalog]

theorem varianceWeight_pos (j : Fin 2) : 0 < varianceWeight j := by
  norm_num [varianceWeight]

theorem riskWeight_pos (k : Fin 2) : 0 < riskWeight k := by
  norm_num [riskWeight]

theorem varianceWeight_sum : ∑ j : Fin 2, varianceWeight j ≤ 1 := by
  norm_num [varianceWeight, Fin.sum_univ_two]

theorem riskWeight_sum : ∑ k : Fin 2, riskWeight k ≤ 1 := by
  norm_num [riskWeight, Fin.sum_univ_two]

def selectVariance (S : Fin 2 → Bool) (_rho : Unit → ℝ) : Fin 2 :=
  if S 0 then 0 else 1

def selectRisk (S : Fin 2 → Bool) (_rho : Unit → ℝ) : Fin 2 :=
  if S 1 then 1 else 0

def badSamples : Finset (Fin 2 → Bool) :=
  finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples
    2 dataLaw prior loss etaCatalog varianceWeight (1 / 4)
      lambdaCatalog riskWeight (1 / 4)

theorem badSamples_mass_le_half :
    (∑ S ∈ badSamples, finiteProductSampleWeight dataLaw S) ≤ (1 : ℝ) / 2 := by
  have hmass :=
    finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le
      (n := 2) (by norm_num) dataLaw dataLaw_isPMF
      prior_isFullSupportPMF loss loss_mem_Icc
      etaCatalog varianceWeight (1 / 4)
      lambdaCatalog riskWeight (1 / 4)
      etaCatalog_pos lambdaCatalog_pos lambdaCatalog_lt
      varianceWeight_pos varianceWeight_sum riskWeight_pos riskWeight_sum
      (by norm_num) (by norm_num)
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

def selectedRiskCertificate (S : Fin 2 → Bool) : Prop :=
  posteriorAverage posterior (finitePopulationRisk dataLaw loss) ≤
    posteriorAverage posterior (fun i => finiteEmpiricalRisk loss i S) +
      (klDiv posterior prior +
          Real.log (1 / ((1 / 4) * riskWeight (selectRisk S posterior)))) /
        lambdaCatalog (selectRisk S posterior) +
      lambdaCatalog (selectRisk S posterior) *
          ((posteriorAverage posterior (fun i => finiteEmpiricalVariance loss i S) +
              (klDiv posterior prior +
                  Real.log (1 /
                    ((1 / 4) * varianceWeight (selectVariance S posterior)))) /
                (etaCatalog (selectVariance S posterior) * (2 : ℝ))) /
            (1 - etaCatalog (selectVariance S posterior) * (2 : ℝ) /
              (2 * ((2 : ℝ) - 1)))) /
        (2 * (2 : ℝ) *
          (1 - lambdaCatalog (selectRisk S posterior) / (3 * (2 : ℝ))))

theorem fairBool_empiricalBernsteinCatalog_witness :
    ∃ S : Fin 2 → Bool, S ∉ badSamples ∧ selectedRiskCertificate S := by
  rcases goodSample_exists with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact
    posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem
      (n := 2) (by norm_num) dataLaw prior loss
      etaCatalog varianceWeight (1 / 4) lambdaCatalog riskWeight (1 / 4)
      etaCatalog_pos etaCatalog_upper lambdaCatalog_pos lambdaCatalog_lt
      selectVariance selectRisk S hS posterior posterior_isPMF

#check finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le
#check posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem

#print axioms finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le
#print axioms posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem
#print axioms fairBool_empiricalBernsteinCatalog_witness

end

end FormalSLT.Examples.CheckFiniteEmpiricalBernsteinRiskCatalog
