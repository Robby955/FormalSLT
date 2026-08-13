import FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete finite PAC-Bayes empirical-variance checker

The finite law has two unequal atoms and two hypotheses with distinct bounded-loss
population variances. The posterior is selected from the first observation.
At `n = 34`, `eta = 33/34`, and `delta = 1/16`, both selector branches receive
a rearranged variance certificate at most `202/825 < 1/4`. Direct bad-set
nonmembership and positive product mass are proved independently.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVariancePACBayes

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes

noncomputable section

/-- Unequal two-point data law: `P(false)=4/5`, `P(true)=1/5`. -/
def dataLaw : Bool → ℝ := fun z => if z then (1 : ℝ) / 5 else 4 / 5

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    cases z <;> norm_num [dataLaw]
  · norm_num [dataLaw]

/-- Uniform full-support prior on the two hypotheses. -/
def prior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  constructor
  · constructor
    · intro i
      norm_num [prior]
    · norm_num [prior]
  · intro i
    norm_num [prior]

/-- Two bounded, deliberately asymmetric losses.  Hypothesis `false` incurs
unit loss only on a `true` observation; hypothesis `true` incurs half loss only
on a `false` observation.  Their population variances are therefore distinct. -/
def loss (h z : Bool) : ℝ :=
  if h = false then (if z = true then 1 else 0)
  else (if z = false then (1 : ℝ) / 2 else 0)

theorem loss_mem_Icc (h z : Bool) : loss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [loss]

/-- Posterior giving weight `3/5` to `favored` and `2/5` to the other hypothesis. -/
def nearPosterior (favored : Bool) : Bool → ℝ := fun h =>
  if h = favored then (3 : ℝ) / 5 else 2 / 5

theorem nearPosterior_isPMF (favored : Bool) : IsPMF (nearPosterior favored) := by
  constructor
  · intro h
    cases favored <;> cases h <;> norm_num [nearPosterior]
  · cases favored <;> norm_num [nearPosterior]

/-- Sample-dependent posterior: favor the first observed label. -/
def selector (S : Fin 34 → Bool) : Bool → ℝ := nearPosterior (S 0)

theorem selector_isPMF (S : Fin 34 → Bool) : IsPMF (selector S) :=
  nearPosterior_isPMF (S 0)

def allFalse : Fin 34 → Bool := fun _ => false
def allTrue : Fin 34 → Bool := fun _ => true

theorem selector_allFalse : selector allFalse = nearPosterior false := by
  rfl

theorem selector_allTrue : selector allTrue = nearPosterior true := by
  rfl

theorem selector_allFalse_weights :
    selector allFalse false = (3 : ℝ) / 5 ∧
      selector allFalse true = (2 : ℝ) / 5 := by
  norm_num [selector, allFalse, nearPosterior]

theorem selector_allTrue_weights :
    selector allTrue false = (2 : ℝ) / 5 ∧
      selector allTrue true = (3 : ℝ) / 5 := by
  norm_num [selector, allTrue, nearPosterior]

theorem selector_takes_two_values : selector allFalse ≠ selector allTrue := by
  intro h
  have hfalse := congrFun h false
  norm_num [selector, allFalse, allTrue, nearPosterior] at hfalse

/-- The two hypotheses have genuinely distinct population variances. -/
theorem populationVariance_false_eq_four_twentyFive :
    finitePopulationVariance dataLaw loss false = (4 : ℝ) / 25 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw, loss]

theorem populationVariance_true_eq_one_twentyFive :
    finitePopulationVariance dataLaw loss true = (1 : ℝ) / 25 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw, loss]

theorem populationVariance_le_four_twentyFive (h : Bool) :
    finitePopulationVariance dataLaw loss h ≤ (4 : ℝ) / 25 := by
  cases h
  · rw [populationVariance_false_eq_four_twentyFive]
  · rw [populationVariance_true_eq_one_twentyFive]
    norm_num

/-- A constant sample gives zero Bessel empirical variance for either hypothesis. -/
theorem empiricalVariance_allFalse_eq_zero (h : Bool) :
    finiteEmpiricalVariance loss h allFalse = 0 := by
  cases h <;>
    norm_num [finiteEmpiricalVariance,
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
      FormalSLT.Statistics.sampleMean, loss, allFalse]

theorem empiricalVariance_allTrue_eq_zero (h : Bool) :
    finiteEmpiricalVariance loss h allTrue = 0 := by
  cases h <;>
    norm_num [finiteEmpiricalVariance,
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
      FormalSLT.Statistics.sampleMean, loss, allTrue]

/-- The two explicit posterior choices yield distinct true posterior variances. -/
theorem selectedPosterior_populationVariance_allFalse_eq_14_125 :
    posteriorAverage (selector allFalse)
        (fun h => finitePopulationVariance dataLaw loss h) = (14 : ℝ) / 125 := by
  norm_num [posteriorAverage, selector, allFalse, nearPosterior,
    populationVariance_false_eq_four_twentyFive,
    populationVariance_true_eq_one_twentyFive]

theorem selectedPosterior_populationVariance_allTrue_eq_11_125 :
    posteriorAverage (selector allTrue)
        (fun h => finitePopulationVariance dataLaw loss h) = (11 : ℝ) / 125 := by
  norm_num [posteriorAverage, selector, allTrue, nearPosterior,
    populationVariance_false_eq_four_twentyFive,
    populationVariance_true_eq_one_twentyFive]

theorem selectedPosterior_populationVariance_differs :
    posteriorAverage (selector allFalse)
        (fun h => finitePopulationVariance dataLaw loss h) ≠
      posteriorAverage (selector allTrue)
        (fun h => finitePopulationVariance dataLaw loss h) := by
  rw [selectedPosterior_populationVariance_allFalse_eq_14_125,
    selectedPosterior_populationVariance_allTrue_eq_11_125]
  norm_num

theorem selectedPosterior_empiricalVariance_allFalse_eq_zero :
    posteriorAverage (selector allFalse)
        (fun h => finiteEmpiricalVariance loss h allFalse) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allFalse_eq_zero]
  simp

theorem selectedPosterior_empiricalVariance_allTrue_eq_zero :
    posteriorAverage (selector allTrue)
        (fun h => finiteEmpiricalVariance loss h allTrue) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allTrue_eq_zero]
  simp

theorem posterior_populationVariance_le_four_twentyFive
    (ρ : Bool → ℝ) (hρ : IsPMF ρ) :
    posteriorAverage ρ (fun h => finitePopulationVariance dataLaw loss h) ≤
      (4 : ℝ) / 25 := by
  unfold posteriorAverage
  calc
    (∑ h : Bool, ρ h * finitePopulationVariance dataLaw loss h) ≤
        ∑ h : Bool, ρ h * ((4 : ℝ) / 25) := by
      exact Finset.sum_le_sum (fun h _ =>
        mul_le_mul_of_nonneg_left
          (populationVariance_le_four_twentyFive h) (hρ.nonneg h))
    _ = (4 : ℝ) / 25 := by
      rw [← Finset.sum_mul, hρ.sum_one]
      norm_num

theorem posterior_empiricalVariance_allFalse_eq_zero
    (ρ : Bool → ℝ) :
    posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h allFalse) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allFalse_eq_zero]
  simp

theorem posterior_empiricalVariance_allTrue_eq_zero
    (ρ : Bool → ℝ) :
    posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h allTrue) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allTrue_eq_zero]
  simp

/-- Tangent-line estimate for both selector outputs: `KL ≤ 1/25`. -/
theorem nearPosterior_kl_le_one_twentyFive (favored : Bool) :
    klDiv (nearPosterior favored) prior ≤ (1 : ℝ) / 25 := by
  have hlogSixFifths : Real.log ((6 : ℝ) / 5) ≤ 1 / 5 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)
    norm_num at h
    exact h
  have hlogFourFifths : Real.log ((4 : ℝ) / 5) ≤ -(1 / 5) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    norm_num at h
    exact h
  have hSixScaled :
      (3 : ℝ) / 5 * Real.log (6 / 5) ≤ (3 : ℝ) / 25 := by
    nlinarith
  have hFourScaled :
      (2 : ℝ) / 5 * Real.log (4 / 5) ≤ -(2 : ℝ) / 25 := by
    nlinarith
  cases favored <;> simp [klDiv, nearPosterior, prior] <;> linarith

theorem selector_kl_le_one_twentyFive (S : Fin 34 → Bool) :
    klDiv (selector S) prior ≤ (1 : ℝ) / 25 :=
  nearPosterior_kl_le_one_twentyFive (S 0)

/-- `log(1/delta)` at `delta=1/16` is at most four. -/
theorem log_inv_sixteenth_le_four :
    Real.log (1 / ((1 : ℝ) / 16)) ≤ 4 := by
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  norm_num only [one_div, inv_div, inv_one]
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
  norm_num
  linarith

theorem sixtySix_twentyFive_lt_log_inv_sixteenth :
    (66 : ℝ) / 25 < Real.log (1 / ((1 : ℝ) / 16)) := by
  have hlogTwo := Real.log_two_gt_d9
  norm_num only [one_div, inv_div, inv_one]
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
  norm_num
  nlinarith

/-- The exact rearrangement denominator at `n=34`, `eta=33/34` is `1/2`. -/
theorem denominator_eq_half :
    1 - ((33 : ℝ) / 34) * 34 / (2 * (34 - 1)) = (1 : ℝ) / 2 := by
  norm_num

/-- The exact specialized right-hand side expected from the rearranged theorem. -/
def certificate (ρ : Bool → ℝ) (S : Fin 34 → Bool) : ℝ :=
  (posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h S) +
      (klDiv ρ prior + Real.log (1 / ((1 : ℝ) / 16))) /
        (((33 : ℝ) / 34) * 34)) /
    (1 - ((33 : ℝ) / 34) * 34 / (2 * (34 - 1)))

/-- Exact rational upper envelope obtained from `KL ≤ 1/25` and `log 16 ≤ 4`. -/
theorem selected_zero_empirical_certificate_le_202_825 (S : Fin 34 → Bool) :
    (((0 : ℝ) +
        (klDiv (selector S) prior + Real.log (1 / ((1 : ℝ) / 16))) /
          (((33 : ℝ) / 34) * 34)) /
      (1 - ((33 : ℝ) / 34) * 34 / (2 * (34 - 1)))) ≤ (202 : ℝ) / 825 := by
  rw [denominator_eq_half]
  have hkl := selector_kl_le_one_twentyFive S
  have hlog := log_inv_sixteenth_le_four
  norm_num
  linarith

/-- The selected-posterior certificate is uniformly below `1/4` on any
sample whose posterior empirical variance is zero. -/
theorem selected_zero_empirical_certificate_lt_quarter (S : Fin 34 → Bool) :
    (((0 : ℝ) +
        (klDiv (selector S) prior + Real.log (1 / ((1 : ℝ) / 16))) /
          (((33 : ℝ) / 34) * 34)) /
      (1 - ((33 : ℝ) / 34) * 34 / (2 * (34 - 1)))) < 1 / 4 := by
  exact lt_of_le_of_lt (selected_zero_empirical_certificate_le_202_825 S) (by norm_num)

theorem posteriorVarianceProxy33_eq
    (ρ : Bool → ℝ) :
    posteriorMarginVarianceProxy ρ
        (fun h => finitePopulationVariance dataLaw loss h / (33 : ℝ)) =
      posteriorAverage ρ (finitePopulationVariance dataLaw loss) / 33 := by
  unfold posteriorMarginVarianceProxy posteriorAverage
  norm_num
  ring

set_option maxRecDepth 2048 in
/-- Directly prove an explicit sample lies outside the actual simultaneous
bad set.  This is independent of the sample's positive product mass. -/
theorem allFalse_not_mem_badSamples :
    allFalse ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((33 : ℝ) / 34) ((1 : ℝ) / 16) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := sixtySix_twentyFive_lt_log_inv_sixteenth
  have hB := posterior_empiricalVariance_allFalse_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

set_option maxRecDepth 2048 in
theorem allTrue_not_mem_badSamples :
    allTrue ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((33 : ℝ) / 34) ((1 : ℝ) / 16) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := sixtySix_twentyFive_lt_log_inv_sixteenth
  have hB := posterior_empiricalVariance_allTrue_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

theorem badSamples_mass_le_sixteenth :
    (∑ S ∈ finiteEmpiricalVariancePACBayesBadSamples
        34 dataLaw prior loss ((33 : ℝ) / 34) ((1 : ℝ) / 16),
      finiteProductSampleWeight dataLaw S) ≤ (1 : ℝ) / 16 := by
  exact finiteEmpiricalVariancePACBayes_badEventMass_le_delta
    (n := 34) (Z := Bool) (ι := Bool)
    (by norm_num) dataLaw dataLaw_isPMF prior_isFullSupportPMF loss
    (fun i z => loss_mem_Icc i z)
    (eta := (33 : ℝ) / 34) (delta := (1 : ℝ) / 16)
    (by norm_num) (by norm_num)

theorem selected_allFalse_posteriorVariance_le_certificate :
    posteriorAverage (selector allFalse) (finitePopulationVariance dataLaw loss) ≤
      certificate (selector allFalse) allFalse := by
  exact posteriorPopulationVariance_le_empiricalVariance_of_not_mem
    (n := 34) (Z := Bool) (ι := Bool) (by norm_num)
    dataLaw prior loss
    (eta := (33 : ℝ) / 34) (delta := (1 : ℝ) / 16)
    (by norm_num) (by norm_num)
    allFalse allFalse_not_mem_badSamples
    (selector allFalse) (selector_isPMF allFalse)

theorem selected_allTrue_posteriorVariance_le_certificate :
    posteriorAverage (selector allTrue) (finitePopulationVariance dataLaw loss) ≤
      certificate (selector allTrue) allTrue := by
  exact posteriorPopulationVariance_le_empiricalVariance_of_not_mem
    (n := 34) (Z := Bool) (ι := Bool) (by norm_num)
    dataLaw prior loss
    (eta := (33 : ℝ) / 34) (delta := (1 : ℝ) / 16)
    (by norm_num) (by norm_num)
    allTrue allTrue_not_mem_badSamples
    (selector allTrue) (selector_isPMF allTrue)

theorem selected_allFalse_certificate_le_202_825 :
    certificate (selector allFalse) allFalse ≤ (202 : ℝ) / 825 := by
  unfold certificate
  rw [selectedPosterior_empiricalVariance_allFalse_eq_zero]
  exact selected_zero_empirical_certificate_le_202_825 allFalse

theorem selected_allTrue_certificate_le_202_825 :
    certificate (selector allTrue) allTrue ≤ (202 : ℝ) / 825 := by
  unfold certificate
  rw [selectedPosterior_empiricalVariance_allTrue_eq_zero]
  exact selected_zero_empirical_certificate_le_202_825 allTrue

/-- The actual simultaneous theorem applies to both posterior branches, and
both resulting upper bounds are strictly below `1/4`. -/
theorem selected_branches_nonvacuous :
    (posteriorAverage (selector allFalse) (finitePopulationVariance dataLaw loss) ≤
        certificate (selector allFalse) allFalse ∧
      certificate (selector allFalse) allFalse < (1 : ℝ) / 4) ∧
    (posteriorAverage (selector allTrue) (finitePopulationVariance dataLaw loss) ≤
        certificate (selector allTrue) allTrue ∧
      certificate (selector allTrue) allTrue < (1 : ℝ) / 4) := by
  exact ⟨⟨selected_allFalse_posteriorVariance_le_certificate,
      selected_allFalse_certificate_le_202_825.trans_lt (by norm_num)⟩,
    ⟨selected_allTrue_posteriorVariance_le_certificate,
      selected_allTrue_certificate_le_202_825.trans_lt (by norm_num)⟩⟩

/-- The two explicit selector-triggering samples each have strictly positive
product mass.  This is intentionally separate from any good-event claim. -/
theorem allFalse_productWeight_pos :
    0 < finiteProductSampleWeight dataLaw allFalse := by
  simp [finiteProductSampleWeight, dataLaw, allFalse]

theorem allTrue_productWeight_pos :
    0 < finiteProductSampleWeight dataLaw allTrue := by
  simp [finiteProductSampleWeight, dataLaw, allTrue]

#check finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
#check finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
#check finiteEmpiricalVariance_expectedPriorBernsteinExpMoment_le_one
#check finiteEmpiricalVariance_posteriorGap_le_of_not_mem
#check finiteEmpiricalVariancePACBayes_badEventMass_le_delta
#check posteriorPopulationVariance_le_empiricalVariance_of_not_mem
#check dataLaw_isPMF
#check prior_isFullSupportPMF
#check loss_mem_Icc
#check selector_isPMF
#check selector_allFalse
#check selector_allTrue
#check selector_allFalse_weights
#check selector_allTrue_weights
#check selector_takes_two_values
#check populationVariance_false_eq_four_twentyFive
#check populationVariance_true_eq_one_twentyFive
#check selectedPosterior_populationVariance_allFalse_eq_14_125
#check selectedPosterior_populationVariance_allTrue_eq_11_125
#check selectedPosterior_populationVariance_differs
#check nearPosterior_kl_le_one_twentyFive
#check selected_zero_empirical_certificate_le_202_825
#check allFalse_not_mem_badSamples
#check allTrue_not_mem_badSamples
#check badSamples_mass_le_sixteenth
#check selected_branches_nonvacuous
#check allFalse_productWeight_pos
#check allTrue_productWeight_pos

#print axioms finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
#print axioms finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
#print axioms finiteEmpiricalVariance_expectedPriorBernsteinExpMoment_le_one
#print axioms finiteEmpiricalVariance_posteriorGap_le_of_not_mem
#print axioms finiteEmpiricalVariancePACBayes_badEventMass_le_delta
#print axioms posteriorPopulationVariance_le_empiricalVariance_of_not_mem
#print axioms dataLaw_isPMF
#print axioms prior_isFullSupportPMF
#print axioms loss_mem_Icc
#print axioms selector_isPMF
#print axioms selector_allFalse
#print axioms selector_allTrue
#print axioms selector_allFalse_weights
#print axioms selector_allTrue_weights
#print axioms selector_takes_two_values
#print axioms populationVariance_false_eq_four_twentyFive
#print axioms populationVariance_true_eq_one_twentyFive
#print axioms selectedPosterior_populationVariance_allFalse_eq_14_125
#print axioms selectedPosterior_populationVariance_allTrue_eq_11_125
#print axioms selectedPosterior_populationVariance_differs
#print axioms nearPosterior_kl_le_one_twentyFive
#print axioms selected_zero_empirical_certificate_le_202_825
#print axioms allFalse_not_mem_badSamples
#print axioms allTrue_not_mem_badSamples
#print axioms badSamples_mass_le_sixteenth
#print axioms selected_branches_nonvacuous
#print axioms allFalse_productWeight_pos
#print axioms allTrue_productWeight_pos

end

end FormalSLT.Examples.CheckFiniteEmpiricalVariancePACBayes
