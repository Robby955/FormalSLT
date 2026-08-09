/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.MarkovPACBayes

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
open scoped BigOperators ENNReal

namespace FormalSLT.Examples.CheckMarkovPACBayes

open StochasticDynamics

noncomputable section

/-- An asymmetric two-state transition law. -/
def asymmetricBoolTransition (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦
      if x then
        if y then ((2 / 3 : NNReal) : ENNReal) else ((1 / 3 : NNReal) : ENNReal)
      else
        if y then ((1 / 4 : NNReal) : ENNReal) else ((3 / 4 : NNReal) : ENNReal))
    (by
      fin_cases x
      · have hsumNN : (2 / 3 : NNReal) + 1 / 3 = 1 := by norm_num
        have hsum : ((2 / 3 : NNReal) : ENNReal) + ((1 / 3 : NNReal) : ENNReal) = 1 := by
          rw [← ENNReal.coe_add, hsumNN]
          rfl
        simpa [Fintype.sum_bool, add_comm] using hsum
      · have hsumNN : (1 / 4 : NNReal) + 3 / 4 = 1 := by norm_num
        have hsum : ((1 / 4 : NNReal) : ENNReal) + ((3 / 4 : NNReal) : ENNReal) = 1 := by
          rw [← ENNReal.coe_add, hsumNN]
          rfl
        simpa [Fintype.sum_bool, add_comm] using hsum)

def boolObservable (x : Bool) : ℝ := if x then 1 else 0

/-- Two constant one-step predictors, indexed by their Boolean prediction. -/
def constantPredictor (i : Bool) (_x : Bool) : ℝ := if i then 1 else 0

def uniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem uniformBoolPrior_isFullSupportPMF : IsFullSupportPMF uniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]
  · norm_num [uniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]

/-- Point posterior on one of the two predictors. -/
def boolPointPosterior (selected i : Bool) : ℝ := if i = selected then 1 else 0

theorem boolPointPosterior_isPMF (selected : Bool) :
    IsPMF (boolPointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;> norm_num [boolPointPosterior]
  · fin_cases selected <;> norm_num [boolPointPosterior, Fintype.sum_bool]

theorem boolPointPosterior_average (selected : Bool) (g : Bool → ℝ) :
    posteriorAverage (boolPointPosterior selected) g = g selected := by
  fin_cases selected <;>
    simp [posteriorAverage, boolPointPosterior]

theorem boolPointPosterior_kl_uniform (selected : Bool) :
    klDiv (boolPointPosterior selected) uniformBoolPrior = Real.log 2 := by
  fin_cases selected <;>
    norm_num [klDiv, boolPointPosterior, uniformBoolPrior, Fintype.sum_bool]

theorem falsePredictor_conditionalSquaredRisk
    (n : ℕ) (x : ℕ → Bool) :
    conditionalSquaredRisk asymmetricBoolTransition boolObservable
        (constantPredictor false) n x =
      if x n then 2 / 3 else 1 / 4 := by
  unfold conditionalSquaredRisk asymmetricBoolTransition boolObservable
    constantPredictor transitionSquaredLoss
  rw [PMF.integral_eq_sum]
  cases h : x n <;>
    norm_num [h, PMF.ofFintype_apply, Fintype.sum_bool]

theorem truePredictor_conditionalSquaredRisk
    (n : ℕ) (x : ℕ → Bool) :
    conditionalSquaredRisk asymmetricBoolTransition boolObservable
        (constantPredictor true) n x =
      if x n then 1 / 3 else 3 / 4 := by
  unfold conditionalSquaredRisk asymmetricBoolTransition boolObservable
    constantPredictor transitionSquaredLoss
  rw [PMF.integral_eq_sum]
  cases h : x n <;>
    norm_num [h, PMF.ofFintype_apply, Fintype.sum_bool]

theorem constantPredictor_mem_Icc (i z : Bool) :
    constantPredictor i z ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> norm_num [constantPredictor]

theorem boolObservable_mem_Icc (z : Bool) :
    boolObservable z ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases z <;> norm_num [boolObservable]

theorem constantPredictor_pathSquaredLoss_add_one
    (k : ℕ) (x : ℕ → Bool) :
    pathSquaredLoss boolObservable (constantPredictor false) k x +
        pathSquaredLoss boolObservable (constantPredictor true) k x = 1 := by
  cases hnext : x (k + 1) <;>
    norm_num [pathSquaredLoss, transitionSquaredLoss, boolObservable,
      constantPredictor, hnext]

theorem constantPredictor_empiricalPrequentialRisk_add_one
    (n : ℕ) (hn : 0 < n) (x : ℕ → Bool) :
    empiricalPrequentialRisk boolObservable (constantPredictor false) n x +
        empiricalPrequentialRisk boolObservable (constantPredictor true) n x = 1 := by
  unfold empiricalPrequentialRisk AnytimeValid.runningMean AnytimeValid.runningSum
  rw [← add_div, ← Finset.sum_add_distrib]
  simp_rw [constantPredictor_pathSquaredLoss_add_one]
  simp [hn.ne']

/-- Select the constant predictor with lower observed prequential risk, breaking ties toward `true`. -/
def lowerEmpiricalRiskIndex (n : ℕ) (x : ℕ → Bool) : Bool :=
  if empiricalPrequentialRisk boolObservable (constantPredictor true) n x ≤
      empiricalPrequentialRisk boolObservable (constantPredictor false) n x then
    true
  else
    false

theorem lowerEmpiricalRiskIndex_allFalse (n : ℕ) (hn : 0 < n) :
    lowerEmpiricalRiskIndex n (fun _ ↦ false) = false := by
  simp [lowerEmpiricalRiskIndex, empiricalPrequentialRisk,
    AnytimeValid.runningMean, AnytimeValid.runningSum, pathSquaredLoss,
    transitionSquaredLoss, boolObservable, constantPredictor, hn.ne']

theorem lowerEmpiricalRiskIndex_allTrue (n : ℕ) (hn : 0 < n) :
    lowerEmpiricalRiskIndex n (fun _ ↦ true) = true := by
  simp [lowerEmpiricalRiskIndex, empiricalPrequentialRisk,
    AnytimeValid.runningMean, AnytimeValid.runningSum, pathSquaredLoss,
    transitionSquaredLoss, boolObservable, constantPredictor, hn.ne']

def lowerEmpiricalRiskPosterior (n : ℕ) (x : ℕ → Bool) : Bool → ℝ :=
  boolPointPosterior (lowerEmpiricalRiskIndex n x)

theorem lowerEmpiricalRiskPosterior_isPMF (n : ℕ) (x : ℕ → Bool) :
    IsPMF (lowerEmpiricalRiskPosterior n x) :=
  boolPointPosterior_isPMF _

theorem lowerEmpiricalRiskPosterior_kl_uniform (n : ℕ) (x : ℕ → Bool) :
    klDiv (lowerEmpiricalRiskPosterior n x) uniformBoolPrior = Real.log 2 :=
  boolPointPosterior_kl_uniform _

theorem lowerEmpiricalRiskPosterior_empiricalRisk_le_half
    (n : ℕ) (hn : 0 < n) (x : ℕ → Bool) :
    markovPosteriorEmpiricalPrequentialRisk boolObservable constantPredictor
        (lowerEmpiricalRiskPosterior n x) n x ≤ 1 / 2 := by
  rw [show lowerEmpiricalRiskPosterior n x =
      boolPointPosterior (lowerEmpiricalRiskIndex n x) by rfl]
  unfold markovPosteriorEmpiricalPrequentialRisk
  rw [boolPointPosterior_average]
  have hadd := constantPredictor_empiricalPrequentialRisk_add_one n hn x
  unfold lowerEmpiricalRiskIndex
  split_ifs with h
  · linarith
  · have hlt :
        empiricalPrequentialRisk boolObservable (constantPredictor false) n x <
          empiricalPrequentialRisk boolObservable (constantPredictor true) n x :=
      lt_of_not_ge h
    linarith

/-- At `n = 1024`, `delta = 1/20`, and `lambda = 1/8`, the complete
posterior-selected PAC-Bayes boundary is below `1/20`. -/
theorem selectedMarkovPACBayesBoundary_lt_one_twentieth :
    (1 / 8 : ℝ) / (8 * (1 - (1 / 8 : ℝ) / 3)) +
        (Real.log 2 + Real.log (1 / (1 / 20 : ℝ))) /
          ((1024 : ℝ) * (1 / 8 : ℝ)) < 1 / 20 := by
  have hlog : Real.log 40 < 4 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 40)]
    have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hcombine :
      Real.log 2 + Real.log (1 / (1 / 20 : ℝ)) = Real.log 40 := by
    norm_num
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (20 : ℝ) ≠ 0)]
    norm_num
  rw [hcombine]
  norm_num
  linarith

/-- End-to-end adaptive-posterior receipt for asymmetric Markov dynamics.
One measurable event has probability at most `1/20`. Outside it, a point
posterior selected from the first `1024` observed transitions has exact
complexity `log 2`, empirical risk at most `1/2`, and posterior-average
conditional risk strictly below `11/20`. -/
theorem asymmetricBool_adaptiveMarkovPACBayes_certificate :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      (markovPathMeasure asymmetricBoolTransition false).real E ≤ 1 / 20 ∧
      ∀ x ∉ E,
        IsPMF (lowerEmpiricalRiskPosterior 1024 x) ∧
        klDiv (lowerEmpiricalRiskPosterior 1024 x) uniformBoolPrior = Real.log 2 ∧
        markovPosteriorEmpiricalPrequentialRisk boolObservable constantPredictor
            (lowerEmpiricalRiskPosterior 1024 x) 1024 x ≤ 1 / 2 ∧
        markovPosteriorAverageConditionalRisk asymmetricBoolTransition
            boolObservable constantPredictor
            (lowerEmpiricalRiskPosterior 1024 x) 1024 x < 11 / 20 := by
  have hbase := markovPACBayes_prequentialRisk_certificate
    (ι := Bool) asymmetricBoolTransition false
    (f := boolObservable) (q := constantPredictor)
    boolObservable_mem_Icc (fun i z ↦ constantPredictor_mem_Icc i z)
    uniformBoolPrior_isFullSupportPMF
    (lam := (1 / 8 : ℝ)) (delta := (1 / 20 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rcases hbase with ⟨E, hE, hmass, houtside⟩
  refine ⟨E, hE, hmass, ?_⟩
  intro x hx
  have hposterior := lowerEmpiricalRiskPosterior_isPMF 1024 x
  have hkl := lowerEmpiricalRiskPosterior_kl_uniform 1024 x
  have hemp := lowerEmpiricalRiskPosterior_empiricalRisk_le_half
    1024 (by norm_num) x
  have hrisk := houtside x hx (lowerEmpiricalRiskPosterior 1024 x)
    hposterior 1024 (by norm_num)
  rw [hkl] at hrisk
  have hboundary := selectedMarkovPACBayesBoundary_lt_one_twentieth
  refine ⟨hposterior, hkl, hemp, ?_⟩
  linarith

/-! Complete audit of the public theorem surface introduced by `MarkovPACBayes`. -/

#check StochasticDynamics.markovRiskShortfall
#check StochasticDynamics.markovPosteriorEmpiricalPrequentialRisk
#check StochasticDynamics.markovPosteriorAverageConditionalRisk
#check StochasticDynamics.runningMean_markovRiskShortfall
#check StochasticDynamics.posteriorAverage_runningMean_markovRiskShortfall
#check StochasticDynamics.markovRiskShortfall_incrementAdapted
#check StochasticDynamics.measurable_markovRiskShortfall
#check StochasticDynamics.integrable_markovRiskShortfall
#check StochasticDynamics.abs_markovRiskShortfall_le_one
#check StochasticDynamics.markovRiskShortfall_condExp_eq_zero
#check StochasticDynamics.markovRiskShortfall_condSecondMoment_le_one_fourth
#check StochasticDynamics.markovPACBayesAnyPosteriorUpperFailure
#check StochasticDynamics.markovPACBayesAnyPosteriorUpperFailure_subset_processFailure
#check StochasticDynamics.markovPACBayes_allPosteriors_bound
#check StochasticDynamics.markovPACBayesExceptionalEvent
#check StochasticDynamics.markovPACBayesExceptionalEvent_measurable
#check StochasticDynamics.markovPACBayesRawFailure_subset_exceptionalEvent
#check StochasticDynamics.markovPACBayesExceptionalEvent_mass_le_delta
#check StochasticDynamics.markovPosteriorAverageConditionalRisk_lt_of_not_mem
#check StochasticDynamics.subGammaCgf_oneFourth_one_div
#check StochasticDynamics.markovPACBayes_prequentialRisk_certificate

#print axioms StochasticDynamics.runningMean_markovRiskShortfall
#print axioms StochasticDynamics.posteriorAverage_runningMean_markovRiskShortfall
#print axioms StochasticDynamics.markovRiskShortfall_incrementAdapted
#print axioms StochasticDynamics.measurable_markovRiskShortfall
#print axioms StochasticDynamics.integrable_markovRiskShortfall
#print axioms StochasticDynamics.abs_markovRiskShortfall_le_one
#print axioms StochasticDynamics.markovRiskShortfall_condExp_eq_zero
#print axioms StochasticDynamics.markovRiskShortfall_condSecondMoment_le_one_fourth
#print axioms StochasticDynamics.markovPACBayesAnyPosteriorUpperFailure_subset_processFailure
#print axioms StochasticDynamics.markovPACBayes_allPosteriors_bound
#print axioms StochasticDynamics.markovPACBayesExceptionalEvent_measurable
#print axioms StochasticDynamics.markovPACBayesRawFailure_subset_exceptionalEvent
#print axioms StochasticDynamics.markovPACBayesExceptionalEvent_mass_le_delta
#print axioms StochasticDynamics.markovPosteriorAverageConditionalRisk_lt_of_not_mem
#print axioms StochasticDynamics.subGammaCgf_oneFourth_one_div
#print axioms StochasticDynamics.markovPACBayes_prequentialRisk_certificate

/-! Complete audit of the named checker receipts. -/

#check uniformBoolPrior_isFullSupportPMF
#check boolPointPosterior_isPMF
#check boolPointPosterior_average
#check boolPointPosterior_kl_uniform
#check falsePredictor_conditionalSquaredRisk
#check truePredictor_conditionalSquaredRisk
#check constantPredictor_mem_Icc
#check boolObservable_mem_Icc
#check constantPredictor_pathSquaredLoss_add_one
#check constantPredictor_empiricalPrequentialRisk_add_one
#check lowerEmpiricalRiskIndex_allFalse
#check lowerEmpiricalRiskIndex_allTrue
#check lowerEmpiricalRiskPosterior_isPMF
#check lowerEmpiricalRiskPosterior_kl_uniform
#check lowerEmpiricalRiskPosterior_empiricalRisk_le_half
#check selectedMarkovPACBayesBoundary_lt_one_twentieth
#check asymmetricBool_adaptiveMarkovPACBayes_certificate

#print axioms uniformBoolPrior_isFullSupportPMF
#print axioms boolPointPosterior_isPMF
#print axioms boolPointPosterior_average
#print axioms boolPointPosterior_kl_uniform
#print axioms falsePredictor_conditionalSquaredRisk
#print axioms truePredictor_conditionalSquaredRisk
#print axioms constantPredictor_mem_Icc
#print axioms boolObservable_mem_Icc
#print axioms constantPredictor_pathSquaredLoss_add_one
#print axioms constantPredictor_empiricalPrequentialRisk_add_one
#print axioms lowerEmpiricalRiskIndex_allFalse
#print axioms lowerEmpiricalRiskIndex_allTrue
#print axioms lowerEmpiricalRiskPosterior_isPMF
#print axioms lowerEmpiricalRiskPosterior_kl_uniform
#print axioms lowerEmpiricalRiskPosterior_empiricalRisk_le_half
#print axioms selectedMarkovPACBayesBoundary_lt_one_twentieth
#print axioms asymmetricBool_adaptiveMarkovPACBayes_certificate

end

end FormalSLT.Examples.CheckMarkovPACBayes
