/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.StochasticDynamics.MarkovRisk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FormalSLT.Examples.CheckMarkovRisk

open StochasticDynamics

#check StochasticDynamics.pathSquaredLoss_condExp
#check StochasticDynamics.markovRiskInnovation_condExp_eq_zero
#check StochasticDynamics.markovPrequentialRiskExceptionalEvent_mass_le_delta
#check StochasticDynamics.averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem

#print axioms StochasticDynamics.pathSquaredLoss_condExp
#print axioms StochasticDynamics.markovRiskInnovation_condExp_eq_zero
#print axioms StochasticDynamics.markovPrequentialRiskExceptionalEvent_mass_le_delta
#print axioms StochasticDynamics.averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem

noncomputable section

/-- Persistent two-state Markov dynamics. -/
def persistentBoolTransition (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y = x then ((3 / 4 : NNReal) : ENNReal) else ((1 / 4 : NNReal) : ENNReal))
    (by
    have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
    have hsum : ((3 / 4 : NNReal) : ENNReal) + ((1 / 4 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hsumNN]
      rfl
    fin_cases x <;> simpa [Fintype.sum_bool, add_comm] using hsum)

def boolObservable (x : Bool) : ℝ := if x then 1 else 0

/-- The fixed predictor equals the transition probability of the next state. -/
def boolPredictor (x : Bool) : ℝ := if x then 3 / 4 else 1 / 4

theorem persistentBool_conditionalSquaredRisk_eq (n : ℕ) (x : ℕ → Bool) :
    conditionalSquaredRisk persistentBoolTransition boolObservable boolPredictor n x = 3 / 16 := by
  unfold conditionalSquaredRisk persistentBoolTransition boolObservable boolPredictor
    transitionSquaredLoss
  rw [PMF.integral_eq_sum]
  cases h : x n <;> norm_num [h, PMF.ofFintype_apply, Fintype.sum_bool]

def singletonTilt : Finset ℝ := {1 / 8}

/-- Four false states followed by four true states, repeated every eight
coordinates.  Exactly two of each eight one-step transitions switch state.
This is a deterministic arithmetic receipt, not a claim that the singleton
path lies outside the exceptional event or has positive path-law mass. -/
def periodEightPath (n : ℕ) : Bool := decide (4 ≤ n % 8)

private def periodEightLossUnits (n : ℕ) : ℕ :=
  if periodEightPath (n + 1) = periodEightPath n then 1 else 9

private lemma periodEightPath_pathSquaredLoss_eq_units (n : ℕ) :
    pathSquaredLoss boolObservable boolPredictor n periodEightPath =
      (periodEightLossUnits n : ℝ) / 16 := by
  generalize hcurrent : periodEightPath n = current
  generalize hnext : periodEightPath (n + 1) = next
  cases current <;> cases next <;>
    norm_num [pathSquaredLoss, transitionSquaredLoss, boolObservable, boolPredictor,
      periodEightLossUnits, hcurrent, hnext]

set_option maxRecDepth 10000 in
private lemma periodEightLossUnits_sum_1024 :
    ∑ n ∈ Finset.range 1024, periodEightLossUnits n = 3072 := by
  decide

theorem periodEightPath_empiricalPrequentialRisk_eight_eq :
    empiricalPrequentialRisk boolObservable boolPredictor 8 periodEightPath = 3 / 16 := by
  norm_num [empiricalPrequentialRisk, AnytimeValid.runningMean, AnytimeValid.runningSum,
    Finset.sum_range_succ, pathSquaredLoss, transitionSquaredLoss, boolObservable,
    boolPredictor, periodEightPath]

theorem periodEightPath_empiricalPrequentialRisk_1024_eq :
    empiricalPrequentialRisk boolObservable boolPredictor 1024 periodEightPath = 3 / 16 := by
  have hsumR :
      ∑ n ∈ Finset.range 1024, (periodEightLossUnits n : ℝ) = 3072 := by
    exact_mod_cast periodEightLossUnits_sum_1024
  unfold empiricalPrequentialRisk AnytimeValid.runningMean AnytimeValid.runningSum
  simp_rw [periodEightPath_pathSquaredLoss_eq_units]
  rw [← Finset.sum_div, hsumR]
  norm_num

/-- At `delta = 1/20`, singleton tilt `1/8`, and `n = 1024`, the
two-sided boundary is strictly below `1/10`. -/
theorem singletonTilt_boundary_lt_one_tenth :
    AnytimeValid.subGammaCgf 1 1 (1 / 8) / (1 / 8) +
        Real.log ((singletonTilt.card : ℝ) / ((1 / 20) / 2)) /
          ((1024 : ℝ) * (1 / 8)) < 1 / 10 := by
  have hlog : Real.log 40 < 4 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 40)]
    have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  norm_num [singletonTilt, AnytimeValid.subGammaCgf]
  linarith

theorem persistentBool_averageConditionalRisk_1024_eq (x : ℕ → Bool) :
    averageConditionalRisk persistentBoolTransition boolObservable boolPredictor 1024 x =
      3 / 16 := by
  unfold averageConditionalRisk AnytimeValid.runningMean AnytimeValid.runningSum
  simp_rw [persistentBool_conditionalSquaredRisk_eq]
  norm_num

theorem persistentBool_pathSquaredLoss_le_nine_sixteenths
    (n : ℕ) (x : ℕ → Bool) :
    pathSquaredLoss boolObservable boolPredictor n x ≤ 9 / 16 := by
  cases hcurrent : x n <;> cases hnext : x (n + 1) <;>
    norm_num [pathSquaredLoss, transitionSquaredLoss, boolObservable, boolPredictor,
      hcurrent, hnext]

/-- The observed endpoint is non-vacuous on every path, before using any
confidence event. -/
theorem persistentBool_empiricalPrequentialRisk_1024_le_nine_sixteenths
    (x : ℕ → Bool) :
    empiricalPrequentialRisk boolObservable boolPredictor 1024 x ≤ 9 / 16 := by
  unfold empiricalPrequentialRisk AnytimeValid.runningMean AnytimeValid.runningSum
  have hsum :
      ∑ i ∈ Finset.range 1024, pathSquaredLoss boolObservable boolPredictor i x ≤
        ∑ _i ∈ Finset.range 1024, (9 / 16 : ℝ) :=
    Finset.sum_le_sum fun i _hi ↦
      persistentBool_pathSquaredLoss_le_nine_sixteenths i x
  calc
    (∑ i ∈ Finset.range 1024, pathSquaredLoss boolObservable boolPredictor i x) /
          (1024 : ℝ) ≤
        (∑ _i ∈ Finset.range 1024, (9 / 16 : ℝ)) / (1024 : ℝ) := by
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    _ = 9 / 16 := by norm_num

/-- Outside the concrete exceptional event, the observed empirical loss lies
in a fully evaluated interval around its exact conditional-risk average. -/
theorem persistentBool_empiricalPrequentialRisk_1024_mem_interval
    (x : ℕ → Bool)
    (hx : x ∉ markovPrequentialRiskExceptionalEvent
      persistentBoolTransition false boolObservable boolPredictor singletonTilt (1 / 20)) :
    empiricalPrequentialRisk boolObservable boolPredictor 1024 x ∈
      Set.Ioo (7 / 80 : ℝ) (23 / 80 : ℝ) := by
  have habs := abs_prequentialRisk_sub_averageConditionalRisk_lt_of_not_mem
    persistentBoolTransition false boolObservable boolPredictor
    (Lam := singletonTilt) (delta := (1 / 20 : ℝ)) (lam := (1 / 8 : ℝ))
    (n := 1024) (x := x) hx (by norm_num) (by simp [singletonTilt])
  have hboundary := singletonTilt_boundary_lt_one_tenth
  have havg := persistentBool_averageConditionalRisk_1024_eq x
  rw [havg] at habs
  rw [Set.mem_Ioo, abs_lt] at *
  constructor <;> linarith

/-- The evaluated empirical-risk upper endpoint remains strictly below one on
every path outside the concrete exceptional event. -/
theorem persistentBool_empirical_upperEndpoint_lt_one
    (x : ℕ → Bool)
    (hx : x ∉ markovPrequentialRiskExceptionalEvent
      persistentBoolTransition false boolObservable boolPredictor singletonTilt (1 / 20)) :
    empiricalPrequentialRisk boolObservable boolPredictor 1024 x + 1 / 10 < 1 := by
  have hinterval := persistentBool_empiricalPrequentialRisk_1024_mem_interval x hx
  rcases hinterval with ⟨_hlower, hupper⟩
  norm_num at hupper ⊢
  linarith

/-- Concrete end-to-end receipt: one measurable event has probability at most
`1/20`; outside it, the latent trajectory-average conditional risk is below
the observed prequential loss plus `1/10` at `n = 1024`.  The exact conditional
risk is `3/16`, the observed loss lies in `(7/80, 23/80)`, and its upper endpoint
remains below one. -/
theorem persistentBool_markovRisk_certificate :
    ∃ E : Set (ℕ → Bool),
      MeasurableSet E ∧
      (markovPathMeasure persistentBoolTransition false).real E ≤ 1 / 20 ∧
      ∀ x ∉ E,
        averageConditionalRisk persistentBoolTransition boolObservable boolPredictor 1024 x =
            3 / 16 ∧
          empiricalPrequentialRisk boolObservable boolPredictor 1024 x ∈
            Set.Ioo (7 / 80 : ℝ) (23 / 80 : ℝ) ∧
          averageConditionalRisk persistentBoolTransition boolObservable boolPredictor 1024 x <
            empiricalPrequentialRisk boolObservable boolPredictor 1024 x + 1 / 10 ∧
          empiricalPrequentialRisk boolObservable boolPredictor 1024 x + 1 / 10 < 1 := by
  let E := markovPrequentialRiskExceptionalEvent
    persistentBoolTransition false boolObservable boolPredictor singletonTilt (1 / 20)
  refine ⟨E, markovPrequentialRiskExceptionalEvent_measurable
    persistentBoolTransition false boolObservable boolPredictor singletonTilt (1 / 20), ?_, ?_⟩
  · have hf : ∀ z, boolObservable z ∈ Set.Icc (0 : ℝ) 1 := by
      intro z
      fin_cases z <;> norm_num [boolObservable]
    have hq : ∀ z, boolPredictor z ∈ Set.Icc (0 : ℝ) 1 := by
      intro z
      fin_cases z <;> norm_num [boolPredictor]
    apply markovPrequentialRiskExceptionalEvent_mass_le_delta
      persistentBoolTransition false hf hq (by norm_num)
    · simp [singletonTilt]
    · intro lam hlam
      simp only [singletonTilt, Finset.mem_singleton] at hlam
      subst lam
      norm_num
  · intro x hx
    have hcert :=
      averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem
        persistentBoolTransition false boolObservable boolPredictor
        (Lam := singletonTilt) (delta := (1 / 20 : ℝ)) (lam := (1 / 8 : ℝ))
        (n := 1024) (x := x) hx (by norm_num) (by simp [singletonTilt])
    have hboundary := singletonTilt_boundary_lt_one_tenth
    refine ⟨persistentBool_averageConditionalRisk_1024_eq x,
      persistentBool_empiricalPrequentialRisk_1024_mem_interval x hx, ?_,
      persistentBool_empirical_upperEndpoint_lt_one x hx⟩
    linarith

#check persistentBool_conditionalSquaredRisk_eq
#check periodEightPath_empiricalPrequentialRisk_eight_eq
#check periodEightPath_empiricalPrequentialRisk_1024_eq
#check singletonTilt_boundary_lt_one_tenth
#check persistentBool_averageConditionalRisk_1024_eq
#check persistentBool_pathSquaredLoss_le_nine_sixteenths
#check persistentBool_empiricalPrequentialRisk_1024_le_nine_sixteenths
#check persistentBool_empiricalPrequentialRisk_1024_mem_interval
#check persistentBool_empirical_upperEndpoint_lt_one
#check persistentBool_markovRisk_certificate

#print axioms persistentBool_conditionalSquaredRisk_eq
#print axioms periodEightPath_empiricalPrequentialRisk_eight_eq
#print axioms periodEightPath_empiricalPrequentialRisk_1024_eq
#print axioms singletonTilt_boundary_lt_one_tenth
#print axioms persistentBool_averageConditionalRisk_1024_eq
#print axioms persistentBool_pathSquaredLoss_le_nine_sixteenths
#print axioms persistentBool_empiricalPrequentialRisk_1024_le_nine_sixteenths
#print axioms persistentBool_empiricalPrequentialRisk_1024_mem_interval
#print axioms persistentBool_empirical_upperEndpoint_lt_one
#print axioms persistentBool_markovRisk_certificate

/-! Complete audit of the public theorem surface introduced by `MarkovRisk`. -/

#check StochasticDynamics.pmfKernel
#check StochasticDynamics.prefixKernel
#check StochasticDynamics.markovPathMeasure
#check StochasticDynamics.transitionSquaredLoss
#check StochasticDynamics.pathSquaredLoss
#check StochasticDynamics.conditionalSquaredRisk
#check StochasticDynamics.markovRiskInnovation
#check StochasticDynamics.empiricalPrequentialRisk
#check StochasticDynamics.averageConditionalRisk
#check StochasticDynamics.markovPrequentialRiskRawFailure
#check StochasticDynamics.markovPrequentialRiskExceptionalEvent

#check StochasticDynamics.measurable_pathSquaredLoss
#check StochasticDynamics.transitionSquaredLoss_mem_Icc
#check StochasticDynamics.integrable_pathSquaredLoss
#check StochasticDynamics.map_traj_next
#check StochasticDynamics.integral_pathSquaredLoss_traj
#check StochasticDynamics.stronglyMeasurable_conditionalSquaredRisk
#check StochasticDynamics.conditionalSquaredRisk_mem_Icc
#check StochasticDynamics.integrable_conditionalSquaredRisk
#check StochasticDynamics.markovRiskInnovation_incrementAdapted
#check StochasticDynamics.measurable_markovRiskInnovation
#check StochasticDynamics.abs_markovRiskInnovation_le_one
#check StochasticDynamics.integrable_markovRiskInnovation
#check StochasticDynamics.markovRiskInnovation_condSecondMoment_le_one
#check StochasticDynamics.runningMean_markovRiskInnovation
#check StochasticDynamics.markovPrequentialRiskRawFailure_mass_le_delta
#check StochasticDynamics.markovPrequentialRiskExceptionalEvent_measurable
#check StochasticDynamics.markovPrequentialRiskRawFailure_subset_exceptionalEvent
#check StochasticDynamics.abs_prequentialRisk_sub_averageConditionalRisk_lt_of_not_mem

#print axioms StochasticDynamics.measurable_pathSquaredLoss
#print axioms StochasticDynamics.transitionSquaredLoss_mem_Icc
#print axioms StochasticDynamics.integrable_pathSquaredLoss
#print axioms StochasticDynamics.map_traj_next
#print axioms StochasticDynamics.integral_pathSquaredLoss_traj
#print axioms StochasticDynamics.stronglyMeasurable_conditionalSquaredRisk
#print axioms StochasticDynamics.conditionalSquaredRisk_mem_Icc
#print axioms StochasticDynamics.integrable_conditionalSquaredRisk
#print axioms StochasticDynamics.markovRiskInnovation_incrementAdapted
#print axioms StochasticDynamics.measurable_markovRiskInnovation
#print axioms StochasticDynamics.abs_markovRiskInnovation_le_one
#print axioms StochasticDynamics.integrable_markovRiskInnovation
#print axioms StochasticDynamics.markovRiskInnovation_condSecondMoment_le_one
#print axioms StochasticDynamics.runningMean_markovRiskInnovation
#print axioms StochasticDynamics.markovPrequentialRiskRawFailure_mass_le_delta
#print axioms StochasticDynamics.markovPrequentialRiskExceptionalEvent_measurable
#print axioms StochasticDynamics.markovPrequentialRiskRawFailure_subset_exceptionalEvent
#print axioms StochasticDynamics.abs_prequentialRisk_sub_averageConditionalRisk_lt_of_not_mem

end

end FormalSLT.Examples.CheckMarkovRisk
