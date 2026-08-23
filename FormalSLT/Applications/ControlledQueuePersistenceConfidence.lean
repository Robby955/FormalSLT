/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueTypedModel
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence

/-!
# Structured persistence confidence for the controlled queue

The generated queue kernels form a one-parameter refresh family.  Conditional
on the current physical state and the newly chosen action, the next state is a
uniform refresh with probability `1 - gamma` and the generated deterministic
queue-step destination with probability `gamma`.

This module estimates the family through one bounded transition statistic:
whether the next state equals that deterministic destination.  Its conditional
mean is the same in every state-action row.  A two-element direct/complement
score catalog therefore gives a time-uniform two-sided confidence sequence for
the scalar hit probability.  For this refresh family, the discrepancy between
two hit probabilities is exactly the total-variation distance between every
corresponding physical transition row.

The true persistence parameter is any real `gamma` in `[0,1)`.  It is not
restricted to the three generated candidates.  Candidate, tilt, and time may
be selected after the common event has been constructed.  This module does not
yet compose the row-TV budget with target-policy OPE or evaluate a frozen path.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

/-- Admissible persistence parameters for the structured queue family. -/
abbrev PersistenceParameter := { gamma : ℝ // gamma ∈ Set.Ico (0 : ℝ) 1 }

/-- Real mass of one destination in the structured refresh family. -/
def refreshEnvironmentMass
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) : ℝ :=
  (1 - (gamma : ℝ)) / 24 +
    if nextState = candidateKernelStepStateAction state action then
      (gamma : ℝ)
    else 0

private theorem refreshEnvironmentMass_pos
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) :
    0 < refreshEnvironmentMass gamma state action nextState := by
  have hbase : 0 < (1 - (gamma : ℝ)) / 24 :=
    div_pos (sub_pos.mpr gamma.property.2) (by norm_num)
  by_cases hstep :
      nextState = candidateKernelStepStateAction state action
  · simp only [refreshEnvironmentMass, hstep, if_pos]
    linarith [gamma.property.1]
  · rw [refreshEnvironmentMass, if_neg hstep, add_zero]
    exact hbase

private theorem refreshEnvironmentMass_sum_one
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action) :
    ∑ nextState : PhysicalState,
      refreshEnvironmentMass gamma state action nextState = 1 := by
  simp_rw [refreshEnvironmentMass]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_ite_eq']
  simp
  ring

/-- Typed environment kernel for an arbitrary persistence parameter. -/
noncomputable def refreshEnvironment
    (gamma : PersistenceParameter) :
    PhysicalState → Action → PMF PhysicalState :=
  fun state action ↦
    PMF.ofFintype
      (fun nextState ↦ ENNReal.ofReal
        (refreshEnvironmentMass gamma state action nextState))
      (by
        rw [← ENNReal.ofReal_one,
          ← refreshEnvironmentMass_sum_one gamma state action]
        exact Eq.symm (ENNReal.ofReal_sum_of_nonneg
          (s := Finset.univ)
          (f := fun nextState ↦
            refreshEnvironmentMass gamma state action nextState)
          (fun nextState _hnextState ↦
            (refreshEnvironmentMass_pos gamma state action nextState).le)))

@[simp]
theorem refreshEnvironment_apply_toReal
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) :
    (refreshEnvironment gamma state action nextState).toReal =
      refreshEnvironmentMass gamma state action nextState := by
  change (ENNReal.ofReal
      (refreshEnvironmentMass gamma state action nextState)).toReal = _
  exact ENNReal.toReal_ofReal
    (refreshEnvironmentMass_pos gamma state action nextState).le

/-- Embed a generated candidate into the parameterized refresh family. -/
def candidatePersistenceParameter
    (candidate : CandidateIndex) : PersistenceParameter :=
  ⟨candidateGamma candidate, by
    fin_cases candidate <;>
      norm_num [candidateGamma, candidateGammaRat,
        ControlledQueueData.candidateGammaTable]⟩

/-- Probability that a refresh-family transition lands on its deterministic
persistence destination. -/
def persistenceHitProbability (gamma : PersistenceParameter) : ℝ :=
  (1 + 23 * (gamma : ℝ)) / 24

/-- Persistence-hit probability of one generated candidate. -/
def candidatePersistenceHitProbability (candidate : CandidateIndex) : ℝ :=
  persistenceHitProbability (candidatePersistenceParameter candidate)

private theorem candidateEnvironment_apply_toReal_refresh
    (candidate : CandidateIndex) (state : PhysicalState) (action : Action)
    (nextState : PhysicalState) :
    (candidateEnvironment candidate state action nextState).toReal =
      (1 - candidateGamma candidate) / 24 +
        if nextState = candidateKernelStepStateAction state action then
          candidateGamma candidate
        else 0 := by
  rw [candidateEnvironment_apply_toReal,
    candidateKernelTableMass_eq_refreshMixture,
    candidateKernelStep_stateActionRowEquiv]
  by_cases hstep :
      nextState = candidateKernelStepStateAction state action
  · simp [hstep, candidateGamma]
  · simp [hstep, candidateGamma]

/-- The generated candidate PMFs are exactly the corresponding members of the
parameterized refresh family. -/
theorem candidateEnvironment_eq_refreshEnvironment
    (candidate : CandidateIndex) :
    candidateEnvironment candidate =
      refreshEnvironment (candidatePersistenceParameter candidate) := by
  funext state action
  apply PMF.ext
  intro nextState
  apply (ENNReal.toReal_eq_toReal_iff'
    ((candidateEnvironment candidate state action).apply_ne_top nextState)
    ((refreshEnvironment (candidatePersistenceParameter candidate)
      state action).apply_ne_top nextState)).mp
  rw [candidateEnvironment_apply_toReal_refresh,
    refreshEnvironment_apply_toReal]
  rfl

/-- Indicator that a controlled transition lands at the deterministic
destination associated with its current physical state and newly chosen
action. -/
def persistenceDestinationHitScore : MarkovTransitionScore Observation :=
  fun current next ↦
    if next.2 = candidateKernelStepStateAction current.2 next.1 then 1 else 0

/-- Direct persistence-hit score (`false`) or its complement (`true`). -/
def orientedPersistenceHitMarkovScore
    (complement : Bool) : MarkovTransitionScore Observation :=
  if complement then
    fun current next ↦ 1 - persistenceDestinationHitScore current next
  else persistenceDestinationHitScore

/-- Direct persistence-hit score or complement in the trajectory API. -/
def orientedPersistenceHitScore
    (complement : Bool) : TrajectoryScore Observation :=
  markovTransitionTrajectoryScore
    (orientedPersistenceHitMarkovScore complement)

theorem orientedPersistenceHitScore_mem_Icc
    (complement : Bool) (n : ℕ)
    (u : (i : Finset.Iic n) → Observation) (next : Observation) :
    orientedPersistenceHitScore complement n u next ∈
      Set.Icc (0 : ℝ) 1 := by
  cases complement <;>
    by_cases hhit : next.2 = candidateKernelStepStateAction
      (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 next.1 <;>
    simp [orientedPersistenceHitScore, markovTransitionTrajectoryScore,
      orientedPersistenceHitMarkovScore, persistenceDestinationHitScore, hhit]

private theorem refreshEnvironment_step_apply_toReal
    (gamma : PersistenceParameter) (state : PhysicalState) (action : Action) :
    (refreshEnvironment gamma state action
      (candidateKernelStepStateAction state action)).toReal =
      persistenceHitProbability gamma := by
  rw [refreshEnvironment_apply_toReal]
  simp only [refreshEnvironmentMass, if_pos]
  unfold persistenceHitProbability
  ring

/-- The persistence-hit score has the same conditional mean in every
augmented behavior row. -/
theorem persistenceDestinationHit_rowRisk
    (gamma : PersistenceParameter) (current : Observation) :
    markovRowRisk
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy)
        persistenceDestinationHitScore current =
      persistenceHitProbability gamma := by
  classical
  unfold markovRowRisk
  rw [PMF.integral_eq_sum, Fintype.sum_prod_type]
  simp only [smul_eq_mul, persistenceDestinationHitScore,
    augmentedBehaviorKernel_apply, ENNReal.toReal_mul]
  have hinner : ∀ action : Action,
      (∑ nextState : PhysicalState,
        (behaviorPolicy current.2 action).toReal *
          (refreshEnvironment gamma current.2 action nextState).toReal *
            (if nextState =
                candidateKernelStepStateAction current.2 action then
              (1 : ℝ)
            else 0)) =
        (behaviorPolicy current.2 action).toReal *
          persistenceHitProbability gamma := by
    intro action
    rw [Finset.sum_eq_single
      (candidateKernelStepStateAction current.2 action)]
    · rw [refreshEnvironment_step_apply_toReal]
      simp
    · intro nextState _hnextState hne
      simp [hne]
    · simp
  simp_rw [hinner]
  rw [← Finset.sum_mul, finitePMF_real_mass_sum, one_mul]

private theorem orientedPersistenceHit_rowRisk_direct
    (gamma : PersistenceParameter) (current : Observation) :
    markovRowRisk
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy)
        (orientedPersistenceHitMarkovScore false) current =
      persistenceHitProbability gamma := by
  simpa [orientedPersistenceHitMarkovScore] using
    persistenceDestinationHit_rowRisk gamma current

private theorem orientedPersistenceHit_rowRisk_complement
    (gamma : PersistenceParameter) (current : Observation) :
    markovRowRisk
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy)
        (orientedPersistenceHitMarkovScore true) current =
      1 - persistenceHitProbability gamma := by
  classical
  unfold markovRowRisk orientedPersistenceHitMarkovScore
  simp only [if_true, PMF.integral_eq_sum, smul_eq_mul, mul_sub, mul_one,
    Finset.sum_sub_distrib, finitePMF_real_mass_sum]
  rw [show
      (∑ next : Observation,
        ((augmentedBehaviorKernel
          (refreshEnvironment gamma) behaviorPolicy current) next).toReal *
            persistenceDestinationHitScore current next) =
          persistenceHitProbability gamma by
        simpa only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul] using
          persistenceDestinationHit_rowRisk gamma current]

/-- Observed fraction of transitions that land on their deterministic
persistence destination. -/
def empiricalPersistenceHitRate
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  trajectoryEmpiricalPrequentialRisk
    (orientedPersistenceHitScore false) n path

private theorem empiricalPersistenceHitRate_complement
    {n : ℕ} (hn : 0 < n) (path : ℕ → Observation) :
    trajectoryEmpiricalPrequentialRisk
        (orientedPersistenceHitScore true) n path =
      1 - empiricalPersistenceHitRate n path := by
  change forwardPrefixMean
      (fun k ↦ 1 - observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) n = _
  rw [forwardPrefixMean_one_sub _ hn]
  rfl

private theorem averageConditionalPersistenceHit_direct
    (gamma : PersistenceParameter) {n : ℕ} (hn : 0 < n)
    (path : ℕ → Observation) :
    trajectoryAverageConditionalRisk
        (prefixKernel
          (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
        (orientedPersistenceHitScore false) n path =
      persistenceHitProbability gamma := by
  have hcond : ∀ k : ℕ,
      conditionalTrajectoryRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore false) k path =
        persistenceHitProbability gamma := by
    intro k
    unfold orientedPersistenceHitScore
    rw [conditionalTrajectoryRisk_markovTransitionTrajectoryScore]
    exact orientedPersistenceHit_rowRisk_direct gamma (path k)
  unfold trajectoryAverageConditionalRisk runningMean runningSum
  simp_rw [hcond]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnreal]

private theorem averageConditionalPersistenceHit_complement
    (gamma : PersistenceParameter) {n : ℕ} (hn : 0 < n)
    (path : ℕ → Observation) :
    trajectoryAverageConditionalRisk
        (prefixKernel
          (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
        (orientedPersistenceHitScore true) n path =
      1 - persistenceHitProbability gamma := by
  have hcond : ∀ k : ℕ,
      conditionalTrajectoryRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore true) k path =
        1 - persistenceHitProbability gamma := by
    intro k
    unfold orientedPersistenceHitScore
    rw [conditionalTrajectoryRisk_markovTransitionTrajectoryScore]
    exact orientedPersistenceHit_rowRisk_complement gamma (path k)
  unfold trajectoryAverageConditionalRisk runningMean runningSum
  simp_rw [hcond]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnreal]

/-- Dirac empirical-Bernstein boundary for one orientation of the persistence
hit statistic. -/
def persistenceHitBoundary
    {τ : Type*} [Fintype τ]
    (weight : τ → ℝ) (lam : τ → ℝ)
    (complement : Bool) (delta : ℝ) (j : τ)
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  trajectoryEmpiricalBernsteinPACBayesBoundary
    (finiteUniformRealPMF Bool) weight lam orientedPersistenceHitScore
    (diracPosterior complement) delta j n path

/-- Two-sided scalar persistence-hit radius. -/
def persistenceHitRadius
    {τ : Type*} [Fintype τ]
    (weight : τ → ℝ) (lam : τ → ℝ)
    (delta : ℝ) (j : τ) (n : ℕ) (path : ℕ → Observation) : ℝ :=
  max
    (persistenceHitBoundary weight lam false delta j n path)
    (persistenceHitBoundary weight lam true delta j n path)

/-- One scalar, time-uniform event controls the persistence-hit probability at
every declared tilt and time.  The exact row-TV theorem below transfers that
control to the structured refresh family. -/
theorem exists_persistenceHitConfidence_event
    {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (gamma : PersistenceParameter) (initial : Observation)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ delta ∧
      ∀ path ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
        |persistenceHitProbability gamma -
            empiricalPersistenceHitRate n path| <
          persistenceHitRadius weight lam delta j n path := by
  rcases exists_trajectoryEmpiricalBernsteinPACBayes_event
      (ι := Bool) (τ := τ)
      (prefixKernel
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
      initial (score := orientedPersistenceHitScore)
      orientedPersistenceHitScore_mem_Icc
      (finiteUniformRealPMF_isFullSupport Bool)
      hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · rw [controlledTrajectoryMeasure_markovBehaviorPolicy,
      ← trajectoryMeasure_prefixKernel_eq_markovPathMeasure]
    exact hmass
  · intro path hpath j n hn
    have hnpos : 0 < n := by omega
    have hdirect := hgood path hpath j
      (diracPosterior false) (diracPosterior_isPMF false) n hn
    have hcomplement := hgood path hpath j
      (diracPosterior true) (diracPosterior_isPMF true) n hn
    unfold trajectoryPosteriorAverageConditionalRisk
      trajectoryPosteriorEmpiricalPrequentialRisk at hdirect hcomplement
    rw [pacBayesPosteriorAverage_dirac,
      pacBayesPosteriorAverage_dirac] at hdirect hcomplement
    change
      trajectoryAverageConditionalRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore false) n path <
        trajectoryEmpiricalPrequentialRisk
            (orientedPersistenceHitScore false) n path +
          persistenceHitBoundary weight lam false delta j n path at hdirect
    change
      trajectoryAverageConditionalRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore true) n path <
        trajectoryEmpiricalPrequentialRisk
            (orientedPersistenceHitScore true) n path +
          persistenceHitBoundary weight lam true delta j n path at hcomplement
    rw [averageConditionalPersistenceHit_direct gamma hnpos] at hdirect
    change
      persistenceHitProbability gamma <
        empiricalPersistenceHitRate n path +
          persistenceHitBoundary weight lam false delta j n path at hdirect
    rw [averageConditionalPersistenceHit_complement gamma hnpos,
      empiricalPersistenceHitRate_complement hnpos] at hcomplement
    rw [abs_lt]
    constructor
    · calc
        -persistenceHitRadius weight lam delta j n path ≤
            -persistenceHitBoundary weight lam true delta j n path := by
          exact neg_le_neg (le_max_right _ _)
        _ < persistenceHitProbability gamma -
            empiricalPersistenceHitRate n path := by
          linarith
    · have hmax :
          persistenceHitBoundary weight lam false delta j n path ≤
            persistenceHitRadius weight lam delta j n path := by
        simpa only [persistenceHitRadius] using le_max_left
          (persistenceHitBoundary weight lam false delta j n path)
          (persistenceHitBoundary weight lam true delta j n path)
      linarith

/-- Exact row-TV distance from any structured true environment to a generated
candidate. -/
theorem refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy
    (gamma : PersistenceParameter) (candidate : CandidateIndex)
    (state : PhysicalState) (action : Action) :
    finitePMFTotalVariation
        (refreshEnvironment gamma state action)
        (candidateEnvironment candidate state action) =
      |persistenceHitProbability gamma -
        candidatePersistenceHitProbability candidate| := by
  classical
  let step := candidateKernelStepStateAction state action
  have hpoint : ∀ nextState : PhysicalState,
      |(refreshEnvironment gamma state action nextState).toReal -
          (candidateEnvironment candidate state action nextState).toReal| =
        (1 / 24 : ℝ) * |(gamma : ℝ) - candidateGamma candidate| +
          if nextState = step then
            (22 / 24 : ℝ) * |(gamma : ℝ) - candidateGamma candidate|
          else 0 := by
    intro nextState
    rw [refreshEnvironment_apply_toReal,
      candidateEnvironment_apply_toReal_refresh]
    change
      |((1 - (gamma : ℝ)) / 24 +
          if nextState = step then (gamma : ℝ) else 0) -
        ((1 - candidateGamma candidate) / 24 +
          if nextState = step then candidateGamma candidate else 0)| = _
    by_cases hstep : nextState = step
    · simp only [hstep, if_pos]
      rw [show
          (1 - (gamma : ℝ)) / 24 + (gamma : ℝ) -
              ((1 - candidateGamma candidate) / 24 +
                candidateGamma candidate) =
            (23 / 24 : ℝ) *
              ((gamma : ℝ) - candidateGamma candidate) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 24)]
      ring
    · simp only [hstep, ↓reduceIte, add_zero]
      rw [show
          (1 - (gamma : ℝ)) / 24 -
              (1 - candidateGamma candidate) / 24 =
            (-1 / 24 : ℝ) *
              ((gamma : ℝ) - candidateGamma candidate) by ring]
      rw [abs_mul]
      norm_num
  unfold finitePMFTotalVariation
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold candidatePersistenceHitProbability candidatePersistenceParameter
    persistenceHitProbability
  rw [show
      (1 + 23 * (gamma : ℝ)) / 24 -
          (1 + 23 * candidateGamma candidate) / 24 =
        (23 / 24 : ℝ) *
          ((gamma : ℝ) - candidateGamma candidate) by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 24)]
  ring

/-- Candidate discrepancy plus the simultaneous scalar confidence radius. -/
def structuredCandidateTVBudget
    {τ : Type*} [Fintype τ]
    (candidate : CandidateIndex) (weight : τ → ℝ) (lam : τ → ℝ)
    (delta : ℝ) (j : τ) (n : ℕ) (path : ℕ → Observation) : ℝ :=
  |candidatePersistenceHitProbability candidate -
      empiricalPersistenceHitRate n path| +
    persistenceHitRadius weight lam delta j n path

/-- On the scalar confidence event, every generated candidate receives a
simultaneous physical-row TV budget.  No action-probability factor is needed. -/
theorem exists_structuredCandidateTVConfidence_event
    {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (gamma : PersistenceParameter) (initial : Observation)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ delta ∧
      ∀ path ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
        ∀ candidate : CandidateIndex,
          ∀ state : PhysicalState, ∀ action : Action,
            finitePMFTotalVariation
                (refreshEnvironment gamma state action)
                (candidateEnvironment candidate state action) <
              structuredCandidateTVBudget
                candidate weight lam delta j n path := by
  rcases exists_persistenceHitConfidence_event
      gamma initial hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro path hpath j n hn candidate state action
  rw [refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy]
  unfold structuredCandidateTVBudget
  calc
    |persistenceHitProbability gamma -
        candidatePersistenceHitProbability candidate| =
      |candidatePersistenceHitProbability candidate -
        persistenceHitProbability gamma| := abs_sub_comm _ _
    _ ≤
      |candidatePersistenceHitProbability candidate -
          empiricalPersistenceHitRate n path| +
        |persistenceHitProbability gamma -
          empiricalPersistenceHitRate n path| := by
      have htriangle := abs_sub_le
        (candidatePersistenceHitProbability candidate)
        (empiricalPersistenceHitRate n path)
        (persistenceHitProbability gamma)
      simpa only [abs_sub_comm
        (empiricalPersistenceHitRate n path)
        (persistenceHitProbability gamma)] using htriangle
    _ < |candidatePersistenceHitProbability candidate -
          empiricalPersistenceHitRate n path| +
        persistenceHitRadius weight lam delta j n path := by
      gcongr
      exact hgood path hpath j n hn

end

end FormalSLT.Applications.ControlledQueue
