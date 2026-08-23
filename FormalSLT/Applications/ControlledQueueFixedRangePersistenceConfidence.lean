/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueuePersistenceConfidence
import FormalSLT.StochasticDynamics.TrajectoryPACBayes

/-!
# Fixed-range persistence confidence for the controlled queue

This module gives the non-variance-adaptive comparator for the structured
persistence-hit statistic.  It is separate from
`ControlledQueuePersistenceConfidence` so the prospectively frozen source
used by the primary structured-OPE protocol remains byte-for-byte unchanged.

The score catalog and estimand match the empirical-Bernstein route.  Only the
stochastic correction is replaced by the fixed-range PAC--Bayes correction.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge
open FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

private theorem fixedRange_orientedPersistenceHit_rowRisk_direct
    (gamma : PersistenceParameter) (current : Observation) :
    markovRowRisk
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy)
        (orientedPersistenceHitMarkovScore false) current =
      persistenceHitProbability gamma := by
  simpa [orientedPersistenceHitMarkovScore] using
    persistenceDestinationHit_rowRisk gamma current

private theorem fixedRange_orientedPersistenceHit_rowRisk_complement
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

private theorem fixedRange_empiricalPersistenceHitRate_complement
    {n : ℕ} (hn : 0 < n) (path : ℕ → Observation) :
    trajectoryEmpiricalPrequentialRisk
        (orientedPersistenceHitScore true) n path =
      1 - empiricalPersistenceHitRate n path := by
  change forwardPrefixMean
      (fun k ↦ 1 - observedTrajectoryScore
        (orientedPersistenceHitScore false) k path) n = _
  rw [forwardPrefixMean_one_sub _ hn]
  rfl

private theorem fixedRange_averageConditionalPersistenceHit_direct
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
    exact fixedRange_orientedPersistenceHit_rowRisk_direct gamma (path k)
  unfold trajectoryAverageConditionalRisk runningMean runningSum
  simp_rw [hcond]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnreal]

private theorem fixedRange_averageConditionalPersistenceHit_complement
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
    exact fixedRange_orientedPersistenceHit_rowRisk_complement gamma (path k)
  unfold trajectoryAverageConditionalRisk runningMean runningSum
  simp_rw [hcond]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnreal]

/-- Fixed-range PAC--Bayes correction for one orientation of the persistence
hit statistic.  Unlike `persistenceHitBoundary`, it contains no empirical
variance statistic. -/
def fixedRangePersistenceHitBoundary
    {τ : Type*} [Fintype τ]
    (weight : τ → ℝ) (lam : τ → ℝ)
    (complement : Bool) (delta : ℝ) (j : τ) (n : ℕ) : ℝ :=
  lam j / (8 * (1 - lam j / 3)) +
    (klDiv (diracPosterior complement) (finiteUniformRealPMF Bool) +
      Real.log (1 / (delta * weight j))) / ((n : ℝ) * lam j)

/-- Two-sided fixed-range persistence-hit radius. -/
def fixedRangePersistenceHitRadius
    {τ : Type*} [Fintype τ]
    (weight : τ → ℝ) (lam : τ → ℝ)
    (delta : ℝ) (j : τ) (n : ℕ) : ℝ :=
  max
    (fixedRangePersistenceHitBoundary weight lam false delta j n)
    (fixedRangePersistenceHitBoundary weight lam true delta j n)

/-- For a fixed true refresh parameter and initial observation, one scalar,
time-uniform fixed-range event controls the persistence-hit probability at
every declared tilt and positive time.  This is the non-variance-adaptive
comparator to `exists_persistenceHitConfidence_event`; the score catalog and
estimand are unchanged. -/
theorem exists_fixedRangePersistenceHitConfidence_event
    {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (gamma : PersistenceParameter) (initial : Observation)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ delta ∧
      ∀ path ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 0 < n →
        |persistenceHitProbability gamma -
            empiricalPersistenceHitRate n path| <
          fixedRangePersistenceHitRadius weight lam delta j n := by
  rcases trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
      (ι := Bool) (τ := τ)
      (prefixKernel
        (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
      initial (score := orientedPersistenceHitScore)
      orientedPersistenceHitScore_mem_Icc
      (finiteUniformRealPMF_isFullSupport Bool)
      hweight hdelta hlam hlam_three with
    ⟨exceptionalEvent, _hmeasurable, hmass, hgood⟩
  refine ⟨exceptionalEventᶜ, ?_, ?_⟩
  · rw [show (exceptionalEventᶜ)ᶜ = exceptionalEvent by simp,
      controlledTrajectoryMeasure_markovBehaviorPolicy,
      ← trajectoryMeasure_prefixKernel_eq_markovPathMeasure]
    exact hmass
  · intro path hpath j n hn
    have hdirect := hgood path (by simpa using hpath) j
      (diracPosterior false) (diracPosterior_isPMF false) n hn
    have hcomplement := hgood path (by simpa using hpath) j
      (diracPosterior true) (diracPosterior_isPMF true) n hn
    unfold trajectoryPosteriorAverageConditionalRisk
      trajectoryPosteriorEmpiricalPrequentialRisk at hdirect hcomplement
    rw [pacBayesPosteriorAverage_dirac,
      pacBayesPosteriorAverage_dirac] at hdirect hcomplement
    have hdirect' :
      trajectoryAverageConditionalRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore false) n path <
        trajectoryEmpiricalPrequentialRisk
            (orientedPersistenceHitScore false) n path +
          fixedRangePersistenceHitBoundary weight lam false delta j n := by
      simpa only [fixedRangePersistenceHitBoundary, add_assoc] using hdirect
    have hcomplement' :
      trajectoryAverageConditionalRisk
          (prefixKernel
            (augmentedBehaviorKernel (refreshEnvironment gamma) behaviorPolicy))
          (orientedPersistenceHitScore true) n path <
        trajectoryEmpiricalPrequentialRisk
            (orientedPersistenceHitScore true) n path +
          fixedRangePersistenceHitBoundary weight lam true delta j n := by
      simpa only [fixedRangePersistenceHitBoundary, add_assoc] using hcomplement
    rw [fixedRange_averageConditionalPersistenceHit_direct gamma hn] at hdirect'
    change
      persistenceHitProbability gamma <
        empiricalPersistenceHitRate n path +
          fixedRangePersistenceHitBoundary weight lam false delta j n
        at hdirect'
    rw [fixedRange_averageConditionalPersistenceHit_complement gamma hn,
      fixedRange_empiricalPersistenceHitRate_complement hn] at hcomplement'
    rw [abs_lt]
    constructor
    · calc
        -fixedRangePersistenceHitRadius weight lam delta j n ≤
            -fixedRangePersistenceHitBoundary weight lam true delta j n := by
          exact neg_le_neg (le_max_right _ _)
        _ < persistenceHitProbability gamma -
            empiricalPersistenceHitRate n path := by
          linarith
    · have hmax :
          fixedRangePersistenceHitBoundary weight lam false delta j n ≤
            fixedRangePersistenceHitRadius weight lam delta j n := by
        simpa only [fixedRangePersistenceHitRadius] using le_max_left
          (fixedRangePersistenceHitBoundary weight lam false delta j n)
          (fixedRangePersistenceHitBoundary weight lam true delta j n)
      linarith

end

end FormalSLT.Applications.ControlledQueue
