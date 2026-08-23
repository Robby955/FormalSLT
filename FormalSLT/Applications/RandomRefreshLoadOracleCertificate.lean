/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadCertificate

/-!
# Two-sided oracle certificate for the random-refresh load model

This module enlarges the four-predictor Brier catalog by one orientation bit.
The normal orientation is the original loss and the flipped orientation is
`1 - loss`.  A single empirical stationary-catalog event is simultaneous over
all eight oriented scores.  Consequently it supplies both an upper bound for
the path-selected empirical-risk minimizer and a matched lower bound for every
declared comparator.

Combining those inequalities with empirical-risk minimality gives an oracle
inequality against every predictor in the fixed catalog, and in particular
against the exact nominal catalog minimum `3/20`.  The event is all-time and
its complement has real outer mass at most `1/20`.  The construction is
independent of the deterministic path and matched-baseline modules; in
particular it makes no named-path event-membership claim.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadOracleCertificate

open RandomRefreshLoadModel

noncomputable section

/-- A predictor together with a normal (`false`) or flipped (`true`) loss
orientation. -/
abbrev OrientedPredictor := Predictor × Bool

/-- The original Brier loss and its affine flip share one finite catalog. -/
def orientedBrierScore (a : OrientedPredictor) : MarkovTransitionScore State :=
  if a.2 then
    fun z y ↦ 1 - brierScore a.1 z y
  else
    brierScore a.1

/-- Uniform prior over the eight oriented predictor atoms. -/
def orientedPredictorPrior : OrientedPredictor → ℝ :=
  finiteUniformRealPMF OrientedPredictor

/-- The single two-sided risk-event budget. -/
def oracleRiskFailureBudget : ℝ := 1 / 20

/-- Point posterior at a predictor and orientation. -/
def orientedPosterior (i : Predictor) (flipped : Bool) :
    OrientedPredictor → ℝ :=
  diracPosterior (i, flipped)

theorem orientedPredictorPrior_isFullSupport :
    IsFullSupportPMF orientedPredictorPrior := by
  exact finiteUniformRealPMF_isFullSupport OrientedPredictor

theorem oracleRiskFailureBudget_pos : 0 < oracleRiskFailureBudget := by
  norm_num [oracleRiskFailureBudget]

theorem orientedPosterior_isPMF (i : Predictor) (flipped : Bool) :
    IsPMF (orientedPosterior i flipped) := by
  exact diracPosterior_isPMF (i, flipped)

/-- Both orientations remain in the unit interval. -/
theorem orientedBrierScore_mem_Icc :
    ∀ a z y, orientedBrierScore a z y ∈ Set.Icc (0 : ℝ) 1 := by
  intro a z y
  rcases a with ⟨i, flipped⟩
  cases flipped
  · simpa [orientedBrierScore] using brierScore_mem_Icc i z y
  · have h := brierScore_mem_Icc i z y
    change 1 - brierScore i z y ∈ Set.Icc (0 : ℝ) 1
    simp only [Set.mem_Icc] at h ⊢
    constructor <;> linarith

/-! ## Affine-flip identities -/

/-- Complementing a unit loss complements its one-step Markov row risk. -/
theorem markovRowRisk_one_sub
    (P : State → PMF State) (score : MarkovTransitionScore State)
    (z : State) :
    markovRowRisk P (fun x y ↦ 1 - score x y) z =
      1 - markovRowRisk P score z := by
  unfold markovRowRisk
  simp only [PMF.integral_eq_sum, smul_eq_mul, mul_sub, mul_one,
    Finset.sum_sub_distrib, finitePMF_real_mass_sum]

/-- Complementing a unit loss complements its stationary Markov risk. -/
theorem stationaryMarkovRisk_one_sub
    (P : State → PMF State) (stationary : PMF State)
    (score : MarkovTransitionScore State) :
    stationaryMarkovRisk P stationary (fun x y ↦ 1 - score x y) =
      1 - stationaryMarkovRisk P stationary score := by
  unfold stationaryMarkovRisk
  simp_rw [markovRowRisk_one_sub]
  simp only [PMF.integral_eq_sum, smul_eq_mul, mul_sub, mul_one,
    Finset.sum_sub_distrib, finitePMF_real_mass_sum]

/-- At a positive horizon, complementing every observed loss complements its
empirical transition risk. -/
theorem empiricalTransitionRisk_one_sub
    (score : MarkovTransitionScore State) (x : ℕ → State)
    {n : ℕ} (hn : 0 < n) :
    empiricalTransitionRisk (fun z y ↦ 1 - score z y) n x =
      1 - empiricalTransitionRisk score n x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold empiricalTransitionRisk runningMean runningSum
  rw [show
      (∑ k ∈ Finset.range n, (1 - score (x k) (x (k + 1)))) =
        (n : ℝ) -
          ∑ k ∈ Finset.range n, score (x k) (x (k + 1)) by
    rw [Finset.sum_sub_distrib]
    simp]
  field_simp [hn0]

/-- Flipping the score negates its centered row-risk function. -/
theorem centeredMarkovRowRisk_one_sub
    (P : State → PMF State) (stationary : PMF State)
    (score : MarkovTransitionScore State) (z : State) :
    centeredMarkovRowRisk P stationary (fun x y ↦ 1 - score x y) z =
      -centeredMarkovRowRisk P stationary score z := by
  unfold centeredMarkovRowRisk
  rw [markovRowRisk_one_sub, stationaryMarkovRisk_one_sub]
  ring

/-- The declared candidate-specific oscillation envelope is unchanged by the
orientation bit. -/
theorem orientedBrierScore_centeredOscillation_le
    (c : Candidate) (a : OrientedPredictor) :
    finiteOscillation
        (centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
          (orientedBrierScore a)) ≤ candidateOscillation c := by
  rcases a with ⟨i, flipped⟩
  cases flipped
  · simpa [orientedBrierScore, candidateReference] using
      (show finiteOscillation
          (centeredMarkovRowRisk (refreshKernel c) uniformLaw
            (brierScore i)) ≤ candidateOscillation c from
        brierScore_centeredOscillation_le c i)
  · apply finiteOscillation_le
    intro x y
    change
      |centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
            (fun z y ↦ 1 - brierScore i z y) y -
          centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
            (fun z y ↦ 1 - brierScore i z y) x| ≤
        candidateOscillation c
    rw [centeredMarkovRowRisk_one_sub, centeredMarkovRowRisk_one_sub]
    calc
      |-centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
            (brierScore i) y -
          -centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
            (brierScore i) x| =
          |centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
              (brierScore i) y -
            centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
              (brierScore i) x| := by
                rw [show
                  -centeredMarkovRowRisk (refreshKernel c)
                        (candidateReference c) (brierScore i) y -
                      -centeredMarkovRowRisk (refreshKernel c)
                        (candidateReference c) (brierScore i) x =
                    -(centeredMarkovRowRisk (refreshKernel c)
                          (candidateReference c) (brierScore i) y -
                        centeredMarkovRowRisk (refreshKernel c)
                          (candidateReference c) (brierScore i) x) by ring,
                  abs_neg]
      _ ≤ finiteOscillation
          (centeredMarkovRowRisk (refreshKernel c) (candidateReference c)
            (brierScore i)) :=
        abs_sub_le_finiteOscillation _ _ _
      _ ≤ candidateOscillation c :=
        (by simpa [candidateReference] using
          brierScore_centeredOscillation_le c i)

/-! ## A finite empirical-risk selector -/

/-- Empirical transition risk of one declared predictor. -/
def empiricalPredictorRisk (x : ℕ → State) (n : ℕ)
    (i : Predictor) : ℝ :=
  empiricalTransitionRisk (brierScore i) n x

private theorem selectedPredictor_exists (x : ℕ → State) (n : ℕ) :
    ∃ i ∈ (Finset.univ : Finset Predictor),
      ∀ j ∈ (Finset.univ : Finset Predictor),
        empiricalPredictorRisk x n i ≤ empiricalPredictorRisk x n j := by
  exact (Finset.univ : Finset Predictor).exists_min_image
    (empiricalPredictorRisk x n) Finset.univ_nonempty

/-- A deterministic finite-catalog empirical-risk minimizer. -/
def oracleSelectedPredictor (x : ℕ → State) (n : ℕ) : Predictor :=
  Classical.choose (selectedPredictor_exists x n)

/-- The selected predictor has no larger empirical risk than any declared
comparator. -/
theorem oracleSelectedPredictor_empiricalRisk_minimal
    (x : ℕ → State) (n : ℕ) (i : Predictor) :
    empiricalPredictorRisk x n (oracleSelectedPredictor x n) ≤
      empiricalPredictorRisk x n i := by
  exact (Classical.choose_spec (selectedPredictor_exists x n)).2
    i (Finset.mem_univ i)

/-! ## Point-posterior translations -/

theorem orientedNormal_stationaryPosteriorRisk (i : Predictor) :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw orientedBrierScore
        (orientedPosterior i false) =
      stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) := by
  unfold stationaryPosteriorMarkovRisk orientedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  rfl

theorem orientedFlipped_stationaryPosteriorRisk (i : Predictor) :
    stationaryPosteriorMarkovRisk
        (refreshKernel Candidate.nominal) uniformLaw orientedBrierScore
        (orientedPosterior i true) =
      1 - stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) := by
  unfold stationaryPosteriorMarkovRisk orientedPosterior
  rw [pacBayesPosteriorAverage_dirac]
  exact stationaryMarkovRisk_one_sub _ _ _

theorem orientedNormal_empiricalPosteriorRisk
    (i : Predictor) (x : ℕ → State) (n : ℕ) :
    empiricalTransitionPosteriorRisk orientedBrierScore
        (orientedPosterior i false) n x = empiricalPredictorRisk x n i := by
  unfold empiricalTransitionPosteriorRisk orientedPosterior
    empiricalPredictorRisk
  rw [pacBayesPosteriorAverage_dirac]
  rfl

theorem orientedFlipped_empiricalPosteriorRisk
    (i : Predictor) (x : ℕ → State) {n : ℕ} (hn : 0 < n) :
    empiricalTransitionPosteriorRisk orientedBrierScore
        (orientedPosterior i true) n x = 1 - empiricalPredictorRisk x n i := by
  unfold empiricalTransitionPosteriorRisk orientedPosterior
    empiricalPredictorRisk
  rw [pacBayesPosteriorAverage_dirac]
  exact empiricalTransitionRisk_one_sub (brierScore i) x hn

/-! ## Explicit upper, lower, and oracle penalties -/

/-- Known-kernel upper-bound width at the path-selected predictor. -/
def selectedUpperBoundary (x : ℕ → State) (n : ℕ) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    orientedBrierScore candidateOscillation candidateWeight
    orientedPredictorPrior
    (orientedPosterior (oracleSelectedPredictor x n) false)
    oracleRiskFailureBudget 0 Candidate.nominal 5 5 n x

/-- Known-kernel flipped-score width for one fixed comparator. -/
def predictorLowerBoundary (x : ℕ → State) (n : ℕ)
    (i : Predictor) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    orientedBrierScore candidateOscillation candidateWeight
    orientedPredictorPrior (orientedPosterior i true)
    oracleRiskFailureBudget 0 Candidate.nominal 5 5 n x

/-- Observable lower endpoint for one fixed comparator. -/
def predictorLowerConfidenceEndpoint (x : ℕ → State) (n : ℕ)
    (i : Predictor) : ℝ :=
  empiricalPredictorRisk x n i - predictorLowerBoundary x n i

/-- Two-sided penalty in the oracle comparison with the exact nominal oracle. -/
def selectedOraclePenalty (x : ℕ → State) (n : ℕ) : ℝ :=
  selectedUpperBoundary x n +
    predictorLowerBoundary x n Predictor.oracle

/-- Exact minimum stationary risk in the declared nominal predictor catalog. -/
def catalogMinimumStationaryRisk : ℝ := 3 / 20

theorem oracle_stationaryRisk_eq_catalogMinimum :
    stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore Predictor.oracle) = catalogMinimumStationaryRisk := by
  rw [nominal_stationaryRisk]
  rfl

/-- The oracle realizes the minimum nominal stationary risk among all four
declared predictors. -/
theorem catalogMinimumStationaryRisk_le (i : Predictor) :
    catalogMinimumStationaryRisk ≤
      stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) := by
  rw [candidate_stationaryRisk Candidate.nominal i]
  fin_cases i <;>
    norm_num [catalogMinimumStationaryRisk, candidateStationaryRiskValue]

/-! ## One simultaneous two-sided event -/

/-- The single oriented-catalog exceptional event. -/
def twoSidedOracleExceptionalEvent : Set (ℕ → State) :=
  empiricalStationaryCatalogExceptionalEvent
    (refreshKernel Candidate.nominal) refreshKernel candidateReference
    orientedBrierScore candidateOscillation candidateWeight
    orientedPredictorPrior oracleRiskFailureBudget

theorem twoSidedOracleExceptionalEvent_mass_le :
    (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
        twoSidedOracleExceptionalEvent ≤ 1 / 20 := by
  simpa [twoSidedOracleExceptionalEvent, oracleRiskFailureBudget] using
    empiricalStationaryCatalogExceptionalEvent_mass_le
      (refreshKernel Candidate.nominal) (0 : State)
      refreshKernel candidateReference orientedBrierScore_mem_Icc
      candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
      orientedBrierScore_centeredOscillation_le
      candidateWeight_isFullSupport orientedPredictorPrior_isFullSupport
      oracleRiskFailureBudget_pos

/-- Event contract with the path/time binders outside every comparator. -/
def IsTwoSidedOracleEvent (goodEvent : Set (ℕ → State)) : Prop :=
  ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
    stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
          (brierScore (oracleSelectedPredictor x n)) <
        empiricalPredictorRisk x n (oracleSelectedPredictor x n) +
          selectedUpperBoundary x n ∧
      (∀ i : Predictor,
        predictorLowerConfidenceEndpoint x n i <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore i) ∧
          stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore (oracleSelectedPredictor x n)) <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore i) +
              selectedUpperBoundary x n + predictorLowerBoundary x n i) ∧
      stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
            (brierScore (oracleSelectedPredictor x n)) <
        catalogMinimumStationaryRisk + selectedOraclePenalty x n

/-- A single all-time event gives the selected upper bound, every comparator's
matched lower bound, and the resulting finite-catalog oracle inequality. -/
theorem exists_randomRefreshLoad_twoSidedOracle_event :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        IsTwoSidedOracleEvent goodEvent := by
  let badEvent := twoSidedOracleExceptionalEvent
  let goodEvent := badEventᶜ
  refine ⟨goodEvent, ?_, ?_⟩
  · simpa [goodEvent, badEvent] using twoSidedOracleExceptionalEvent_mass_le
  · intro x hx n hn
    have hxBad : x ∉ badEvent := by
      simpa [goodEvent] using hx
    have hrowZero : ∀ z : State,
        finitePMFTotalVariation
            ((refreshKernel Candidate.nominal) z)
            (refreshKernel Candidate.nominal z) ≤ 0 := by
      intro z
      simp [finitePMFTotalVariation]
    have hupperRaw := empiricalStationaryCatalog_allPosteriors_of_not_mem
      (refreshKernel Candidate.nominal) uniformLaw
      (uniformLaw_invariant Candidate.nominal)
      refreshKernel candidateReference orientedBrierScore_mem_Icc
      candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
      orientedBrierScore_centeredOscillation_le
      candidateWeight_isFullSupport orientedPredictorPrior_isFullSupport
      oracleRiskFailureBudget_pos hxBad Candidate.nominal 5 5
      (eta := 0) (by norm_num) hrowZero
      (orientedPosterior (oracleSelectedPredictor x n) false)
      (orientedPosterior_isPMF _ false) n hn
    rw [orientedNormal_stationaryPosteriorRisk,
      orientedNormal_empiricalPosteriorRisk] at hupperRaw
    have hupper :
        stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore (oracleSelectedPredictor x n)) <
          empiricalPredictorRisk x n (oracleSelectedPredictor x n) +
            selectedUpperBoundary x n := by
      simpa [selectedUpperBoundary, badEvent,
        twoSidedOracleExceptionalEvent] using hupperRaw
    have hall : ∀ i : Predictor,
        predictorLowerConfidenceEndpoint x n i <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore i) ∧
          stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore (oracleSelectedPredictor x n)) <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore i) +
              selectedUpperBoundary x n + predictorLowerBoundary x n i := by
      intro i
      have hlowerRaw := empiricalStationaryCatalog_allPosteriors_of_not_mem
        (refreshKernel Candidate.nominal) uniformLaw
        (uniformLaw_invariant Candidate.nominal)
        refreshKernel candidateReference orientedBrierScore_mem_Icc
        candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
        orientedBrierScore_centeredOscillation_le
        candidateWeight_isFullSupport orientedPredictorPrior_isFullSupport
        oracleRiskFailureBudget_pos hxBad Candidate.nominal 5 5
        (eta := 0) (by norm_num) hrowZero
        (orientedPosterior i true) (orientedPosterior_isPMF i true) n hn
      rw [orientedFlipped_stationaryPosteriorRisk,
        orientedFlipped_empiricalPosteriorRisk i x (by omega)] at hlowerRaw
      change
        1 - stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore i) <
          1 - empiricalPredictorRisk x n i +
            predictorLowerBoundary x n i at hlowerRaw
      have hlower :
          predictorLowerConfidenceEndpoint x n i <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore i) := by
        unfold predictorLowerConfidenceEndpoint
        linarith
      have hminimal := oracleSelectedPredictor_empiricalRisk_minimal x n i
      have hcompare :
          stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore (oracleSelectedPredictor x n)) <
            stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore i) +
              selectedUpperBoundary x n + predictorLowerBoundary x n i := by
        linarith
      exact ⟨hlower, hcompare⟩
    have horacle := (hall Predictor.oracle).2
    have hbenchmark :
        stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
              (brierScore (oracleSelectedPredictor x n)) <
          catalogMinimumStationaryRisk + selectedOraclePenalty x n := by
      rw [oracle_stationaryRisk_eq_catalogMinimum] at horacle
      unfold selectedOraclePenalty
      linarith
    exact ⟨hupper, hall, hbenchmark⟩

/-- The same event yields the weak-inequality form commonly used to state an
oracle bound. -/
theorem exists_randomRefreshLoad_twoSidedOracle_le_event :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
                (brierScore (oracleSelectedPredictor x n)) ≤
            catalogMinimumStationaryRisk + selectedOraclePenalty x n := by
  rcases exists_randomRefreshLoad_twoSidedOracle_event with
    ⟨goodEvent, hmass, hgood⟩
  exact ⟨goodEvent, hmass, fun x hx n hn ↦ (hgood x hx n hn).2.2.le⟩

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadOracleCertificate
