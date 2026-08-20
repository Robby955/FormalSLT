/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadModel
import FormalSLT.StochasticDynamics.EmpiricalStationaryCatalog

/-!
# Statistical certificate configuration for the random-refresh load model

This module fixes the finite candidate and score priors, transition-coordinate
prior, confidence levels, and path/time selectors used by the twenty-state
application.  The resulting theorem gives one event of probability at least
`19/20`, simultaneous over all times with all rows visited, on which the
selected nominal candidate, depth five, risk tilt five, transition tilt
`1/8`, and oracle point posterior satisfy the empirical stationary-catalog
certificate.

The theorem controls the real outer mass of the complement by `1/20`; it does
not separately prove measurability of the selected event.  This is the
probabilistic event layer.  It does not assert that a particular
named deterministic path belongs to the event, and it does not yet evaluate
the displayed boundary numerically.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.PACBayesKL FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadModel

noncomputable section

/-- Common invariant-law reference for every candidate. -/
def candidateReference (_c : Candidate) : PMF State := uniformLaw

/-- Uniform prior over the three predeclared kernels. -/
def candidateWeight : Candidate → ℝ := finiteUniformRealPMF Candidate

/-- Uniform prior over the four predeclared predictors. -/
def predictorPrior : Predictor → ℝ := finiteUniformRealPMF Predictor

/-- Uniform prior over all `20 * 20 * 2 = 800` transition coordinates. -/
def transitionPrior : TransitionCoordinate State → ℝ :=
  finiteUniformRealPMF (TransitionCoordinate State)

/-- The transition-confidence layer uses one predeclared tilt atom. -/
def transitionWeight : Unit → ℝ := finiteUniformRealPMF Unit

/-- Fixed transition-confidence tilt. -/
def transitionTilt (_k : Unit) : ℝ := 1 / 8

/-- Risk-event failure budget. -/
def riskFailureBudget : ℝ := 1 / 40

/-- Transition-event failure budget. -/
def transitionFailureBudget : ℝ := 1 / 40

/-- Selected kernel candidate.  It is predeclared and may later be replaced
by a path-dependent selector without changing the common event theorem. -/
def selectCandidate (_x : ℕ → State) (_n : ℕ) : Candidate :=
  Candidate.nominal

/-- Selected finite Poisson depth. -/
def selectDepth (_x : ℕ → State) (_n : ℕ) : ℕ := 5

/-- Selected geometric risk-tilt index, corresponding to tilt `1/64`. -/
def selectRiskTilt (_x : ℕ → State) (_n : ℕ) : ℕ := 5

/-- Selected transition-confidence tilt atom. -/
def selectTransitionTilt (_x : ℕ → State) (_n : ℕ) : Unit := ()

/-- Fixed point posterior used in the numerical receipt. -/
def oraclePosterior : Predictor → ℝ := diracPosterior Predictor.oracle

/-- Point posterior on the correctly specified nominal oracle predictor. -/
def selectPosterior (_x : ℕ → State) (_n : ℕ) : Predictor → ℝ :=
  oraclePosterior

/-- Empirical all-row kernel budget used by the unknown-kernel certificate. -/
def selectedEmpiricalKernelTVBudget (n : ℕ) (x : ℕ → State) : ℝ :=
  empiricalCandidateKernelTVBudget (refreshKernel Candidate.nominal)
    transitionPrior transitionWeight transitionTilt
    transitionFailureBudget () n x

/-- Depth-five boundary when the nominal kernel is treated as known exactly. -/
def selectedKnownKernelBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    brierScore candidateOscillation candidateWeight predictorPrior
    oraclePosterior riskFailureBudget 0 Candidate.nominal 5 5 n x

/-- Matched depth-five boundary with the empirical transition uncertainty. -/
def selectedUnknownKernelBoundary (n : ℕ) (x : ℕ → State) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    brierScore candidateOscillation candidateWeight predictorPrior
    oraclePosterior riskFailureBudget
    (selectedEmpiricalKernelTVBudget n x) Candidate.nominal 5 5 n x

theorem candidateWeight_isFullSupport :
    IsFullSupportPMF candidateWeight := by
  exact finiteUniformRealPMF_isFullSupport Candidate

theorem predictorPrior_isFullSupport :
    IsFullSupportPMF predictorPrior := by
  exact finiteUniformRealPMF_isFullSupport Predictor

theorem transitionPrior_isFullSupport :
    IsFullSupportPMF transitionPrior := by
  exact finiteUniformRealPMF_isFullSupport (TransitionCoordinate State)

theorem transitionWeight_isFullSupport :
    IsFullSupportPMF transitionWeight := by
  exact finiteUniformRealPMF_isFullSupport Unit

theorem transitionTilt_pos (k : Unit) : 0 < transitionTilt k := by
  cases k
  norm_num [transitionTilt]

theorem transitionTilt_lt_one (k : Unit) : transitionTilt k < 1 := by
  cases k
  norm_num [transitionTilt]

theorem riskFailureBudget_pos : 0 < riskFailureBudget := by
  norm_num [riskFailureBudget]

theorem transitionFailureBudget_pos : 0 < transitionFailureBudget := by
  norm_num [transitionFailureBudget]

theorem candidateOscillation_nonneg (c : Candidate) :
    0 ≤ candidateOscillation c := by
  cases c <;> norm_num [candidateOscillation]

theorem selectPosterior_isPMF (x : ℕ → State) (n : ℕ) :
    IsPMF (selectPosterior x n) := by
  exact diracPosterior_isPMF Predictor.oracle

/-- One event whose complement has real outer mass at most `1/20` for the
fixed application selectors.  The theorem remains all-time after the explicit
all-row coverage premise. -/
theorem exists_randomRefreshLoad_selected_event :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : State, 0 < transitionVisitMass z n x) →
            let eta := empiricalCandidateKernelTVBudget
              (refreshKernel Candidate.nominal) transitionPrior
              transitionWeight transitionTilt transitionFailureBudget () n x
            stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                (diracPosterior Predictor.oracle) <
              empiricalTransitionPosteriorRisk brierScore
                  (diracPosterior Predictor.oracle) n x +
                empiricalStationaryCatalogBoundary
                  refreshKernel candidateReference brierScore
                  candidateOscillation candidateWeight predictorPrior
                  (diracPosterior Predictor.oracle) riskFailureBudget eta
                  Candidate.nominal 5 5 n x ∧
              finiteDobrushinCoefficient
                  (refreshKernel Candidate.nominal) ≤
                finiteDobrushinCoefficient
                    (refreshKernel Candidate.nominal) + 2 * eta ∧
              IsOscillationContraction
                (refreshKernel Candidate.nominal)
                (finiteDobrushinCoefficient
                    (refreshKernel Candidate.nominal) + 2 * eta) ∧
              (finiteDobrushinCoefficient
                    (refreshKernel Candidate.nominal) + 2 * eta < 1 →
                ∀ stationaryOne stationaryTwo : PMF State,
                  IsInvariantPMF (refreshKernel Candidate.nominal)
                      stationaryOne →
                  IsInvariantPMF (refreshKernel Candidate.nominal)
                      stationaryTwo →
                  stationaryOne = stationaryTwo) := by
  have h := exists_selectedEmpiricalStationaryCatalog_event
    (refreshKernel Candidate.nominal) uniformLaw
    (uniformLaw_invariant Candidate.nominal) (0 : State)
    refreshKernel candidateReference brierScore_mem_Icc
    candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
    brierScore_centeredOscillation_le candidateWeight_isFullSupport
    predictorPrior_isFullSupport transitionPrior_isFullSupport
    transitionWeight_isFullSupport transitionTilt_pos transitionTilt_lt_one
    riskFailureBudget_pos transitionFailureBudget_pos
    selectCandidate selectDepth selectRiskTilt selectTransitionTilt
    selectPosterior selectPosterior_isPMF
  rcases h with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · convert hmass using 1
    all_goals norm_num [riskFailureBudget, transitionFailureBudget]
  · intro x hx n hn hvisit
    simpa [riskFailureBudget, transitionFailureBudget, selectCandidate,
      selectDepth, selectRiskTilt, selectTransitionTilt, selectPosterior,
      oraclePosterior] using
      hgood x hx n hn hvisit

/-- One common event with complement real outer mass at most `1/20` supports a
matched known-kernel (`eta = 0`) and empirical-kernel comparison.  The two
inequalities use the same path, time, posterior, depth, tilt, and risk
exceptional event. -/
theorem exists_randomRefreshLoad_matched_event :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : State, 0 < transitionVisitMass z n x) →
            stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                oraclePosterior <
              empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  n x + selectedKnownKernelBoundary n x ∧
            stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                oraclePosterior <
              empiricalTransitionPosteriorRisk brierScore oraclePosterior
                  n x + selectedUnknownKernelBoundary n x ∧
            finiteDobrushinCoefficient
                (refreshKernel Candidate.nominal) ≤
              finiteDobrushinCoefficient
                  (refreshKernel Candidate.nominal) +
                2 * selectedEmpiricalKernelTVBudget n x ∧
            IsOscillationContraction
              (refreshKernel Candidate.nominal)
              (finiteDobrushinCoefficient
                  (refreshKernel Candidate.nominal) +
                2 * selectedEmpiricalKernelTVBudget n x) := by
  let P := refreshKernel Candidate.nominal
  let riskBad := empiricalStationaryCatalogExceptionalEvent
    P refreshKernel candidateReference brierScore candidateOscillation
      candidateWeight predictorPrior riskFailureBudget
  have hriskMass :
      (markovPathMeasure P 0).real riskBad ≤ riskFailureBudget := by
    simpa [riskBad] using empiricalStationaryCatalogExceptionalEvent_mass_le
      P (0 : State) refreshKernel candidateReference brierScore_mem_Icc
      candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
      brierScore_centeredOscillation_le candidateWeight_isFullSupport
      predictorPrior_isFullSupport riskFailureBudget_pos
  rcases exists_empiricalCandidateKernelTV_event
      P (0 : State) transitionPrior_isFullSupport
      transitionWeight_isFullSupport transitionFailureBudget_pos
      transitionTilt_pos transitionTilt_lt_one with
    ⟨transitionGood, htransitionMass, htransitionGood⟩
  let goodEvent := riskBadᶜ ∩ transitionGood
  refine ⟨goodEvent, ?_, ?_⟩
  · have hunion := measureReal_union_le
      (μ := markovPathMeasure P 0) riskBad transitionGoodᶜ
    calc
      (markovPathMeasure P 0).real goodEventᶜ =
          (markovPathMeasure P 0).real (riskBad ∪ transitionGoodᶜ) := by
        congr 1
        ext y
        by_cases hyrisk : y ∈ riskBad <;>
          by_cases hytransition : y ∈ transitionGood <;>
            simp [goodEvent, hyrisk, hytransition]
      _ ≤ (markovPathMeasure P 0).real riskBad +
          (markovPathMeasure P 0).real transitionGoodᶜ := hunion
      _ ≤ riskFailureBudget + transitionFailureBudget :=
        add_le_add hriskMass htransitionMass
      _ = 1 / 20 := by
        norm_num [riskFailureBudget, transitionFailureBudget]
  · intro x hx n hn hvisit
    have hxRisk : x ∉ riskBad := hx.1
    have hxTransition : x ∈ transitionGood := hx.2
    have hrowZero : ∀ z : State,
        finitePMFTotalVariation (P z)
            (refreshKernel Candidate.nominal z) ≤ 0 := by
      intro z
      simp [P, finitePMFTotalVariation]
    have hknown := empiricalStationaryCatalog_allPosteriors_of_not_mem
      P uniformLaw (uniformLaw_invariant Candidate.nominal)
      refreshKernel candidateReference brierScore_mem_Icc
      candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
      brierScore_centeredOscillation_le candidateWeight_isFullSupport
      predictorPrior_isFullSupport riskFailureBudget_pos hxRisk
      Candidate.nominal 5 5 (eta := 0) (by norm_num) hrowZero
      oraclePosterior (diracPosterior_isPMF Predictor.oracle) n hn
    let eta := selectedEmpiricalKernelTVBudget n x
    have hrow : ∀ z : State,
        finitePMFTotalVariation (P z)
            (refreshKernel Candidate.nominal z) ≤ eta := by
      simpa [eta, selectedEmpiricalKernelTVBudget, P] using
        htransitionGood x hxTransition () n hn hvisit
          (refreshKernel Candidate.nominal)
    have heta : 0 ≤ eta := by
      exact (finitePMFTotalVariation_nonneg
        (P (0 : State)) (refreshKernel Candidate.nominal 0)).trans
          (hrow 0)
    have hunknown := empiricalStationaryCatalog_allPosteriors_of_not_mem
      P uniformLaw (uniformLaw_invariant Candidate.nominal)
      refreshKernel candidateReference brierScore_mem_Icc
      candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
      brierScore_centeredOscillation_le candidateWeight_isFullSupport
      predictorPrior_isFullSupport riskFailureBudget_pos hxRisk
      Candidate.nominal 5 5 heta hrow oraclePosterior
      (diracPosterior_isPMF Predictor.oracle) n hn
    have hcoefficient :=
      finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
        P (refreshKernel Candidate.nominal) hrow
    have hcontraction :=
      candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
        P (refreshKernel Candidate.nominal) hrow
    simpa [P, eta, selectedKnownKernelBoundary,
      selectedUnknownKernelBoundary, selectedEmpiricalKernelTVBudget] using
      And.intro hknown (And.intro hunknown
        (And.intro hcoefficient hcontraction))

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadModel
