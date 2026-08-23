/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadCertificate
import FormalSLT.Applications.RandomRefreshLoadPath

/-!
# Adaptive finite-catalog selection for the random-refresh load model

This module makes three path-and-time-dependent choices inside finite,
predeclared catalogs.  The empirical successor frequency selects one of the
three refresh kernels at the midpoints between their successor masses.  An
ordered tournament selects the first empirical-risk minimizer among the four
predictors.  Finally, a finite `9 * 7` grid selects a depth and risk-tilt atom
that minimizes the exact empirical stationary-catalog boundary.

The common-event theorem at the end substitutes these selectors into the
already simultaneous catalog event.  It does not construct a selected
e-process, prove selector measurability, or assert that the named balanced
path belongs to the good event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadAdaptiveSelection

open RandomRefreshLoadModel RandomRefreshLoadPath

noncomputable section

/-- Horizon of the deterministic balanced-path application. -/
def adaptiveHorizon : ℕ := 200000

@[simp] theorem adaptiveHorizon_eq : adaptiveHorizon = 200000 := rfl

/-! ## Candidate selection from the successor frequency -/

/-- Fraction of observed transitions that follow the common deterministic
successor edge.  At time zero this uses Lean's total real division convention. -/
def empiricalSuccessorRate (x : ℕ → State) (n : ℕ) : ℝ :=
  (∑ z : State, transitionEdgeMass z (successor z) n x) / (n : ℝ)

/-- Midpoint selector for the three candidate successor masses.  Equality at
a midpoint is resolved in favor of the candidate with larger `gamma`. -/
def adaptiveCandidate (x : ℕ → State) (n : ℕ) : Candidate :=
  if empiricalSuccessorRate x n < 73 / 320 then Candidate.low
  else if empiricalSuccessorRate x n < 111 / 320 then Candidate.nominal
  else Candidate.high

/-- The balanced path's successor rate is exactly the nominal value. -/
theorem balancedPath_empiricalSuccessorRate :
    empiricalSuccessorRate balancedPath adaptiveHorizon = 23 / 80 := by
  unfold empiricalSuccessorRate
  simp_rw [adaptiveHorizon_eq, balancedPath_transitionEdgeMass]
  norm_num [Finset.card_univ, state_card]

/-- The midpoint selector chooses the nominal kernel on the balanced path. -/
theorem balancedPath_adaptiveCandidate :
    adaptiveCandidate balancedPath adaptiveHorizon = Candidate.nominal := by
  rw [adaptiveCandidate, balancedPath_empiricalSuccessorRate]
  norm_num

/-- A second concrete selector branch: a constant zero path has no successor
edges at time two. -/
def constantZeroPath (_k : ℕ) : State := 0

theorem constantZeroPath_empiricalSuccessorRate :
    empiricalSuccessorRate constantZeroPath 2 = 0 := by
  have hzero : ∀ z : State,
      transitionEdgeMass z (successor z) 2 constantZeroPath = 0 := by
    intro z
    by_cases hz : z = 0
    · subst z
      have hsuccessor : (0 : State) ≠ successor 0 := by decide
      simp [transitionEdgeMass, transitionIndicatorScore,
        constantZeroPath, hsuccessor]
    · have hzeroNe : (0 : State) ≠ z := Ne.symm hz
      simp [transitionEdgeMass, transitionIndicatorScore,
        constantZeroPath, hzeroNe]
  simp [empiricalSuccessorRate, hzero]

theorem constantZeroPath_adaptiveCandidate :
    adaptiveCandidate constantZeroPath 2 = Candidate.low := by
  rw [adaptiveCandidate, constantZeroPath_empiricalSuccessorRate]
  norm_num

/-! ## Tie-broken empirical-risk selection -/

/-- Empirical transition risk of one declared predictor. -/
def empiricalPredictorRisk (x : ℕ → State) (n : ℕ)
    (i : Predictor) : ℝ :=
  empiricalTransitionRisk (brierScore i) n x

/-- Prefer the earlier predictor when its empirical risk is no larger. -/
private def preferPredictor (x : ℕ → State) (n : ℕ)
    (earlier later : Predictor) : Predictor :=
  if empiricalPredictorRisk x n earlier ≤ empiricalPredictorRisk x n later
  then earlier else later

private theorem preferPredictor_risk_le_left
    (x : ℕ → State) (n : ℕ) (i j : Predictor) :
    empiricalPredictorRisk x n (preferPredictor x n i j) ≤
      empiricalPredictorRisk x n i := by
  unfold preferPredictor
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_ge h

private theorem preferPredictor_risk_le_right
    (x : ℕ → State) (n : ℕ) (i j : Predictor) :
    empiricalPredictorRisk x n (preferPredictor x n i j) ≤
      empiricalPredictorRisk x n j := by
  unfold preferPredictor
  split_ifs with h
  · exact h
  · exact le_rfl

/-- Deterministic empirical-risk minimizer.  Ties are resolved in the order
`constant`, `loadOnly`, `oracle`, `early`. -/
def adaptivePredictor (x : ℕ → State) (n : ℕ) : Predictor :=
  preferPredictor x n Predictor.constant
    (preferPredictor x n Predictor.loadOnly
      (preferPredictor x n Predictor.oracle Predictor.early))

/-- The selected predictor has no larger empirical risk than any member of
the fixed four-predictor catalog. -/
theorem adaptivePredictor_empiricalRisk_minimal
    (x : ℕ → State) (n : ℕ) (i : Predictor) :
    empiricalPredictorRisk x n (adaptivePredictor x n) ≤
      empiricalPredictorRisk x n i := by
  fin_cases i
  · exact preferPredictor_risk_le_left x n _ _
  · exact (preferPredictor_risk_le_right x n _ _).trans
      (preferPredictor_risk_le_left x n _ _)
  · exact (preferPredictor_risk_le_right x n _ _).trans
      ((preferPredictor_risk_le_right x n _ _).trans
        (preferPredictor_risk_le_left x n _ _))
  · exact (preferPredictor_risk_le_right x n _ _).trans
      ((preferPredictor_risk_le_right x n _ _).trans
        (preferPredictor_risk_le_right x n _ _))

/-- The balanced transition table reproduces every nominal stationary risk
in the four-predictor catalog. -/
private theorem empiricalTransitionRisk_eq_edgeMass_sum
    (score : MarkovTransitionScore State) (n : ℕ) (x : ℕ → State) :
    empiricalTransitionRisk score n x =
      (∑ z : State, ∑ y : State,
        transitionEdgeMass z y n x * score z y) / (n : ℝ) := by
  classical
  have hpoint (k : ℕ) :
      score (x k) (x (k + 1)) =
        ∑ z : State, ∑ y : State,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
    rw [Fintype.sum_eq_single (x k)]
    · rw [Fintype.sum_eq_single (x (k + 1))]
      · simp [transitionIndicatorScore]
      · intro y hy
        have hne : x (k + 1) ≠ y := Ne.symm hy
        simp [transitionIndicatorScore, hne]
    · intro z hz
      have hne : x k ≠ z := Ne.symm hz
      simp [transitionIndicatorScore, hne]
  unfold empiricalTransitionRisk runningMean runningSum
  congr 1
  calc
    ∑ k ∈ Finset.range n, score (x k) (x (k + 1)) =
        ∑ k ∈ Finset.range n, ∑ z : State, ∑ y : State,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact hpoint k
    _ = ∑ z : State, ∑ y : State, ∑ k ∈ Finset.range n,
          transitionIndicatorScore z y (x k) (x (k + 1)) * score z y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.sum_comm]
    _ = ∑ z : State, ∑ y : State,
          transitionEdgeMass z y n x * score z y := by
      apply Finset.sum_congr rfl
      intro z _hz
      apply Finset.sum_congr rfl
      intro y _hy
      rw [transitionEdgeMass, Finset.sum_mul]

private theorem balancedPath_edgeFrequency_eq_nominal (z y : State) :
    transitionEdgeMass z y adaptiveHorizon balancedPath /
        (adaptiveHorizon : ℝ) =
      (uniformLaw z).toReal *
        (refreshKernel Candidate.nominal z y).toReal := by
  rw [adaptiveHorizon_eq, balancedPath_transitionEdgeMass,
    uniformLaw_apply_toReal, refreshKernel_apply_toReal]
  by_cases h : y = successor z
  · simp [h, candidateBase, candidateBaseNN,
      candidateGamma, candidateGammaNN]
    norm_num
  · simp [h, candidateBase, candidateBaseNN]
    norm_num

theorem balancedPath_empiricalPredictorRisk (i : Predictor) :
    empiricalPredictorRisk balancedPath adaptiveHorizon i =
      candidateStationaryRiskValue Candidate.nominal i := by
  unfold empiricalPredictorRisk
  calc
    empiricalTransitionRisk (brierScore i) adaptiveHorizon balancedPath =
        (∑ z : State, ∑ y : State,
          transitionEdgeMass z y adaptiveHorizon balancedPath *
            brierScore i z y) / (adaptiveHorizon : ℝ) :=
      empiricalTransitionRisk_eq_edgeMass_sum _ _ _
    _ = ∑ z : State, ∑ y : State,
          (transitionEdgeMass z y adaptiveHorizon balancedPath /
            (adaptiveHorizon : ℝ)) * brierScore i z y := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = ∑ z : State, ∑ y : State,
          (uniformLaw z).toReal *
            (refreshKernel Candidate.nominal z y).toReal *
              brierScore i z y := by
      simp_rw [balancedPath_edgeFrequency_eq_nominal]
    _ = stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
          (brierScore i) := by
      unfold stationaryMarkovRisk markovRowRisk
      simp only [PMF.integral_eq_sum, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = candidateStationaryRiskValue Candidate.nominal i :=
      candidate_stationaryRisk Candidate.nominal i

/-- The tie-broken empirical-risk selector chooses the oracle on the balanced
path. -/
theorem balancedPath_adaptivePredictor :
    adaptivePredictor balancedPath adaptiveHorizon = Predictor.oracle := by
  have hc := balancedPath_empiricalPredictorRisk Predictor.constant
  have hl := balancedPath_empiricalPredictorRisk Predictor.loadOnly
  have ho := balancedPath_empiricalPredictorRisk Predictor.oracle
  have he := balancedPath_empiricalPredictorRisk Predictor.early
  have hoe : preferPredictor balancedPath adaptiveHorizon
      Predictor.oracle Predictor.early = Predictor.oracle := by
    unfold preferPredictor
    rw [ho, he]
    norm_num [candidateStationaryRiskValue]
  have hlo : preferPredictor balancedPath adaptiveHorizon Predictor.loadOnly
      (preferPredictor balancedPath adaptiveHorizon
        Predictor.oracle Predictor.early) = Predictor.oracle := by
    rw [hoe]
    unfold preferPredictor
    rw [hl, ho]
    norm_num [candidateStationaryRiskValue]
  unfold adaptivePredictor
  rw [hlo]
  unfold preferPredictor
  rw [hc, ho]
  norm_num [candidateStationaryRiskValue]

/-- On the constant zero path, the load-only, oracle, and early predictors
tie, so the declared order selects `loadOnly`. -/
theorem constantZeroPath_empiricalPredictorRisk (i : Predictor) :
    empiricalPredictorRisk constantZeroPath 2 i =
      match i with
      | .constant => 1 / 25
      | .loadOnly => 9 / 400
      | .oracle => 9 / 400
      | .early => 9 / 400 := by
  fin_cases i <;>
    norm_num [empiricalPredictorRisk, empiricalTransitionRisk,
      runningMean, runningSum, brierScore, predictorProbability,
      overloadIndicator, constantZeroPath, successor_val]

theorem constantZeroPath_adaptivePredictor :
    adaptivePredictor constantZeroPath 2 = Predictor.loadOnly := by
  have hc := constantZeroPath_empiricalPredictorRisk Predictor.constant
  have hl := constantZeroPath_empiricalPredictorRisk Predictor.loadOnly
  have ho := constantZeroPath_empiricalPredictorRisk Predictor.oracle
  have he := constantZeroPath_empiricalPredictorRisk Predictor.early
  have hoe : preferPredictor constantZeroPath 2
      Predictor.oracle Predictor.early = Predictor.oracle := by
    unfold preferPredictor
    rw [ho, he]
    norm_num
  have hlo : preferPredictor constantZeroPath 2 Predictor.loadOnly
      (preferPredictor constantZeroPath 2 Predictor.oracle Predictor.early) =
        Predictor.loadOnly := by
    rw [hoe]
    unfold preferPredictor
    rw [hl, ho]
    norm_num
  unfold adaptivePredictor
  rw [hlo]
  unfold preferPredictor
  rw [hc, hl]
  norm_num

/-- Point posterior at the path-and-time empirical-risk minimizer. -/
def adaptivePosterior (x : ℕ → State) (n : ℕ) : Predictor → ℝ :=
  diracPosterior (adaptivePredictor x n)

theorem adaptivePosterior_isPMF (x : ℕ → State) (n : ℕ) :
    IsPMF (adaptivePosterior x n) := by
  exact diracPosterior_isPMF (adaptivePredictor x n)

theorem balancedPath_adaptivePosterior :
    adaptivePosterior balancedPath adaptiveHorizon = oraclePosterior := by
  rw [adaptivePosterior, balancedPath_adaptivePredictor]
  rfl

/-! ## Finite depth--tilt boundary grid -/

/-- Predeclared depths `0, ..., 8`. -/
abbrev DepthChoice := Fin 9

/-- Predeclared risk-tilt indices `0, ..., 6`. -/
abbrev RiskTiltChoice := Fin 7

/-- One atom in the finite depth--risk-tilt grid. -/
abbrev BoundaryChoice := DepthChoice × RiskTiltChoice

/-- Candidate-specific empirical transition radius used after adaptive
candidate selection. -/
def adaptiveEmpiricalKernelTVBudget (x : ℕ → State) (n : ℕ) : ℝ :=
  empiricalCandidateKernelTVBudget (refreshKernel (adaptiveCandidate x n))
    transitionPrior transitionWeight transitionTilt
    transitionFailureBudget () n x

/-- Exact empirical stationary-catalog boundary at one declared grid atom. -/
def adaptiveBoundaryAtom (x : ℕ → State) (n : ℕ)
    (choice : BoundaryChoice) : ℝ :=
  empiricalStationaryCatalogBoundary refreshKernel candidateReference
    brierScore candidateOscillation candidateWeight predictorPrior
    (adaptivePosterior x n) riskFailureBudget
    (adaptiveEmpiricalKernelTVBudget x n) (adaptiveCandidate x n)
    choice.1.val choice.2.val n x

private theorem adaptiveBoundaryChoice_exists (x : ℕ → State) (n : ℕ) :
    ∃ choice ∈ (Finset.univ : Finset BoundaryChoice),
      ∀ other ∈ (Finset.univ : Finset BoundaryChoice),
        adaptiveBoundaryAtom x n choice ≤ adaptiveBoundaryAtom x n other := by
  exact (Finset.univ : Finset BoundaryChoice).exists_min_image
    (adaptiveBoundaryAtom x n) Finset.univ_nonempty

/-- A concrete path-and-time-dependent argmin over the `9 * 7` grid. -/
def adaptiveBoundaryChoice (x : ℕ → State) (n : ℕ) : BoundaryChoice :=
  Classical.choose (adaptiveBoundaryChoice_exists x n)

/-- Minimality against every predeclared depth--tilt atom. -/
theorem adaptiveBoundaryChoice_minimal (x : ℕ → State) (n : ℕ)
    (other : BoundaryChoice) :
    adaptiveBoundaryAtom x n (adaptiveBoundaryChoice x n) ≤
      adaptiveBoundaryAtom x n other := by
  exact (Classical.choose_spec (adaptiveBoundaryChoice_exists x n)).2
    other (Finset.mem_univ other)

/-- Selected depth, always in `{0, ..., 8}` by its type. -/
def adaptiveDepth (x : ℕ → State) (n : ℕ) : ℕ :=
  (adaptiveBoundaryChoice x n).1.val

/-- Selected risk-tilt index, always in `{0, ..., 6}` by its type. -/
def adaptiveRiskTilt (x : ℕ → State) (n : ℕ) : ℕ :=
  (adaptiveBoundaryChoice x n).2.val

/-- Exact boundary selected by the finite grid argmin. -/
def adaptiveSelectedBoundary (x : ℕ → State) (n : ℕ) : ℝ :=
  adaptiveBoundaryAtom x n (adaptiveBoundaryChoice x n)

/-- The selected atom is no worse than the predeclared depth-five,
risk-tilt-five atom on the same path and at the same time.  This does not
identify which atom is the argmin. -/
theorem adaptiveSelectedBoundary_le_fixedFive
    (x : ℕ → State) (n : ℕ) :
    adaptiveSelectedBoundary x n ≤
      adaptiveBoundaryAtom x n
        ((⟨5, by norm_num⟩ : DepthChoice),
          (⟨5, by norm_num⟩ : RiskTiltChoice)) := by
  exact adaptiveBoundaryChoice_minimal x n _

/-! ## Common-event substitution -/

/-- One common event with complement real outer mass at most `1/20` supports
the path-and-time candidate, posterior, depth, and risk-tilt selectors above.
The event remains simultaneous; this theorem is substitution into that event,
not a selected-process construction or a measurability claim. -/
theorem exists_randomRefreshLoad_adaptiveSelection_event :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : State, 0 < transitionVisitMass z n x) →
            stationaryPosteriorMarkovRisk
                (refreshKernel Candidate.nominal) uniformLaw brierScore
                (adaptivePosterior x n) <
              empiricalTransitionPosteriorRisk brierScore
                  (adaptivePosterior x n) n x +
                adaptiveSelectedBoundary x n ∧
            finiteDobrushinCoefficient
                (refreshKernel Candidate.nominal) ≤
              finiteDobrushinCoefficient
                  (refreshKernel (adaptiveCandidate x n)) +
                2 * adaptiveEmpiricalKernelTVBudget x n ∧
            IsOscillationContraction
              (refreshKernel Candidate.nominal)
              (finiteDobrushinCoefficient
                  (refreshKernel (adaptiveCandidate x n)) +
                2 * adaptiveEmpiricalKernelTVBudget x n) := by
  have h := exists_selectedEmpiricalStationaryCatalog_event
    (refreshKernel Candidate.nominal) uniformLaw
    (uniformLaw_invariant Candidate.nominal) (0 : State)
    refreshKernel candidateReference brierScore_mem_Icc
    candidateOscillation_nonneg refreshKernel_dobrushinCoefficient_lt_one
    brierScore_centeredOscillation_le candidateWeight_isFullSupport
    predictorPrior_isFullSupport transitionPrior_isFullSupport
    transitionWeight_isFullSupport transitionTilt_pos transitionTilt_lt_one
    riskFailureBudget_pos transitionFailureBudget_pos
    adaptiveCandidate adaptiveDepth adaptiveRiskTilt
    (fun _x _n ↦ ()) adaptivePosterior adaptivePosterior_isPMF
  rcases h with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · convert hmass using 1
    all_goals norm_num [riskFailureBudget, transitionFailureBudget]
  · intro x hx n hn hvisit
    have hselected := hgood x hx n hn hvisit
    simpa [adaptiveDepth, adaptiveRiskTilt, adaptiveSelectedBoundary,
      adaptiveBoundaryAtom, adaptiveEmpiricalKernelTVBudget] using
      ⟨hselected.1, hselected.2.1, hselected.2.2.1⟩

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadAdaptiveSelection
