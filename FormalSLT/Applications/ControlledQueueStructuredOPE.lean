/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueOPECatalog
import FormalSLT.Applications.ControlledQueuePersistenceConfidence
import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustFiniteDepthOPE

/-!
# Structured unknown-dynamics OPE for the controlled queue

This module intersects two events on the same controlled trajectory:

* a target-policy OPE event for every atom of a finite, predeclared
  candidate--depth catalog; and
* the scalar persistence-confidence event for the queue refresh family.

Candidate--depth atom `q` receives risk budget
`deltaRisk * catalogWeight q`. The allocated budgets sum exactly to
`deltaRisk`, so the finite union costs at most `deltaRisk`; intersecting it
with the persistence event costs at most `deltaRisk + deltaPersistence`, with
no independence or sample splitting.

On the common event, candidate, depth, both tilt atoms, posterior, and time may
be selected from their predeclared catalogs after observing the path.  The
true persistence parameter, initial observation, catalog, weights, tilts, and
confidence allocations remain fixed before the event.

For candidate persistence weight `alpha`, depth `m`, and scalar physical-row
TV budget `eta`, the robust residual is

`alpha ^ m + 2 * ((1 + B_m) * eta)`,

where `B_m = finiteDepthPoissonClosedSpanBound alpha 1 m`.  There is no
behavior-probability conversion in this residual because the persistence
event directly controls every physical action-conditioned row.

The theorem assumes the true environment belongs to the one-parameter refresh
family.  It is not a general unknown-kernel result, a family-membership test,
a selected e-process, a frozen-path good-event certificate, or a cumulative
policy-value theorem.  The two causal Beta predictors remain outside the
stationary twelve-hypothesis score catalog.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

/-- A controlled queue trajectory. -/
abbrev QueuePath := ℕ → Observation

/-- Candidate-specific closed span of the depth-`m` Poisson potential. -/
def queueCandidateFiniteDepthSpan
    (candidate : CandidateIndex) (depth : ℕ) : ℝ :=
  finiteDepthPoissonClosedSpanBound (candidateGamma candidate) 1 depth

/-- Candidate-specific finite-depth potential for the twelve fixed queue
hypotheses. -/
def queueCandidateFiniteDepthPotential
    (candidate : CandidateIndex) (depth : ℕ) :
    QueueHypothesis → PhysicalState → ℝ :=
  candidateTargetPolicyFiniteDepthPotential
    (candidateEnvironment candidate)
    queueHypothesisTargetPolicy queueHypothesisReference
    queueHypothesisScore depth

/-- The OPE boundary for one preallocated candidate--depth risk event. -/
def structuredQueueOPEBoundary
    {τ : Type*} [Fintype τ]
    (candidate : CandidateIndex) (depth : ℕ)
    (weight : τ → ℝ) (lam : τ → ℝ)
    (delta : ℝ) (j : τ)
    (posterior : QueueHypothesis → ℝ)
    (n : ℕ) (path : QueuePath) : ℝ :=
  stationaryTargetPolicyOPEBoundary
    queueHypothesisPrior weight lam
    (markovBehaviorPolicyAsHistory behaviorPolicy)
    queueHypothesisTargetPolicy queueHypothesisScore
    (queueCandidateFiniteDepthPotential candidate depth)
    (queueCandidateFiniteDepthSpan candidate depth)
    (3 / 2 : ℝ) posterior delta j n path

/-- Robust structured misspecification residual for one candidate and depth. -/
def structuredQueueFiniteDepthResidual
    (candidate : CandidateIndex) (depth : ℕ) (eta : ℝ) : ℝ :=
  candidateGamma candidate ^ depth +
    2 * ((1 + queueCandidateFiniteDepthSpan candidate depth) * eta)

/-- Every candidate-specific finite-depth potential obeys its closed span. -/
theorem queueCandidateFiniteDepthPotential_span
    (candidate : CandidateIndex) (depth : ℕ)
    (hypothesis : QueueHypothesis) (state nextState : PhysicalState) :
    |queueCandidateFiniteDepthPotential candidate depth hypothesis nextState -
        queueCandidateFiniteDepthPotential candidate depth hypothesis state| ≤
      queueCandidateFiniteDepthSpan candidate depth := by
  have halpha := (candidateGamma_mem_Ico candidate).1
  have halphaOne := (candidateGamma_mem_Ico candidate).2
  rw [show
      queueCandidateFiniteDepthSpan candidate depth =
        finiteDepthPoissonSpanBound (candidateGamma candidate) 1 depth by
    unfold queueCandidateFiniteDepthSpan
    exact (finiteDepthPoissonSpanBound_closed halphaOne depth).symm]
  exact finiteDepthPoissonPotential_span
    (targetPolicyKernel (candidateEnvironment candidate)
      (queueHypothesisTargetPolicy hypothesis))
    (queueHypothesisReference hypothesis)
    (targetPolicyRowScore (candidateEnvironment candidate)
      (queueHypothesisTargetPolicy hypothesis)
      (queueHypothesisScore hypothesis)) depth
    halpha
    (candidateTargetPolicyKernel_isOscillationContraction
      candidate (queueHypothesisTargetPolicy hypothesis))
    (by
      simpa [queueHypothesisTargetPolicy, queueHypothesisReference,
        queueHypothesisScore] using
        fixedBrierScore_centeredTargetPolicyRowRisk_finiteOscillation_le_one
          candidate hypothesis.1 uniformStateReference hypothesis.2)
    state nextState

/-- One finite predeclared candidate--depth catalog and one persistence event
give a same-path structured unknown-dynamics OPE certificate.

The candidate--depth atom, both tilt atoms, posterior, and time are universally
quantified inside the common event. -/
theorem exists_structuredControlledQueueFiniteCatalogOPE_event
    {κ τRisk τPersistence : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype τRisk] [DecidableEq τRisk] [Nonempty τRisk]
    [Fintype τPersistence] [DecidableEq τPersistence]
    [Nonempty τPersistence]
    (gamma : PersistenceParameter) (initial : Observation)
    (catalog : κ → CandidateIndex × ℕ)
    {catalogWeight : κ → ℝ}
    (hcatalogWeight : IsFullSupportPMF catalogWeight)
    {riskWeight : τRisk → ℝ}
    (hRiskWeight : IsFullSupportPMF riskWeight)
    {riskLam : τRisk → ℝ}
    (hRiskLam : ∀ j, 0 < riskLam j)
    (hRiskLamOne : ∀ j, riskLam j < 1)
    {persistenceWeight : τPersistence → ℝ}
    (hPersistenceWeight : IsFullSupportPMF persistenceWeight)
    {persistenceLam : τPersistence → ℝ}
    (hPersistenceLam : ∀ j, 0 < persistenceLam j)
    (hPersistenceLamOne : ∀ j, persistenceLam j < 1)
    {deltaRisk deltaPersistence : ℝ}
    (hdeltaRisk : 0 < deltaRisk)
    (hdeltaPersistence : 0 < deltaPersistence) :
    ∃ goodEvent : Set QueuePath,
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ deltaRisk + deltaPersistence ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        ∀ q : κ, ∀ jRisk : τRisk, ∀ jPersistence : τPersistence,
          ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
            stationaryTargetPolicyPosteriorRisk
                (refreshEnvironment gamma)
                queueHypothesisTargetPolicy
                (queueHypothesisStationary (refreshEnvironment gamma))
                queueHypothesisScore posterior <
              structuredQueueOPEBoundary
                  (catalog q).1 (catalog q).2 riskWeight riskLam
                  (deltaRisk * catalogWeight q) jRisk posterior n path +
                structuredQueueFiniteDepthResidual
                  (catalog q).1 (catalog q).2
                  (structuredCandidateTVBudget
                    (catalog q).1 persistenceWeight persistenceLam
                    deltaPersistence jPersistence n path) := by
  classical
  let mu := controlledTrajectoryMeasure
    (refreshEnvironment gamma)
    (markovBehaviorPolicyAsHistory behaviorPolicy) initial
  have hriskWitness (q : κ) :
      ∃ riskGood : Set QueuePath,
        mu.real riskGoodᶜ ≤ deltaRisk * catalogWeight q ∧
        ∀ path ∈ riskGood, ∀ j : τRisk,
          ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryTargetPolicyPosteriorRisk
                  (refreshEnvironment gamma)
                  queueHypothesisTargetPolicy
                  (queueHypothesisStationary (refreshEnvironment gamma))
                  queueHypothesisScore posterior <
                structuredQueueOPEBoundary
                    (catalog q).1 (catalog q).2 riskWeight riskLam
                    (deltaRisk * catalogWeight q) j posterior n path -
                  stationaryTargetPolicyPosteriorResidualAverage
                    (refreshEnvironment gamma)
                    queueHypothesisTargetPolicy
                    (queueHypothesisStationary (refreshEnvironment gamma))
                    queueHypothesisScore
                    (queueCandidateFiniteDepthPotential
                      (catalog q).1 (catalog q).2)
                    posterior n path := by
    let candidate := (catalog q).1
    let depth := (catalog q).2
    have hB : 0 ≤ queueCandidateFiniteDepthSpan candidate depth := by
      rw [show
          queueCandidateFiniteDepthSpan candidate depth =
            finiteDepthPoissonSpanBound
              (candidateGamma candidate) 1 depth by
        unfold queueCandidateFiniteDepthSpan
        exact (finiteDepthPoissonSpanBound_closed
          (candidateGamma_mem_Ico candidate).2 depth).symm]
      exact finiteDepthPoissonSpanBound_nonneg
        (candidateGamma_mem_Ico candidate).1 (by norm_num) depth
    have hspan : ∀ hypothesis state nextState,
        |queueCandidateFiniteDepthPotential
              candidate depth hypothesis nextState -
            queueCandidateFiniteDepthPotential
              candidate depth hypothesis state| ≤
          queueCandidateFiniteDepthSpan candidate depth :=
      queueCandidateFiniteDepthPotential_span candidate depth
    have hbase :=
      exists_stationaryApproximateTargetPolicyOPE_signedResidual_event
        (ι := QueueHypothesis) (τ := τRisk)
        (refreshEnvironment gamma)
        (markovBehaviorPolicyAsHistory behaviorPolicy) initial
        queueHypothesisTargetPolicy
        (queueHypothesisStationary (refreshEnvironment gamma))
        (queueHypothesisStationary_isInvariant (refreshEnvironment gamma))
        queueHypothesisScore queueHypothesisScore_mem_Icc
        (queueCandidateFiniteDepthPotential candidate depth)
        (B := queueCandidateFiniteDepthSpan candidate depth)
        (C := (3 / 2 : ℝ)) hB (by norm_num) hspan
        queueHypothesis_overlap queueHypothesis_ratioBound_three_halves
        (prior := queueHypothesisPrior) queueHypothesisPrior_isFullSupport
        (weight := riskWeight) hRiskWeight
        (lam := riskLam)
        (delta := deltaRisk * catalogWeight q)
        (mul_pos hdeltaRisk (hcatalogWeight.pos q))
        hRiskLam hRiskLamOne
    simpa only [mu, candidate, depth, structuredQueueOPEBoundary] using hbase
  let riskGood : κ → Set QueuePath := fun q ↦
    Classical.choose (hriskWitness q)
  have hriskGoodSpec (q : κ) := Classical.choose_spec (hriskWitness q)
  let riskBad : Set QueuePath := ⋃ q : κ, (riskGood q)ᶜ
  have hriskMass : mu.real riskBad ≤ deltaRisk := by
    dsimp only [riskBad]
    calc
      mu.real (⋃ q : κ, (riskGood q)ᶜ) ≤
          ∑ q : κ, mu.real ((riskGood q)ᶜ) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ q : κ, deltaRisk * catalogWeight q := by
        apply Finset.sum_le_sum
        intro q _hq
        exact (hriskGoodSpec q).1
      _ = deltaRisk := by
        rw [← Finset.mul_sum, hcatalogWeight.sum_one, mul_one]
  rcases exists_structuredCandidateTVConfidence_event
      (τ := τPersistence) gamma initial
      (weight := persistenceWeight) (lam := persistenceLam)
      (delta := deltaPersistence)
      hPersistenceWeight hdeltaPersistence
      hPersistenceLam hPersistenceLamOne with
    ⟨persistenceGood, hpersistenceMass, hpersistenceGood⟩
  let goodEvent : Set QueuePath := riskBadᶜ ∩ persistenceGood
  refine ⟨goodEvent, ?_, ?_⟩
  · have hunion := measureReal_union_le
      (μ := mu) riskBad persistenceGoodᶜ
    calc
      mu.real goodEventᶜ =
          mu.real (riskBad ∪ persistenceGoodᶜ) := by
        congr 1
        ext path
        by_cases hrisk : path ∈ riskBad <;>
          by_cases hpersistence : path ∈ persistenceGood <;>
            simp [goodEvent, hrisk, hpersistence]
      _ ≤ mu.real riskBad + mu.real persistenceGoodᶜ := hunion
      _ ≤ deltaRisk + deltaPersistence :=
        add_le_add hriskMass hpersistenceMass
  · intro path hpath n hn q jRisk jPersistence posterior hposterior
    let candidate := (catalog q).1
    let depth := (catalog q).2
    let B := queueCandidateFiniteDepthSpan candidate depth
    let eta := structuredCandidateTVBudget candidate persistenceWeight
      persistenceLam deltaPersistence jPersistence n path
    have hpathRisk : path ∈ riskGood q := by
      by_contra hnot
      exact hpath.1 (Set.mem_iUnion.mpr ⟨q, by simpa using hnot⟩)
    have hraw := (hriskGoodSpec q).2
      path hpathRisk jRisk posterior hposterior n hn
    have hpathPersistence : path ∈ persistenceGood := hpath.2
    have hrowStrict := hpersistenceGood
      path hpathPersistence jPersistence n hn candidate
    have hrow : ∀ state action,
        finitePMFTotalVariation
            (refreshEnvironment gamma state action)
            (candidateEnvironment candidate state action) ≤ eta := by
      intro state action
      exact (hrowStrict state action).le
    have heta : 0 ≤ eta :=
      (finitePMFTotalVariation_nonneg
        (refreshEnvironment gamma (0 : PhysicalState) (0 : Action))
        (candidateEnvironment candidate (0 : PhysicalState) (0 : Action))).trans
          (hrow 0 0)
    have hresidual : ∀ hypothesis state,
        |approximateTargetPolicyPoissonResidual
            (refreshEnvironment gamma)
            (queueHypothesisTargetPolicy hypothesis)
            (queueHypothesisStationary
              (refreshEnvironment gamma) hypothesis)
            (queueHypothesisScore hypothesis)
            (queueCandidateFiniteDepthPotential
              candidate depth hypothesis) state| ≤
          structuredQueueFiniteDepthResidual candidate depth eta := by
      intro hypothesis state
      have hrobust :=
        abs_approximateTargetPolicyPoissonResidual_le_candidateOscillation
          (refreshEnvironment gamma) (candidateEnvironment candidate)
          (queueHypothesisTargetPolicy hypothesis)
          (queueHypothesisStationary
            (refreshEnvironment gamma) hypothesis)
          (queueHypothesisStationary_isInvariant
            (refreshEnvironment gamma) hypothesis)
          heta (queueHypothesisScore_mem_Icc hypothesis)
          (queueCandidateFiniteDepthPotential_span
            candidate depth hypothesis) hrow state
      have hosc :=
        finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
          (candidateEnvironment candidate)
          (queueHypothesisTargetPolicy hypothesis)
          (queueHypothesisReference hypothesis)
          (queueHypothesisScore hypothesis) depth
          (candidateGamma_mem_Ico candidate).1
          (candidateTargetPolicyKernel_isOscillationContraction
            candidate (queueHypothesisTargetPolicy hypothesis))
          (by
            simpa [queueHypothesisTargetPolicy, queueHypothesisReference,
              queueHypothesisScore] using
              fixedBrierScore_centeredTargetPolicyRowRisk_finiteOscillation_le_one
                candidate hypothesis.1 uniformStateReference hypothesis.2)
      have hcombined := hrobust.trans (add_le_add hosc (le_refl _))
      simpa only [structuredQueueFiniteDepthResidual, B, eta, mul_one] using
        hcombined
    have hnpos : 0 < n := by omega
    have hnegative :=
      neg_stationaryTargetPolicyPosteriorResidualAverage_le
        (refreshEnvironment gamma)
        queueHypothesisTargetPolicy
        (queueHypothesisStationary (refreshEnvironment gamma))
        queueHypothesisScore
        (queueCandidateFiniteDepthPotential candidate depth)
        hresidual hposterior n hnpos path
    have hposteriorResidual :
        posteriorAverage posterior
            (fun _hypothesis : QueueHypothesis ↦
              structuredQueueFiniteDepthResidual candidate depth eta) =
          structuredQueueFiniteDepthResidual candidate depth eta := by
      unfold posteriorAverage
      rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
    rw [hposteriorResidual] at hnegative
    dsimp only [candidate, depth, B, eta] at hraw hnegative ⊢
    linarith

/-! ## Generated supports and fresh confidence allocations -/

/-- Seven depths frozen in the generated queue model. -/
abbrev QueueDepthIndex := Fin 7

private theorem depthGrid_length : depthGrid.length = 7 := rfl

/-- Generated depth selected by a depth-grid atom. -/
def queueDepth (index : QueueDepthIndex) : ℕ :=
  depthGrid.get (Fin.cast depthGrid_length.symm index)

/-- The three generated candidates crossed with the seven frozen depths. -/
abbrev QueueCandidateDepthIndex := CandidateIndex × QueueDepthIndex

/-- Concrete twenty-one-atom candidate--depth catalog. -/
def queueCandidateDepthCatalog
    (index : QueueCandidateDepthIndex) : CandidateIndex × ℕ :=
  (index.1, queueDepth index.2)

/-- Uniform confidence allocation over the twenty-one candidate--depth atoms.
This is a checked Lean allocation, not a generated model field. -/
def queueCandidateDepthWeight : QueueCandidateDepthIndex → ℝ :=
  finiteUniformRealPMF QueueCandidateDepthIndex

/-- The admissible prefix of the generated tilt grid.  The generated terminal
atom `1` is deliberately excluded because the event APIs require `lambda < 1`. -/
abbrev QueueStructuredTiltIndex := Fin 4

private theorem admissibleTiltGrid_length : (tiltGrid.take 4).length = 4 := rfl

/-- One of the four predeclared admissible queue tilts. -/
def queueStructuredTilt (index : QueueStructuredTiltIndex) : ℝ :=
  (((tiltGrid.take 4).get
    (Fin.cast admissibleTiltGrid_length.symm index) : ℚ) : ℝ)

/-- Uniform confidence allocation over the four admissible tilts. This is a
checked Lean allocation, not a generated model field. -/
def queueStructuredTiltWeight : QueueStructuredTiltIndex → ℝ :=
  finiteUniformRealPMF QueueStructuredTiltIndex

/-- The predeclared candidate--depth catalog has twenty-one atoms. -/
@[simp]
theorem queueCandidateDepth_card :
    Fintype.card QueueCandidateDepthIndex = 21 := by
  norm_num [QueueCandidateDepthIndex, CandidateIndex, QueueDepthIndex]

/-- Every candidate--depth atom receives mass `1 / 21`. -/
@[simp]
theorem queueCandidateDepthWeight_apply (index : QueueCandidateDepthIndex) :
    queueCandidateDepthWeight index = (1 / 21 : ℝ) := by
  norm_num [queueCandidateDepthWeight, finiteUniformRealPMF]

/-- The candidate--depth allocation has full support. -/
theorem queueCandidateDepthWeight_isFullSupport :
    IsFullSupportPMF queueCandidateDepthWeight :=
  finiteUniformRealPMF_isFullSupport QueueCandidateDepthIndex

/-- Every admissible tilt atom receives mass `1 / 4`. -/
@[simp]
theorem queueStructuredTiltWeight_apply (index : QueueStructuredTiltIndex) :
    queueStructuredTiltWeight index = (1 / 4 : ℝ) := by
  norm_num [queueStructuredTiltWeight, finiteUniformRealPMF,
    QueueStructuredTiltIndex]

/-- The admissible tilt allocation has full support. -/
theorem queueStructuredTiltWeight_isFullSupport :
    IsFullSupportPMF queueStructuredTiltWeight :=
  finiteUniformRealPMF_isFullSupport QueueStructuredTiltIndex

/-- Every predeclared admissible tilt is positive. -/
theorem queueStructuredTilt_pos (index : QueueStructuredTiltIndex) :
    0 < queueStructuredTilt index := by
  fin_cases index <;>
    norm_num [queueStructuredTilt, admissibleTiltGrid_length,
      ControlledQueueData.tiltGrid]

/-- Every predeclared admissible tilt is strictly below one. -/
theorem queueStructuredTilt_lt_one (index : QueueStructuredTiltIndex) :
    queueStructuredTilt index < 1 := by
  fin_cases index <;>
    norm_num [queueStructuredTilt, admissibleTiltGrid_length,
      ControlledQueueData.tiltGrid]

/-- Concrete structured queue OPE boundary for a frozen candidate--depth atom. -/
def queueStructuredOPEBoundary
    (q : QueueCandidateDepthIndex)
    (jRisk : QueueStructuredTiltIndex)
    (posterior : QueueHypothesis → ℝ)
    (n : ℕ) (path : QueuePath) : ℝ :=
  structuredQueueOPEBoundary
    (queueCandidateDepthCatalog q).1
    (queueCandidateDepthCatalog q).2
    queueStructuredTiltWeight queueStructuredTilt
    (queueRiskFailureBudget * queueCandidateDepthWeight q)
    jRisk posterior n path

/-- Concrete path-dependent residual for a frozen candidate--depth atom. -/
def queueStructuredFiniteDepthResidual
    (q : QueueCandidateDepthIndex)
    (jPersistence : QueueStructuredTiltIndex)
    (n : ℕ) (path : QueuePath) : ℝ :=
  structuredQueueFiniteDepthResidual
    (queueCandidateDepthCatalog q).1
    (queueCandidateDepthCatalog q).2
    (structuredCandidateTVBudget
      (queueCandidateDepthCatalog q).1
      queueStructuredTiltWeight queueStructuredTilt
      queueTransitionFailureBudget jPersistence n path)

/-- One `19 / 20` outer event supports adaptive selection from all three
generated candidates, seven frozen depths, four risk tilts, four persistence
tilts, twelve-hypothesis posteriors, and every time `n >= 2`. -/
theorem exists_controlledQueueStructuredAdaptiveOPE_event
    (gamma : PersistenceParameter) (initial : Observation) :
    ∃ goodEvent : Set QueuePath,
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        ∀ q : QueueCandidateDepthIndex,
          ∀ jRisk jPersistence : QueueStructuredTiltIndex,
            ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
              stationaryTargetPolicyPosteriorRisk
                  (refreshEnvironment gamma)
                  queueHypothesisTargetPolicy
                  (queueHypothesisStationary (refreshEnvironment gamma))
                  queueHypothesisScore posterior <
                queueStructuredOPEBoundary
                    q jRisk posterior n path +
                  queueStructuredFiniteDepthResidual
                    q jPersistence n path := by
  rcases exists_structuredControlledQueueFiniteCatalogOPE_event
      gamma initial queueCandidateDepthCatalog
      queueCandidateDepthWeight_isFullSupport
      queueStructuredTiltWeight_isFullSupport
      queueStructuredTilt_pos queueStructuredTilt_lt_one
      queueStructuredTiltWeight_isFullSupport
      queueStructuredTilt_pos queueStructuredTilt_lt_one
      queueRiskFailureBudget_pos queueTransitionFailureBudget_pos with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · norm_num [queueRiskFailureBudget, queueTransitionFailureBudget] at hmass ⊢
    exact hmass
  · intro path hpath n hn q jRisk jPersistence posterior hposterior
    have h := hgood path hpath n hn q jRisk jPersistence posterior hposterior
    simpa only [queueStructuredOPEBoundary,
      queueStructuredFiniteDepthResidual] using h

/-- Explicit substitution form of the structured queue event.  Every selector
is restricted to a catalog fixed before the event. -/
theorem exists_selectedControlledQueueStructuredAdaptiveOPE_event
    (gamma : PersistenceParameter) (initial : Observation)
    (selectCandidateDepth : QueuePath → ℕ → QueueCandidateDepthIndex)
    (selectRiskTilt selectPersistenceTilt :
      QueuePath → ℕ → QueueStructuredTiltIndex)
    (selectPosterior : QueuePath → ℕ → QueueHypothesis → ℝ)
    (hselectPosterior : ∀ path n, IsPMF (selectPosterior path n)) :
    ∃ goodEvent : Set QueuePath,
      (controlledTrajectoryMeasure
          (refreshEnvironment gamma)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment gamma)
            queueHypothesisTargetPolicy
            (queueHypothesisStationary (refreshEnvironment gamma))
            queueHypothesisScore (selectPosterior path n) <
          queueStructuredOPEBoundary
              (selectCandidateDepth path n)
              (selectRiskTilt path n)
              (selectPosterior path n) n path +
            queueStructuredFiniteDepthResidual
              (selectCandidateDepth path n)
              (selectPersistenceTilt path n) n path := by
  rcases exists_controlledQueueStructuredAdaptiveOPE_event
      gamma initial with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro path hpath n hn
  exact hgood path hpath n hn
    (selectCandidateDepth path n)
    (selectRiskTilt path n) (selectPersistenceTilt path n)
    (selectPosterior path n) (hselectPosterior path n)

end

end FormalSLT.Applications.ControlledQueue
