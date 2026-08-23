/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueContraction
import FormalSLT.StochasticDynamics.FiniteInvariantExistence
import FormalSLT.StochasticDynamics.StationaryTargetPolicyEmpiricalFiniteDepthOPE

/-!
# Fixed controlled-queue OPE catalog

This module fixes the twelve stationary queue hypotheses obtained by pairing
the four generated target policies with the three generated fixed Brier
predictors. It specializes the same-path empirical finite-depth target-policy
OPE theorem to the nominal candidate, the uniform physical-state reference,
contraction factor `3 / 4`, centered row-risk envelope `D = 1`, and importance
ratio cap `3 / 2`.

The true environment and finite depth remain fixed inputs to the event. The
left-hand stationary risks use the canonical invariant PMFs supplied by finite
state-space existence; no uniqueness or explicit stationary-risk value is
claimed. The event is simultaneous over all posterior PMFs and all times, but
still requires every augmented behavior row to have been visited at the
displayed horizon.

This is not a named-trace certificate, a good-event membership proof, a
data-selected candidate or depth, or a final numerical receipt. The two causal
Beta predictors are history dependent and remain outside this stationary
twelve-atom catalog.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL FormalSLT.StochasticDynamics
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData

noncomputable section

/-- Four generated target policies paired with three fixed Brier predictors. -/
abbrev QueueHypothesis := TargetPolicyIndex × FixedPredictorIndex

/-- The nominal candidate occupies row one of the frozen candidate table. -/
def nominalCandidateIndex : CandidateIndex := 1

/-- Typed nominal candidate environment. -/
def nominalCandidateEnvironment : PhysicalState → Action → PMF PhysicalState :=
  candidateEnvironment nominalCandidateIndex

/-- Target policy selected by a queue hypothesis. -/
def queueHypothesisTargetPolicy
    (hypothesis : QueueHypothesis) : MarkovTargetPolicy PhysicalState Action :=
  targetPolicy hypothesis.1

/-- Fixed Brier score selected by a queue hypothesis. -/
def queueHypothesisScore
    (hypothesis : QueueHypothesis) :
    TargetPolicyTransitionScore PhysicalState Action :=
  fixedBrierScore hypothesis.2

/-- Canonical invariant PMF for the true target-policy kernel. -/
def queueHypothesisStationary
    (P : PhysicalState → Action → PMF PhysicalState)
    (hypothesis : QueueHypothesis) : PMF PhysicalState :=
  finiteInvariantPMF (targetPolicyKernel P
    (queueHypothesisTargetPolicy hypothesis))

/-- Uniform physical-state reference used by every finite-depth potential. -/
def queueHypothesisReference (_hypothesis : QueueHypothesis) : PMF PhysicalState :=
  uniformStateReference

/-- Uniform prior over the twelve fixed queue hypotheses. -/
def queueHypothesisPrior : QueueHypothesis → ℝ :=
  finiteUniformRealPMF QueueHypothesis

/-- Uniform prior over augmented behavior-transition coordinates. -/
def queueTransitionPrior : TransitionCoordinate Observation → ℝ :=
  finiteUniformRealPMF (TransitionCoordinate Observation)

/-- Singleton risk-tilt allocation. -/
def queueRiskTiltWeight : Unit → ℝ := finiteUniformRealPMF Unit

/-- Singleton transition-tilt allocation. -/
def queueTransitionTiltWeight : Unit → ℝ := finiteUniformRealPMF Unit

/-- Fixed risk tilt used by the queue catalog. -/
def queueRiskTilt (_atom : Unit) : ℝ := 1 / 4

/-- Fixed transition-confidence tilt used by the queue catalog. -/
def queueTransitionTilt (_atom : Unit) : ℝ := 1 / 4

/-- Risk-event failure budget. -/
def queueRiskFailureBudget : ℝ := 1 / 40

/-- Transition-event failure budget. -/
def queueTransitionFailureBudget : ℝ := 1 / 40

/-- Fixed-depth potential catalog for the nominal candidate. -/
def queueHypothesisFiniteDepthPotential
    (depth : ℕ) : QueueHypothesis → PhysicalState → ℝ :=
  candidateTargetPolicyFiniteDepthPotential
    nominalCandidateEnvironment queueHypothesisTargetPolicy
    queueHypothesisReference queueHypothesisScore depth

/-- Empirical augmented-kernel budget against the nominal candidate. -/
def queueEmpiricalKernelTVBudget
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  empiricalCandidateKernelTVBudget
    (augmentedBehaviorKernel nominalCandidateEnvironment behaviorPolicy)
    queueTransitionPrior queueTransitionTiltWeight queueTransitionTilt
    queueTransitionFailureBudget () n path

/-- Specialized empirical finite-depth OPE boundary for the fixed queue
catalog. -/
def queueEmpiricalFiniteDepthOPEBoundary
    (depth : ℕ) (posterior : QueueHypothesis → ℝ)
    (n : ℕ) (path : ℕ → Observation) : ℝ :=
  stationaryTargetPolicyOPEBoundary
    queueHypothesisPrior queueRiskTiltWeight queueRiskTilt
    (markovBehaviorPolicyAsHistory behaviorPolicy)
    queueHypothesisTargetPolicy queueHypothesisScore
    (queueHypothesisFiniteDepthPotential depth)
    (finiteDepthPoissonClosedSpanBound (3 / 4 : ℝ) 1 depth)
    (3 / 2 : ℝ) posterior queueRiskFailureBudget () n path

/-- Specialized robust residual using the same-path empirical augmented-kernel
budget. -/
def queueEmpiricalFiniteDepthResidual
    (depth n : ℕ) (path : ℕ → Observation) : ℝ :=
  (3 / 4 : ℝ) ^ depth +
    4 * ((1 + finiteDepthPoissonClosedSpanBound
      (3 / 4 : ℝ) 1 depth) * queueEmpiricalKernelTVBudget n path)

/-- The nominal candidate has persistence weight `3 / 4`. -/
@[simp]
theorem nominalCandidateGamma_eq_three_fourths :
    candidateGamma nominalCandidateIndex = (3 / 4 : ℝ) := by
  norm_num [nominalCandidateIndex, candidateGamma,
    candidateGammaRat,
    ControlledQueueData.candidateGammaTable]

/-- The fixed hypothesis catalog has twelve atoms. -/
@[simp]
theorem queueHypothesis_card : Fintype.card QueueHypothesis = 12 := by
  norm_num [QueueHypothesis, TargetPolicyIndex, FixedPredictorIndex]

/-- The queue-hypothesis prior is exactly uniform with mass `1 / 12`. -/
@[simp]
theorem queueHypothesisPrior_apply (hypothesis : QueueHypothesis) :
    queueHypothesisPrior hypothesis = (1 / 12 : ℝ) := by
  norm_num [queueHypothesisPrior, finiteUniformRealPMF]

/-- The augmented transition-confidence catalog contains 48 source rows,
48 destination rows, and two indicator sides. -/
@[simp]
theorem queueTransitionCoordinate_card :
    Fintype.card (TransitionCoordinate Observation) = 4608 := by
  let coordinateEquiv :
      TransitionCoordinate Observation ≃
        Observation × (Observation × Bool) :=
    { toFun := fun coordinate ↦
        (coordinate.source, (coordinate.destination, coordinate.complement))
      invFun := fun coordinate ↦
        ⟨coordinate.1, coordinate.2.1, coordinate.2.2⟩
      left_inv := by
        intro coordinate
        cases coordinate
        rfl
      right_inv := by
        intro coordinate
        rcases coordinate with ⟨source, destination, complement⟩
        rfl }
  rw [Fintype.card_congr coordinateEquiv]
  norm_num [Observation, ControlledObservation, PhysicalState, Action]

/-- The fresh transition-coordinate prior has mass `1 / 4608` on every
coordinate. -/
@[simp]
theorem queueTransitionPrior_apply
    (coordinate : TransitionCoordinate Observation) :
    queueTransitionPrior coordinate = (1 / 4608 : ℝ) := by
  norm_num [queueTransitionPrior, finiteUniformRealPMF]

/-- The uniform twelve-atom prior has full support. -/
theorem queueHypothesisPrior_isFullSupport :
    IsFullSupportPMF queueHypothesisPrior :=
  finiteUniformRealPMF_isFullSupport QueueHypothesis

/-- The uniform transition-coordinate prior has full support. -/
theorem queueTransitionPrior_isFullSupport :
    IsFullSupportPMF queueTransitionPrior :=
  finiteUniformRealPMF_isFullSupport (TransitionCoordinate Observation)

/-- The singleton risk-tilt allocation has full support. -/
theorem queueRiskTiltWeight_isFullSupport :
    IsFullSupportPMF queueRiskTiltWeight :=
  finiteUniformRealPMF_isFullSupport Unit

/-- The singleton transition-tilt allocation has full support. -/
theorem queueTransitionTiltWeight_isFullSupport :
    IsFullSupportPMF queueTransitionTiltWeight :=
  finiteUniformRealPMF_isFullSupport Unit

/-- The fixed risk tilt is positive. -/
theorem queueRiskTilt_pos (atom : Unit) : 0 < queueRiskTilt atom := by
  cases atom
  norm_num [queueRiskTilt]

/-- The fixed risk tilt is below one. -/
theorem queueRiskTilt_lt_one (atom : Unit) : queueRiskTilt atom < 1 := by
  cases atom
  norm_num [queueRiskTilt]

/-- The fixed transition tilt is positive. -/
theorem queueTransitionTilt_pos (atom : Unit) :
    0 < queueTransitionTilt atom := by
  cases atom
  norm_num [queueTransitionTilt]

/-- The fixed transition tilt is below one. -/
theorem queueTransitionTilt_lt_one (atom : Unit) :
    queueTransitionTilt atom < 1 := by
  cases atom
  norm_num [queueTransitionTilt]

/-- The risk-event budget is positive. -/
theorem queueRiskFailureBudget_pos : 0 < queueRiskFailureBudget := by
  norm_num [queueRiskFailureBudget]

/-- The transition-event budget is positive. -/
theorem queueTransitionFailureBudget_pos :
    0 < queueTransitionFailureBudget := by
  norm_num [queueTransitionFailureBudget]

/-- The canonical true target-policy stationary witness is invariant. -/
theorem queueHypothesisStationary_isInvariant
    (P : PhysicalState → Action → PMF PhysicalState)
    (hypothesis : QueueHypothesis) :
    IsInvariantPMF
      (targetPolicyKernel P (queueHypothesisTargetPolicy hypothesis))
      (queueHypothesisStationary P hypothesis) :=
  finiteInvariantPMF_isInvariant _

/-- Every hypothesis score is bounded in `[0,1]`. -/
theorem queueHypothesisScore_mem_Icc
    (hypothesis : QueueHypothesis) (state : PhysicalState)
    (action : Action) (nextState : PhysicalState) :
    queueHypothesisScore hypothesis state action nextState ∈
      Set.Icc (0 : ℝ) 1 := by
  exact fixedBrierScore_mem_Icc hypothesis.2 state action nextState

/-- Every hypothesis target-policy kernel under the nominal candidate
contracts finite oscillation by `3 / 4`. -/
theorem queueHypothesis_nominal_isOscillationContraction
    (hypothesis : QueueHypothesis) :
    IsOscillationContraction
      (targetPolicyKernel nominalCandidateEnvironment
        (queueHypothesisTargetPolicy hypothesis))
      (3 / 4 : ℝ) := by
  have h := candidateTargetPolicyKernel_isOscillationContraction
    nominalCandidateIndex (queueHypothesisTargetPolicy hypothesis)
  rw [nominalCandidateGamma_eq_three_fourths] at h
  simpa [nominalCandidateEnvironment] using h

/-- The generic bounded-score certificate supplies `D = 1` for every queue
hypothesis under the nominal candidate. -/
theorem queueHypothesis_nominal_centeredRowRiskOscillation_le_one
    (hypothesis : QueueHypothesis) :
    finiteOscillation
        (centeredMarkovRowRisk
          (targetPolicyKernel nominalCandidateEnvironment
            (queueHypothesisTargetPolicy hypothesis))
          (queueHypothesisReference hypothesis)
          (targetPolicyRowScore nominalCandidateEnvironment
            (queueHypothesisTargetPolicy hypothesis)
            (queueHypothesisScore hypothesis))) ≤ 1 := by
  simpa [nominalCandidateEnvironment, queueHypothesisTargetPolicy,
    queueHypothesisReference, queueHypothesisScore] using
    fixedBrierScore_centeredTargetPolicyRowRisk_finiteOscillation_le_one
      nominalCandidateIndex hypothesis.1 uniformStateReference hypothesis.2

/-- Every queue-hypothesis target policy overlaps the generated behavior
policy. -/
theorem queueHypothesis_overlap (hypothesis : QueueHypothesis) :
    ControlledPolicyOverlap
      (markovBehaviorPolicyAsHistory behaviorPolicy)
      (markovTargetPolicyAsHistory
        (queueHypothesisTargetPolicy hypothesis)) := by
  simpa [queueHypothesisTargetPolicy] using
    behavior_targetPolicy_overlap hypothesis.1

/-- Every queue-hypothesis target policy obeys the generated ratio cap
`3 / 2`. -/
theorem queueHypothesis_ratioBound_three_halves
    (hypothesis : QueueHypothesis) :
    ControlledPolicyRatioBound
      (markovBehaviorPolicyAsHistory behaviorPolicy)
      (markovTargetPolicyAsHistory
        (queueHypothesisTargetPolicy hypothesis))
      (3 / 2 : ℝ) := by
  simpa [queueHypothesisTargetPolicy] using
    behavior_targetPolicy_ratioBound_three_halves hypothesis.1

/-- One `19 / 20` outer event controls the twelve fixed queue hypotheses for
the nominal candidate and any depth fixed before the event.

The event is simultaneous over posterior PMFs and time. At the displayed time,
all 48 augmented source rows must have positive visit mass. -/
theorem exists_nominalControlledQueueEmpiricalFiniteDepthOPE_event
    (P : PhysicalState → Action → PMF PhysicalState)
    (initial : Observation) (depth : ℕ) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure P
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent,
        ∀ posterior : QueueHypothesis → ℝ, IsPMF posterior →
          ∀ n : ℕ, 2 ≤ n →
            (∀ current : Observation,
              0 < transitionVisitMass current n path) →
              stationaryTargetPolicyPosteriorRisk
                  P queueHypothesisTargetPolicy
                  (queueHypothesisStationary P)
                  queueHypothesisScore posterior <
                queueEmpiricalFiniteDepthOPEBoundary
                    depth posterior n path +
                  queueEmpiricalFiniteDepthResidual depth n path := by
  rcases
      exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event
        (ι := QueueHypothesis) (τRisk := Unit) (τTransition := Unit)
        P nominalCandidateEnvironment behaviorPolicy initial
        behaviorPolicy_apply_toReal
        queueHypothesisTargetPolicy
        (queueHypothesisStationary P) queueHypothesisReference
        (queueHypothesisStationary_isInvariant P)
        queueHypothesisScore queueHypothesisScore_mem_Icc
        (alpha := (3 / 4 : ℝ)) (D := (1 : ℝ)) (C := (3 / 2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        queueHypothesis_nominal_isOscillationContraction
        queueHypothesis_nominal_centeredRowRiskOscillation_le_one
        depth queueHypothesis_overlap
        queueHypothesis_ratioBound_three_halves
        queueHypothesisPrior_isFullSupport
        queueRiskTiltWeight_isFullSupport
        queueRiskTilt_pos queueRiskTilt_lt_one
        queueTransitionPrior_isFullSupport
        queueTransitionTiltWeight_isFullSupport
        queueTransitionTilt_pos queueTransitionTilt_lt_one
        queueRiskFailureBudget_pos queueTransitionFailureBudget_pos with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · norm_num [queueRiskFailureBudget, queueTransitionFailureBudget] at hmass ⊢
    exact hmass
  · intro path hpath posterior hposterior n hn hvisit
    have h := hgood path hpath () () posterior hposterior n hn hvisit
    have hresidual :
        posteriorAverage posterior
            (fun _hypothesis : QueueHypothesis ↦
              queueEmpiricalFiniteDepthResidual depth n path) =
          queueEmpiricalFiniteDepthResidual depth n path := by
      unfold posteriorAverage
      rw [← Finset.sum_mul, hposterior.sum_one, one_mul]
    have hspecialized :
        stationaryTargetPolicyPosteriorRisk
            P queueHypothesisTargetPolicy (queueHypothesisStationary P)
              queueHypothesisScore posterior <
          queueEmpiricalFiniteDepthOPEBoundary depth posterior n path +
            posteriorAverage posterior
              (fun _hypothesis : QueueHypothesis ↦
                queueEmpiricalFiniteDepthResidual depth n path) := by
      simpa only [queueEmpiricalFiniteDepthOPEBoundary,
        queueHypothesisFiniteDepthPotential,
        queueEmpiricalFiniteDepthResidual, queueEmpiricalKernelTVBudget,
        mul_one] using h
    rw [hresidual] at hspecialized
    exact hspecialized

end

end FormalSLT.Applications.ControlledQueue
