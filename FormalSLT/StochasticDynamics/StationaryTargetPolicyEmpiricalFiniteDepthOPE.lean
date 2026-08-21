/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledKernelTV
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence
import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustFiniteDepthOPE

/-!
# Empirical-kernel finite-depth target-policy OPE

This module intersects two time-uniform events under the same controlled path
law.  The first leaves the signed target-policy Poisson residual explicit.  The
second estimates every row of the augmented behavior kernel.  For a behavior
policy with exact mass `1 / 2` on every action, an augmented row-TV budget
`etaAug` yields the physical action-row budget `2 * etaAug`.  The resulting
fixed-candidate, fixed-depth residual is

`alpha ^ m * D + 4 * ((1 + B_m) * etaAug)`.

The candidate environment, target-policy catalog, reference PMFs, contraction
certificates, and depth are fixed before the event.  The event is simultaneous
over both finite tilt catalogs, posterior PMFs, and time.  Normalized empirical
transition control requires every augmented source row to have been visited at
the displayed horizon.

This module does not select the candidate or depth, construct invariant PMFs,
prove that a named path belongs to the event, or derive queue-specific
contraction, score, reference, or numerical certificates.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τRisk τTransition : Type*}
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Fixed-candidate, fixed-depth target-policy OPE with a same-path empirical
augmented-kernel radius.

The two failure budgets remain separate: `deltaRisk` appears in the OPE
boundary and `deltaTransition` in the empirical transition radius.  Their
events are intersected by a union bound, with no independence assumption. -/
theorem exists_stationaryEmpiricalRobustCandidateFiniteDepthTargetPolicyOPE_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τRisk] [DecidableEq τRisk] [Nonempty τRisk]
    [Fintype τTransition] [DecidableEq τTransition] [Nonempty τTransition]
    (P Q : Z → A → PMF Z)
    (beta : MarkovBehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (hbetaHalf : ∀ state action,
      (beta state action).toReal = (1 / 2 : ℝ))
    (pi : ι → MarkovTargetPolicy Z A)
    (stationary reference : ι → PMF Z)
    (hinvariant : ∀ i,
      IsInvariantPMF (targetPolicyKernel P (pi i)) (stationary i))
    (score : ι → TargetPolicyTransitionScore Z A)
    (hscore : ∀ i state action nextState,
      score i state action nextState ∈ Set.Icc (0 : ℝ) 1)
    {alpha D C : ℝ}
    (halpha : 0 ≤ alpha)
    (halpha_one : alpha < 1)
    (hDnonneg : 0 ≤ D)
    (hC : 0 < C)
    (hcontract : ∀ i,
      IsOscillationContraction (targetPolicyKernel Q (pi i)) alpha)
    (hD : ∀ i,
      finiteOscillation
        (centeredMarkovRowRisk
          (targetPolicyKernel Q (pi i))
          (reference i)
          (targetPolicyRowScore Q (pi i) (score i))) ≤ D)
    (m : ℕ)
    (hoverlap : ∀ i,
      ControlledPolicyOverlap
        (markovBehaviorPolicyAsHistory beta)
        (markovTargetPolicyAsHistory (pi i)))
    (hratio : ∀ i,
      ControlledPolicyRatioBound
        (markovBehaviorPolicyAsHistory beta)
        (markovTargetPolicyAsHistory (pi i)) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τRisk → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τRisk → ℝ}
    (hlam : ∀ j, 0 < lam j)
    (hlam_one : ∀ j, lam j < 1)
    {transitionPrior : TransitionCoordinate (ControlledObservation Z A) → ℝ}
    (htransitionPrior : IsFullSupportPMF transitionPrior)
    {transitionWeight : τTransition → ℝ}
    (htransitionWeight : IsFullSupportPMF transitionWeight)
    {transitionLam : τTransition → ℝ}
    (htransitionLam : ∀ k, 0 < transitionLam k)
    (htransitionLam_one : ∀ k, transitionLam k < 1)
    {deltaRisk deltaTransition : ℝ}
    (hdeltaRisk : 0 < deltaRisk)
    (hdeltaTransition : 0 < deltaTransition) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P
          (markovBehaviorPolicyAsHistory beta) initial).real goodEventᶜ ≤
        deltaRisk + deltaTransition ∧
      ∀ x ∈ goodEvent, ∀ jRisk : τRisk, ∀ kTransition : τTransition,
        ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ, 2 ≤ n →
            (∀ current : ControlledObservation Z A,
              0 < transitionVisitMass current n x) →
              let etaAug := empiricalCandidateKernelTVBudget
                (augmentedBehaviorKernel Q beta)
                transitionPrior transitionWeight transitionLam
                deltaTransition kTransition n x
              stationaryTargetPolicyPosteriorRisk
                  P pi stationary score posterior <
                stationaryTargetPolicyOPEBoundary
                    prior weight lam
                    (markovBehaviorPolicyAsHistory beta)
                    pi score
                    (candidateTargetPolicyFiniteDepthPotential
                      Q pi reference score m)
                    (finiteDepthPoissonClosedSpanBound alpha D m)
                    C posterior deltaRisk jRisk n x +
                  posteriorAverage posterior
                    (fun _i : ι ↦
                      alpha ^ m * D +
                        4 * ((1 +
                          finiteDepthPoissonClosedSpanBound alpha D m) *
                          etaAug)) := by
  let B : ℝ := finiteDepthPoissonClosedSpanBound alpha D m
  have hB : 0 ≤ B := by
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed halpha_one m).symm]
    exact finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hspan : ∀ i state nextState,
      |candidateTargetPolicyFiniteDepthPotential
          Q pi reference score m i nextState -
        candidateTargetPolicyFiniteDepthPotential
          Q pi reference score m i state| ≤ B := by
    intro i state nextState
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed halpha_one m).symm]
    exact finiteDepthPoissonPotential_span
      (targetPolicyKernel Q (pi i)) (reference i)
      (targetPolicyRowScore Q (pi i) (score i)) m
      halpha (hcontract i) (hD i) state nextState
  letI : Nonempty (ControlledObservation Z A) := ⟨initial⟩
  rcases exists_stationaryApproximateTargetPolicyOPE_signedResidual_event
      P (markovBehaviorPolicyAsHistory beta) initial
      pi stationary hinvariant score hscore
      (candidateTargetPolicyFiniteDepthPotential Q pi reference score m)
      hB hC hspan hoverlap hratio
      hprior hweight hdeltaRisk hlam hlam_one with
    ⟨riskGood, hriskMass, hriskGood⟩
  rcases exists_empiricalCandidateKernelTV_event
      (augmentedBehaviorKernel P beta) initial
      htransitionPrior htransitionWeight hdeltaTransition
      htransitionLam htransitionLam_one with
    ⟨transitionGood, htransitionMass, htransitionGood⟩
  have htransitionMassControlled :
      (controlledTrajectoryMeasure P
          (markovBehaviorPolicyAsHistory beta) initial).real
          transitionGoodᶜ ≤ deltaTransition := by
    rw [controlledTrajectoryMeasure_markovBehaviorPolicy]
    exact htransitionMass
  let goodEvent := riskGood ∩ transitionGood
  refine ⟨goodEvent, ?_, ?_⟩
  · have hunion := measureReal_union_le
      (μ := controlledTrajectoryMeasure P
        (markovBehaviorPolicyAsHistory beta) initial)
      riskGoodᶜ transitionGoodᶜ
    calc
      (controlledTrajectoryMeasure P
          (markovBehaviorPolicyAsHistory beta) initial).real goodEventᶜ =
          (controlledTrajectoryMeasure P
            (markovBehaviorPolicyAsHistory beta) initial).real
              (riskGoodᶜ ∪ transitionGoodᶜ) := by
        congr 1
        ext path
        by_cases hrisk : path ∈ riskGood <;>
          by_cases htransition : path ∈ transitionGood <;>
            simp [goodEvent, hrisk, htransition]
      _ ≤ (controlledTrajectoryMeasure P
            (markovBehaviorPolicyAsHistory beta) initial).real riskGoodᶜ +
          (controlledTrajectoryMeasure P
            (markovBehaviorPolicyAsHistory beta) initial).real
              transitionGoodᶜ := hunion
      _ ≤ deltaRisk + deltaTransition :=
        add_le_add hriskMass htransitionMassControlled
  · intro x hx jRisk kTransition posterior hposterior n hn hvisit
    have hxRisk : x ∈ riskGood := hx.1
    have hxTransition : x ∈ transitionGood := hx.2
    let etaAug : ℝ := empiricalCandidateKernelTVBudget
      (augmentedBehaviorKernel Q beta)
      transitionPrior transitionWeight transitionLam
      deltaTransition kTransition n x
    have hrowAug : ∀ current : ControlledObservation Z A,
        finitePMFTotalVariation
            (augmentedBehaviorKernel P beta current)
            (augmentedBehaviorKernel Q beta current) ≤ etaAug := by
      exact htransitionGood x hxTransition kTransition n hn hvisit
        (augmentedBehaviorKernel Q beta)
    have hetaAug : 0 ≤ etaAug :=
      (finitePMFTotalVariation_nonneg
        (augmentedBehaviorKernel P beta initial)
        (augmentedBehaviorKernel Q beta initial)).trans (hrowAug initial)
    have hrowEnvDiv := environmentKernel_rowTV_le_div_behaviorFloor
      P Q beta (behaviorFloor := (1 / 2 : ℝ)) (eta := etaAug)
      (by norm_num)
      (by
        intro state action
        rw [hbetaHalf state action])
      hrowAug
    have hrowEnv : ∀ state action,
        finitePMFTotalVariation (P state action) (Q state action) ≤
          2 * etaAug := by
      intro state action
      have hrow := hrowEnvDiv state action
      calc
        finitePMFTotalVariation (P state action) (Q state action) ≤
            etaAug / (1 / 2 : ℝ) := hrow
        _ = 2 * etaAug := by ring
    have hetaEnv : 0 ≤ 2 * etaAug :=
      mul_nonneg (by norm_num) hetaAug
    have hresidual : ∀ i state,
        |approximateTargetPolicyPoissonResidual
          P (pi i) (stationary i) (score i)
            (candidateTargetPolicyFiniteDepthPotential
              Q pi reference score m i) state| ≤
          alpha ^ m * D + 4 * ((1 + B) * etaAug) := by
      intro i state
      have hrobust :=
        abs_approximateTargetPolicyPoissonResidual_le_candidateOscillation
          P Q (pi i) (stationary i) (hinvariant i)
          hetaEnv (hscore i) (hspan i) hrowEnv state
      have hosc :=
        finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
          Q (pi i) (reference i) (score i) m
          halpha (hcontract i) (hD i)
      have hbound := hrobust.trans (add_le_add hosc (le_refl _))
      calc
        _ ≤ alpha ^ m * D + 2 * ((1 + B) * (2 * etaAug)) := hbound
        _ = alpha ^ m * D + 4 * ((1 + B) * etaAug) := by ring
    have hrisk := hriskGood x hxRisk jRisk posterior hposterior n hn
    have hresidualAverage :=
      neg_stationaryTargetPolicyPosteriorResidualAverage_le
        P pi stationary score
        (candidateTargetPolicyFiniteDepthPotential Q pi reference score m)
        hresidual hposterior n (by omega) x
    dsimp only [etaAug]
    simpa only [B] using (show
      stationaryTargetPolicyPosteriorRisk
          P pi stationary score posterior <
        stationaryTargetPolicyOPEBoundary
            prior weight lam (markovBehaviorPolicyAsHistory beta)
            pi score
            (candidateTargetPolicyFiniteDepthPotential
              Q pi reference score m)
            B C posterior deltaRisk jRisk n x +
          posteriorAverage posterior
            (fun _i : ι ↦ alpha ^ m * D + 4 * ((1 + B) * etaAug)) by
      linarith)

end

end FormalSLT.StochasticDynamics
