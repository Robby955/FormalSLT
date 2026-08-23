/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryTargetPolicyApproximateOPE

/-!
# Fixed-candidate finite-depth robust target-policy OPE

This module composes the approximate stationary target-policy OPE event with
a finite-depth Poisson potential built from a fixed candidate environment.
For candidate target-kernel contraction coefficient `alpha`, centered
row-risk oscillation bound `D`, depth `m`, and uniform action-conditioned
environment-row total-variation radius `etaEnv`, the potential span is

`B_m = finiteDepthPoissonClosedSpanBound alpha D m`

and the pointwise true-kernel residual envelope is

`alpha ^ m * D + 2 * ((1 + B_m) * etaEnv)`.

The residual envelope is added outside the existing importance-weighted OPE
boundary, so it is not multiplied by the policy-ratio bound `C`.  One outer
event is simultaneous over path, finite tilt atom, posterior PMF, and time.

The true and candidate environments, behavior policy, target-policy catalog,
true invariant PMFs, candidate reference PMFs, score catalog, contraction and
misspecification certificates, and depth are fixed before the event.  This
module does not estimate or select a candidate kernel, construct invariant
laws, infer the row-TV radius from data, intersect an empirical transition
event, or license candidate or depth selection after observing the path.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τ : Type*}
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The depth-`m` candidate Poisson potential for each target policy, centered
using a fixed candidate reference PMF.  Candidate-reference invariance is not
required by the finite-depth construction. -/
def candidateTargetPolicyFiniteDepthPotential
    (Q : Z → A → PMF Z)
    (π : ι → MarkovTargetPolicy Z A)
    (reference : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (m : ℕ) : ι → Z → ℝ :=
  fun i ↦
    finiteDepthPoissonPotential
      (targetPolicyKernel Q (π i))
      (reference i)
      (targetPolicyRowScore Q (π i) (score i))
      m

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Finite-depth contraction controls the oscillation of the candidate
target-policy Poisson drift by the terminal geometric residual
`alpha ^ m * D`. -/
lemma finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
    (Q : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (reference : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (m : ℕ) {alpha D : ℝ}
    (halpha : 0 ≤ alpha)
    (hcontract :
      IsOscillationContraction (targetPolicyKernel Q π) alpha)
    (hD :
      finiteOscillation
        (centeredMarkovRowRisk
          (targetPolicyKernel Q π) reference
          (targetPolicyRowScore Q π score)) ≤ D) :
    finiteOscillation
      (targetPolicyPoissonDrift Q π score
        (finiteDepthPoissonPotential
          (targetPolicyKernel Q π) reference
          (targetPolicyRowScore Q π score) m)) ≤
      alpha ^ m * D := by
  have hdrift :
      targetPolicyPoissonDrift Q π score
          (finiteDepthPoissonPotential
            (targetPolicyKernel Q π) reference
            (targetPolicyRowScore Q π score) m) =
        markovPoissonDrift
          (targetPolicyKernel Q π)
          (targetPolicyRowScore Q π score)
          (finiteDepthPoissonPotential
            (targetPolicyKernel Q π) reference
            (targetPolicyRowScore Q π score) m) := by
    funext state
    exact targetPolicyPoissonDrift_eq_markovPoissonDrift
      Q π score _ state
  rw [hdrift]
  exact finiteOscillation_markovPoissonDrift_finiteDepth_le
    (targetPolicyKernel Q π) reference
    (targetPolicyRowScore Q π score) m
    halpha hcontract hD

/-- Fixed-candidate, fixed-depth robust target-policy OPE.

The candidate environment `Q`, reference PMFs, contraction certificate,
physical action-row radius, and depth `m` are deterministic inputs fixed
before the outer event.  On that event the result remains simultaneous over
the observed path, every declared tilt atom, every posterior PMF, and every
time `n >= 2`.  The robust residual is outside the OPE boundary and is not
multiplied by the importance-ratio bound `C`. -/
theorem exists_stationaryRobustCandidateFiniteDepthTargetPolicyOPE_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P Q : Z → A → PMF Z)
    (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : ι → MarkovTargetPolicy Z A)
    (stationary reference : ι → PMF Z)
    (hinvariant : ∀ i,
      IsInvariantPMF
        (targetPolicyKernel P (π i)) (stationary i))
    (score : ι → TargetPolicyTransitionScore Z A)
    (hscore : ∀ i z a y,
      score i z a y ∈ Set.Icc (0 : ℝ) 1)
    {alpha D etaEnv C : ℝ}
    (halpha : 0 ≤ alpha)
    (halpha_one : alpha < 1)
    (hDnonneg : 0 ≤ D)
    (hetaEnv : 0 ≤ etaEnv)
    (hC : 0 < C)
    (hcontract : ∀ i,
      IsOscillationContraction
        (targetPolicyKernel Q (π i)) alpha)
    (hD : ∀ i,
      finiteOscillation
        (centeredMarkovRowRisk
          (targetPolicyKernel Q (π i))
          (reference i)
          (targetPolicyRowScore Q (π i) (score i))) ≤ D)
    (hrowTV : ∀ state action,
      finitePMFTotalVariation
        (P state action) (Q state action) ≤ etaEnv)
    (m : ℕ)
    (hoverlap : ∀ i,
      ControlledPolicyOverlap
        β (markovTargetPolicyAsHistory (π i)))
    (hratio : ∀ i,
      ControlledPolicyRatioBound
        β (markovTargetPolicyAsHistory (π i)) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j)
    (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P β initial).real goodEventᶜ ≤ delta ∧
      ∀ x ∈ goodEvent, ∀ j : τ,
        ∀ posterior : ι → ℝ, IsPMF posterior →
          ∀ n : ℕ, 2 ≤ n →
            stationaryTargetPolicyPosteriorRisk
                P π stationary score posterior <
              stationaryTargetPolicyOPEBoundary
                prior weight lam β π score
                (candidateTargetPolicyFiniteDepthPotential
                  Q π reference score m)
                (finiteDepthPoissonClosedSpanBound alpha D m)
                C posterior delta j n x +
              posteriorAverage posterior
                (fun _i : ι ↦
                  alpha ^ m * D +
                    2 * ((1 +
                      finiteDepthPoissonClosedSpanBound alpha D m) *
                      etaEnv)) := by
  let B : ℝ := finiteDepthPoissonClosedSpanBound alpha D m
  have hB : 0 ≤ B := by
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed halpha_one m).symm]
    exact finiteDepthPoissonSpanBound_nonneg halpha hDnonneg m
  have hspan : ∀ i z y,
      |candidateTargetPolicyFiniteDepthPotential
          Q π reference score m i y -
        candidateTargetPolicyFiniteDepthPotential
          Q π reference score m i z| ≤ B := by
    intro i z y
    rw [show B = finiteDepthPoissonSpanBound alpha D m by
      dsimp [B]
      exact (finiteDepthPoissonSpanBound_closed halpha_one m).symm]
    exact finiteDepthPoissonPotential_span
      (targetPolicyKernel Q (π i)) (reference i)
      (targetPolicyRowScore Q (π i) (score i)) m
      halpha (hcontract i) (hD i) z y
  have hresidual : ∀ i z,
      |approximateTargetPolicyPoissonResidual
        P (π i) (stationary i) (score i)
          (candidateTargetPolicyFiniteDepthPotential
            Q π reference score m i) z| ≤
        alpha ^ m * D + 2 * ((1 + B) * etaEnv) := by
    intro i z
    have hrobust :=
      abs_approximateTargetPolicyPoissonResidual_le_candidateOscillation
        P Q (π i) (stationary i) (hinvariant i)
        hetaEnv (hscore i) (hspan i) hrowTV z
    have hosc :=
      finiteOscillation_targetPolicyPoissonDrift_finiteDepth_le
        Q (π i) (reference i) (score i) m
        halpha (hcontract i) (hD i)
    exact hrobust.trans (add_le_add hosc (le_refl _))
  have hbase := exists_stationaryApproximateTargetPolicyOPE_event
    P β initial π stationary hinvariant score hscore
    (candidateTargetPolicyFiniteDepthPotential Q π reference score m)
    hB hC hspan hresidual hoverlap hratio
    hprior hweight hdelta hlam hlam_one
  simpa only [B] using hbase

end

end FormalSLT.StochasticDynamics
