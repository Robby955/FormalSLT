/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryTargetPolicyApproximateOPE
import FormalSLT.StochasticDynamics.TrajectoryPACBayes

/-!
# Fixed-range stationary target-policy off-policy evaluation

This module combines the controlled importance-weighting and approximate
Poisson identities with the fixed-range trajectory PAC--Bayes certificate.
It is the non-variance-adaptive counterpart of
`StationaryTargetPolicyApproximateOPE`: the same normalized observed scores
and signed residual are used, but the stochastic term is the deterministic
sub-gamma correction

`lambda / (8 * (1 - lambda / 3))`.

The environment, behavior propensities, target-policy catalog, invariant
laws, potentials, and tilt catalog are fixed inputs.  The theorem does not
estimate a kernel, construct a potential, prove named-path event membership,
or compare the resulting width with an empirical-Bernstein width.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τ : Type*}
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Fixed-range target-policy OPE right-hand side for one declared tilt.
Unlike `stationaryTargetPolicyOPEBoundary`, this boundary contains no
path-dependent empirical-variance term. -/
def stationaryTargetPolicyFixedRangeOPEBoundary
    [Fintype ι] [Fintype τ]
    (prior : ι → ℝ) (weight : τ → ℝ) (lam : τ → ℝ)
    (β : BehaviorPolicy Z A) (π : ι → MarkovTargetPolicy Z A)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (B C : ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (j : τ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  C * (1 + 2 * B) *
      (stationaryTargetPolicyPosteriorEmpiricalScore
          β π score potential B C posterior n x +
        lam j / (8 * (1 - lam j / 3)) +
        (klDiv posterior prior + Real.log (1 / (delta * weight j))) /
          ((n : ℝ) * lam j)) - B

omit [Nonempty Z] in
/-- The trajectory conditional-risk target for normalized controlled Poisson
scores is exactly the affine stationary risk plus the encountered signed
approximate-Poisson residual. -/
theorem trajectoryPosteriorAverageConditionalRisk_controlledPoissonScore_eq
    [Fintype ι]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (π : ι → MarkovTargetPolicy Z A) (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hoverlap : ∀ i, ControlledPolicyOverlap
      β (markovTargetPolicyAsHistory (π i)))
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → ControlledObservation Z A) :
    trajectoryPosteriorAverageConditionalRisk
        (controlledPrefixKernel P β)
        (fun i ↦ controlledNormalizedImportanceScore β
          (markovTargetPolicyAsHistory (π i))
          (targetPolicyPoissonControlledScore
            (score i) (potential i) B) C)
        posterior n x =
      (stationaryTargetPolicyPosteriorRisk
          P π stationary score posterior +
        stationaryTargetPolicyPosteriorResidualAverage
          P π stationary score potential posterior n x + B) /
        (C * (1 + 2 * B)) := by
  rw [←
    posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean_approximate
      P π stationary score potential hB hC posterior hposterior n hn x]
  unfold trajectoryPosteriorAverageConditionalRisk
    trajectoryAverageConditionalRisk posteriorAverage runningMean runningSum
    forwardPrefixMean
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  simpa only [stationaryTargetPolicyPredictableMean] using
    conditionalTrajectoryRisk_controlledNormalizedImportanceScore
      P β (markovTargetPolicyAsHistory (π i))
        (targetPolicyPoissonControlledScore (score i) (potential i) B)
        C (hoverlap i) k x

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] in
/-- The trajectory empirical-risk target for normalized controlled Poisson
scores is the observed target-policy OPE score average. -/
theorem trajectoryPosteriorEmpiricalPrequentialRisk_controlledPoissonScore_eq
    [Fintype ι]
    (β : BehaviorPolicy Z A) (π : ι → MarkovTargetPolicy Z A)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (B C : ℝ)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) :
    trajectoryPosteriorEmpiricalPrequentialRisk
        (fun i ↦ controlledNormalizedImportanceScore β
          (markovTargetPolicyAsHistory (π i))
          (targetPolicyPoissonControlledScore
            (score i) (potential i) B) C)
        posterior n x =
      stationaryTargetPolicyPosteriorEmpiricalScore
        β π score potential B C posterior n x := by
  rfl

omit [Nonempty Z] in
/-- Signed-residual fixed-range stationary target-policy OPE.

One outer event is simultaneous over positive times, posterior PMFs, and the
fixed finite tilt catalog.  The approximate-Poisson residual remains explicit
so a second event may provide a pathwise envelope without changing the risk
event.  The invariant-law premise is retained to identify the supplied laws as
stationary and to match the approximate-OPE interface; the concentration proof
uses the explicit signed-residual identity and does not otherwise consume that
premise. -/
theorem exists_stationaryApproximateTargetPolicyFixedRangeOPE_signedResidual_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : ι → MarkovTargetPolicy Z A) (stationary : ι → PMF Z)
    (hinvariant : ∀ i, IsInvariantPMF
      (targetPolicyKernel P (π i)) (stationary i))
    (score : ι → TargetPolicyTransitionScore Z A)
    (hscore : ∀ i z a y, score i z a y ∈ Set.Icc (0 : ℝ) 1)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hspan : ∀ i z y, |potential i y - potential i z| ≤ B)
    (hoverlap : ∀ i, ControlledPolicyOverlap
      β (markovTargetPolicyAsHistory (π i)))
    (hratio : ∀ i, ControlledPolicyRatioBound
      β (markovTargetPolicyAsHistory (π i)) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P β initial).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 0 < n →
              stationaryTargetPolicyPosteriorRisk
                  P π stationary score posterior <
                stationaryTargetPolicyFixedRangeOPEBoundary
                    prior weight lam β π score potential B C
                      posterior delta j n x -
                  stationaryTargetPolicyPosteriorResidualAverage
                    P π stationary score potential posterior n x := by
  -- Invariance supplies the stationary interpretation.  The concentration
  -- algebra consumes the explicit approximate-Poisson identity below.
  let _ := hinvariant
  have hcorrected : ∀ i n u a y,
      targetPolicyPoissonControlledScore
          (score i) (potential i) B n u a y ∈ Set.Icc (0 : ℝ) 1 := by
    intro i n u a y
    exact targetPolicyPoissonControlledScore_mem_Icc
      hB (hscore i) (hspan i) n u a y
  have hnormalized : ∀ i n u next,
      controlledNormalizedImportanceScore β
          (markovTargetPolicyAsHistory (π i))
          (targetPolicyPoissonControlledScore
            (score i) (potential i) B) C n u next ∈
        Set.Icc (0 : ℝ) 1 := by
    intro i n u next
    exact controlledNormalizedImportanceScore_mem_Icc
      (hoverlap i) (hratio i) hC (hcorrected i) n u next
  rcases trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
      (ι := ι) (τ := τ) (Z := ControlledObservation Z A)
      (controlledPrefixKernel P β) initial
      (score := fun i ↦ controlledNormalizedImportanceScore β
        (markovTargetPolicyAsHistory (π i))
        (targetPolicyPoissonControlledScore
          (score i) (potential i) B) C)
      hnormalized hprior hweight hdelta hlam hlam_three with
    ⟨exceptionalEvent, _hmeasurable, hmass, hgood⟩
  refine ⟨exceptionalEventᶜ, ?_, ?_⟩
  · simpa [controlledTrajectoryMeasure] using hmass
  · intro x hx j posterior hposterior n hn
    have hbase := hgood x (by simpa using hx) j posterior hposterior n hn
    rw [trajectoryPosteriorAverageConditionalRisk_controlledPoissonScore_eq
      P β π stationary score potential hB hC hoverlap
        posterior hposterior n hn x] at hbase
    rw [trajectoryPosteriorEmpiricalPrequentialRisk_controlledPoissonScore_eq]
      at hbase
    have hden : 0 < C * (1 + 2 * B) :=
      mul_pos hC (by linarith)
    have hscaled := (div_lt_iff₀ hden).mp hbase
    unfold stationaryTargetPolicyFixedRangeOPEBoundary
    linarith

omit [Nonempty Z] in
/-- Fixed-range approximate-Poisson OPE with a supplied pointwise residual
envelope. -/
theorem exists_stationaryApproximateTargetPolicyFixedRangeOPE_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : ι → MarkovTargetPolicy Z A) (stationary : ι → PMF Z)
    (hinvariant : ∀ i, IsInvariantPMF
      (targetPolicyKernel P (π i)) (stationary i))
    (score : ι → TargetPolicyTransitionScore Z A)
    (hscore : ∀ i z a y, score i z a y ∈ Set.Icc (0 : ℝ) 1)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hspan : ∀ i z y, |potential i y - potential i z| ≤ B)
    {residualEnvelope : ι → ℝ}
    (hresidual : ∀ i z,
      |approximateTargetPolicyPoissonResidual
        P (π i) (stationary i) (score i) (potential i) z| ≤
          residualEnvelope i)
    (hoverlap : ∀ i, ControlledPolicyOverlap
      β (markovTargetPolicyAsHistory (π i)))
    (hratio : ∀ i, ControlledPolicyRatioBound
      β (markovTargetPolicyAsHistory (π i)) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_three : ∀ j, lam j < 3) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P β initial).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 0 < n →
              stationaryTargetPolicyPosteriorRisk
                  P π stationary score posterior <
                stationaryTargetPolicyFixedRangeOPEBoundary
                    prior weight lam β π score potential B C
                      posterior delta j n x +
                  posteriorAverage posterior residualEnvelope := by
  rcases
      exists_stationaryApproximateTargetPolicyFixedRangeOPE_signedResidual_event
        P β initial π stationary hinvariant score hscore potential
        hB hC hspan hoverlap hratio hprior hweight hdelta hlam hlam_three with
    ⟨goodEvent, hmass, hraw⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hbase := hraw x hx j posterior hposterior n hn
  have hres := neg_stationaryTargetPolicyPosteriorResidualAverage_le
    P π stationary score potential hresidual hposterior n hn x
  linarith

end

end FormalSLT.StochasticDynamics
