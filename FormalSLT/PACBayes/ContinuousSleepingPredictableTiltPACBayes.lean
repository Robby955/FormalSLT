/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingEProcessMixture
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous PAC-Bayes bridge for finite-prefix predictable-tilt sleeping mixtures

This module combines three pieces that previously existed separately:

* time-varying predictable conditional means for bounded adapted observations;
* the observable forward-predictor quadratic penalty;
* an exact finite-prefix implementation of a countable sleeping strategy
  mixture.

For every hypothesis, the exact master contains only the active strategy
prefix and a closed-form polynomial sleeping tail.  A continuous prior over an
arbitrary measurable hypothesis space then produces one crossing event.  On
its complement, every eligible posterior and every active strategy atom obey
the same empirical-Bernstein PAC-Bayes inequality.

The selected strategy atom is global across the posterior: this module does
not place a posterior over model-strategy pairs or allow hypothesis-specific
tilts.  The polynomial wake-time allocation charges only logarithmic strategy
selection cost.

The normalized target is the strategy-weighted conditional mean encountered
along the monitored path.  With a time-varying strategy this is not the
ordinary unweighted prefix risk.  A constant post-wake strategy gives an
ordinary suffix average, and the atom starting at zero gives the full prefix.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous
open scoped BigOperators

namespace FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-! ## Exact finite-prefix hypothesis-indexed master -/

/-- The exact sleeping predictable-mean master attached to one hypothesis. -/
def continuousSleepingForwardPredictableMeanMasterProcess
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) :
    Theta -> Nat -> Omega -> Real :=
  fun theta =>
    countableSleepingForwardPredictableMeanMasterProcess
      (X theta) (mean theta) strategy

/-- One crossing event for the continuous prior mixture of finite-prefix
hypothesis-indexed masters. -/
def continuousSleepingPredictableTiltExceptionalEvent
    (prior : Measure Theta)
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) (delta : Real) : Set Omega :=
  {omega | exists n : Nat, 0 < n ∧
    (1 / delta) <=
      continuousPriorMixtureProcess prior
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy) n omega}

omit [MeasurableSpace Theta] in
/-- Each hypothesis-indexed finite-prefix master is an e-process. -/
theorem continuousSleepingForwardPredictableMeanMasterProcess_eProcess
    [IsProbabilityMeasure mu]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {L : Real}
    (hL1 : L < 1)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hstrategy_range : forall j k omega,
      strategy j k omega ∈ Set.Icc (0 : Real) L)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (theta : Theta) :
    EProcess mu F
      (continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta) := by
  unfold continuousSleepingForwardPredictableMeanMasterProcess
  exact
    countableSleepingForwardPredictableMeanMasterProcess_eProcess_of_bounded
      hL1 (hX_adapted theta) (hmean_adapted theta)
        hstrategy_adapted (hX_unit theta) hstrategy_range (hmean theta)

omit [MeasurableSpace Theta] in
/-- The unused polynomial tail makes every hypothesis-indexed master strictly
positive without additional stochastic assumptions. -/
theorem continuousSleepingForwardPredictableMeanMasterProcess_pos
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (n : Nat) (omega : Omega) :
    0 < continuousSleepingForwardPredictableMeanMasterProcess
      X mean strategy theta n omega := by
  unfold continuousSleepingForwardPredictableMeanMasterProcess
    countableSleepingForwardPredictableMeanMasterProcess
  exact countableSleepingProcessMixture_pos
    (fun _ _ _ => (Real.exp_pos _).le) n omega

/-! ## Selected-atom score -/

/-- Exact predictor-residual empirical-Bernstein score for one hypothesis and
one sleeping predictable strategy atom. -/
def continuousSleepingPredictableTiltScore
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    (sleepingStrategy strategy j k omega *
        (mean theta k omega - X theta k omega) -
      forwardEmpiricalBernsteinPsi
          (sleepingStrategy strategy j k omega) *
        (X theta k omega -
          forwardPredictorProcess (X theta) k omega) ^ 2)

omit [MeasurableSpace Theta] in
/-- Pathwise selected-atom competition against the finite-prefix master. -/
theorem continuousSleepingPredictableTiltScore_le_logMaster_sub_logWeight
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) {j n : Nat} (hjn : j < n) (omega : Omega) :
    continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega <=
      Real.log
          (continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy theta n omega) -
        Real.log (polynomialEpochWeight j) := by
  simpa [continuousSleepingPredictableTiltScore,
    continuousSleepingForwardPredictableMeanMasterProcess] using
      (forwardPredictableMeanScore_le_log_countableSleepingMaster_sub_logWeight
        (X theta) (mean theta) strategy hjn omega)

/-! ## Continuous-prior crossing control -/

/-- Ville control for the continuous prior mixture of finite-prefix masters.
The product-integrability assumptions are the explicit Fubini obligations. -/
theorem continuousSleepingPredictableTiltExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {L delta : Real}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hstrategy_range : forall j k omega,
      strategy j k omega ∈ Set.Icc (0 : Real) L)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy) n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy p.1 (n + 1) p.2) (prior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy p.2 (n + 1) p.1)
        ((mu.restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy p.2 n p.1) (mu.prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy p.2 n p.1)
        ((mu.restrict s).prod prior)) :
    mu.real (continuousSleepingPredictableTiltExceptionalEvent
      prior X mean strategy delta) <= delta := by
  let M := continuousSleepingForwardPredictableMeanMasterProcess
    X mean strategy
  have hfixed : ∀ᵐ theta ∂prior, Supermartingale (M theta) F mu :=
    Filter.Eventually.of_forall fun theta =>
      (continuousSleepingForwardPredictableMeanMasterProcess_eProcess
        hL1 hX_adapted hmean_adapted hstrategy_adapted hX_unit
          hstrategy_range hmean theta).supermartingale
  have hnonneg : forall theta n omega, 0 <= M theta n omega := by
    intro theta n omega
    exact (continuousSleepingForwardPredictableMeanMasterProcess_pos
      X mean strategy theta n omega).le
  have hmix := continuousPriorMixture_supermartingale
    (prior := prior) (M := M) h_adapted_mix h_integrable_mix
      hM_int_next hM_int_next_restrict hM_int_current
      hM_int_current_restrict hfixed hnonneg
  have hcross := continuousPriorMixture_crossing_bound
    (prior := prior) (M := M) hdelta hmix.1 hmix.2
      (fun theta omega =>
        (continuousSleepingForwardPredictableMeanMasterProcess_eProcess
          hL1 hX_adapted hmean_adapted hstrategy_adapted hX_unit
            hstrategy_range hmean theta).start_one omega)
  simpa [continuousSleepingPredictableTiltExceptionalEvent, M] using hcross

/-- Outside the one prior-mixture crossing event, every eligible posterior and
every positive reporting time satisfy the master log-wealth inequality. -/
theorem continuousSleepingPredictableTilt_allPosteriorsLogMaster_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingPredictableTiltExceptionalEvent
      prior X mean strategy delta) :
    forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 0 < n ->
        Integrable
          (fun theta => Real.log
            (continuousSleepingForwardPredictableMeanMasterProcess
              X mean strategy theta n omega)) posterior ->
        (∫ theta, Real.log
            (continuousSleepingForwardPredictableMeanMasterProcess
              X mean strategy theta n omega) ∂posterior) <
          (InformationTheory.klDiv posterior prior).toReal +
            Real.log (1 / delta) := by
  intro posterior hposterior hposterior_prior hllr n hn hlog_integrable
  letI : IsProbabilityMeasure posterior := hposterior
  let M := continuousSleepingForwardPredictableMeanMasterProcess
    X mean strategy
  have hM_pos : forall theta, 0 < M theta n omega := fun theta =>
    continuousSleepingForwardPredictableMeanMasterProcess_pos
      X mean strategy theta n omega
  have hmix_lt :
      continuousPriorMixtureProcess prior M n omega < 1 / delta := by
    apply lt_of_not_ge
    intro hcross
    apply homega
    exact ⟨n, hn, by simpa [M] using hcross⟩
  have hexp_eq :
      (fun theta => Real.exp (Real.log (M theta n omega))) =
        fun theta => M theta n omega := by
    funext theta
    exact Real.exp_log (hM_pos theta)
  have hexp_int : Integrable
      (fun theta => Real.exp (Real.log (M theta n omega))) prior := by
    rw [hexp_eq]
    simpa [M] using hprior_integrable n omega
  have hmix_pos : 0 < continuousPriorMixtureProcess prior M n omega := by
    have hpos := integral_exp_pos hexp_int
    rw [hexp_eq] at hpos
    simpa [continuousPriorMixtureProcess] using hpos
  have hdv := continuous_donsker_varadhan posterior prior
    hposterior_prior (fun theta => Real.log (M theta n omega))
      hexp_int (by simpa [M] using hlog_integrable) hllr
  rw [hexp_eq] at hdv
  have hdv' :
      (∫ theta, Real.log (M theta n omega) ∂posterior) <=
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (continuousPriorMixtureProcess prior M n omega) := by
    simpa [continuousPriorMixtureProcess] using hdv
  have hthreshold_pos : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hlog_lt :
      Real.log (continuousPriorMixtureProcess prior M n omega) <
        Real.log (1 / delta) :=
    Real.strictMonoOn_log hmix_pos hthreshold_pos hmix_lt
  have hfinal :
      (∫ theta, Real.log (M theta n omega) ∂posterior) <
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) :=
    lt_of_le_of_lt hdv'
      (add_lt_add_right hlog_lt
        (InformationTheory.klDiv posterior prior).toReal)
  simpa [M] using hfinal

/-- The common event supports post-path selection of both a continuous
posterior and an active countable sleeping strategy atom. -/
theorem continuousSleepingPredictableTilt_selectedAtomScore_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingPredictableTiltExceptionalEvent
      prior X mean strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n) (hn : 0 < n)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy theta n omega)) posterior)
    (hscore_integrable : Integrable
      (fun theta => continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega) posterior) :
    (∫ theta, continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega ∂posterior) <
      (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) - Real.log (polynomialEpochWeight j) := by
  letI : IsProbabilityMeasure posterior := hposterior
  have hpac :=
    continuousSleepingPredictableTilt_allPosteriorsLogMaster_of_not_mem
      prior hdelta hprior_integrable homega posterior hposterior
        hposterior_prior hllr n hn hlog_integrable
  have hpoint := fun theta =>
    continuousSleepingPredictableTiltScore_le_logMaster_sub_logWeight
      X mean strategy theta hjn omega
  have hrhs_integrable : Integrable
      (fun theta => Real.log
          (continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy theta n omega) -
        Real.log (polynomialEpochWeight j)) posterior :=
    hlog_integrable.sub (integrable_const _)
  have hintegral_le :=
    integral_mono hscore_integrable hrhs_integrable hpoint
  rw [integral_sub hlog_integrable (integrable_const _)] at hintegral_le
  simp only [integral_const, probReal_univ, one_smul] at hintegral_le
  linarith

/-! ## Interpretable weighted monitored-risk endpoint -/

/-- Shared accumulated exposure of one sleeping strategy atom. -/
def continuousSleepingPredictableTiltExposure
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n, sleepingStrategy strategy j k omega

/-- Tilt-weighted conditional mean for one hypothesis. -/
def continuousSleepingWeightedConditionalMeanAt
    (mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    sleepingStrategy strategy j k omega * mean theta k omega

/-- Tilt-weighted observed loss for one hypothesis. -/
def continuousSleepingWeightedObservationAt
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    sleepingStrategy strategy j k omega * X theta k omega

/-- Observable predictor-residual quadratic penalty for one hypothesis. -/
def continuousSleepingPredictorQuadraticPenaltyAt
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    forwardEmpiricalBernsteinPsi
        (sleepingStrategy strategy j k omega) *
      (X theta k omega -
        forwardPredictorProcess (X theta) k omega) ^ 2

/-- Posterior integral of the tilt-weighted conditional mean. -/
def continuousSleepingPosteriorWeightedConditionalMean
    (posterior : Measure Theta)
    (mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∫ theta, continuousSleepingWeightedConditionalMeanAt
    mean strategy theta j n omega ∂posterior

/-- Posterior integral of the tilt-weighted observation. -/
def continuousSleepingPosteriorWeightedObservation
    (posterior : Measure Theta)
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∫ theta, continuousSleepingWeightedObservationAt
    X strategy theta j n omega ∂posterior

/-- Posterior integral of the observable predictor-residual penalty. -/
def continuousSleepingPosteriorPredictorQuadraticPenalty
    (posterior : Measure Theta)
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∫ theta, continuousSleepingPredictorQuadraticPenaltyAt
    X strategy theta j n omega ∂posterior

/-- Normalized tilt-weighted conditional mean. -/
def continuousSleepingPosteriorNormalizedConditionalMean
    (posterior : Measure Theta)
    (mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  continuousSleepingPosteriorWeightedConditionalMean
      posterior mean strategy j n omega /
    continuousSleepingPredictableTiltExposure strategy j n omega

/-- Normalized tilt-weighted observed loss. -/
def continuousSleepingPosteriorNormalizedObservation
    (posterior : Measure Theta)
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  continuousSleepingPosteriorWeightedObservation
      posterior X strategy j n omega /
    continuousSleepingPredictableTiltExposure strategy j n omega

/-- Exact normalized selected-atom boundary. -/
def continuousSleepingPredictableTiltBoundary
    (prior posterior : Measure Theta)
    (X : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (delta : Real) (j n : Nat) (omega : Omega) : Real :=
  continuousSleepingPosteriorNormalizedObservation
      posterior X strategy j n omega +
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) - Real.log (polynomialEpochWeight j) +
        continuousSleepingPosteriorPredictorQuadraticPenalty
          posterior X strategy j n omega) /
      continuousSleepingPredictableTiltExposure strategy j n omega

omit [MeasurableSpace Theta] in
/-- Exact pointwise decomposition into conditional mean, observation, and
observable predictor-residual penalty. -/
theorem continuousSleepingPredictableTiltScore_eq
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) :
    continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega =
      continuousSleepingWeightedConditionalMeanAt
          mean strategy theta j n omega -
        continuousSleepingWeightedObservationAt
          X strategy theta j n omega -
        continuousSleepingPredictorQuadraticPenaltyAt
          X strategy theta j n omega := by
  unfold continuousSleepingPredictableTiltScore
    continuousSleepingWeightedConditionalMeanAt
    continuousSleepingWeightedObservationAt
    continuousSleepingPredictorQuadraticPenaltyAt
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- Posterior integration preserves the exact score decomposition. -/
theorem integral_continuousSleepingPredictableTiltScore
    (posterior : Measure Theta)
    (X mean : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega)
    (hconditional : Integrable
      (fun theta => continuousSleepingWeightedConditionalMeanAt
        mean strategy theta j n omega) posterior)
    (hobservation : Integrable
      (fun theta => continuousSleepingWeightedObservationAt
        X strategy theta j n omega) posterior)
    (hpenalty : Integrable
      (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
        X strategy theta j n omega) posterior) :
    (∫ theta, continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega ∂posterior) =
      continuousSleepingPosteriorWeightedConditionalMean
          posterior mean strategy j n omega -
        continuousSleepingPosteriorWeightedObservation
          posterior X strategy j n omega -
        continuousSleepingPosteriorPredictorQuadraticPenalty
          posterior X strategy j n omega := by
  have hpoint :
      (fun theta => continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega) =
      fun theta =>
        continuousSleepingWeightedConditionalMeanAt
            mean strategy theta j n omega -
          continuousSleepingWeightedObservationAt
            X strategy theta j n omega -
          continuousSleepingPredictorQuadraticPenaltyAt
            X strategy theta j n omega := by
    funext theta
    exact continuousSleepingPredictableTiltScore_eq
      X mean strategy theta j n omega
  rw [hpoint]
  unfold continuousSleepingPosteriorWeightedConditionalMean
    continuousSleepingPosteriorWeightedObservation
    continuousSleepingPosteriorPredictorQuadraticPenalty
  calc
    (∫ theta,
        continuousSleepingWeightedConditionalMeanAt
              mean strategy theta j n omega -
            continuousSleepingWeightedObservationAt
              X strategy theta j n omega -
          continuousSleepingPredictorQuadraticPenaltyAt
            X strategy theta j n omega ∂posterior) =
        (∫ theta,
            continuousSleepingWeightedConditionalMeanAt
                mean strategy theta j n omega -
              continuousSleepingWeightedObservationAt
                X strategy theta j n omega ∂posterior) -
          ∫ theta, continuousSleepingPredictorQuadraticPenaltyAt
            X strategy theta j n omega ∂posterior :=
      integral_sub (hconditional.sub hobservation) hpenalty
    _ =
        (∫ theta, continuousSleepingWeightedConditionalMeanAt
          mean strategy theta j n omega ∂posterior) -
        (∫ theta, continuousSleepingWeightedObservationAt
          X strategy theta j n omega ∂posterior) -
        ∫ theta, continuousSleepingPredictorQuadraticPenaltyAt
          X strategy theta j n omega ∂posterior := by
      rw [integral_sub hconditional hobservation]

/-- Outside the common event, one selected strategy and posterior satisfy the
unnormalized weighted monitored-risk bound. -/
theorem continuousSleepingPredictableTilt_weighted_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingPredictableTiltExceptionalEvent
      prior X mean strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n) (hn : 0 < n)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy theta n omega)) posterior)
    (hconditional : Integrable
      (fun theta => continuousSleepingWeightedConditionalMeanAt
        mean strategy theta j n omega) posterior)
    (hobservation : Integrable
      (fun theta => continuousSleepingWeightedObservationAt
        X strategy theta j n omega) posterior)
    (hpenalty : Integrable
      (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
        X strategy theta j n omega) posterior) :
    continuousSleepingPosteriorWeightedConditionalMean
        posterior mean strategy j n omega <
      continuousSleepingPosteriorWeightedObservation
          posterior X strategy j n omega +
        (InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) - Real.log (polynomialEpochWeight j) +
        continuousSleepingPosteriorPredictorQuadraticPenalty
          posterior X strategy j n omega := by
  have hscore_integrable : Integrable
      (fun theta => continuousSleepingPredictableTiltScore
        X mean strategy theta j n omega) posterior := by
    have hpoint :
        (fun theta => continuousSleepingPredictableTiltScore
          X mean strategy theta j n omega) =
        fun theta =>
          continuousSleepingWeightedConditionalMeanAt
              mean strategy theta j n omega -
            continuousSleepingWeightedObservationAt
              X strategy theta j n omega -
            continuousSleepingPredictorQuadraticPenaltyAt
              X strategy theta j n omega := by
      funext theta
      exact continuousSleepingPredictableTiltScore_eq
        X mean strategy theta j n omega
    rw [hpoint]
    exact (hconditional.sub hobservation).sub hpenalty
  have hscore :=
    continuousSleepingPredictableTilt_selectedAtomScore_of_not_mem
      prior hdelta hprior_integrable homega posterior hposterior
        hposterior_prior hllr hjn hn hlog_integrable hscore_integrable
  rw [integral_continuousSleepingPredictableTiltScore posterior
    X mean strategy j n omega hconditional hobservation hpenalty] at hscore
  linarith

/-- Positive exposure converts the weighted inequality into an interpretable
normalized conditional-mean certificate. -/
theorem continuousSleepingPredictableTilt_normalized_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingPredictableTiltExceptionalEvent
      prior X mean strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n) (hn : 0 < n)
    (hexposure : 0 <
      continuousSleepingPredictableTiltExposure strategy j n omega)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy theta n omega)) posterior)
    (hconditional : Integrable
      (fun theta => continuousSleepingWeightedConditionalMeanAt
        mean strategy theta j n omega) posterior)
    (hobservation : Integrable
      (fun theta => continuousSleepingWeightedObservationAt
        X strategy theta j n omega) posterior)
    (hpenalty : Integrable
      (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
        X strategy theta j n omega) posterior) :
    continuousSleepingPosteriorNormalizedConditionalMean
        posterior mean strategy j n omega <
      continuousSleepingPredictableTiltBoundary
        prior posterior X strategy delta j n omega := by
  have hweighted := continuousSleepingPredictableTilt_weighted_of_not_mem
    prior hdelta hprior_integrable homega posterior hposterior
      hposterior_prior hllr hjn hn hlog_integrable hconditional
      hobservation hpenalty
  have hdiv := (div_lt_div_iff_of_pos_right hexposure).2 hweighted
  unfold continuousSleepingPosteriorNormalizedConditionalMean
    continuousSleepingPredictableTiltBoundary
    continuousSleepingPosteriorNormalizedObservation
  exact lt_of_lt_of_eq hdiv (by ring)

/-- One event of outer mass at least `1 - delta` carries the normalized
time-varying monitored-risk bound simultaneously over all active sleeping
strategy atoms, positive reporting times, and eligible continuous posteriors.

The posterior and atom may be selected from the realized path.  The strategy
catalog itself is fixed in advance, and each atom remains predictable. -/
theorem exists_continuousSleepingPredictableTiltPACBayes_normalized_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta -> Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {L delta : Real}
    (hL1 : L < 1) (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hmean_adapted : forall theta, StronglyAdapted F (mean theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hX_unit : forall theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hstrategy_range : forall j k omega,
      strategy j k omega ∈ Set.Icc (0 : Real) L)
    (hmean : forall theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy) n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy p.1 (n + 1) p.2) (prior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy p.2 (n + 1) p.1)
        ((mu.restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        continuousSleepingForwardPredictableMeanMasterProcess
          X mean strategy p.2 n p.1) (mu.prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingForwardPredictableMeanMasterProcess
            X mean strategy p.2 n p.1)
        ((mu.restrict s).prod prior))
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingForwardPredictableMeanMasterProcess
        X mean strategy theta n omega) prior) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        forall omega, omega ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              0 < continuousSleepingPredictableTiltExposure
                strategy j n omega ->
              Integrable
                (fun theta => Real.log
                  (continuousSleepingForwardPredictableMeanMasterProcess
                    X mean strategy theta n omega)) posterior ->
              Integrable
                (fun theta => continuousSleepingWeightedConditionalMeanAt
                  mean strategy theta j n omega) posterior ->
              Integrable
                (fun theta => continuousSleepingWeightedObservationAt
                  X strategy theta j n omega) posterior ->
              Integrable
                (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
                  X strategy theta j n omega) posterior ->
              continuousSleepingPosteriorNormalizedConditionalMean
                  posterior mean strategy j n omega <
                continuousSleepingPredictableTiltBoundary
                  prior posterior X strategy delta j n omega := by
  let badEvent := continuousSleepingPredictableTiltExceptionalEvent
    prior X mean strategy delta
  have hmass : mu.real badEvent <= delta := by
    simpa [badEvent] using
      continuousSleepingPredictableTiltExceptionalEvent_mass_le_delta
        prior hL1 hdelta hX_adapted hmean_adapted hstrategy_adapted
          hX_unit hstrategy_range hmean h_adapted_mix h_integrable_mix
          hM_int_next hM_int_next_restrict hM_int_current
          hM_int_current_restrict
  refine ⟨badEventᶜ, by simpa, ?_⟩
  intro omega homega posterior hposterior hposterior_prior hllr j n hjn
    hexposure hlog_integrable hconditional hobservation hpenalty
  apply continuousSleepingPredictableTilt_normalized_of_not_mem
    prior hdelta hprior_integrable (omega := omega)
      (by simpa [badEvent] using homega) posterior hposterior
      hposterior_prior hllr hjn (Nat.zero_lt_of_lt hjn) hexposure
      hlog_integrable hconditional hobservation hpenalty

end

end FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
