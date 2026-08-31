/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousCountableSleepingEProcessPACBayes
import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectorySleepingPredictableTiltMasterProcess
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingPredictableTiltOrdinaryRisk

/-!
# Countable sleeping-strategy posteriors on measurable trajectories

This module crosses an arbitrary measurable hypothesis space with the active
prefix of a fixed countable catalog of measurable prefix-predictable trajectory
tilts. One event supports post-path selection of both a hypothesis posterior
and a posterior on the strategies active before the reporting time. The two
selections pay separate continuous-model and compressed active-strategy KL
terms.

The raw theorem below controls the selected strategy-weighted conditional-risk
gap. The ordinary-risk endpoint additionally compares the induced time weights
with uniform weights on the encountered prefix. The target is posterior-
averaged conditional risk encountered along that prefix. It is not future,
stationary, population, or deployment risk.

The countable catalog is fixed before observing the trajectory. This is
confidence allocation over a declared catalog, not coin betting or competition
with every legal predictable strategy.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
open FormalSLT.PACBayes.ContinuousCountableSleepingEProcessPACBayes
open FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

/-! ## Active-prefix score and weighted quantities -/

/-- Empirical-Bernstein e-process for one hypothesis and one declared sleeping
strategy atom. -/
def continuousMeasurableTrajectoryCountableSleepingEBComponent
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) (j : Nat) : Nat -> (Nat -> Z) -> Real :=
  forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
    (observedTrajectoryScore (score theta))
    (conditionalTrajectoryRisk K (score theta))
    (sleepingStrategy
      (observedTrajectoryPredictableStrategyCatalog strategy) j)

/-- Conditional-risk score averaged over a posterior on the active strategy
prefix, pointwise in the hypothesis. -/
def continuousTrajectoryCountableSleepingWeightedConditionalAt
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (theta : Theta) (x : Nat -> Z) : Real :=
  posteriorAverage strategyPosterior fun j =>
    continuousSleepingWeightedConditionalMeanAt
      (fun theta => conditionalTrajectoryRisk K (score theta))
      (observedTrajectoryPredictableStrategyCatalog strategy)
      theta j.1 n x

/-- Observed score averaged over a posterior on the active strategy prefix,
pointwise in the hypothesis. -/
def continuousTrajectoryCountableSleepingWeightedObservationAt
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (theta : Theta) (x : Nat -> Z) : Real :=
  posteriorAverage strategyPosterior fun j =>
    continuousSleepingWeightedObservationAt
      (fun theta => observedTrajectoryScore (score theta))
      (observedTrajectoryPredictableStrategyCatalog strategy)
      theta j.1 n x

/-- Observable forward-predictor quadratic penalty averaged over a posterior
on the active strategy prefix, pointwise in the hypothesis. -/
def continuousTrajectoryCountableSleepingQuadraticPenaltyAt
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (theta : Theta) (x : Nat -> Z) : Real :=
  posteriorAverage strategyPosterior fun j =>
    continuousSleepingPredictorQuadraticPenaltyAt
      (fun theta => observedTrajectoryScore (score theta))
      (observedTrajectoryPredictableStrategyCatalog strategy)
      theta j.1 n x

/-- Posterior integral of the active-strategy weighted conditional risk. -/
def continuousTrajectoryCountableSleepingWeightedConditionalRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  ∫ theta, continuousTrajectoryCountableSleepingWeightedConditionalAt
    K score strategy strategyPosterior theta x ∂modelPosterior

/-- Posterior integral of the active-strategy weighted observed score. -/
def continuousTrajectoryCountableSleepingWeightedObservation
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  ∫ theta, continuousTrajectoryCountableSleepingWeightedObservationAt
    score strategy strategyPosterior theta x ∂modelPosterior

/-- Posterior integral of the active-strategy observable quadratic penalty. -/
def continuousTrajectoryCountableSleepingQuadraticPenalty
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  ∫ theta, continuousTrajectoryCountableSleepingQuadraticPenaltyAt
    score strategy strategyPosterior theta x ∂modelPosterior

omit [MeasurableSpace Theta] in
/-- The active-strategy posterior log value is exactly the weighted
conditional-minus-observed score minus the predictor quadratic penalty. -/
theorem continuousTrajectoryCountableSleeping_activeLogValue_eq
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (theta : Theta) (x : Nat -> Z) :
    activeStrategyPosteriorLogValue
        (continuousMeasurableTrajectoryCountableSleepingEBComponent
          K score strategy)
        strategyPosterior theta x =
      continuousTrajectoryCountableSleepingWeightedConditionalAt
          K score strategy strategyPosterior theta x -
        continuousTrajectoryCountableSleepingWeightedObservationAt
          score strategy strategyPosterior theta x -
        continuousTrajectoryCountableSleepingQuadraticPenaltyAt
          score strategy strategyPosterior theta x := by
  unfold activeStrategyPosteriorLogValue posteriorAverage
    continuousTrajectoryCountableSleepingWeightedConditionalAt
    continuousTrajectoryCountableSleepingWeightedObservationAt
    continuousTrajectoryCountableSleepingQuadraticPenaltyAt
  have hterm (j : Fin n) :
      Real.log
          (continuousMeasurableTrajectoryCountableSleepingEBComponent
            K score strategy theta j.1 n x) =
        continuousSleepingWeightedConditionalMeanAt
            (fun theta => conditionalTrajectoryRisk K (score theta))
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j.1 n x -
          continuousSleepingWeightedObservationAt
            (fun theta => observedTrajectoryScore (score theta))
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j.1 n x -
          continuousSleepingPredictorQuadraticPenaltyAt
            (fun theta => observedTrajectoryScore (score theta))
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j.1 n x := by
    rw [show
      continuousMeasurableTrajectoryCountableSleepingEBComponent
          K score strategy theta j.1 n x =
        Real.exp
          (continuousSleepingPredictableTiltScore
            (fun theta => observedTrajectoryScore (score theta))
            (fun theta => conditionalTrajectoryRisk K (score theta))
            (observedTrajectoryPredictableStrategyCatalog strategy)
            theta j.1 n x) by
      unfold continuousMeasurableTrajectoryCountableSleepingEBComponent
        continuousSleepingPredictableTiltScore
      rw [forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq]]
    rw [Real.log_exp]
    exact continuousSleepingPredictableTiltScore_eq
      (fun theta => observedTrajectoryScore (score theta))
      (fun theta => conditionalTrajectoryRisk K (score theta))
      (observedTrajectoryPredictableStrategyCatalog strategy)
      theta j.1 n x
  simp_rw [hterm]
  simp only [posteriorAverage, mul_sub, Finset.sum_sub_distrib]

/-- Integrating the exact active-strategy score decomposition over the model
posterior preserves its three terms. -/
theorem integral_continuousTrajectoryCountableSleeping_activeLogValue
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z)
    (hconditional : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingWeightedConditionalAt
          K score strategy strategyPosterior theta x) modelPosterior)
    (hobservation : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingWeightedObservationAt
          score strategy strategyPosterior theta x) modelPosterior)
    (hpenalty : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingQuadraticPenaltyAt
          score strategy strategyPosterior theta x) modelPosterior) :
    (∫ theta, activeStrategyPosteriorLogValue
        (continuousMeasurableTrajectoryCountableSleepingEBComponent
          K score strategy)
        strategyPosterior theta x ∂modelPosterior) =
      continuousTrajectoryCountableSleepingWeightedConditionalRisk
          K score strategy modelPosterior strategyPosterior x -
        continuousTrajectoryCountableSleepingWeightedObservation
          score strategy modelPosterior strategyPosterior x -
        continuousTrajectoryCountableSleepingQuadraticPenalty
          score strategy modelPosterior strategyPosterior x := by
  have hpoint :
      (fun theta => activeStrategyPosteriorLogValue
        (continuousMeasurableTrajectoryCountableSleepingEBComponent
          K score strategy)
        strategyPosterior theta x) =
      fun theta =>
        continuousTrajectoryCountableSleepingWeightedConditionalAt
            K score strategy strategyPosterior theta x -
          continuousTrajectoryCountableSleepingWeightedObservationAt
            score strategy strategyPosterior theta x -
          continuousTrajectoryCountableSleepingQuadraticPenaltyAt
            score strategy strategyPosterior theta x := by
    funext theta
    exact continuousTrajectoryCountableSleeping_activeLogValue_eq
      K score strategy strategyPosterior theta x
  rw [hpoint]
  unfold continuousTrajectoryCountableSleepingWeightedConditionalRisk
    continuousTrajectoryCountableSleepingWeightedObservation
    continuousTrajectoryCountableSleepingQuadraticPenalty
  calc
    _ =
        (∫ theta,
          continuousTrajectoryCountableSleepingWeightedConditionalAt
              K score strategy strategyPosterior theta x -
            continuousTrajectoryCountableSleepingWeightedObservationAt
              score strategy strategyPosterior theta x ∂modelPosterior) -
          ∫ theta,
            continuousTrajectoryCountableSleepingQuadraticPenaltyAt
              score strategy strategyPosterior theta x ∂modelPosterior :=
      integral_sub (hconditional.sub hobservation) hpenalty
    _ = _ := by
      rw [integral_sub hconditional hobservation]

/-! ## One raw factorized-posterior event -/

/-- One event controls the active-strategy weighted conditional-risk gap for
every reporting time, eligible path-selected model posterior, and path-selected
posterior on the active prefix of the declared countable strategy catalog. -/
theorem
    exists_continuousMeasurableTrajectoryCountableSleepingStrategyPACBayes_raw_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    {L : Real} (hL1 : L < 1)
    (hstrategy_range : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta /\
        forall x, x ∈ goodEvent ->
          forall modelPosterior : Measure Theta,
            IsProbabilityMeasure modelPosterior ->
            modelPosterior ≪ modelPrior ->
            Integrable (llr modelPosterior modelPrior) modelPosterior ->
            forall n : Nat, 0 < n ->
              forall strategyPosterior : Fin n -> Real,
                IsPMF strategyPosterior ->
                continuousTrajectoryCountableSleepingWeightedConditionalRisk
                      K score strategy modelPosterior strategyPosterior x -
                    continuousTrajectoryCountableSleepingWeightedObservation
                      score strategy modelPosterior strategyPosterior x <
                  (InformationTheory.klDiv
                      modelPosterior modelPrior).toReal +
                    klDiv
                      (liftPolynomialActivePosterior strategyPosterior)
                      (polynomialActiveTailPrior n) +
                    Real.log (1 / delta) +
                    continuousTrajectoryCountableSleepingQuadraticPenalty
                      score strategy modelPosterior strategyPosterior x := by
  let F := Filtration.piLE (X := fun _ : Nat => Z)
  let mu := trajectoryMeasure K x0
  let E : Theta -> Nat -> Nat -> (Nat -> Z) -> Real :=
    continuousMeasurableTrajectoryCountableSleepingEBComponent
      K score strategy
  have hE : forall theta j, EProcess mu F (E theta j) := by
    intro theta j
    dsimp [E, continuousMeasurableTrajectoryCountableSleepingEBComponent]
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
        hL1
        (observedTrajectoryScore_incrementAdapted_parameterized_of_joint
          hscore_joint theta)
        (conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
          K hscore_joint theta)
        (sleepingStrategy_stronglyAdapted
          (observedTrajectoryPredictableStrategyCatalog strategy)
          (fun i =>
            observedTrajectoryPredictableTilt_stronglyAdapted_of_stronglyMeasurable
              (strategy i) (hstrategy_meas i)) j)
        (fun k x => observedTrajectoryScore_mem_Icc
          (hscore_unit theta) k x)
        (fun k x => sleepingStrategy_mem_Icc
          (strategy := observedTrajectoryPredictableStrategyCatalog strategy)
          (fun i r y => hstrategy_range i r
            (Preorder.frestrictLe r y)) j k x)
        (fun k => observedTrajectoryScore_condExp_parameterized_of_joint
          K x0 hscore_joint hscore_unit theta k)
  have hsleep : forall theta j n x, n <= j -> E theta j n x = 1 := by
    intro theta j n x hnj
    dsimp [E, continuousMeasurableTrajectoryCountableSleepingEBComponent]
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_sleeping_of_time_le
        (observedTrajectoryScore (score theta))
        (conditionalTrajectoryRisk K (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy) hnj x
  have hEpos : forall theta j n x, 0 < E theta j n x := by
    intro theta j n x
    dsimp [E, continuousMeasurableTrajectoryCountableSleepingEBComponent]
    exact Real.exp_pos _
  have hjoint_filtered (n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod (F n)
        (inferInstance : MeasurableSpace Theta)]
        (fun q : (Nat -> Z) × Theta =>
          continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy q.2 n q.1) := by
    simpa [F] using
      (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_filtered
        K score hscore_joint strategy hstrategy_meas n)
  have hjoint_ambient (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) :=
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_ambient
      K score hscore_joint strategy hstrategy_meas n
  have hmaster_pos (theta : Theta) (n : Nat) (x : Nat -> Z) :
      0 < continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x := by
    unfold continuousTrajectorySleepingPredictableTiltMasterProcess
    exact continuousSleepingForwardPredictableMeanMasterProcess_pos
      (fun theta => observedTrajectoryScore (score theta))
      (fun theta => conditionalTrajectoryRisk K (score theta))
      (observedTrajectoryPredictableStrategyCatalog strategy) theta n x
  have hM_int_current (n : Nat) : Integrable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) (mu.prod modelPrior) := by
    refine Integrable.of_bound (hjoint_ambient n).aestronglyMeasurable
      (polynomialSleepingTail n +
        ∑ j ∈ Finset.range n,
          polynomialEpochWeight j * Real.exp ((n : Real) * L)) ?_
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_pos (hmaster_pos q.2 n q.1)]
      exact continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_le
        K score hscore_unit hscore_joint strategy hL1 hstrategy_range
          q.2 n q.1
  have hM_int_next (n : Nat) : Integrable
      (fun q : Theta × (Nat -> Z) =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.1 (n + 1) q.2) (modelPrior.prod mu) := by
    simpa [Function.comp_def] using (hM_int_current (n + 1)).swap
  have hM_int_restrict (n : Nat) {s : Set (Nat -> Z)} : Integrable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) ((mu.restrict s).prod modelPrior) :=
    (hM_int_current n).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hprior_integrable (n : Nat) (x : Nat -> Z) : Integrable
      (fun theta => continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x) modelPrior := by
    have hmap : Measurable (fun theta : Theta => ((x, theta) :
        (Nat -> Z) × Theta)) := measurable_const.prodMk measurable_id
    have hsection_raw := (hjoint_ambient n).comp_measurable hmap
    have hsection : StronglyMeasurable
        (fun theta => continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy theta n x) := by
      simpa only [Function.comp_def] using hsection_raw
    refine Integrable.of_bound hsection.aestronglyMeasurable
      (polynomialSleepingTail n +
        ∑ j ∈ Finset.range n,
          polynomialEpochWeight j * Real.exp ((n : Real) * L)) ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_pos (hmaster_pos theta n x)]
      exact continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_le
        K score hscore_unit hscore_joint strategy hL1 hstrategy_range
          theta n x
  have h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess modelPrior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy)) := by
    intro n
    change StronglyMeasurable[F n]
      (fun x => ∫ theta,
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy theta n x ∂modelPrior)
    letI : MeasurableSpace (Nat -> Z) := F n
    exact StronglyMeasurable.integral_prod_right' (hjoint_filtered n)
  have h_integrable_mix (n : Nat) : Integrable
      (continuousPriorMixtureProcess modelPrior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy) n) mu :=
    (hM_int_current n).integral_prod_left
  have hmaster_generic :
      parameterizedCountableSleepingEProcessMaster E =
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy := by
    rfl
  have hcontinuous_generic :
      continuousCountableSleepingEProcessMaster modelPrior E =
        continuousPriorMixtureProcess modelPrior
          (continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy) := by
    rw [continuousCountableSleepingEProcessMaster, hmaster_generic]
  rcases
      exists_continuousCountableSleepingEProcessPACBayes_factorized_event
        (mu := mu) (F := F) modelPrior E hE hsleep hEpos hdelta
        (by simpa [hcontinuous_generic] using h_adapted_mix)
        (by simpa [hcontinuous_generic] using h_integrable_mix)
        (by simpa [hmaster_generic] using hM_int_next)
        (fun n _s _hs _hfinite => by
          simpa [hmaster_generic] using hM_int_restrict (n + 1))
        (by simpa [hmaster_generic] using hM_int_current)
        (fun n _s _hs _hfinite => by
          simpa [hmaster_generic] using hM_int_restrict n)
        (by simpa [hmaster_generic] using hprior_integrable) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx modelPosterior hmodelPosterior hposterior_prior hllr
    n hn strategyPosterior hstrategyPosterior
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  have hmap : Measurable (fun theta : Theta => ((x, theta) :
      (Nat -> Z) × Theta)) := measurable_const.prodMk measurable_id
  have hmaster_section_raw := (hjoint_ambient n).comp_measurable hmap
  have hmaster_section : StronglyMeasurable
      (fun theta => continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x) := by
    simpa only [Function.comp_def] using hmaster_section_raw
  let C : Real := polynomialSleepingTail n +
    ∑ i ∈ Finset.range n,
      polynomialEpochWeight i * Real.exp ((n : Real) * L)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg (polynomialSleepingTail_pos n)
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (polynomialEpochWeight_pos i).le (Real.exp_pos _).le)
  have hlog : Integrable
      (fun theta => Real.log
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy theta n x)) modelPosterior := by
    have hlog_meas : StronglyMeasurable
        (fun theta => Real.log
          (continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy theta n x)) :=
      (Real.measurable_log.comp hmaster_section.measurable).stronglyMeasurable
    refine Integrable.of_bound hlog_meas.aestronglyMeasurable
      (|Real.log (polynomialSleepingTail n)| + |Real.log C|) ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs]
      have hlower := Real.log_le_log (polynomialSleepingTail_pos n)
        (continuousTrajectorySleepingPredictableTiltMasterProcess_tail_le
          K score strategy theta n x)
      have hupper_master :
          continuousTrajectorySleepingPredictableTiltMasterProcess
              K score strategy theta n x <= C := by
        dsimp [C]
        exact continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_le
          K score hscore_unit hscore_joint strategy hL1 hstrategy_range
            theta n x
      have hupper := Real.log_le_log (hmaster_pos theta n x) hupper_master
      apply abs_le.mpr
      constructor
      · have htail_abs := neg_abs_le (Real.log (polynomialSleepingTail n))
        have hC_abs : 0 <= |Real.log C| := abs_nonneg _
        linarith
      · have hC_abs := le_abs_self (Real.log C)
        have htail_abs : 0 <= |Real.log (polynomialSleepingTail n)| :=
          abs_nonneg _
        linarith
  have hmean_int (k : Nat) : Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x)
      modelPosterior :=
    integrable_conditionalTrajectoryRisk_parameter_of_joint
      K hscore_joint hscore_unit modelPosterior k x
  have hX_meas (k : Nat) : StronglyMeasurable
      (fun theta => observedTrajectoryScore (score theta) k x) :=
    stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      hscore_joint k x
  have hX_unit (theta : Theta) (k : Nat) :
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    observedTrajectoryScore_mem_Icc (hscore_unit theta) k x
  have hX_int (k : Nat) : Integrable
      (fun theta => observedTrajectoryScore (score theta) k x)
      modelPosterior := by
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit theta k).1]
      exact (hX_unit theta k).2
  have hconditionalAt : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingWeightedConditionalAt
          K score strategy strategyPosterior theta x) modelPosterior := by
    unfold continuousTrajectoryCountableSleepingWeightedConditionalAt
      posteriorAverage continuousSleepingWeightedConditionalMeanAt
    have hsum : Integrable
        (fun theta => ∑ j : Fin n,
          strategyPosterior j *
            ∑ k ∈ Finset.range n,
              sleepingStrategy
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  j.1 k x *
                conditionalTrajectoryRisk K (score theta) k x)
        modelPosterior := by
      apply integrable_finsetSum
      intro j _hj
      have hinner : Integrable
          (fun theta => ∑ k ∈ Finset.range n,
            sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j.1 k x *
              conditionalTrajectoryRisk K (score theta) k x)
          modelPosterior := by
        apply integrable_finsetSum
        intro k _hk
        exact (hmean_int k).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j.1 k x)
      exact hinner.const_mul (strategyPosterior j)
    exact hsum
  have hobservationAt : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingWeightedObservationAt
          score strategy strategyPosterior theta x) modelPosterior := by
    unfold continuousTrajectoryCountableSleepingWeightedObservationAt
      posteriorAverage continuousSleepingWeightedObservationAt
    have hsum : Integrable
        (fun theta => ∑ j : Fin n,
          strategyPosterior j *
            ∑ k ∈ Finset.range n,
              sleepingStrategy
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  j.1 k x *
                observedTrajectoryScore (score theta) k x)
        modelPosterior := by
      apply integrable_finsetSum
      intro j _hj
      have hinner : Integrable
          (fun theta => ∑ k ∈ Finset.range n,
            sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j.1 k x *
              observedTrajectoryScore (score theta) k x)
          modelPosterior := by
        apply integrable_finsetSum
        intro k _hk
        exact (hX_int k).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j.1 k x)
      exact hinner.const_mul (strategyPosterior j)
    exact hsum
  let Xparameter : Nat -> Theta -> Real := fun k theta =>
    observedTrajectoryScore (score theta) k x
  have hXparameter (k : Nat) : StronglyMeasurable (Xparameter k) := by
    simpa only [Xparameter] using hX_meas k
  have hpenaltyAt : Integrable
      (fun theta =>
        continuousTrajectoryCountableSleepingQuadraticPenaltyAt
          score strategy strategyPosterior theta x) modelPosterior := by
    unfold continuousTrajectoryCountableSleepingQuadraticPenaltyAt
      posteriorAverage continuousSleepingPredictorQuadraticPenaltyAt
    have hsum : Integrable
        (fun theta => ∑ j : Fin n,
          strategyPosterior j *
            ∑ k ∈ Finset.range n,
              forwardEmpiricalBernsteinPsi
                  (sleepingStrategy
                    (observedTrajectoryPredictableStrategyCatalog strategy)
                    j.1 k x) *
                (Xparameter k theta -
                  forwardPredictorProcess Xparameter k theta) ^ 2)
        modelPosterior := by
      apply integrable_finsetSum
      intro j _hj
      have hinner : Integrable
          (fun theta => ∑ k ∈ Finset.range n,
            forwardEmpiricalBernsteinPsi
                (sleepingStrategy
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  j.1 k x) *
              (Xparameter k theta -
                forwardPredictorProcess Xparameter k theta) ^ 2)
          modelPosterior := by
        apply integrable_finsetSum
        intro k _hk
        have hpredictor : StronglyMeasurable
            (forwardPredictorProcess Xparameter k) := by
          unfold forwardPredictorProcess forwardPredictor
          split_ifs
          · exact stronglyMeasurable_const
          · unfold forwardPrefixMean
            have hsum : StronglyMeasurable
                (∑ i ∈ Finset.range k, Xparameter i) :=
              Finset.stronglyMeasurable_sum (Finset.range k) fun i _ =>
                hXparameter i
            simpa only [Finset.sum_apply, div_eq_mul_inv] using
              hsum.mul_const ((k : Real)⁻¹)
        have hsq_meas : StronglyMeasurable (fun theta =>
            (Xparameter k theta -
              forwardPredictorProcess Xparameter k theta) ^ 2) :=
          ((hXparameter k).sub hpredictor).pow 2
        have hsq_int : Integrable (fun theta =>
            (Xparameter k theta -
              forwardPredictorProcess Xparameter k theta) ^ 2)
            modelPosterior := by
          refine Integrable.of_bound hsq_meas.aestronglyMeasurable 1 ?_
          exact Filter.Eventually.of_forall fun theta => by
            have hXtheta : Xparameter k theta ∈ Set.Icc (0 : Real) 1 := by
              simpa only [Xparameter] using hX_unit theta k
            have hPtheta := forwardPredictorProcess_mem_Icc_of_mem_Icc
              (X := Xparameter)
              (fun i theta => by
                constructor
                · simpa only [Xparameter] using (hX_unit theta i).1
                · simpa only [Xparameter] using (hX_unit theta i).2) k theta
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            rcases hXtheta with ⟨hXlo, hXhi⟩
            rcases hPtheta with ⟨hPlo, hPhi⟩
            nlinarith
        exact hsq_int.const_mul
          (forwardEmpiricalBernsteinPsi
            (sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy)
              j.1 k x))
      exact hinner.const_mul (strategyPosterior j)
    simpa only [Xparameter, forwardPredictorProcess] using hsum
  have hscore_int : Integrable
      (fun theta => activeStrategyPosteriorLogValue E
        strategyPosterior theta x) modelPosterior := by
    have hdiff := (hconditionalAt.sub hobservationAt).sub hpenaltyAt
    convert hdiff using 1
    funext theta
    exact continuousTrajectoryCountableSleeping_activeLogValue_eq
      K score strategy strategyPosterior theta x
  have hraw := hgood x hx modelPosterior hmodelPosterior
    hposterior_prior hllr n hn strategyPosterior hstrategyPosterior
    (by simpa [hmaster_generic] using hlog) hscore_int
  rw [integral_continuousTrajectoryCountableSleeping_activeLogValue
    K score strategy modelPosterior strategyPosterior x
    hconditionalAt hobservationAt hpenaltyAt] at hraw
  linarith

/-! ## Ordinary encountered-prefix quantities -/

/-- Time-`k` predictable weight induced by the selected posterior on the
active prefix of the countable strategy catalog. -/
def continuousTrajectoryCountableSleepingStrategyEffectiveWeight
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (k : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage strategyPosterior fun j =>
    sleepingStrategy
      (observedTrajectoryPredictableStrategyCatalog strategy) j.1 k x

/-- Total exposure of the posterior-induced predictable time weights. -/
def continuousTrajectoryCountableSleepingStrategyExposure
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  ∑ k ∈ Finset.range n,
    continuousTrajectoryCountableSleepingStrategyEffectiveWeight
      strategy strategyPosterior k x

/-- Total-variation discrepancy between uniform prefix weights and the
normalized time weights induced by the selected strategy posterior. -/
def continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  finiteUniformNormalizedWeightDiscrepancy (Finset.range n)
    (fun k => continuousTrajectoryCountableSleepingStrategyEffectiveWeight
      strategy strategyPosterior k x)
    (continuousTrajectoryCountableSleepingStrategyExposure
      strategy strategyPosterior x)

omit [MeasurableSpace Z] in
private theorem integral_countableSleepingStrategyPosterior_weightedSum
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (value : Theta -> Nat -> Real) (x : Nat -> Z)
    (hvalue : forall k, Integrable (fun theta => value theta k)
      modelPosterior) :
    (∫ theta, posteriorAverage strategyPosterior (fun j =>
        ∑ k ∈ Finset.range n,
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy)
              j.1 k x * value theta k) ∂modelPosterior) =
      ∑ k ∈ Finset.range n,
        continuousTrajectoryCountableSleepingStrategyEffectiveWeight
            strategy strategyPosterior k x *
          ∫ theta, value theta k ∂modelPosterior := by
  unfold posteriorAverage
    continuousTrajectoryCountableSleepingStrategyEffectiveWeight
  calc
    (∫ theta, ∑ j : Fin n,
        strategyPosterior j *
          ∑ k ∈ Finset.range n,
            sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j.1 k x * value theta k ∂modelPosterior) =
        ∑ j : Fin n, ∫ theta,
          strategyPosterior j *
            ∑ k ∈ Finset.range n,
              sleepingStrategy
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  j.1 k x * value theta k ∂modelPosterior := by
      rw [integral_finsetSum Finset.univ]
      intro j _hj
      exact (integrable_finsetSum (Finset.range n) fun k _hk =>
        (hvalue k).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy)
            j.1 k x)).const_mul (strategyPosterior j)
    _ = ∑ j : Fin n,
        strategyPosterior j *
          ∑ k ∈ Finset.range n,
            sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j.1 k x *
              ∫ theta, value theta k ∂modelPosterior := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_const_mul]
      rw [integral_finsetSum (Finset.range n) (fun k _hk =>
        (hvalue k).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy)
            j.1 k x))]
      simp only [integral_const_mul]
    _ = ∑ j : Fin n, ∑ k ∈ Finset.range n,
        (strategyPosterior j *
          sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy)
            j.1 k x) *
          ∫ theta, value theta k ∂modelPosterior := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ k ∈ Finset.range n, ∑ j : Fin n,
        (strategyPosterior j *
          sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy)
            j.1 k x) *
          ∫ theta, value theta k ∂modelPosterior := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range n,
        (∑ j : Fin n,
          strategyPosterior j *
            sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy)
              j.1 k x) *
          ∫ theta, value theta k ∂modelPosterior := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]

omit [MeasurableSpace Z] in
private theorem integral_mem_Icc_zero_one
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (f : Theta -> Real) (hf : Integrable f posterior)
    (hunit : forall theta, f theta ∈ Set.Icc (0 : Real) 1) :
    (∫ theta, f theta ∂posterior) ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun theta => (hunit theta).1)
  · have hle := integral_mono hf (integrable_const (1 : Real))
      (fun theta => (hunit theta).2)
    simpa using hle

private theorem
    continuousTrajectoryCountableSleepingWeightedConditionalRisk_eq_sum
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z)
    (hmean_int : forall k, Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x)
      modelPosterior) :
    continuousTrajectoryCountableSleepingWeightedConditionalRisk
        K score strategy modelPosterior strategyPosterior x =
      ∑ k ∈ Finset.range n,
        continuousTrajectoryCountableSleepingStrategyEffectiveWeight
            strategy strategyPosterior k x *
          ∫ theta, conditionalTrajectoryRisk K (score theta) k x
            ∂modelPosterior := by
  simpa [continuousTrajectoryCountableSleepingWeightedConditionalRisk,
    continuousTrajectoryCountableSleepingWeightedConditionalAt,
    continuousSleepingWeightedConditionalMeanAt] using
      (integral_countableSleepingStrategyPosterior_weightedSum
        strategy modelPosterior strategyPosterior
        (fun theta k => conditionalTrajectoryRisk K (score theta) k x)
        x hmean_int)

omit [MeasurableSpace Z] in
private theorem
    continuousTrajectoryCountableSleepingWeightedObservation_eq_sum
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Measure Theta)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z)
    (hX_int : forall k, Integrable
      (fun theta => observedTrajectoryScore (score theta) k x)
      modelPosterior) :
    continuousTrajectoryCountableSleepingWeightedObservation
        score strategy modelPosterior strategyPosterior x =
      ∑ k ∈ Finset.range n,
        continuousTrajectoryCountableSleepingStrategyEffectiveWeight
            strategy strategyPosterior k x *
          ∫ theta, observedTrajectoryScore (score theta) k x
            ∂modelPosterior := by
  simpa [continuousTrajectoryCountableSleepingWeightedObservation,
    continuousTrajectoryCountableSleepingWeightedObservationAt,
    continuousSleepingWeightedObservationAt] using
      (integral_countableSleepingStrategyPosterior_weightedSum
        strategy modelPosterior strategyPosterior
        (fun theta k => observedTrajectoryScore (score theta) k x)
        x hX_int)

private theorem
    continuousTrajectoryPosteriorAverageConditionalPrefixRisk_eq_sum
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (modelPosterior : Measure Theta) (n : Nat) (x : Nat -> Z)
    (hmean_int : forall k, Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x)
      modelPosterior) :
    continuousTrajectoryPosteriorAverageConditionalSuffixRisk
        K score modelPosterior 0 n x =
      (∑ k ∈ Finset.range n,
        ∫ theta, conditionalTrajectoryRisk K (score theta) k x
          ∂modelPosterior) / (n : Real) := by
  unfold continuousTrajectoryPosteriorAverageConditionalSuffixRisk
  simp only [Nat.Ico_zero_eq_range, Nat.sub_zero]
  rw [integral_div]
  rw [integral_finsetSum (Finset.range n) (fun k _hk => hmean_int k)]

omit [MeasurableSpace Z] in
private theorem
    continuousTrajectoryPosteriorEmpiricalPrefixRisk_eq_sum
    (score : Theta -> TrajectoryScore Z)
    (modelPosterior : Measure Theta) (n : Nat) (x : Nat -> Z)
    (hX_int : forall k, Integrable
      (fun theta => observedTrajectoryScore (score theta) k x)
      modelPosterior) :
    continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        score modelPosterior 0 n x =
      (∑ k ∈ Finset.range n,
        ∫ theta, observedTrajectoryScore (score theta) k x
          ∂modelPosterior) / (n : Real) := by
  unfold continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
  simp only [Nat.Ico_zero_eq_range, Nat.sub_zero]
  rw [integral_div]
  rw [integral_finsetSum (Finset.range n) (fun k _hk => hX_int k)]

/-- The ordinary posterior-averaged conditional prefix risk differs from the
normalized strategy-posterior weighted risk by at most the realized
time-weight discrepancy. -/
theorem
    abs_continuousTrajectoryPosteriorConditionalPrefixRisk_sub_countableSleepingNormalized_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (modelPosterior : Measure Theta) [IsProbabilityMeasure modelPosterior]
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (hn : 0 < n) (x : Nat -> Z)
    (hexposure : 0 <
      continuousTrajectoryCountableSleepingStrategyExposure
        strategy strategyPosterior x) :
    |continuousTrajectoryPosteriorAverageConditionalSuffixRisk
          K score modelPosterior 0 n x -
        continuousTrajectoryCountableSleepingWeightedConditionalRisk
            K score strategy modelPosterior strategyPosterior x /
          continuousTrajectoryCountableSleepingStrategyExposure
            strategy strategyPosterior x| <=
      continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy
        strategy strategyPosterior x := by
  have hmean_int (k : Nat) : Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x)
      modelPosterior :=
    integrable_conditionalTrajectoryRisk_parameter_of_joint
      K hscore_joint hscore_unit modelPosterior k x
  rw [continuousTrajectoryPosteriorAverageConditionalPrefixRisk_eq_sum
    K score modelPosterior n x hmean_int]
  rw [continuousTrajectoryCountableSleepingWeightedConditionalRisk_eq_sum
    K score strategy modelPosterior strategyPosterior x hmean_int]
  have hs : (Finset.range n).Nonempty :=
    ⟨0, Finset.mem_range.mpr hn⟩
  simpa [continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy]
    using
      (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
        (Finset.range n) hs
        (fun k =>
          continuousTrajectoryCountableSleepingStrategyEffectiveWeight
            strategy strategyPosterior k x)
        (fun k => ∫ theta,
          conditionalTrajectoryRisk K (score theta) k x ∂modelPosterior)
        hexposure.ne' rfl
        (fun k _hk => integral_mem_Icc_zero_one modelPosterior
          (fun theta => conditionalTrajectoryRisk K (score theta) k x)
          (hmean_int k) (fun theta =>
            conditionalTrajectoryRisk_mem_Icc_of_joint K
              (jointlyStronglyMeasurableTrajectoryScore_section
                hscore_joint theta)
              (hscore_unit theta) k x)))

/-- The analogous finite-TV comparison for the posterior empirical prefix
risk under the same selected strategy posterior. -/
theorem
    abs_continuousTrajectoryPosteriorEmpiricalPrefixRisk_sub_countableSleepingNormalized_le
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (modelPosterior : Measure Theta) [IsProbabilityMeasure modelPosterior]
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (hn : 0 < n) (x : Nat -> Z)
    (hexposure : 0 <
      continuousTrajectoryCountableSleepingStrategyExposure
        strategy strategyPosterior x) :
    |continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score modelPosterior 0 n x -
        continuousTrajectoryCountableSleepingWeightedObservation
            score strategy modelPosterior strategyPosterior x /
          continuousTrajectoryCountableSleepingStrategyExposure
            strategy strategyPosterior x| <=
      continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy
        strategy strategyPosterior x := by
  have hX_meas (k : Nat) : StronglyMeasurable
      (fun theta => observedTrajectoryScore (score theta) k x) :=
    stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      hscore_joint k x
  have hX_int (k : Nat) : Integrable
      (fun theta => observedTrajectoryScore (score theta) k x)
      modelPosterior := by
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      have hunit := observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k x
      rw [Real.norm_eq_abs, abs_of_nonneg hunit.1]
      exact hunit.2
  rw [continuousTrajectoryPosteriorEmpiricalPrefixRisk_eq_sum
    score modelPosterior n x hX_int]
  rw [continuousTrajectoryCountableSleepingWeightedObservation_eq_sum
    score strategy modelPosterior strategyPosterior x hX_int]
  have hs : (Finset.range n).Nonempty :=
    ⟨0, Finset.mem_range.mpr hn⟩
  simpa [continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy]
    using
      (abs_uniformAverage_sub_normalizedWeightedAverage_le_discrepancy
        (Finset.range n) hs
        (fun k =>
          continuousTrajectoryCountableSleepingStrategyEffectiveWeight
            strategy strategyPosterior k x)
        (fun k => ∫ theta,
          observedTrajectoryScore (score theta) k x ∂modelPosterior)
        hexposure.ne' rfl
        (fun k _hk => integral_mem_Icc_zero_one modelPosterior
          (fun theta => observedTrajectoryScore (score theta) k x)
          (hX_int k) (fun theta =>
            observedTrajectoryScore_mem_Icc (hscore_unit theta) k x)))

/-- Observable ordinary encountered-prefix endpoint for an arbitrary
measurable model posterior and a posterior on the active prefix of the
declared countable strategy catalog. -/
def continuousTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
    (modelPrior modelPosterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (delta : Real) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score modelPosterior 0 n x +
    ((InformationTheory.klDiv modelPosterior modelPrior).toReal +
          klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n) +
        Real.log (1 / delta) +
        continuousTrajectoryCountableSleepingQuadraticPenalty
          score strategy modelPosterior strategyPosterior x) /
      continuousTrajectoryCountableSleepingStrategyExposure
        strategy strategyPosterior x +
    2 * continuousTrajectoryCountableSleepingStrategyUniformDiscrepancy
      strategy strategyPosterior x

/-- One trajectory event controls ordinary encountered conditional prefix
risk for every reporting time, every eligible path-selected posterior on an
arbitrary measurable hypothesis space, and every path-selected posterior on
the active prefix of a fixed countable predictable-strategy catalog.

Model and strategy selection pay separate KL terms. The realized nonuniform
time weights pay twice their finite total-variation discrepancy from uniform
prefix weights. The conclusion is encountered conditional prefix risk, not
future, stationary, population, or deployment risk. -/
theorem
    exists_continuousMeasurableTrajectoryCountableSleepingStrategyPACBayes_ordinaryPrefixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    {L : Real} (hL1 : L < 1)
    (hstrategy_range : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    (modelPrior : Measure Theta) [IsProbabilityMeasure modelPrior]
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta /\
        forall x, x ∈ goodEvent ->
          forall modelPosterior : Measure Theta,
            IsProbabilityMeasure modelPosterior ->
            modelPosterior ≪ modelPrior ->
            Integrable (llr modelPosterior modelPrior) modelPosterior ->
            forall n : Nat, 0 < n ->
              forall strategyPosterior : Fin n -> Real,
                IsPMF strategyPosterior ->
                0 < continuousTrajectoryCountableSleepingStrategyExposure
                    strategy strategyPosterior x ->
                continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                    K score modelPosterior 0 n x <
                  continuousTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
                    modelPrior modelPosterior score strategy
                    strategyPosterior delta x := by
  rcases
      exists_continuousMeasurableTrajectoryCountableSleepingStrategyPACBayes_raw_event
        K x0 score hscore_unit hscore_joint strategy hstrategy_meas hL1
        hstrategy_range modelPrior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx modelPosterior hmodelPosterior hposterior_prior hllr
    n hn strategyPosterior hstrategyPosterior hexposure
  letI : IsProbabilityMeasure modelPosterior := hmodelPosterior
  have hraw := hgood x hx modelPosterior hmodelPosterior
    hposterior_prior hllr n hn strategyPosterior hstrategyPosterior
  have hconditional :=
    abs_continuousTrajectoryPosteriorConditionalPrefixRisk_sub_countableSleepingNormalized_le
      K score hscore_unit hscore_joint modelPosterior strategy
      strategyPosterior hn x hexposure
  have hempirical :=
    abs_continuousTrajectoryPosteriorEmpiricalPrefixRisk_sub_countableSleepingNormalized_le
      score hscore_unit hscore_joint modelPosterior strategy
      strategyPosterior hn x hexposure
  have hdiv := (div_lt_div_iff_of_pos_right hexposure).2 hraw
  have hnormalized :
      continuousTrajectoryCountableSleepingWeightedConditionalRisk
            K score strategy modelPosterior strategyPosterior x /
          continuousTrajectoryCountableSleepingStrategyExposure
            strategy strategyPosterior x -
        continuousTrajectoryCountableSleepingWeightedObservation
            score strategy modelPosterior strategyPosterior x /
          continuousTrajectoryCountableSleepingStrategyExposure
            strategy strategyPosterior x <
        ((InformationTheory.klDiv modelPosterior modelPrior).toReal +
              klDiv (liftPolynomialActivePosterior strategyPosterior)
                (polynomialActiveTailPrior n) +
            Real.log (1 / delta) +
            continuousTrajectoryCountableSleepingQuadraticPenalty
              score strategy modelPosterior strategyPosterior x) /
          continuousTrajectoryCountableSleepingStrategyExposure
            strategy strategyPosterior x := by
    calc
      _ =
          (continuousTrajectoryCountableSleepingWeightedConditionalRisk
                K score strategy modelPosterior strategyPosterior x -
              continuousTrajectoryCountableSleepingWeightedObservation
                score strategy modelPosterior strategyPosterior x) /
            continuousTrajectoryCountableSleepingStrategyExposure
              strategy strategyPosterior x := by ring
      _ < _ := hdiv
  have hconditionalUpper := (abs_le.mp hconditional).2
  have hempiricalUpper := (abs_le.mp hempirical).1
  unfold continuousTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
  linarith

end

end FormalSLT.StochasticDynamics
