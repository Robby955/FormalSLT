/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectorySleepingCountableTiltPACBayes

/-!
# Measurable-state sleeping predictable-tilt master processes

This module supplies the measurable-process foundation for countable catalogs
of prefix-predictable trajectory tilts on arbitrary measurable state spaces.
Joint score measurability and prefix measurability of every catalog atom give
filtered and ambient joint path--hypothesis measurability of the exact sleeping
master process. Uniform boundedness gives a deterministic finite-time envelope.

The module deliberately stops at these reusable process-level facts. It does
not assert a PAC-Bayes event, select a strategy atom from observed data, or
derive normalized or ordinary risk.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

/-- Measurability contract for a predeclared catalog of prefix-predictable
trajectory tilts on a general measurable state space. -/
def StronglyMeasurableTrajectoryPredictableTiltCatalog
    (strategy : Nat -> TrajectoryPredictableTilt Z) : Prop :=
  forall j n, StronglyMeasurable (strategy j n)

/-- Evaluating a measurable prefix rule on the observed prefix gives a
predictable path process without any countability assumption on the state. -/
theorem observedTrajectoryPredictableTilt_stronglyAdapted_of_stronglyMeasurable
    (tilt : TrajectoryPredictableTilt Z)
    (htilt : forall n, StronglyMeasurable (tilt n)) :
    StronglyAdapted (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryPredictableTilt tilt) := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (htilt n).comp_measurable (comap_measurable _)

private theorem stronglyMeasurable_measurablePredictableTiltForwardPredictor
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X : Nat -> Alpha -> Real) {k : Nat}
    (hX : forall i, i < k -> StronglyMeasurable (X i)) :
    StronglyMeasurable (forwardPredictorProcess X k) := by
  unfold forwardPredictorProcess forwardPredictor
  split_ifs
  · exact stronglyMeasurable_const
  · unfold forwardPrefixMean
    have hsum : StronglyMeasurable (∑ i ∈ Finset.range k, X i) :=
      Finset.stronglyMeasurable_sum (Finset.range k) fun i hi =>
        hX i (Finset.mem_range.mp hi)
    simpa only [Finset.sum_apply, div_eq_mul_inv] using
      hsum.mul_const ((k : Real)⁻¹)

private theorem
    stronglyMeasurable_measurablePredictableTiltForwardLowerProcess
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X mean lambda : Nat -> Alpha -> Real) {n : Nat}
    (hX : forall k, k < n -> StronglyMeasurable (X k))
    (hmean : forall k, k < n -> StronglyMeasurable (mean k))
    (hlambda : forall k, k < n -> StronglyMeasurable (lambda k)) :
    StronglyMeasurable
      (forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean lambda n) := by
  have hpredictor (k : Nat) (hk : k < n) :
      StronglyMeasurable (forwardPredictorProcess X k) :=
    stronglyMeasurable_measurablePredictableTiltForwardPredictor X
      (fun i hi => hX i (hi.trans hk))
  have hscore : StronglyMeasurable
      (∑ k ∈ Finset.range n, fun a =>
        lambda k a * (mean k a - X k a) -
          forwardEmpiricalBernsteinPsi (lambda k a) *
            (X k a - forwardPredictorProcess X k a) ^ 2) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hpsi := stronglyMeasurable_forwardEmpiricalBernsteinPsi_comp
      (hlambda k hklt)
    exact ((hlambda k hklt).mul ((hmean k hklt).sub (hX k hklt))).sub
      (hpsi.mul (((hX k hklt).sub (hpredictor k hklt)).pow 2))
  have hexp := Real.continuous_exp.comp_stronglyMeasurable hscore
  convert hexp using 1
  funext a
  rw [forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq]
  simp only [Finset.sum_apply]

/-- A fixed atom of a measurable prefix-predictable strategy catalog is jointly
measurable in the filtered path and hypothesis parameter. This is the summand
used by the finite-prefix sleeping master process. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltComponentProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    (j n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2))
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j)
          n q.1) := by
  let mProd : MeasurableSpace ((Nat -> Z) × Theta) :=
    MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)
  letI : MeasurableSpace ((Nat -> Z) × Theta) := mProd
  change StronglyMeasurable
    (fun q : (Nat -> Z) × Theta =>
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        (observedTrajectoryScore (score q.2))
        (conditionalTrajectoryRisk K (score q.2))
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j)
        n q.1)
  let X : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    observedTrajectoryScore (score q.2) k q.1
  let mean : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    conditionalTrajectoryRisk K (score q.2) k q.1
  let lambda : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    sleepingStrategy
      (observedTrajectoryPredictableStrategyCatalog strategy) j k q.1
  have hX : forall k, k < n -> StronglyMeasurable (X k) := by
    intro k hk
    dsimp [X]
    exact stronglyMeasurable_observedTrajectoryScore_joint_filtered
      hscore_joint (Nat.succ_le_iff.mpr hk)
  have hmean : forall k, k < n -> StronglyMeasurable (mean k) := by
    intro k hk
    dsimp [mean]
    exact stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
      K hscore_joint (Nat.le_of_lt hk)
  have hcatalog : forall i, StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryPredictableStrategyCatalog strategy i) := by
    intro i
    exact observedTrajectoryPredictableTilt_stronglyAdapted_of_stronglyMeasurable
      (strategy i) (hstrategy_meas i)
  have hlambda : forall k, k < n -> StronglyMeasurable (lambda k) := by
    intro k hk
    have hpath : StronglyMeasurable[
        (Filtration.piLE (X := fun _ : Nat => Z)) n]
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k) :=
      ((sleepingStrategy_stronglyAdapted
        (observedTrajectoryPredictableStrategyCatalog strategy)
        hcatalog j) k).mono
          ((Filtration.piLE (X := fun _ : Nat => Z)).mono
            (Nat.le_of_lt hk))
    dsimp [lambda]
    exact hpath.comp_measurable measurable_fst
  convert
    (stronglyMeasurable_measurablePredictableTiltForwardLowerProcess
      X mean lambda hX hmean hlambda) using 1
  funext q
  rfl

/-- Ambient joint measurability of one sleeping strategy component follows
from its filtered-product measurability. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltComponentProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    (j n : Nat) :
    StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2))
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j)
          n q.1) := by
  exact stronglyMeasurable_trajectory_ambient_of_filtered_prod n
    (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltComponentProcess_filtered
      K score hscore_joint strategy hstrategy_meas j n)

/-- Joint score measurability and prefix measurability of the strategy catalog
give filtered joint path--hypothesis measurability of the exact sleeping
master process on an arbitrary measurable state space. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) := by
  let mProd : MeasurableSpace ((Nat -> Z) × Theta) :=
    MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)
  letI : MeasurableSpace ((Nat -> Z) × Theta) := mProd
  change StronglyMeasurable
    (fun q : (Nat -> Z) × Theta =>
      continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy q.2 n q.1)
  have hsum : StronglyMeasurable
      (∑ j ∈ Finset.range n, fun q : (Nat -> Z) × Theta =>
        polynomialEpochWeight j *
          forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
            (observedTrajectoryScore (score q.2))
            (conditionalTrajectoryRisk K (score q.2))
            (sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j)
            n q.1) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun j _ =>
      (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltComponentProcess_filtered
        K score hscore_joint strategy hstrategy_meas j n).const_mul
          (polynomialEpochWeight j)
  have hadd : StronglyMeasurable
      ((fun _ : ((Nat -> Z) × Theta) => polynomialSleepingTail n) +
        ∑ j ∈ Finset.range n, fun q : (Nat -> Z) × Theta =>
          polynomialEpochWeight j *
            forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
              (observedTrajectoryScore (score q.2))
              (conditionalTrajectoryRisk K (score q.2))
              (sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy) j)
              n q.1) :=
    stronglyMeasurable_const.add hsum
  convert hadd using 1
  funext q
  simp only [Pi.add_apply, Finset.sum_apply]
  rfl

/-- Ambient joint measurability follows from the filtered-product result. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (hstrategy_meas :
      StronglyMeasurableTrajectoryPredictableTiltCatalog strategy)
    (n : Nat) :
    StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) := by
  exact stronglyMeasurable_trajectory_ambient_of_filtered_prod n
    (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_filtered
      K score hscore_joint strategy hstrategy_meas n)

/-- Uniform boundedness supplies a deterministic finite-time envelope for the
arbitrary-state time-varying sleeping master process. -/
theorem continuousMeasurableTrajectorySleepingPredictableTiltMasterProcess_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {L : Real} (hL1 : L < 1)
    (hstrategy_range : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    (theta : Theta) (n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x <=
      polynomialSleepingTail n +
        ∑ j ∈ Finset.range n,
          polynomialEpochWeight j * Real.exp ((n : Real) * L) := by
  unfold continuousTrajectorySleepingPredictableTiltMasterProcess
    continuousSleepingForwardPredictableMeanMasterProcess
    countableSleepingForwardPredictableMeanMasterProcess
    countableSleepingProcessMixture
  have hsum :
      (∑ j ∈ Finset.range n,
        polynomialEpochWeight j *
          forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
            (observedTrajectoryScore (score theta))
            (conditionalTrajectoryRisk K (score theta))
            (sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j)
            n x) <=
        ∑ j ∈ Finset.range n,
          polynomialEpochWeight j * Real.exp ((n : Real) * L) := by
    apply Finset.sum_le_sum
    intro j _hj
    apply mul_le_mul_of_nonneg_left _ (polynomialEpochWeight_pos j).le
    exact forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_le_exp hL1
      (fun k path => observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k path)
      (fun k path =>
        (conditionalTrajectoryRisk_mem_Icc_of_joint K
          (jointlyStronglyMeasurableTrajectoryScore_section
            hscore_joint theta) (hscore_unit theta) k path).2)
      (fun k path =>
        sleepingStrategy_mem_Icc
          (strategy := observedTrajectoryPredictableStrategyCatalog strategy)
          (fun i r y => hstrategy_range i r
            (Preorder.frestrictLe r y)) j k path)
      n x
  linarith

end

end FormalSLT.StochasticDynamics
