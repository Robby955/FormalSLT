/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectorySleepingCountableTiltPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingPredictableTiltOrdinaryRisk

/-!
# Time-varying predictable-tilt suffix risk on measurable state spaces

This module removes the finite-state assumption from the time-varying
predictable-tilt ordinary-risk theorem.  The score family is jointly strongly
measurable in the hypothesis, complete prefix, and next state.  Each strategy
atom is strongly measurable in the prefix available before its next bet.

One outer-probability event then controls every observed path in the event,
every eligible path-selected posterior, every predeclared strategy atom, and
every nonempty reporting suffix with positive realized exposure.  The target
is ordinary posterior-averaged conditional risk encountered on that suffix.
The conversion from nonuniform realized tilt weights pays twice their finite
total-variation discrepancy from uniform suffix weights.

No finite, countable, topological, standard-Borel, stationarity, or
finite-memory assumption is imposed on the state space.  The conclusion is
not a population, future, deployment, or stationary-risk statement.
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

/-- Joint score measurability and prefix measurability of the strategy catalog
give filtered joint path--hypothesis measurability of the exact sleeping
master on an arbitrary measurable state space. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMaster_filtered
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
  let X : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    observedTrajectoryScore (score q.2) k q.1
  let mean : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    conditionalTrajectoryRisk K (score q.2) k q.1
  let lambda : Nat -> Nat -> ((Nat -> Z) × Theta) -> Real := fun j k q =>
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
  have hcatalog : forall j, StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryPredictableStrategyCatalog strategy j) := by
    intro j
    exact observedTrajectoryPredictableTilt_stronglyAdapted_of_stronglyMeasurable
      (strategy j) (hstrategy_meas j)
  have hlambda (j : Nat) : forall k, k < n ->
      StronglyMeasurable (lambda j k) := by
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
  have hcomponent (j : Nat) : StronglyMeasurable (fun q =>
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean (lambda j) n q) :=
    stronglyMeasurable_measurablePredictableTiltForwardLowerProcess
      X mean (lambda j) hX hmean (hlambda j)
  have hsum : StronglyMeasurable
      (∑ j ∈ Finset.range n, fun q =>
        polynomialEpochWeight j *
          forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
            X mean (lambda j) n q) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun j _ =>
      (hcomponent j).const_mul (polynomialEpochWeight j)
  have hadd : StronglyMeasurable
      ((fun _ : ((Nat -> Z) × Theta) => polynomialSleepingTail n) +
        ∑ j ∈ Finset.range n, fun q =>
          polynomialEpochWeight j *
            forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
              X mean (lambda j) n q) :=
    stronglyMeasurable_const.add hsum
  convert hadd using 1
  funext q
  simp only [Pi.add_apply, Finset.sum_apply]
  rfl

/-- Ambient joint measurability follows from the filtered product result. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMaster_ambient
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
    (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMaster_filtered
      K score hscore_joint strategy hstrategy_meas n)

/-- Uniform boundedness supplies a deterministic finite-time envelope for the
arbitrary-state time-varying sleeping master. -/
theorem continuousMeasurableTrajectorySleepingPredictableTiltMaster_le
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

/-! ## Common-event normalized-risk theorem -/

/-- One outer-mass event controls normalized encountered conditional suffix
risk for every eligible path-selected posterior, wake time, reporting time,
and predeclared measurable predictable strategy atom on an arbitrary
measurable state space.

The positive-exposure premise is explicit because normalization divides by
the realized total tilt.  The posterior, wake, and reporting time may be
chosen from the path after the event is realized; the strategy catalog itself
is fixed before the path is observed. -/
theorem
    exists_continuousMeasurableTrajectorySleepingPredictableTiltPACBayes_normalized_event
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
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              0 < continuousSleepingPredictableTiltExposure
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j n x ->
              continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
                  K score strategy posterior j n x <
                continuousTrajectorySleepingPredictableTiltBoundary
                  prior posterior score strategy delta j n x := by
  let F := Filtration.piLE (X := fun _ : Nat => Z)
  let mu := trajectoryMeasure K x0
  have hjoint_filtered (n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod (F n)
        (inferInstance : MeasurableSpace Theta)]
        (fun q : (Nat -> Z) × Theta =>
          continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy q.2 n q.1) := by
    simpa [F] using
      (stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMaster_filtered
        K score hscore_joint strategy hstrategy_meas n)
  have hjoint_ambient (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) :=
    stronglyMeasurable_continuousMeasurableTrajectorySleepingPredictableTiltMaster_ambient
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
          K score strategy q.2 n q.1) (mu.prod prior) := by
    refine Integrable.of_bound (hjoint_ambient n).aestronglyMeasurable
      (polynomialSleepingTail n +
        ∑ j ∈ Finset.range n,
          polynomialEpochWeight j * Real.exp ((n : Real) * L)) ?_
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_pos (hmaster_pos q.2 n q.1)]
      exact continuousMeasurableTrajectorySleepingPredictableTiltMaster_le
        K score hscore_unit hscore_joint strategy hL1 hstrategy_range
          q.2 n q.1
  have hM_int_next (n : Nat) : Integrable
      (fun q : Theta × (Nat -> Z) =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.1 (n + 1) q.2) (prior.prod mu) := by
    simpa [Function.comp_def] using (hM_int_current (n + 1)).swap
  have hM_int_restrict (n : Nat) {s : Set (Nat -> Z)} : Integrable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) ((mu.restrict s).prod prior) :=
    (hM_int_current n).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hprior_integrable (n : Nat) (x : Nat -> Z) : Integrable
      (fun theta => continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x) prior := by
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
      exact continuousMeasurableTrajectorySleepingPredictableTiltMaster_le
        K score hscore_unit hscore_joint strategy hL1 hstrategy_range
          theta n x
  have h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy)) := by
    intro n
    change StronglyMeasurable[F n]
      (fun x => ∫ theta,
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy theta n x ∂prior)
    letI : MeasurableSpace (Nat -> Z) := F n
    exact StronglyMeasurable.integral_prod_right' (hjoint_filtered n)
  have h_integrable_mix (n : Nat) : Integrable
      (continuousPriorMixtureProcess prior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy) n) mu :=
    (hM_int_current n).integral_prod_left
  have hstrategy_adapted (j : Nat) : StronglyAdapted F
      (observedTrajectoryPredictableStrategyCatalog strategy j) := by
    simpa [F, observedTrajectoryPredictableStrategyCatalog] using
      (observedTrajectoryPredictableTilt_stronglyAdapted_of_stronglyMeasurable
        (strategy j) (hstrategy_meas j))
  have hstrategy_observed_range : forall j k x,
      observedTrajectoryPredictableStrategyCatalog strategy j k x ∈
        Set.Icc (0 : Real) L := by
    intro j k x
    exact hstrategy_range j k (Preorder.frestrictLe k x)
  rcases
      exists_continuousSleepingPredictableTiltPACBayes_normalized_event
        (mu := mu) (F := F) prior hL1 hdelta
        (fun theta =>
          observedTrajectoryScore_incrementAdapted_parameterized_of_joint
            hscore_joint theta)
        (fun theta =>
          conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
            K hscore_joint theta)
        hstrategy_adapted
        (fun theta k x => observedTrajectoryScore_mem_Icc
          (hscore_unit theta) k x)
        hstrategy_observed_range
        (fun theta k =>
          observedTrajectoryScore_condExp_parameterized_of_joint
            K x0 hscore_joint hscore_unit theta k)
        h_adapted_mix h_integrable_mix hM_int_next
        (fun n _s _hs _hfinite => hM_int_restrict (n + 1))
        hM_int_current (fun n _s _hs _hfinite => hM_int_restrict n)
        hprior_integrable with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr j n hjn hexposure
  letI : IsProbabilityMeasure posterior := hposterior
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
          K score strategy theta n x)) posterior := by
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
        exact continuousMeasurableTrajectorySleepingPredictableTiltMaster_le
          K score hscore_unit hscore_joint strategy hL1 hstrategy_range
            theta n x
      have hupper := Real.log_le_log (hmaster_pos theta n x) hupper_master
      apply abs_le.mpr
      constructor
      · have htail_abs := neg_abs_le (Real.log (polynomialSleepingTail n))
        have hC_abs : 0 <= |Real.log C| := abs_nonneg _
        linarith
      · have hC_abs := le_abs_self (Real.log C)
        have htail_abs : 0 <= |Real.log (polynomialSleepingTail n)| := abs_nonneg _
        linarith
  have hX_parameter (k : Nat) : StronglyMeasurable
      (fun theta => observedTrajectoryScore (score theta) k x) :=
    stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      hscore_joint k x
  have hX_unit (theta : Theta) (k : Nat) :
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    observedTrajectoryScore_mem_Icc (hscore_unit theta) k x
  have hconditional : Integrable
      (fun theta => continuousSleepingWeightedConditionalMeanAt
        (fun theta => conditionalTrajectoryRisk K (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedConditionalMeanAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (integrable_conditionalTrajectoryRisk_parameter_of_joint
        K hscore_joint hscore_unit posterior k x).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hobservation : Integrable
      (fun theta => continuousSleepingWeightedObservationAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedObservationAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            observedTrajectoryScore (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      have hX_int : Integrable
          (fun theta => observedTrajectoryScore (score theta) k x)
          posterior := by
        refine Integrable.of_bound (hX_parameter k).aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun theta => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit theta k).1]
          exact (hX_unit theta k).2
      exact hX_int.const_mul
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hpenalty : Integrable
      (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    let Xparameter : Nat -> Theta -> Real := fun k theta =>
      observedTrajectoryScore (score theta) k x
    have hXparameter (k : Nat) : StronglyMeasurable (Xparameter k) := by
      simpa only [Xparameter] using hX_parameter k
    unfold continuousSleepingPredictorQuadraticPenaltyAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy) j k x) *
            (Xparameter k theta -
              forwardPredictorProcess Xparameter k theta) ^ 2) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      have hpredictor : StronglyMeasurable
          (forwardPredictorProcess Xparameter k) :=
        stronglyMeasurable_measurablePredictableTiltForwardPredictor
          Xparameter (fun i _hi => hXparameter i)
      have hsq_meas : StronglyMeasurable (fun theta =>
          (Xparameter k theta - forwardPredictorProcess Xparameter k theta) ^ 2) :=
        ((hXparameter k).sub hpredictor).pow 2
      have hsq_int : Integrable (fun theta =>
          (Xparameter k theta - forwardPredictorProcess Xparameter k theta) ^ 2)
          posterior := by
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
            (observedTrajectoryPredictableStrategyCatalog strategy) j k x))
    convert hsum using 1
    funext theta
    simp only [Xparameter, Finset.sum_apply, forwardPredictorProcess]
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr
    j n hjn hexposure hlog hconditional hobservation hpenalty
  simpa [continuousTrajectorySleepingPosteriorNormalizedConditionalRisk,
    continuousTrajectorySleepingPredictableTiltBoundary,
    continuousTrajectorySleepingPredictableTiltMasterProcess] using hbound

/-! ## Common-event ordinary-risk theorem -/

/-- One outer-mass event controls ordinary encountered conditional suffix risk
on every nonempty path-selected suffix, for every eligible path-selected
posterior and every predeclared measurable predictable strategy atom, on an
arbitrary measurable state space.

The conclusion is simultaneous in `x`, `posterior`, `j`, and `n` in that
order.  Positive realized exposure is an explicit premise.  The conversion
from the normalized tilt-weighted risk pays twice the exact finite
uniform-weight discrepancy. -/
theorem
    exists_continuousMeasurableTrajectorySleepingPredictableTiltPACBayes_ordinarySuffixRisk_event
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
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              0 < continuousSleepingPredictableTiltExposure
                (observedTrajectoryPredictableStrategyCatalog strategy)
                j n x ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior j n x <
                continuousTrajectorySleepingPredictableTiltOrdinarySuffixBoundary
                  prior posterior score strategy delta j n x := by
  rcases
      exists_continuousMeasurableTrajectorySleepingPredictableTiltPACBayes_normalized_event
        K x0 score hscore_unit hscore_joint strategy hstrategy_meas
          hL1 hstrategy_range prior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr j n hjn hexposure
  letI : IsProbabilityMeasure posterior := hposterior
  have hweighted := hgood x hx posterior hposterior hposterior_prior hllr
    j n hjn hexposure
  have hmean_meas (k : Nat) : StronglyMeasurable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x) :=
    stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
      K hscore_joint k x
  have hX_meas (k : Nat) : StronglyMeasurable
      (fun theta => observedTrajectoryScore (score theta) k x) :=
    stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
      hscore_joint k x
  have hmean_unit (theta : Theta) (k : Nat) :
      conditionalTrajectoryRisk K (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    conditionalTrajectoryRisk_mem_Icc_of_joint K
      (jointlyStronglyMeasurableTrajectoryScore_section
        hscore_joint theta) (hscore_unit theta) k x
  have hX_unit (theta : Theta) (k : Nat) :
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    observedTrajectoryScore_mem_Icc (hscore_unit theta) k x
  have hmean_int (k : Nat) : Integrable
      (fun theta => conditionalTrajectoryRisk K (score theta) k x) posterior := by
    refine Integrable.of_bound (hmean_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmean_unit theta k).1]
      exact (hmean_unit theta k).2
  have hX_int (k : Nat) : Integrable
      (fun theta => observedTrajectoryScore (score theta) k x) posterior := by
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit theta k).1]
      exact (hX_unit theta k).2
  have hordinaryConditional : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        conditionalTrajectoryRisk K (score theta) k x) / (n - j : Nat))
      posterior := by
    apply Integrable.div_const
    have hsum : Integrable
        (∑ k ∈ Finset.Ico j n, fun theta =>
          conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact hmean_int k
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hordinaryEmpirical : Integrable (fun theta =>
      (∑ k ∈ Finset.Ico j n,
        observedTrajectoryScore (score theta) k x) / (n - j : Nat))
      posterior := by
    apply Integrable.div_const
    have hsum : Integrable
        (∑ k ∈ Finset.Ico j n, fun theta =>
          observedTrajectoryScore (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact hX_int k
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedConditionalAt : Integrable (fun theta =>
      continuousSleepingWeightedConditionalMeanAt
        (fun theta => conditionalTrajectoryRisk K (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedConditionalMeanAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (hmean_int k).const_mul
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedEmpiricalAt : Integrable (fun theta =>
      continuousSleepingWeightedObservationAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta j n x) posterior := by
    unfold continuousSleepingWeightedObservationAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) j k x *
            observedTrajectoryScore (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (hX_int k).const_mul
        (sleepingStrategy
          (observedTrajectoryPredictableStrategyCatalog strategy) j k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hweightedConditional : Integrable (fun theta =>
      continuousSleepingWeightedConditionalMeanAt
          (fun theta => conditionalTrajectoryRisk K (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior := hweightedConditionalAt.div_const _
  have hweightedEmpirical : Integrable (fun theta =>
      continuousSleepingWeightedObservationAt
          (fun theta => observedTrajectoryScore (score theta))
          (observedTrajectoryPredictableStrategyCatalog strategy)
          theta j n x /
        continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog strategy) j n x)
      posterior := hweightedEmpiricalAt.div_const _
  have hconditional :=
    abs_continuousTrajectoryPosteriorAverageConditionalSuffixRisk_sub_normalized_le
      K score posterior strategy hjn x hexposure
      (fun theta k => hmean_unit theta k)
      hordinaryConditional hweightedConditional
  have hempirical :=
    abs_continuousTrajectoryPosteriorEmpiricalSuffixRisk_sub_normalized_le
      score posterior strategy hjn x hexposure
      (fun theta k => hX_unit theta k)
      hordinaryEmpirical hweightedEmpirical
  exact continuousTrajectorySleepingPredictableTilt_ordinaryRisk_of_weighted
    K score posterior prior strategy delta j n x hweighted
      hconditional hempirical

end

end FormalSLT.StochasticDynamics
