/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingCountableTiltPACBayes

/-!
# Sleeping suffix PAC-Bayes bounds on arbitrary measurable state spaces

This module connects the generic sleeping predictable-process machinery to
complete-prefix trajectory kernels on an arbitrary measurable state space.
Constant post-wake tilts need no countability or discrete-state measurability
shortcut.  Joint score measurability supplies the filtered product sections,
and a supplied Markov kernel supplies the conditional-risk process directly.

The resulting event is uniform over the eligible hypothesis posterior, wake
time, reporting time, and a predeclared countable tilt catalog.  The catalog is
confidence allocation, not coin betting, a master strategy posterior, or
parameter-free inference.  The target is encountered conditional suffix risk,
not future, stationary, population, or deployment risk.  No standard-Borel or
disintegration assumption is introduced.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

private theorem stronglyMeasurable_measurableSleepingForwardPredictor
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
    stronglyMeasurable_measurableSleepingForwardLowerProcess
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
    stronglyMeasurable_measurableSleepingForwardPredictor X
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

/-- For a fixed constant-tilt catalog, the complete sleeping master is jointly
measurable in the filtered path and hypothesis parameter on any measurable
state space. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingConstantTiltMaster_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (eta : Nat -> Real) (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score (countableConstantTrajectoryTiltCatalog eta) q.2 n q.1) := by
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
      (observedTrajectoryPredictableStrategyCatalog
        (countableConstantTrajectoryTiltCatalog eta)) j k q.1
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
  have hlambda (j : Nat) : forall k, k < n ->
      StronglyMeasurable (lambda j k) := by
    intro k _hk
    dsimp [lambda]
    unfold sleepingStrategy observedTrajectoryPredictableStrategyCatalog
      observedTrajectoryPredictableTilt countableConstantTrajectoryTiltCatalog
    split_ifs <;> exact stronglyMeasurable_const
  have hcomponent (j : Nat) : StronglyMeasurable (fun q =>
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean (lambda j) n q) :=
    stronglyMeasurable_measurableSleepingForwardLowerProcess
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

/-- Ambient product measurability of the arbitrary-state constant-tilt
sleeping master. -/
theorem
    stronglyMeasurable_continuousMeasurableTrajectorySleepingConstantTiltMaster_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (eta : Nat -> Real) (n : Nat) :
    StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score (countableConstantTrajectoryTiltCatalog eta) q.2 n q.1) := by
  exact stronglyMeasurable_trajectory_ambient_of_filtered_prod n
    (stronglyMeasurable_continuousMeasurableTrajectorySleepingConstantTiltMaster_filtered
      K score hscore_joint eta n)

private theorem stronglyAdapted_observedConstantTiltCatalog
    (eta : Nat -> Real) (j : Nat) :
    StronglyAdapted (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryPredictableStrategyCatalog
        (countableConstantTrajectoryTiltCatalog eta) j) := by
  intro n
  change StronglyMeasurable[(Filtration.piLE (X := fun _ : Nat => Z)) n]
    (fun _ : Nat -> Z => eta j)
  exact stronglyMeasurable_const

/-- Deterministic finite-time envelope for the arbitrary-state constant-tilt
sleeping master. -/
theorem continuousMeasurableTrajectorySleepingConstantTiltMaster_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (eta : Nat -> Real) {L : Real} (hL1 : L < 1)
    (heta_range : forall j, eta j ∈ Set.Icc (0 : Real) L)
    (theta : Theta) (n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingPredictableTiltMasterProcess
        K score (countableConstantTrajectoryTiltCatalog eta) theta n x <=
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
              (observedTrajectoryPredictableStrategyCatalog
                (countableConstantTrajectoryTiltCatalog eta)) j)
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
      (fun k path => by
        exact sleepingStrategy_mem_Icc
          (strategy := observedTrajectoryPredictableStrategyCatalog
            (countableConstantTrajectoryTiltCatalog eta))
          (fun i r y => by
            simpa [observedTrajectoryPredictableStrategyCatalog,
              observedTrajectoryPredictableTilt,
              countableConstantTrajectoryTiltCatalog] using heta_range i)
          j k path)
      n x
  linarith

/-- One outer-mass event controls ordinary encountered conditional risk on
every nonempty suffix for a fixed positive constant-tilt catalog, without any
finite or discrete-state assumption. -/
theorem
    exists_continuousMeasurableTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (eta : Nat -> Real) {L : Real}
    (heta_pos : forall j, 0 < eta j)
    (heta_upper : forall j, eta j <= L) (hL1 : L < 1)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall w n : Nat, w < n ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior w n x <
                continuousTrajectorySleepingConstantTiltSuffixBoundary
                  prior posterior score eta delta w n x := by
  let strategy := countableConstantTrajectoryTiltCatalog (Z := Z) eta
  let F := Filtration.piLE (X := fun _ : Nat => Z)
  let mu := trajectoryMeasure K x0
  have hjoint_filtered (n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod (F n)
        (inferInstance : MeasurableSpace Theta)]
        (fun q : (Nat -> Z) × Theta =>
          continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy q.2 n q.1) := by
    simpa [F, strategy] using
      (stronglyMeasurable_continuousMeasurableTrajectorySleepingConstantTiltMaster_filtered
        K score hscore_joint eta n)
  have hjoint_ambient (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) := by
    simpa [strategy] using
      (stronglyMeasurable_continuousMeasurableTrajectorySleepingConstantTiltMaster_ambient
        K score hscore_joint eta n)
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
      simpa [strategy] using
        (continuousMeasurableTrajectorySleepingConstantTiltMaster_le
          K score hscore_unit hscore_joint eta hL1
          (fun j => ⟨(heta_pos j).le, heta_upper j⟩) q.2 n q.1)
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
      simpa [strategy] using
        (continuousMeasurableTrajectorySleepingConstantTiltMaster_le
          K score hscore_unit hscore_joint eta hL1
          (fun j => ⟨(heta_pos j).le, heta_upper j⟩) theta n x)
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
  have hstrategy_range : forall j k x,
      observedTrajectoryPredictableStrategyCatalog strategy j k x ∈
        Set.Icc (0 : Real) L := by
    intro j k x
    simpa [strategy, observedTrajectoryPredictableStrategyCatalog,
      observedTrajectoryPredictableTilt,
      countableConstantTrajectoryTiltCatalog] using
        (show eta j ∈ Set.Icc (0 : Real) L from
          ⟨(heta_pos j).le, heta_upper j⟩)
  rcases
      exists_continuousSleepingPredictableTiltPACBayes_normalized_event
        (mu := mu) (F := F) prior hL1 hdelta
        (fun theta =>
          observedTrajectoryScore_incrementAdapted_parameterized_of_joint
            hscore_joint theta)
        (fun theta =>
          conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
            K hscore_joint theta)
        (fun j => by
          simpa [strategy] using
            (stronglyAdapted_observedConstantTiltCatalog
              (Z := Z) eta j))
        (fun theta k x => observedTrajectoryScore_mem_Icc
          (hscore_unit theta) k x)
        hstrategy_range
        (fun theta k =>
          observedTrajectoryScore_condExp_parameterized_of_joint
            K x0 hscore_joint hscore_unit theta k)
        h_adapted_mix h_integrable_mix hM_int_next
        (fun n _s _hs _hfinite => hM_int_restrict (n + 1))
        hM_int_current (fun n _s _hs _hfinite => hM_int_restrict n)
        hprior_integrable with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr w n hwn
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
        simpa [strategy] using
          (continuousMeasurableTrajectorySleepingConstantTiltMaster_le
            K score hscore_unit hscore_joint eta hL1
            (fun j => ⟨(heta_pos j).le, heta_upper j⟩) theta n x)
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
        theta w n x) posterior := by
    unfold continuousSleepingWeightedConditionalMeanAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) w k x *
            conditionalTrajectoryRisk K (score theta) k x) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      exact (integrable_conditionalTrajectoryRisk_parameter_of_joint
        K hscore_joint hscore_unit posterior k x).const_mul
          (sleepingStrategy
            (observedTrajectoryPredictableStrategyCatalog strategy) w k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hobservation : Integrable
      (fun theta => continuousSleepingWeightedObservationAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta w n x) posterior := by
    unfold continuousSleepingWeightedObservationAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          sleepingStrategy
              (observedTrajectoryPredictableStrategyCatalog strategy) w k x *
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
          (observedTrajectoryPredictableStrategyCatalog strategy) w k x)
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hpenalty : Integrable
      (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
        (fun theta => observedTrajectoryScore (score theta))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        theta w n x) posterior := by
    let Xparameter : Nat -> Theta -> Real := fun k theta =>
      observedTrajectoryScore (score theta) k x
    have hXparameter (k : Nat) : StronglyMeasurable (Xparameter k) := by
      simpa only [Xparameter] using hX_parameter k
    unfold continuousSleepingPredictorQuadraticPenaltyAt
    have hsum : Integrable
        (∑ k ∈ Finset.range n, fun theta =>
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy
                (observedTrajectoryPredictableStrategyCatalog strategy) w k x) *
            (Xparameter k theta -
              forwardPredictorProcess Xparameter k theta) ^ 2) posterior := by
      apply integrable_finsetSum'
      intro k _hk
      have hpredictor : StronglyMeasurable
          (forwardPredictorProcess Xparameter k) :=
        stronglyMeasurable_measurableSleepingForwardPredictor
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
            (observedTrajectoryPredictableStrategyCatalog strategy) w k x))
    convert hsum using 1
    funext theta
    simp only [Xparameter, Finset.sum_apply, forwardPredictorProcess]
  have hexposure : 0 < continuousSleepingPredictableTiltExposure
      (observedTrajectoryPredictableStrategyCatalog strategy) w n x := by
    simpa [strategy] using
      (show 0 < continuousSleepingPredictableTiltExposure
          (observedTrajectoryPredictableStrategyCatalog
            (countableConstantTrajectoryTiltCatalog eta)) w n x by
        rw [continuousTrajectorySleepingExposure_countableConstant eta hwn.le x]
        exact mul_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hwn)) (heta_pos w))
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr
    w n hwn hexposure hlog hconditional hobservation hpenalty
  have htrajectory :
      continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
          K score strategy posterior w n x <
        continuousTrajectorySleepingPredictableTiltBoundary
          prior posterior score strategy delta w n x := by
    simpa [continuousTrajectorySleepingPosteriorNormalizedConditionalRisk,
      continuousTrajectorySleepingPredictableTiltBoundary,
      continuousTrajectorySleepingPredictableTiltMasterProcess,
      strategy] using hbound
  simpa [strategy,
    continuousTrajectorySleepingPosteriorNormalizedConditionalRisk_countableConstant
      K score posterior eta hwn (heta_pos w) x,
    continuousTrajectorySleepingPredictableTiltBoundary_countableConstant
      prior posterior score eta delta hwn (heta_pos w) x] using htrajectory

/-- Confidence allocation over a predeclared countable constant-tilt catalog
gives one arbitrary-state event simultaneous in posterior, atom, wake, and
reporting time. -/
theorem
    exists_continuousMeasurableTrajectorySleepingCountableTiltPACBayes_suffixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (q lam : Nat -> Real)
    (hq_pos : forall a, 0 < q a) (hq_sum : HasSum q 1)
    {L : Real} (hlam_pos : forall a, 0 < lam a)
    (hlam_upper : forall a, lam a <= L) (hL1 : L < 1)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall a w n : Nat, w < n ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior w n x <
                continuousTrajectorySleepingCountableTiltSuffixBoundary
                  prior posterior score q lam delta a w n x := by
  classical
  let mu := trajectoryMeasure K x0
  have hatom : forall a : Nat,
      ∃ event : Set (Nat -> Z),
        mu.real eventᶜ <= delta * q a ∧
          forall x, x ∈ event ->
            forall posterior : Measure Theta,
              IsProbabilityMeasure posterior -> posterior ≪ prior ->
              Integrable (llr posterior prior) posterior ->
              forall w n : Nat, w < n ->
                continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                    K score posterior w n x <
                  continuousTrajectorySleepingConstantTiltSuffixBoundary
                    prior posterior score (fun _ => lam a)
                      (delta * q a) w n x := by
    intro a
    exact
      exists_continuousMeasurableTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
        K x0 score hscore_unit hscore_joint (fun _ => lam a)
        (fun _ => hlam_pos a) (fun _ => hlam_upper a) hL1 prior
        (mul_pos hdelta (hq_pos a))
  choose event hmass hgood using hatom
  let goodEvent : Set (Nat -> Z) := ⋂ a, event a
  refine ⟨goodEvent, ?_, ?_⟩
  · have hatomENNReal : forall a,
        mu (event a)ᶜ <= ENNReal.ofReal (delta * q a) := by
      intro a
      calc
        mu (event a)ᶜ = ENNReal.ofReal (mu.real (event a)ᶜ) := by
          rw [ofReal_measureReal]
        _ <= ENNReal.ofReal (delta * q a) :=
          ENNReal.ofReal_le_ofReal (hmass a)
    have hallocated : HasSum (fun a => delta * q a) delta := by
      simpa using hq_sum.mul_left delta
    have hsummable : Summable (fun a => delta * q a) :=
      hallocated.summable
    have hnonneg : forall a, 0 <= delta * q a :=
      fun a => mul_nonneg hdelta.le (hq_pos a).le
    have hunionENNReal : mu (⋃ a, (event a)ᶜ) <= ENNReal.ofReal delta := by
      calc
        mu (⋃ a, (event a)ᶜ) <= ∑' a, mu (event a)ᶜ := measure_iUnion_le _
        _ <= ∑' a, ENNReal.ofReal (delta * q a) :=
          ENNReal.tsum_le_tsum hatomENNReal
        _ = ENNReal.ofReal delta := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable,
            hallocated.tsum_eq]
    change mu.real goodEventᶜ <= delta
    rw [show goodEventᶜ = ⋃ a, (event a)ᶜ by simp [goodEvent]]
    calc
      mu.real (⋃ a, (event a)ᶜ) <= (ENNReal.ofReal delta).toReal := by
        exact ENNReal.toReal_mono (by simp) hunionENNReal
      _ = delta := ENNReal.toReal_ofReal hdelta.le
  · intro x hx posterior hposterior hposterior_prior hllr a w n hwn
    have hxa : x ∈ event a := Set.mem_iInter.mp hx a
    have hbound := hgood a x hxa posterior hposterior hposterior_prior hllr
      w n hwn
    simpa [continuousTrajectorySleepingCountableTiltSuffixBoundary_eq_constant]
      using hbound

/-- Polynomial confidence weights and geometric fixed tilts specialize the
arbitrary-state countable allocation theorem. -/
theorem
    exists_continuousMeasurableTrajectorySleepingGeometricTiltPACBayes_suffixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall a w n : Nat, w < n ->
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior w n x <
                continuousTrajectorySleepingGeometricTiltSuffixBoundary
                  prior posterior score delta a w n x := by
  simpa [continuousTrajectorySleepingGeometricTiltSuffixBoundary] using
    (exists_continuousMeasurableTrajectorySleepingCountableTiltPACBayes_suffixRisk_event
      K x0 score hscore_unit hscore_joint polynomialEpochWeight
      geometricForwardTilt polynomialEpochWeight_pos
      polynomialEpochWeight_hasSum geometricForwardTilt_pos
      geometricForwardTilt_le_half (by norm_num : (1 / 2 : Real) < 1)
      prior hdelta)

end

end FormalSLT.StochasticDynamics
