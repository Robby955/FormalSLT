/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.TrajectoryPredictableTiltPACBayes

/-!
# Countable sleeping predictable strategies for nonstationary trajectories

This module specializes the exact finite-tail sleeping master to bounded
scores observed along arbitrary prefix-dependent finite-state trajectory
kernels.  The predictable conditional mean is the kernel risk at the prefix
actually encountered, so it may vary with the model, time, and full observed
history.

The endpoint is a normalized strategy-weighted average of those encountered
one-step conditional risks.  It is not a stationary, population, future, or
ordinary unweighted prefix risk without an additional specialization.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.TimeUniformContinuous
open FormalSLT.PACBayes.ContinuousSleepingPredictableTiltPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Evaluate every prefix-predictable strategy atom on the observed path. -/
def observedTrajectoryPredictableStrategyCatalog
    (strategy : Nat -> TrajectoryPredictableTilt Z) :
    Nat -> Nat -> (Nat -> Z) -> Real :=
  fun j => observedTrajectoryPredictableTilt (strategy j)

/-- Hypothesis-indexed exact sleeping master for an observed trajectory. -/
def continuousTrajectorySleepingPredictableTiltMasterProcess
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z) :
    Theta -> Nat -> (Nat -> Z) -> Real :=
  continuousSleepingForwardPredictableMeanMasterProcess
    (fun theta => observedTrajectoryScore (score theta))
    (fun theta => conditionalTrajectoryRisk K (score theta))
    (observedTrajectoryPredictableStrategyCatalog strategy)

/-- Normalized posterior strategy-weighted conditional risk encountered along
the observed nonstationary trajectory. -/
def continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (posterior : Measure Theta) (j n : Nat) (x : Nat -> Z) : Real :=
  continuousSleepingPosteriorNormalizedConditionalMean posterior
    (fun theta => conditionalTrajectoryRisk K (score theta))
    (observedTrajectoryPredictableStrategyCatalog strategy) j n x

/-- Normalized posterior strategy-weighted observed trajectory score. -/
def continuousTrajectorySleepingPosteriorNormalizedEmpiricalRisk
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (posterior : Measure Theta) (j n : Nat) (x : Nat -> Z) : Real :=
  continuousSleepingPosteriorNormalizedObservation posterior
    (fun theta => observedTrajectoryScore (score theta))
    (observedTrajectoryPredictableStrategyCatalog strategy) j n x

/-- Exact selected-atom boundary for the trajectory specialization. -/
def continuousTrajectorySleepingPredictableTiltBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  continuousSleepingPredictableTiltBoundary prior posterior
    (fun theta => observedTrajectoryScore (score theta))
    (observedTrajectoryPredictableStrategyCatalog strategy)
    delta j n x

private theorem stronglyMeasurable_forwardPredictorProcess_of_parameter_prefix
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
    stronglyMeasurable_forwardPredictableTiltMeanLowerProcess_of_prefix
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
    stronglyMeasurable_forwardPredictorProcess_of_parameter_prefix X
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

/-- At each finite time, coordinatewise hypothesis measurability of the score
family implies filtered joint path-parameter measurability of the exact
sleeping master.  Finiteness of the state space is used to assemble the
coordinate sections over the finite observed prefix. -/
theorem
    stronglyMeasurable_continuousTrajectorySleepingPredictableTiltMasterProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (strategy : Nat -> TrajectoryPredictableTilt Z) (n : Nat) :
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
    exact stronglyMeasurable_observedTrajectoryScore_parameter_prod
      score hscore_parameter (Nat.succ_le_iff.mpr hk)
  have hmean : forall k, k < n -> StronglyMeasurable (mean k) := by
    intro k hk
    dsimp [mean]
    exact stronglyMeasurable_conditionalTrajectoryRisk_parameter_prod
      K score hscore_parameter (Nat.le_of_lt hk)
  have hcatalog : forall j, StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryPredictableStrategyCatalog strategy j) := by
    intro j
    exact observedTrajectoryPredictableTilt_stronglyAdapted (strategy j)
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
          ((Filtration.piLE (X := fun _ : Nat => Z)).mono (Nat.le_of_lt hk))
    dsimp [lambda]
    exact hpath.comp_measurable measurable_fst
  have hcomponent (j : Nat) : StronglyMeasurable (fun q =>
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean (lambda j) n q) :=
    stronglyMeasurable_forwardPredictableTiltMeanLowerProcess_of_prefix
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

/-- The filtered joint master is also measurable for the ambient product
sigma-algebra. -/
theorem
    stronglyMeasurable_continuousTrajectorySleepingPredictableTiltMasterProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (strategy : Nat -> TrajectoryPredictableTilt Z) (n : Nat) :
    StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) := by
  have hfiltered :=
    stronglyMeasurable_continuousTrajectorySleepingPredictableTiltMasterProcess_filtered
      K score hscore_parameter strategy n
  exact (hfiltered.measurable.mono
    (measurableSpace_prod_piLE_le_ambient
      (Theta := Theta) (Z := Z) n) le_rfl).stronglyMeasurable

omit [MeasurableSpace Theta] [Fintype Z] [MeasurableSingletonClass Z] in
/-- The closed-form sleeping tail is a pointwise lower bound for the exact
finite-prefix master. -/
theorem continuousTrajectorySleepingPredictableTiltMasterProcess_tail_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (theta : Theta) (n : Nat) (x : Nat -> Z) :
    polynomialSleepingTail n <=
      continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x := by
  unfold continuousTrajectorySleepingPredictableTiltMasterProcess
    continuousSleepingForwardPredictableMeanMasterProcess
    countableSleepingForwardPredictableMeanMasterProcess
    countableSleepingProcessMixture
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
    mul_nonneg (polynomialEpochWeight_pos j).le (Real.exp_pos _).le)

omit [MeasurableSpace Theta] in
/-- A deterministic finite-time envelope for the trajectory sleeping master.
The envelope is deliberately left in finite-prefix form; it is sufficient for
all product-integrability and section-integrability obligations. -/
theorem continuousTrajectorySleepingPredictableTiltMasterProcess_le
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
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
      (fun k path => observedTrajectoryScore_mem_Icc (hscore theta) k path)
      (fun k path =>
        (conditionalTrajectoryRisk_mem_Icc K (hscore theta) k path).2)
      (fun k path => by
        exact sleepingStrategy_mem_Icc
          (strategy := observedTrajectoryPredictableStrategyCatalog strategy)
          (fun i r y => by
            exact hstrategy_range i r (Preorder.frestrictLe r y))
          j k path)
      n x
  linarith

/-- The generic continuous sleeping-master theorem specializes to genuinely
time-varying prefix-conditional trajectory risk.  The explicit continuous
mixture hypotheses are the remaining parameter-measurability and Fubini
interface; the pathwise stochastic assumptions are discharged here from the
trajectory kernel and bounded score family. -/
theorem
    exists_continuousTrajectorySleepingPredictableTiltPACBayes_normalized_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {L : Real} (hL1 : L < 1)
    (hstrategy_range : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta)
    (h_adapted_mix : StronglyAdapted
      (Filtration.piLE (X := fun _ : Nat => Z))
      (continuousPriorMixtureProcess prior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy) n) (trajectoryMeasure K x0))
    (hM_int_next : forall n, Integrable
      (fun p : Theta × (Nat -> Z) =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy p.1 (n + 1) p.2)
      (prior.prod (trajectoryMeasure K x0)))
    (hM_int_next_restrict : forall n, forall {s : Set (Nat -> Z)},
      MeasurableSet s -> trajectoryMeasure K x0 s < ⊤ -> Integrable
        (fun p : (Nat -> Z) × Theta =>
          continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy p.2 (n + 1) p.1)
        (((trajectoryMeasure K x0).restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy p.2 n p.1)
      ((trajectoryMeasure K x0).prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set (Nat -> Z)},
      MeasurableSet s -> trajectoryMeasure K x0 s < ⊤ -> Integrable
        (fun p : (Nat -> Z) × Theta =>
          continuousTrajectorySleepingPredictableTiltMasterProcess
            K score strategy p.2 n p.1)
        (((trajectoryMeasure K x0).restrict s).prod prior))
    (hprior_integrable : forall n x, Integrable
      (fun theta => continuousTrajectorySleepingPredictableTiltMasterProcess
        K score strategy theta n x) prior) :
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
              Integrable
                (fun theta => Real.log
                  (continuousTrajectorySleepingPredictableTiltMasterProcess
                    K score strategy theta n x)) posterior ->
              Integrable
                (fun theta => continuousSleepingWeightedConditionalMeanAt
                  (fun theta => conditionalTrajectoryRisk K (score theta))
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  theta j n x) posterior ->
              Integrable
                (fun theta => continuousSleepingWeightedObservationAt
                  (fun theta => observedTrajectoryScore (score theta))
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  theta j n x) posterior ->
              Integrable
                (fun theta => continuousSleepingPredictorQuadraticPenaltyAt
                  (fun theta => observedTrajectoryScore (score theta))
                  (observedTrajectoryPredictableStrategyCatalog strategy)
                  theta j n x) posterior ->
              continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
                  K score strategy posterior j n x <
                continuousTrajectorySleepingPredictableTiltBoundary
                  prior posterior score strategy delta j n x := by
  rcases
      exists_continuousSleepingPredictableTiltPACBayes_normalized_event
        (mu := trajectoryMeasure K x0)
        (F := Filtration.piLE (X := fun _ : Nat => Z))
        prior hL1 hdelta
        (fun theta => observedTrajectoryScore_incrementAdapted (score theta))
        (fun theta => conditionalTrajectoryRisk_stronglyAdapted K (score theta))
        (fun j => observedTrajectoryPredictableTilt_stronglyAdapted
          (strategy j))
        (fun theta k x => observedTrajectoryScore_mem_Icc
          (hscore theta) k x)
        (fun j k x => hstrategy_range j k
          (Preorder.frestrictLe k x))
        (fun theta k => observedTrajectoryScore_condExp
          K x0 (score theta) (hscore theta) k)
        h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
        hM_int_current hM_int_current_restrict hprior_integrable with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr j n hjn
    hexposure hlog hconditional hobservation hpenalty
  unfold continuousTrajectorySleepingPosteriorNormalizedConditionalRisk
    continuousTrajectorySleepingPredictableTiltBoundary
    observedTrajectoryPredictableStrategyCatalog
  exact hgood x hx posterior hposterior hposterior_prior hllr j n hjn
    hexposure hlog hconditional hobservation hpenalty

/-- Coordinatewise parameter measurability and the pointwise range contracts
derive every product-integrability, restricted-product, prior-section,
posterior-section, and prior-mixture adaptedness obligation of the continuous
sleeping-master theorem.  No separate Fubini or finite-time integrability
premise remains in this finite-state trajectory adapter. -/
theorem
    exists_continuousTrajectorySleepingPredictableTiltPACBayes_normalized_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (strategy : Nat -> TrajectoryPredictableTilt Z)
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
      (stronglyMeasurable_continuousTrajectorySleepingPredictableTiltMasterProcess_filtered
        K score hscore_parameter strategy n)
  have hjoint_ambient (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        continuousTrajectorySleepingPredictableTiltMasterProcess
          K score strategy q.2 n q.1) :=
    stronglyMeasurable_continuousTrajectorySleepingPredictableTiltMasterProcess_ambient
      K score hscore_parameter strategy n
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
      exact continuousTrajectorySleepingPredictableTiltMasterProcess_le
        K score hscore strategy hL1 hstrategy_range q.2 n q.1
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
      exact continuousTrajectorySleepingPredictableTiltMasterProcess_le
        K score hscore strategy hL1 hstrategy_range theta n x
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
          K score strategy) n) mu := by
    exact (hM_int_current n).integral_prod_left
  rcases
      exists_continuousTrajectorySleepingPredictableTiltPACBayes_normalized_event
      K x0 score hscore strategy hL1 hstrategy_range prior hdelta
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
        exact continuousTrajectorySleepingPredictableTiltMasterProcess_le
          K score hscore strategy hL1 hstrategy_range theta n x
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
      (fun theta => observedTrajectoryScore (score theta) k x) := by
    simpa only [observedTrajectoryScore] using
      hscore_parameter k (Preorder.frestrictLe k x) (x (k + 1))
  have hX_unit (theta : Theta) (k : Nat) :
      observedTrajectoryScore (score theta) k x ∈ Set.Icc (0 : Real) 1 :=
    observedTrajectoryScore_mem_Icc (hscore theta) k x
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
      have hmean_meas := stronglyMeasurable_conditionalTrajectoryRisk_parameter
        K score hscore_parameter k x
      have hmean_int : Integrable
          (fun theta => conditionalTrajectoryRisk K (score theta) k x)
          posterior := by
        refine Integrable.of_bound hmean_meas.aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun theta => by
          have hrisk := conditionalTrajectoryRisk_mem_Icc K (hscore theta) k x
          rw [Real.norm_eq_abs, abs_of_nonneg hrisk.1]
          exact hrisk.2
      exact hmean_int.const_mul
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
          (fun theta => observedTrajectoryScore (score theta) k x) posterior := by
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
        stronglyMeasurable_forwardPredictorProcess_of_parameter_prefix
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
  exact hgood x hx posterior hposterior hposterior_prior hllr j n hjn
    hexposure hlog hconditional hobservation hpenalty

end

end FormalSLT.StochasticDynamics
