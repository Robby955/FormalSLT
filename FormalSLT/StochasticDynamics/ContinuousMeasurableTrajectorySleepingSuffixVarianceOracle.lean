/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectorySleepingCountableTiltPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingSuffixVarianceOracle

/-!
# Observable sleeping suffix-variance oracle on measurable state spaces

This module is the stochastic adapter for the state-independent suffix
variance oracle.  Joint score measurability supplies its fixed-parameter score
sections, while the arbitrary-state geometric sleeping event supplies the one
common event.  No deterministic oracle algebra is repeated.

Posterior, wake, reporting time, and the exact finite-prefix atom may depend on
the observed path.  The atom is a noncomputable exact catalog argmin, not coin
betting or parameter-free inference.  The target remains encountered
conditional suffix risk, not future, stationary, population, or deployment
risk.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

/-- Joint score measurability implies strong measurability in the hypothesis
parameter at every fixed prefix and next state. -/
theorem stronglyMeasurable_parameterizedTrajectoryScore_parameter_of_joint
    {score : Theta -> TrajectoryScore Z}
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) (u : (i : Finset.Iic n) -> Z) (y : Z) :
    StronglyMeasurable (fun theta => score theta n u y) := by
  have hmap : Measurable (fun theta : Theta => (theta, (u, y))) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  simpa only [Function.comp_def] using
    (hscore_joint n).comp_measurable hmap

/-- One arbitrary-state event supports the exact finite-prefix observable
suffix-variance selector at every reporting time. -/
theorem
    exists_continuousMeasurableTrajectorySleepingSuffixVarianceOracle_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (posterior : (Nat -> Z) -> Nat -> Measure Theta)
    (hposterior : forall x n,
      IsProbabilityMeasure (posterior x n))
    (hposterior_prior : forall x n, posterior x n ≪ prior)
    (hllr : forall x n,
      Integrable (llr (posterior x n) prior) (posterior x n))
    (wake : (Nat -> Z) -> Nat -> Nat) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent -> forall n : Nat,
          4 <= n - wake x n ->
            let rho := posterior x n
            let w := wake x n
            let selected :=
              continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
                prior rho score delta w n x
            selected ∈ Finset.range
                (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1) ∧
              continuousTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score rho w n x <
                continuousTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x ∧
              continuousTrajectorySleepingSuffixVarianceSelectedExcess
                  prior rho score delta w n x <=
                continuousTrajectorySleepingSuffixVarianceLILEnvelope
                  prior rho score delta w n x ∧
              continuousTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x <=
                continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
                    score rho w n x +
                  continuousTrajectorySleepingSuffixVarianceLILEnvelope
                    prior rho score delta w n x := by
  have hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y) :=
    fun n u y =>
      stronglyMeasurable_parameterizedTrajectoryScore_parameter_of_joint
        hscore_joint n u y
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_continuousMeasurableTrajectorySleepingGeometricTiltPACBayes_suffixRisk_event
      K x0 score hscore_unit hscore_joint prior hdelta
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hsuffix
  let rho := posterior x n
  let w := wake x n
  let selected :=
    continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
      prior rho score delta w n x
  letI : IsProbabilityMeasure rho := hposterior x n
  have hselected_mem : selected ∈ Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1) :=
    continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
      prior rho score delta w n x
  have hrisk := hgood x hx rho (hposterior x n)
    (hposterior_prior x n) (hllr x n) selected w n (by omega)
  have hselected_risk :
      continuousTrajectoryPosteriorAverageConditionalSuffixRisk
          K score rho w n x <
        continuousTrajectorySleepingSuffixVarianceSelectedBoundary
          prior rho score delta w n x := by
    rw [continuousTrajectorySleepingSuffixVarianceSelectedBoundary_eq
      prior rho score hdelta]
    exact hrisk
  have hLIL :=
    continuousTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
      prior rho score hscore_unit hscore_parameter hdelta hdelta1
        (w := w) (n := n) hsuffix x
  have hboundary :=
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary_le_LILEnvelope
      prior rho score hscore_unit hscore_parameter hdelta hdelta1
        (w := w) (n := n) hsuffix x
  exact ⟨hselected_mem, hselected_risk, hLIL, hboundary⟩

end

end FormalSLT.StochasticDynamics
