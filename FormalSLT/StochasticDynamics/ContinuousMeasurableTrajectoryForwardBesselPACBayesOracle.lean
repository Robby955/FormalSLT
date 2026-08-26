/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes

/-!
# Growing-prefix PAC-Bayes oracle on measurable trajectory spaces

This module specializes the continuous-hypothesis countable-tilt oracle to
trajectory losses on an arbitrary measurable state space. A single event
simultaneously controls every reporting time, a posterior selected from the
observed path, and the exact best atom in a growing geometric tilt prefix.

The controlled quantity has ordinary trajectory semantics: posterior-averaged
kernel-conditional loss along the encountered prefixes, compared with the
posterior-averaged observed prequential loss. The selected boundary has an
observable LIL-order envelope. Its convergence to zero for a time-varying
posterior is conditional on the displayed pathwise KL-complexity rate.

No stationarity, population-risk, future-risk, finite-state, or
finite-hypothesis conclusion is asserted here. The exact real-valued argmin is
noncomputable; executable certificate selection is a separate layer.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesCountable
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

/-- The exact best geometric tilt in the reporting-time prefix, specialized
to observed trajectory losses. -/
def continuousMeasurableTrajectoryGrowingPrefixArgmin
    (prior : Measure Theta) (score : Theta -> TrajectoryScore Z)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (x : Nat -> Z) : Nat :=
  continuousGrowingPrefixForwardBesselPACBayesArgmin prior
    (fun theta => observedTrajectoryScore (score theta)) posterior delta n x

/-- The exact selected continuous-posterior trajectory boundary. -/
def continuousMeasurableTrajectoryGrowingPrefixBoundary
    (prior : Measure Theta) (score : Theta -> TrajectoryScore Z)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (x : Nat -> Z) : Real :=
  countableContinuousForwardPredictableMeanBesselBoundary prior
    polynomialForwardTiltWeight geometricForwardTilt
    (fun theta => observedTrajectoryScore (score theta)) posterior delta
    (continuousMeasurableTrajectoryGrowingPrefixArgmin
      prior score posterior delta n x) n x

/-- Observable LIL-order envelope for the selected trajectory boundary. -/
def continuousMeasurableTrajectoryGrowingPrefixLILEnvelope
    (prior : Measure Theta) (score : Theta -> TrajectoryScore Z)
    (posterior : Measure Theta) (delta : Real) (n : Nat)
    (x : Nat -> Z) : Real :=
  continuousGrowingPrefixForwardBesselPACBayesLILEnvelope prior
    (fun theta => observedTrajectoryScore (score theta)) posterior delta n x

/-- One countable-master event controls arbitrary measurable-state trajectory
losses for every reporting time and the supplied path-selected posterior. At
each time, the exact best atom in the growing geometric prefix controls the
posterior-averaged conditional loss along the encountered prefixes by the
observed prequential loss plus an observable LIL-order boundary. -/
theorem exists_continuousMeasurableTrajectoryGrowingPrefixForwardBesselPACBayesOracle_event
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
      Integrable (llr (posterior x n) prior) (posterior x n)) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        (∀ x ∈ goodEvent, forall n : Nat, 4 <= n ->
          let rho := posterior x n
          let selected :=
            continuousMeasurableTrajectoryGrowingPrefixArgmin
              prior score rho delta n x
          selected ∈ Finset.range
              (growingPrefixForwardBesselPACBayesMaxIndex n + 1) ∧
            continuousTrajectoryPosteriorAverageConditionalRisk
                K score rho n x <
              continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                  score rho n x +
                continuousMeasurableTrajectoryGrowingPrefixBoundary
                  prior score rho delta n x ∧
            continuousMeasurableTrajectoryGrowingPrefixBoundary
                prior score rho delta n x <=
              continuousMeasurableTrajectoryGrowingPrefixLILEnvelope
                prior score rho delta n x ∧
            continuousMeasurableTrajectoryGrowingPrefixBoundary
                prior score rho delta n x <=
              allTimeGeometricPolynomialForwardRate
                (fun _ => (InformationTheory.klDiv rho prior).toReal)
                delta n) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
              (fun n =>
                (InformationTheory.klDiv (posterior x n) prior).toReal /
                  (2 : Real) ^ (geometricForwardTiltIndex n + 1))
              Filter.atTop (nhds 0) ->
            Filter.Tendsto
              (fun n =>
                continuousMeasurableTrajectoryGrowingPrefixBoundary
                  prior score (posterior x n) delta n x)
              Filter.atTop (nhds 0)) := by
  have hprocess_filtered (j n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod
        ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
        (fun q : (Nat -> Z) × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (observedTrajectoryScore (score q.2))
            (conditionalTrajectoryRisk K (score q.2))
            (geometricForwardTilt j) n q.1) :=
    stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered
      K hscore_joint (geometricForwardTilt j) n
  have hprocess_ambient (j n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2))
          (geometricForwardTilt j) n q.1) :=
    stronglyMeasurable_trajectory_ambient_of_filtered_prod
      n (hprocess_filtered j n)
  obtain ⟨goodEvent, hmass, hgood, hvanish⟩ :=
    exists_continuousGrowingPrefixForwardBesselPACBayesOracle_event
      (mu := trajectoryMeasure K x0)
      (F := Filtration.piLE (X := fun _ : Nat => Z))
      prior hdelta hdelta1
      (fun theta =>
        observedTrajectoryScore_incrementAdapted_parameterized_of_joint
          hscore_joint theta)
      (fun theta =>
        conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
          K hscore_joint theta)
      (fun theta k x => observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k x)
      (fun theta k x => conditionalTrajectoryRisk_mem_Icc_of_joint
        K (jointlyStronglyMeasurableTrajectoryScore_section
          hscore_joint theta) (hscore_unit theta) k x)
      (fun theta k => observedTrajectoryScore_condExp_parameterized_of_joint
        K x0 hscore_joint hscore_unit theta k)
      (fun k x =>
        stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
          hscore_joint k x)
      (fun k x =>
        stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
          K hscore_joint k x)
      hprocess_ambient hprocess_filtered posterior hposterior
      hposterior_prior hllr
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn
    simpa only [continuousMeasurableTrajectoryGrowingPrefixArgmin,
      continuousMeasurableTrajectoryGrowingPrefixBoundary,
      continuousMeasurableTrajectoryGrowingPrefixLILEnvelope,
      continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
      continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic] using
      hgood x hx n hn
  · intro x hx hcomplexity
    simpa only [continuousMeasurableTrajectoryGrowingPrefixArgmin,
      continuousMeasurableTrajectoryGrowingPrefixBoundary] using
      hvanish x hx hcomplexity

end

end FormalSLT.StochasticDynamics
