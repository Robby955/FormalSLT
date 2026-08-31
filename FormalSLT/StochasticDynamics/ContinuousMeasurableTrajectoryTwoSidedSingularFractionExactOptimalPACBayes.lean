/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionExactOptimalPACBayes
import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayes

/-!
# Exact scalar-fraction PAC-Bayes on measurable trajectory spaces

This module specializes the continuous two-sided all-fractions event and its
exact scalar-fraction optimizer to bounded trajectory scores on arbitrary
measurable hypothesis and state spaces. The existing jointly measurable
trajectory-score contract supplies all process-measurability obligations.

One set whose complement has outer mass at most `delta` controls every
reporting time `n >= 2`, every eligible posterior selected after observing the
path, and, in the first theorem, every admissible scalar fraction selected
after the path, posterior, and time. That all-fractions endpoint retains an
explicit rational-fraction route for finite certificates. The exact corollary
instead uses the attained noncomputable scalar optimizer and is not itself an
executable selection procedure.

Both conclusions concern posterior-averaged conditional loss along the
encountered trajectory prefixes. They do not certify future, population,
stationary, or deployment risk, and they do not compete with a predictable
strategy class or a coin-betting construction.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes
open FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes
open FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionExactOptimalPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

/-- The continuous scalar-fraction PAC-Bayes boundary specialized to observed
trajectory scores. -/
def continuousTrajectorySingularFractionBesselBoundary
    (prior : Measure Theta) (score : Theta -> TrajectoryScore Z)
    (posterior : Measure Theta) (delta lam : Real)
    (n : Nat) (x : Nat -> Z) : Real :=
  continuousSingularFractionBesselBoundary prior
    (fun theta => observedTrajectoryScore (score theta))
    posterior delta lam n x

/-- For bounded jointly measurable trajectory scores on arbitrary measurable
state and hypothesis spaces, one set with complement outer mass at most
`delta` controls the absolute encountered-prefix conditional-minus-observed
risk gap for every eligible path-selected posterior, every reporting time
`n >= 2`, and every later admissible scalar fraction.

Because the fraction is quantified after the event, a certificate may use any
explicit admissible rational fraction without invoking the noncomputable exact
optimizer. This is simultaneous scalar-fraction control, not competition with
an arbitrary predictable strategy class. -/
theorem exists_continuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayes_allFractions_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n -> forall lam : Real,
              0 < lam -> lam <= Real.exp (-1) ->
              |continuousTrajectoryPosteriorAverageConditionalRisk
                    K score posterior n x -
                continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x| <
                continuousTrajectorySingularFractionBesselBoundary
                  prior score posterior (delta / 2) lam n x := by
  rcases
      exists_continuousTwoSidedSingularFractionBesselPACBayes_allFractions_event
        (mu := trajectoryMeasure K x0)
        (F := Filtration.piLE (X := fun _ : Nat => Z)) prior
        hdelta hdelta_one
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
        (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_ambient
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_filtered
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_ambient
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_filtered
          K hscore_joint) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr n hn lam hlam hlam_exp
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr
    n hn lam hlam hlam_exp
  simpa only [continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic,
    continuousTrajectorySingularFractionBesselBoundary] using hbound

/-- Under the same arbitrary measurable trajectory contract, one set with
complement outer mass at most `delta` controls the exact scalar-fraction-
optimized two-sided encountered-prefix risk gap at every reporting time and
for every eligible posterior selected from the observed path.

The optimizer is selected only after the generic all-fractions event is
available. It is noncomputable, and this theorem does not claim an executable
optimizer, future-risk control, or predictable-strategy competition. -/
theorem exists_continuousMeasurableTrajectoryTwoSidedSingularFractionExactOptimalPACBayes_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              |continuousTrajectoryPosteriorAverageConditionalRisk
                    K score posterior n x -
                continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x| <
                singularFractionExactBoundary
                    (continuousTrajectoryPosteriorHybridBesselPenalty
                      score posterior n x)
                    (continuousSingularFractionBesselEffectiveConfidence
                      prior posterior (delta / 2)) /
                  (n : Real) := by
  rcases
      exists_continuousTwoSidedSingularFractionExactOptimalPACBayes_event
        (mu := trajectoryMeasure K x0)
        (F := Filtration.piLE (X := fun _ : Nat => Z)) prior
        hdelta hdelta_one
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
        (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_ambient
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_filtered
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_ambient
          K hscore_joint)
        (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_filtered
          K hscore_joint) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr n hn
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr n hn
  simpa only [continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic,
    continuousTrajectoryPosteriorHybridBesselPenalty_eq_generic] using hbound

end

end FormalSLT.StochasticDynamics
