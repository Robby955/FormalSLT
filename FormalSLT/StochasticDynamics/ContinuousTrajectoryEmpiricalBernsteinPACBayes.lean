/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes

/-!
# Continuous-hypothesis trajectory empirical-Bernstein PAC-Bayes

This module specializes the continuous predictable-mean forward-Bessel
PAC-Bayes theorem to arbitrary prefix-dependent finite-state trajectory
kernels.  The hypothesis parameter may be any measurable space, the prior is
an arbitrary probability measure, and every probability posterior absolutely
continuous with respect to the prior and with integrable log-likelihood ratio
is supported on the same outer-probability event.

The supplied trajectory score family is pointwise `[0,1]`-valued and
measurable in the hypothesis parameter at every finite prefix and next state.
The two joint-process strong-measurability hypotheses expose the remaining
analytic obligation needed to integrate the actual pathwise e-process over
the prior: ambient product measurability and measurability for the product of
the path filtration at time `n` with the hypothesis sigma algebra.  No
concentration or MGF statement is assumed through these interfaces.

The state space remains finite and discrete and the declared tilt catalog
remains finite.  This file makes no continuous-state claim.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

local instance continuousTrajectoryPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {Theta Tau Z : Type*} [MeasurableSpace Theta]
  [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- A real-valued function on a product with finite discrete right factor is
strongly measurable when each left section is strongly measurable. -/
theorem stronglyMeasurable_uncurry_of_finite_discrete_right
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    [Fintype Beta] [MeasurableSingletonClass Beta]
    (f : Alpha -> Beta -> Real)
    (hf : forall b, StronglyMeasurable (fun a => f a b)) :
    StronglyMeasurable (fun q : Alpha × Beta => f q.1 q.2) := by
  classical
  have heq : (fun q : Alpha × Beta => f q.1 q.2) =
      ∑ b : Beta, fun q => if q.2 = b then f q.1 b else 0 := by
    funext q
    simp
  rw [heq]
  exact Finset.stronglyMeasurable_sum Finset.univ fun b _ =>
    StronglyMeasurable.ite
      (measurable_snd (measurableSet_singleton b))
      ((hf b).comp_measurable measurable_fst) stronglyMeasurable_const

/-- Parameter measurability of the finite-kernel conditional trajectory risk
follows from coordinatewise parameter measurability of the score. -/
theorem stronglyMeasurable_conditionalTrajectoryRisk_parameter
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (n : Nat) (x : Nat -> Z) :
    StronglyMeasurable (fun theta =>
      conditionalTrajectoryRisk K (score theta) n x) := by
  let u := Preorder.frestrictLe n x
  have hjoint : StronglyMeasurable (fun q : Theta × Z =>
      score q.1 n u q.2) :=
    stronglyMeasurable_uncurry_of_finite_discrete_right
      (fun theta y => score theta n u y)
      (fun y => hscore_parameter n u y)
  unfold conditionalTrajectoryRisk
  change StronglyMeasurable (fun theta =>
    ∫ y, score theta n u y ∂K n u)
  exact StronglyMeasurable.integral_prod_right' (ν := K n u) hjoint

/-- Posterior-integrated average conditional risk along the encountered
trajectory prefixes. -/
def continuousTrajectoryPosteriorAverageConditionalRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, trajectoryAverageConditionalRisk K (score theta) n x ∂posterior

/-- Posterior-integrated observed prequential trajectory risk. -/
def continuousTrajectoryPosteriorEmpiricalPrequentialRisk
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, trajectoryEmpiricalPrequentialRisk (score theta) n x ∂posterior

/-- Posterior integral of the observed per-hypothesis hybrid-Bessel penalty. -/
def continuousTrajectoryPosteriorHybridBesselPenalty
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, forwardHybridBesselPenalty
    (fun k => observedTrajectoryScore (score theta) k x) n ∂posterior

/-- Exact continuous-posterior trajectory empirical-Bernstein boundary at one
declared tilt. -/
def continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
    (prior : Measure Theta) (weight : Tau -> Real) (lam : Tau -> Real)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (delta : Real) (j : Tau) (n : Nat) (x : Nat -> Z) : Real :=
  ((InformationTheory.klDiv posterior prior).toReal +
      Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        continuousTrajectoryPosteriorHybridBesselPenalty
          score posterior n x) /
    ((n : Real) * lam j)

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The trajectory boundary is definitionally the generic continuous
predictable-mean boundary specialized to observed trajectory scores. -/
theorem continuousTrajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic
    (prior : Measure Theta) (weight : Tau -> Real) (lam : Tau -> Real)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (delta : Real) (j : Tau) (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
        prior weight lam score posterior delta j n x =
      continuousForwardPredictableMeanBesselBoundary
        prior weight lam
        (fun theta => observedTrajectoryScore (score theta))
        posterior delta j n x := by
  rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- The posterior-integrated trajectory risk is the posterior integral of the
generic predictable prefix mean. -/
theorem continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorAverageConditionalRisk
        K score posterior n x =
      ∫ theta, forwardPrefixMean
        (fun k => conditionalTrajectoryRisk K (score theta) k x) n
        ∂posterior := by
  rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The posterior-integrated empirical trajectory risk is the posterior
integral of the generic observed prefix mean. -/
theorem continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk
        score posterior n x =
      ∫ theta, forwardPrefixMean
        (fun k => observedTrajectoryScore (score theta) k x) n
        ∂posterior := by
  rfl

omit [Nonempty Tau] in
/-- One outer-mass event controls continuous-posterior trajectory
empirical-Bernstein PAC-Bayes at every `n >= 2` and every declared finite
tilt.  The posterior may be selected after observing the path because the
event is already uniform over every eligible posterior measure. -/
theorem exists_continuousTrajectoryEmpiricalBernsteinPACBayes_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum : ∑ j, weight j = 1)
    {lam : Tau -> Real} {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1)
    (hjoint_ambient : forall j n, StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2))
          (lam j) n q.1))
    (hjoint_filtered : forall j n,
      StronglyMeasurable[MeasurableSpace.prod
        ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
        (fun q : (Nat -> Z) × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (observedTrajectoryScore (score q.2))
            (conditionalTrajectoryRisk K (score q.2))
            (lam j) n q.1)) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, forall j : Tau,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              continuousTrajectoryPosteriorAverageConditionalRisk
                  K score posterior n x <
                continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x +
                  continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
                    prior weight lam score posterior delta j n x := by
  rcases exists_continuousForwardPredictableMeanBesselPACBayes_event
      (mu := trajectoryMeasure K x0)
      (F := Filtration.piLE (X := fun _ : Nat => Z))
      prior hweight_pos hweight_sum hdelta hlam hlam_one
      (fun theta => observedTrajectoryScore_incrementAdapted (score theta))
      (fun theta => conditionalTrajectoryRisk_stronglyAdapted K (score theta))
      (fun theta k x => observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k x)
      (fun theta k x => conditionalTrajectoryRisk_mem_Icc
        K (hscore_unit theta) k x)
      (fun theta k => observedTrajectoryScore_condExp
        K x0 (score theta) (hscore_unit theta) k)
      (fun k x => hscore_parameter k
        (Preorder.frestrictLe k x) (x (k + 1)))
      (fun k x => stronglyMeasurable_conditionalTrajectoryRisk_parameter
        K score hscore_parameter k x)
      hjoint_ambient hjoint_filtered with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior hposterior_prior hllr n hn
  have hbound := hgood x hx j posterior hposterior
    hposterior_prior hllr n hn
  simpa only [continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic,
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic] using hbound

end

end FormalSLT.StochasticDynamics
