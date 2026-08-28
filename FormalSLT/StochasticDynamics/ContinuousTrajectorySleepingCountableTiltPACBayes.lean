/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingOrdinaryRiskPACBayes
import FormalSLT.PACBayes.ForwardBesselPACBayesCountable

/-!
# Countable constant-tilt selection for sleeping trajectory PAC-Bayes bounds

This module confidence-allocates the ordinary suffix-risk theorem over a
predeclared countable catalog of positive constant post-wake tilts. Atom `a`
receives confidence `delta * q a`; intersecting the atomwise good events gives
one event simultaneous in the hypothesis posterior, tilt atom, wake time, and
reporting time.

This construction is weighted confidence allocation over a catalog. It is not
a single master e-process, parameter-free inference, or coin betting. The
target is the conditional risk encountered along the monitored suffix. It is
not future, stationary, population, or deployment risk without another bridge.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The observable suffix-risk boundary for tilt-catalog atom `a` and wake
time `w`. The two selection costs are separate: `q a` pays for the tilt atom,
while `polynomialEpochWeight w` pays for the wake time. -/
def continuousTrajectorySleepingCountableTiltSuffixBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (q lam : Nat -> Real)
    (delta : Real) (a w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior w n x +
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / (delta * q a)) -
        Real.log (polynomialEpochWeight w) +
        continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
          score posterior (fun _ => lam a) w n x) /
      (((n - w : Nat) : Real) * lam a)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem continuousTrajectorySleepingCountableTiltSuffixBoundary_eq_constant
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (q lam : Nat -> Real)
    (delta : Real) (a w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingCountableTiltSuffixBoundary
        prior posterior score q lam delta a w n x =
      continuousTrajectorySleepingConstantTiltSuffixBoundary
        prior posterior score (fun _ => lam a) (delta * q a) w n x := by
  rfl

/-- One outer-mass event simultaneously controls every declared constant-tilt
atom, every eligible measurable-space posterior, and every nonempty monitored
suffix. Tilt atom, posterior, wake time, and reporting time may all be selected
after observing the path.

This is a countable Bonferroni/Kraft allocation, not a claim that the atoms
form one master e-process or that the procedure is parameter-free. -/
theorem
    exists_continuousTrajectorySleepingCountableTiltPACBayes_suffixRisk_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
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
      exists_continuousTrajectorySleepingConstantTiltPACBayes_suffixRisk_event_of_parameterMeasurable
        K x0 score hscore hscore_parameter (fun _ => lam a)
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
    rw [show goodEventᶜ = ⋃ a, (event a)ᶜ by
      simp [goodEvent]]
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

/-! ## Concrete polynomial-weight, geometric-tilt catalog -/

/-- The concrete catalog uses polynomial confidence weights and geometric
fixed tilts. The tilt atom remains independently selectable from the wake
time. -/
def continuousTrajectorySleepingGeometricTiltSuffixBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectorySleepingCountableTiltSuffixBoundary prior posterior score
    polynomialEpochWeight geometricForwardTilt delta a w n x

/-- Concrete polynomial/geometric specialization of the countable confidence
allocation theorem. -/
theorem
    exists_continuousTrajectorySleepingGeometricTiltPACBayes_suffixRisk_event_of_parameterMeasurable
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
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
    (exists_continuousTrajectorySleepingCountableTiltPACBayes_suffixRisk_event_of_parameterMeasurable
      K x0 score hscore hscore_parameter
      polynomialEpochWeight geometricForwardTilt
      polynomialEpochWeight_pos polynomialEpochWeight_hasSum
      geometricForwardTilt_pos geometricForwardTilt_le_half
      (by norm_num : (1 / 2 : Real) < 1) prior hdelta)

end

end FormalSLT.StochasticDynamics
