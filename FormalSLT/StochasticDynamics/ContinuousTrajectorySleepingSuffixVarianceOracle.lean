/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingCountableTiltPACBayesOracle

/-!
# Observable suffix-variance oracle for sleeping trajectory PAC-Bayes bounds

This module separates the raw, path-observed suffix quadratic variation from
the geometric-tilt penalty.  The penalty factors exactly as `psi(lambda) * Q`,
and `Q` lies in `[0, n - w]`.  An exact finite-prefix selector then minimizes
the observable excess width over the predeclared geometric catalog.  Its
selected excess admits a finite-time observable dyadic square-root envelope
on the same countable confidence-allocation event.  The envelope has
iterated-logarithm order only when posterior KL and wake-selection cost are
controlled relative to the suffix length.

The selector is an exact argmin over a finite prefix of a fixed countable
catalog.  It is not a single master e-process, coin betting, or parameter-free
inference.  The risk target is the encountered conditional risk on `[w,n)`,
not future, stationary, population, or deployment risk.  The predictor in the
observable quadratic variation may use the full trajectory history before
each scored time; the risk average itself starts at `w`.  The standalone
boundary formulas are not coverage certificates for an ineligible posterior;
the event theorem requires absolute continuity and integrable log density.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle
open scoped BigOperators Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Posterior-integrated raw prediction-residual quadratic variation on
`[w,n)`.  At time `k`, the forward predictor uses the full history before
`k`, including observations before `w`. -/
def continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (w n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta,
    ∑ k ∈ Finset.Ico w n,
      (observedTrajectoryScore (score theta) k x -
        forwardPredictorProcess
          (observedTrajectoryScore (score theta)) k x) ^ 2
    ∂posterior

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A constant-tilt suffix penalty is exactly `psi(lambda)` times the raw
observable suffix quadratic variation. -/
theorem continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_eq
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (lam : Real) (w n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior (fun _ => lam) w n x =
      forwardEmpiricalBernsteinPsi lam *
        continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
          score posterior w n x := by
  unfold continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
  simp_rw [← Finset.mul_sum]
  exact integral_const_mul _ _

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Prefix means remain measurable in a parameter when every preceding
coordinate is measurable in that parameter. -/
private theorem stronglyMeasurable_suffixVarianceForwardPredictor
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

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- For unit-bounded scores, the raw observable suffix quadratic variation is
between zero and the suffix length. -/
theorem continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
        score posterior w n x ∈ Set.Icc 0 ((n - w : Nat) : Real) := by
  let X : Nat -> Theta -> Real := fun k theta =>
    observedTrajectoryScore (score theta) k x
  have hX_meas (k : Nat) : StronglyMeasurable (X k) := by
    change StronglyMeasurable
      (fun theta => score theta k (Preorder.frestrictLe k x) (x (k + 1)))
    exact hscore_parameter k _ _
  have hX_unit (theta : Theta) (k : Nat) : X k theta ∈ Set.Icc (0 : Real) 1 :=
    hscore theta k _ _
  have hsquare_meas (k : Nat) : StronglyMeasurable (fun theta =>
      (X k theta - forwardPredictorProcess X k theta) ^ 2) := by
    have hpredictor : StronglyMeasurable (forwardPredictorProcess X k) :=
      stronglyMeasurable_suffixVarianceForwardPredictor
        X (fun i _hi => hX_meas i)
    exact ((hX_meas k).sub hpredictor).pow 2
  have hsquare_mem (theta : Theta) (k : Nat) :
      (X k theta - forwardPredictorProcess X k theta) ^ 2 ∈
        Set.Icc (0 : Real) 1 := by
    have hpred := forwardPredictorProcess_mem_Icc_of_mem_Icc
      (X := X) (fun i theta => hX_unit theta i) k theta
    constructor
    · positivity
    · rcases hX_unit theta k with ⟨hX0, hX1⟩
      rcases hpred with ⟨hP0, hP1⟩
      nlinarith
  have hintegrable : Integrable (fun theta =>
      ∑ k ∈ Finset.Ico w n,
        (X k theta - forwardPredictorProcess X k theta) ^ 2) posterior := by
    have hsum : Integrable
        (∑ k ∈ Finset.Ico w n, fun theta =>
          (X k theta - forwardPredictorProcess X k theta) ^ 2)
        posterior := by
      apply integrable_finsetSum'
      intro k _hk
      refine Integrable.of_bound (hsquare_meas k).aestronglyMeasurable 1 ?_
      exact Filter.Eventually.of_forall fun theta => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hsquare_mem theta k).1]
        exact (hsquare_mem theta k).2
    convert hsum using 1
    funext theta
    simp only [Finset.sum_apply]
  have hpoint_nonneg : forall theta,
      0 <= ∑ k ∈ Finset.Ico w n,
        (X k theta - forwardPredictorProcess X k theta) ^ 2 := by
    intro theta
    exact Finset.sum_nonneg fun k _hk => (hsquare_mem theta k).1
  have hpoint_upper : forall theta,
      (∑ k ∈ Finset.Ico w n,
        (X k theta - forwardPredictorProcess X k theta) ^ 2) <=
        ((n - w : Nat) : Real) := by
    intro theta
    calc
      (∑ k ∈ Finset.Ico w n,
          (X k theta - forwardPredictorProcess X k theta) ^ 2) <=
          ∑ _k ∈ Finset.Ico w n, (1 : Real) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hsquare_mem theta k).2
      _ = ((n - w : Nat) : Real) := by
        simp [Nat.card_Ico, hwn]
  unfold continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
  change (∫ theta,
      ∑ k ∈ Finset.Ico w n,
        (X k theta - forwardPredictorProcess X k theta) ^ 2
      ∂posterior) ∈ Set.Icc 0 ((n - w : Nat) : Real)
  constructor
  · exact integral_nonneg hpoint_nonneg
  · calc
      (∫ theta,
          ∑ k ∈ Finset.Ico w n,
            (X k theta - forwardPredictorProcess X k theta) ^ 2
          ∂posterior) <=
          ∫ _theta, ((n - w : Nat) : Real) ∂posterior :=
        integral_mono hintegrable (integrable_const _) hpoint_upper
      _ = ((n - w : Nat) : Real) := by simp

/-- Observable excess for geometric atom `a`, written in terms of raw suffix
quadratic variation and wake-adjusted confidence. -/
def continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) : Real :=
  let effectiveDelta :=
    continuousTrajectorySleepingSuffixEffectiveConfidence delta w
  let Q := continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  (continuousGeometricForwardBesselPACBayesComplexity
        prior posterior effectiveDelta a +
      forwardEmpiricalBernsteinPsi (geometricForwardTilt a) * Q) /
    (((n - w : Nat) : Real) * geometricForwardTilt a)

/-- Ordinary observed suffix risk plus one geometric atom's observable
excess. -/
def continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior w n x +
    continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
      prior posterior score delta a w n x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The raw-variance boundary is exactly the already established geometric
sleeping boundary. -/
theorem continuousTrajectorySleepingGeometricTiltSuffixBoundary_eq_suffixVariance
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) {delta : Real}
    (hdelta : 0 < delta) (a w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingGeometricTiltSuffixBoundary
        prior posterior score delta a w n x =
      continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        prior posterior score delta a w n x := by
  have hlog := continuousTrajectorySleeping_geometricTiltWake_log_cost
    hdelta a w
  unfold continuousTrajectorySleepingGeometricTiltSuffixBoundary
    continuousTrajectorySleepingCountableTiltSuffixBoundary
    continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
    continuousGeometricForwardBesselPACBayesComplexity
  rw [continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_eq]
  dsimp
  rw [show
    (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / (delta * polynomialEpochWeight a)) -
          Real.log (polynomialEpochWeight w) +
          forwardEmpiricalBernsteinPsi (geometricForwardTilt a) *
            continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
              score posterior w n x =
        (InformationTheory.klDiv posterior prior).toReal +
          (Real.log (1 / (delta * polynomialEpochWeight a)) -
            Real.log (polynomialEpochWeight w)) +
          forwardEmpiricalBernsteinPsi (geometricForwardTilt a) *
            continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
              score posterior w n x by ring,
    hlog]

/-- Largest atom in the geometric catalog prefix admitted by suffix length
`n - w`. -/
def continuousTrajectorySleepingSuffixVarianceMaxIndex (w n : Nat) : Nat :=
  growingPrefixForwardBesselPACBayesMaxIndex (n - w)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem continuousTrajectorySleepingSuffixVariance_exists_argmin
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    ∃ a ∈ Finset.range
        (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1),
      ∀ a' ∈ Finset.range
          (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1),
        continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
            prior posterior score delta a w n x <=
          continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
            prior posterior score delta a' w n x := by
  classical
  exact (Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1)).exists_min_image
    (fun a => continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
      prior posterior score delta a w n x)
    (by simp)

/-- Exact minimizer of the observable excess over the finite geometric prefix
admitted by the suffix length. -/
def continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Nat :=
  Classical.choose
    (continuousTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The exact suffix-variance selector belongs to its finite catalog prefix. -/
theorem continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
        prior posterior score delta w n x ∈
      Finset.range
        (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1) := by
  exact (Classical.choose_spec
    (continuousTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)).1

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The exact suffix-variance selector has no larger excess than any supported
atom. -/
theorem continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) {a : Nat}
    (ha : a ∈ Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1)) :
    continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta
          (continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
            prior posterior score delta w n x) w n x <=
      continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta a w n x := by
  exact (Classical.choose_spec
    (continuousTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)).2 a ha

/-- Excess selected by the exact finite-prefix suffix-variance oracle. -/
def continuousTrajectorySleepingSuffixVarianceSelectedExcess
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
    prior posterior score delta
      (continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
        prior posterior score delta w n x) w n x

/-- Observable ordinary-risk endpoint selected by the finite-prefix
suffix-variance oracle. -/
def continuousTrajectorySleepingSuffixVarianceSelectedBoundary
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior w n x +
    continuousTrajectorySleepingSuffixVarianceSelectedExcess
      prior posterior score delta w n x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected boundary is the existing sleeping catalog endpoint at the
selected atom. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedBoundary_eq
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) {delta : Real}
    (hdelta : 0 < delta) (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x =
      continuousTrajectorySleepingGeometricTiltSuffixBoundary
        prior posterior score delta
          (continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
            prior posterior score delta w n x) w n x := by
  rw [continuousTrajectorySleepingGeometricTiltSuffixBoundary_eq_suffixVariance
    prior posterior score hdelta]
  rfl

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected ordinary-risk endpoint is no larger than any geometric atom
in the admitted finite prefix. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedBoundary_le
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) {delta : Real}
    (hdelta : 0 < delta) (w n : Nat) (x : Nat -> Z) {a : Nat}
    (ha : a ∈ Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1)) :
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x <=
      continuousTrajectorySleepingGeometricTiltSuffixBoundary
        prior posterior score delta a w n x := by
  rw [continuousTrajectorySleepingGeometricTiltSuffixBoundary_eq_suffixVariance
    prior posterior score hdelta]
  unfold continuousTrajectorySleepingSuffixVarianceSelectedBoundary
    continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
  exact add_le_add_right
    (continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
      prior posterior score delta w n x ha) _

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Observable quadratic rate for one sleeping suffix geometric atom. -/
theorem continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_le_observableRate
    (prior posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (delta : Real) (a : Nat) {w n : Nat} (hwn : w < n)
    (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta a w n x <=
      (continuousGeometricForwardBesselPACBayesComplexity prior posterior
            (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) a *
          geometricForwardEffectiveScale a +
        2 * continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
              score posterior w n x /
            geometricForwardEffectiveScale a) /
        ((n - w : Nat) : Real) := by
  let Q := continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  have hQ := continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc
    score hscore hscore_parameter posterior (Nat.le_of_lt hwn) x
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (geometricForwardTilt_le_half a)
  have hvar :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt a) * Q <=
        2 * (geometricForwardTilt a) ^ 2 * Q :=
    mul_le_mul_of_nonneg_right hpsi (by simpa [Q] using hQ.1)
  have hmpos : 0 < (n - w : Nat) := Nat.sub_pos_of_lt hwn
  have hdenpos : 0 < ((n - w : Nat) : Real) * geometricForwardTilt a :=
    mul_pos (Nat.cast_pos.mpr hmpos) (geometricForwardTilt_pos a)
  unfold continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
    geometricForwardEffectiveScale
  change
    (continuousGeometricForwardBesselPACBayesComplexity prior posterior
          (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) a +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt a) * Q) /
      (((n - w : Nat) : Real) * geometricForwardTilt a) <= _
  calc
    (continuousGeometricForwardBesselPACBayesComplexity prior posterior
          (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) a +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt a) * Q) /
        (((n - w : Nat) : Real) * geometricForwardTilt a) <=
      (continuousGeometricForwardBesselPACBayesComplexity prior posterior
          (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) a +
        2 * (geometricForwardTilt a) ^ 2 * Q) /
        (((n - w : Nat) : Real) * geometricForwardTilt a) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      linarith
    _ =
      (continuousGeometricForwardBesselPACBayesComplexity prior posterior
            (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) a *
          (2 : Real) ^ (a + 1) +
        2 * Q / (2 : Real) ^ (a + 1)) /
        ((n - w : Nat) : Real) := by
      unfold geometricForwardTilt
      field_simp [show ((n - w : Nat) : Real) ≠ 0 by positivity]

/-- Largest-prefix complexity at wake-adjusted confidence and suffix length. -/
def continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    (prior posterior : Measure Theta) (delta : Real)
    (w n : Nat) : Real :=
  continuousGrowingPrefixForwardBesselPACBayesComplexity prior posterior
    (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) (n - w)

/-- Finite-time observable dyadic square-root envelope for the exact sleeping
suffix selector.  It has iterated-logarithm order under controlled posterior
KL and wake-selection cost. -/
def continuousTrajectorySleepingSuffixVarianceLILEnvelope
    (prior posterior : Measure Theta)
    (score : Theta -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  let A := continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    prior posterior delta w n
  let Q := continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
    ((n - w : Nat) : Real)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The exact finite-prefix selected excess is bounded by the finite-time
observable dyadic square-root envelope. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
    (prior posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceSelectedExcess
        prior posterior score delta w n x <=
      continuousTrajectorySleepingSuffixVarianceLILEnvelope
        prior posterior score delta w n x := by
  let m := n - w
  let maxIndex := growingPrefixForwardBesselPACBayesMaxIndex m
  let effectiveDelta :=
    continuousTrajectorySleepingSuffixEffectiveConfidence delta w
  let A := continuousGrowingPrefixForwardBesselPACBayesComplexity
    prior posterior effectiveDelta m
  let Q := continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  have heffective_pos : 0 < effectiveDelta :=
    mul_pos hdelta (polynomialEpochWeight_pos w)
  have hweight_le_one : polynomialEpochWeight w <= 1 := by
    unfold polynomialEpochWeight
    rw [div_le_one (by positivity :
      (0 : Real) < ((w : Real) + 1) * ((w : Real) + 2))]
    have hw0 : (0 : Real) <= w := Nat.cast_nonneg w
    nlinarith
  have heffective_one : effectiveDelta <= 1 := by
    dsimp [effectiveDelta,
      continuousTrajectorySleepingSuffixEffectiveConfidence]
    calc
      delta * polynomialEpochWeight w <= 1 * polynomialEpochWeight w :=
        mul_le_mul_of_nonneg_right hdelta1 (polynomialEpochWeight_pos w).le
      _ <= 1 := by simpa using hweight_le_one
  have hAhalf : (1 : Real) / 2 <= A := by
    simpa [A] using
      continuousGrowingPrefixForwardBesselPACBayesComplexity_half_le
        prior posterior heffective_pos heffective_one m
  have hQmem : Q ∈ Set.Icc 0 (m : Real) := by
    simpa [Q, m] using
      continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc
        score hscore hscore_parameter posterior (by omega) x
  have hscale :
      4 * (m : Real) < geometricForwardEffectiveScale maxIndex ^ 2 := by
    simpa [maxIndex] using
      growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul hsuffix
  have hcover :
      2 * Q < A * geometricForwardEffectiveScale maxIndex ^ 2 := by
    calc
      2 * Q <= 2 * (m : Real) :=
        mul_le_mul_of_nonneg_left hQmem.2 (by norm_num)
      _ < (1 / 2 : Real) *
          geometricForwardEffectiveScale maxIndex ^ 2 := by
        nlinarith
      _ <= A * geometricForwardEffectiveScale maxIndex ^ 2 :=
        mul_le_mul_of_nonneg_right hAhalf
          (sq_nonneg (geometricForwardEffectiveScale maxIndex))
  obtain ⟨a, ha, horacle⟩ :=
    exists_dyadic_quadratic_oracle hAhalf hQmem.1 hcover
  have hale : a <= maxIndex := by
    have halt : a < maxIndex + 1 := by
      simpa only [Finset.mem_range] using ha
    omega
  have hAa :
      continuousGeometricForwardBesselPACBayesComplexity
          prior posterior effectiveDelta a <= A := by
    simpa [A, maxIndex, continuousGrowingPrefixForwardBesselPACBayesComplexity]
      using continuousGeometricForwardBesselPACBayesComplexity_mono
        prior posterior heffective_pos hale
  have hselected :
      continuousTrajectorySleepingSuffixVarianceSelectedExcess
          prior posterior score delta w n x <=
        (continuousGeometricForwardBesselPACBayesComplexity
              prior posterior effectiveDelta a *
            geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) := by
    have hargmin :=
      continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
        prior posterior score delta w n x
          (by simpa [continuousTrajectorySleepingSuffixVarianceMaxIndex,
            maxIndex, m] using ha)
    have hobservable :=
      continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_le_observableRate
        prior posterior score hscore hscore_parameter delta a
          (w := w) (n := n) (by omega) x
    exact hargmin.trans (by simpa [Q, effectiveDelta, m,
      continuousTrajectorySleepingSuffixVarianceSelectedExcess] using hobservable)
  have hscale0 : 0 <= geometricForwardEffectiveScale a :=
    (geometricForwardEffectiveScale_pos a).le
  have hcomplexityRate :
      (continuousGeometricForwardBesselPACBayesComplexity
              prior posterior effectiveDelta a *
            geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) <=
        (A * geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    have hmul := mul_le_mul_of_nonneg_right hAa hscale0
    linarith
  have horacleRate :
      (A * geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) <=
        (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
          (m : Real) :=
    div_le_div_of_nonneg_right horacle (Nat.cast_nonneg m)
  calc
    continuousTrajectorySleepingSuffixVarianceSelectedExcess
        prior posterior score delta w n x <=
      (continuousGeometricForwardBesselPACBayesComplexity
              prior posterior effectiveDelta a *
            geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) := hselected
    _ <= (A * geometricForwardEffectiveScale a +
          2 * Q / geometricForwardEffectiveScale a) /
          (m : Real) := hcomplexityRate
    _ <= (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
          (m : Real) := horacleRate
    _ = continuousTrajectorySleepingSuffixVarianceLILEnvelope
        prior posterior score delta w n x := by
      simp [continuousTrajectorySleepingSuffixVarianceLILEnvelope,
        continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity,
        A, Q, effectiveDelta, m]

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected ordinary-risk endpoint is bounded by observed suffix risk
plus the observable LIL-order excess envelope. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedBoundary_le_LILEnvelope
    (prior posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x <=
      continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score posterior w n x +
        continuousTrajectorySleepingSuffixVarianceLILEnvelope
          prior posterior score delta w n x := by
  unfold continuousTrajectorySleepingSuffixVarianceSelectedBoundary
  exact add_le_add_right
    (continuousTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
      prior posterior score hscore hscore_parameter hdelta hdelta1 hsuffix x) _

/-- One confidence-allocation event simultaneously supports the exact
finite-prefix suffix-variance selector at every reporting time.  The posterior,
wake, time, and selected catalog atom may all depend on the observed path. -/
theorem exists_continuousTrajectorySleepingSuffixVarianceOracle_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
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
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_continuousTrajectorySleepingGeometricTiltPACBayes_suffixRisk_event_of_parameterMeasurable
      K x0 score hscore hscore_parameter prior hdelta
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hsuffix
  let rho := posterior x n
  let w := wake x n
  let selected :=
    continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
      prior rho score delta w n x
  letI : IsProbabilityMeasure rho := hposterior x n
  have hselected_mem : selected ∈ Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1) := by
    exact continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
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
      prior rho score hscore hscore_parameter hdelta hdelta1
        (w := w) (n := n) hsuffix x
  have hboundary :=
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary_le_LILEnvelope
      prior rho score hscore hscore_parameter hdelta hdelta1
        (w := w) (n := n) hsuffix x
  exact ⟨hselected_mem, hselected_risk, hLIL, hboundary⟩

end

end FormalSLT.StochasticDynamics
