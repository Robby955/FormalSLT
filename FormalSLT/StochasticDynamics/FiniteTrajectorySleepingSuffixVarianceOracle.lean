/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingOrdinaryRiskPACBayes
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingSuffixVarianceOracle

/-!
# Finite observable sleeping suffix-variance certificates

This module rewrites the observable sleeping suffix-variance oracle for finite
hypothesis PMFs.  Posterior integrals, relative entropy, observable quadratic
variation, geometric-atom excesses, and selected boundaries are all finite
sums or ordinary real expressions.  A second endpoint also expands each
finite-state transition kernel into its supplied PMF table.

The exact selector minimizes over the admitted finite geometric prefix.  It is
not a coin-betting master or a parameter-free construction.  The common event
allows the posterior, wake, reporting time, and selector to depend on the
observed path.  Its target is the posterior-averaged conditional risk
encountered on the selected suffix, not future, stationary, population, or
deployment risk without an additional bridge.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayesOracle
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ### Finite observable suffix quantities -/

/-- Finite-posterior raw prediction-residual quadratic variation on `[w,n)`.
The forward predictor still uses the complete history before each `k`. -/
def finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage posterior fun h =>
    ∑ k ∈ Finset.Ico w n,
      (observedTrajectoryScore (score h) k x -
        forwardPredictorProcess
          (observedTrajectoryScore (score h)) k x) ^ 2

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Converting a finite posterior PMF to a measure changes no raw observable
suffix quadratic variation. -/
theorem continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (score : ι -> TrajectoryScore Z) {posterior : ι -> Real}
    (hposterior : IsPMF posterior) (w n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
        score hposterior.toPMF.toMeasure w n x =
      finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
        score posterior w n x := by
  unfold continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation
    finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
  exact integral_toPMF_eq_posteriorAverage hposterior _

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The finite constant-tilt penalty factors as `psi(lambda)` times the raw
finite-posterior suffix quadratic variation. -/
theorem finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_eq
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (score : ι -> TrajectoryScore Z) {posterior : ι -> Real}
    (hposterior : IsPMF posterior) (lam : Real)
    (w n : Nat) (x : Nat -> Z) :
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior (fun _ => lam) w n x =
      forwardEmpiricalBernsteinPsi lam *
        finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
          score posterior w n x := by
  rw [← continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_toPMF
      score hposterior (fun _ => lam) w n x]
  rw [continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_eq]
  rw [continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_toPMF
      score hposterior w n x]

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Unit-bounded finite scores put the raw observable suffix quadratic
variation between zero and the suffix length. -/
theorem finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y, score h n u y ∈ Set.Icc (0 : Real) 1)
    {posterior : ι -> Real} (hposterior : IsPMF posterior)
    {w n : Nat} (hwn : w <= n) (x : Nat -> Z) :
    finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
        score posterior w n x ∈ Set.Icc 0 ((n - w : Nat) : Real) := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let posteriorMeasure : Measure ι := hposterior.toPMF.toMeasure
  letI : IsProbabilityMeasure posteriorMeasure := by
    unfold posteriorMeasure
    infer_instance
  have hparameter : forall k u y,
      StronglyMeasurable (fun h => score h k u y) := by
    intro k u y
    exact (measurable_of_finite _).stronglyMeasurable
  have hbound :=
    continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc
      score hscore hparameter posteriorMeasure hwn x
  unfold posteriorMeasure at hbound
  rw [continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_toPMF
      score hposterior w n x] at hbound
  exact hbound

/-- Finite KL plus the wake-adjusted geometric-atom confidence charge and raw
observable suffix-variance penalty. -/
def finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) : Real :=
  let effectiveDelta :=
    continuousTrajectorySleepingSuffixEffectiveConfidence delta w
  let Q := finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  (geometricForwardBesselPACBayesComplexity
        prior posterior effectiveDelta a +
      forwardEmpiricalBernsteinPsi (geometricForwardTilt a) * Q) /
    (((n - w : Nat) : Real) * geometricForwardTilt a)

/-- Finite posterior empirical suffix risk plus one observable geometric-atom
excess. -/
def finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) : Real :=
  finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior w n x +
    finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
      prior posterior score delta a w n x

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- A continuous-measure geometric excess is exactly the finite expression
under a full-support finite prior. -/
theorem continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score delta a w n x =
      finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta a w n x := by
  unfold continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
    finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
    continuousGeometricForwardBesselPACBayesComplexity
    geometricForwardBesselPACBayesComplexity
  dsimp
  rw [toReal_informationTheory_klDiv_toPMF_eq_of_fullSupport
      hposterior hprior]
  rw [continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_toPMF
      score hposterior w n x]

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- A continuous-measure geometric boundary is exactly the finite expression
under finite prior and posterior PMFs. -/
theorem continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (a w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score delta a w n x =
      finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        prior posterior score delta a w n x := by
  unfold continuousTrajectorySleepingSuffixVarianceGeometricTiltBoundary
    finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
  rw [continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_toPMF
      score hposterior w n x]
  rw [continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
      hprior hposterior score delta a w n x]

/-! ### Exact finite-prefix selector -/

/-- Largest geometric atom admitted by the suffix length. -/
def finiteTrajectorySleepingSuffixVarianceMaxIndex (w n : Nat) : Nat :=
  continuousTrajectorySleepingSuffixVarianceMaxIndex w n

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem finiteTrajectorySleepingSuffixVariance_exists_argmin
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    ∃ a ∈ Finset.range
        (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1),
      ∀ a' ∈ Finset.range
          (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1),
        finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
            prior posterior score delta a w n x <=
          finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
            prior posterior score delta a' w n x := by
  classical
  exact (Finset.range
      (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1)).exists_min_image
    (fun a => finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
      prior posterior score delta a w n x)
    (by simp)

/-- Exact minimizer of the finite observable excess over the admitted
geometric prefix. -/
def finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Nat :=
  Classical.choose
    (finiteTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The finite selector belongs to the admitted geometric prefix. -/
theorem finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
        prior posterior score delta w n x ∈
      Finset.range
        (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1) := by
  exact (Classical.choose_spec
    (finiteTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)).1

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The finite selector has no larger excess than any admitted atom. -/
theorem finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) {a : Nat}
    (ha : a ∈ Finset.range
      (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1)) :
    finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta
          (finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
            prior posterior score delta w n x) w n x <=
      finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta a w n x := by
  exact (Classical.choose_spec
    (finiteTrajectorySleepingSuffixVariance_exists_argmin
      prior posterior score delta w n x)).2 a ha

/-- Observable finite excess chosen by the exact finite-prefix selector. -/
def finiteTrajectorySleepingSuffixVarianceSelectedExcess
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
    prior posterior score delta
      (finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
        prior posterior score delta w n x) w n x

/-- Finite ordinary-risk endpoint chosen by the exact finite-prefix selector. -/
def finiteTrajectorySleepingSuffixVarianceSelectedBoundary
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior w n x +
    finiteTrajectorySleepingSuffixVarianceSelectedExcess
      prior posterior score delta w n x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected finite boundary is no larger than every admitted geometric
atom boundary. -/
theorem finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) {a : Nat}
    (ha : a ∈ Finset.range
      (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1)) :
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x <=
      finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
        prior posterior score delta a w n x := by
  unfold finiteTrajectorySleepingSuffixVarianceSelectedBoundary
    finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary
  exact add_le_add_right
    (finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
      prior posterior score delta w n x ha) _

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The continuous and finite exact selectors may choose different minimizing
indices, but their selected excess values agree. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedExcess_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceSelectedExcess
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score delta w n x =
      finiteTrajectorySleepingSuffixVarianceSelectedExcess
        prior posterior score delta w n x := by
  let priorMeasure := hprior.toIsPMF.toPMF.toMeasure
  let posteriorMeasure := hposterior.toPMF.toMeasure
  let continuousSelected :=
    continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin
      priorMeasure posteriorMeasure score delta w n x
  let finiteSelected :=
    finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
      prior posterior score delta w n x
  have hcontinuous_mem : continuousSelected ∈ Finset.range
      (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1) := by
    simpa [continuousSelected, priorMeasure, posteriorMeasure,
      finiteTrajectorySleepingSuffixVarianceMaxIndex,
      continuousTrajectorySleepingSuffixVarianceMaxIndex] using
      continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
        priorMeasure posteriorMeasure score delta w n x
  have hfinite_mem : finiteSelected ∈ Finset.range
      (continuousTrajectorySleepingSuffixVarianceMaxIndex w n + 1) := by
    simpa [continuousSelected, finiteSelected,
      finiteTrajectorySleepingSuffixVarianceMaxIndex,
      continuousTrajectorySleepingSuffixVarianceMaxIndex] using
      finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
        prior posterior score delta w n x
  apply le_antisymm
  · have hle :=
      continuousTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
        priorMeasure posteriorMeasure score delta w n x hfinite_mem
    rw [continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
        hprior hposterior score delta continuousSelected w n x] at hle
    rw [continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
        hprior hposterior score delta finiteSelected w n x] at hle
    change continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        priorMeasure posteriorMeasure score delta continuousSelected w n x <=
      finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta finiteSelected w n x
    rw [continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
        hprior hposterior score delta continuousSelected w n x]
    exact hle
  · have hle :=
      finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_le
        prior posterior score delta w n x hcontinuous_mem
    change finiteTrajectorySleepingSuffixVarianceGeometricTiltExcess
        prior posterior score delta finiteSelected w n x <=
      continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess
        priorMeasure posteriorMeasure score delta continuousSelected w n x
    rw [continuousTrajectorySleepingSuffixVarianceGeometricTiltExcess_toPMF
        hprior hposterior score delta continuousSelected w n x]
    exact hle

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The continuous selected endpoint is exactly the finite selected endpoint. -/
theorem continuousTrajectorySleepingSuffixVarianceSelectedBoundary_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceSelectedBoundary
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score delta w n x =
      finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x := by
  unfold continuousTrajectorySleepingSuffixVarianceSelectedBoundary
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
  rw [continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_toPMF
      score hposterior w n x]
  rw [continuousTrajectorySleepingSuffixVarianceSelectedExcess_toPMF
      hprior hposterior score delta w n x]

/-! ### Finite dyadic envelope -/

/-- Largest-prefix finite KL complexity at wake-adjusted confidence. -/
def finiteTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    (prior posterior : ι -> Real) (delta : Real)
    (w n : Nat) : Real :=
  growingPrefixForwardBesselPACBayesComplexity prior posterior
    (continuousTrajectorySleepingSuffixEffectiveConfidence delta w) (n - w)

/-- Finite observable dyadic square-root envelope for the exact selector.  Its
iterated-logarithm interpretation still requires controlled posterior KL and
wake cost relative to the suffix length. -/
def finiteTrajectorySleepingSuffixVarianceLILEnvelope
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) : Real :=
  let A := finiteTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    prior posterior delta w n
  let Q := finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation
    score posterior w n x
  (2 * A + (5 / 2 : Real) * A * Real.sqrt (2 * Q / A)) /
    ((n - w : Nat) : Real)

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem
    continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (delta : Real) (w n : Nat) :
    continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        delta w n =
      finiteTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
        prior posterior delta w n := by
  unfold continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    finiteTrajectorySleepingSuffixVarianceGrowingPrefixComplexity
    continuousGrowingPrefixForwardBesselPACBayesComplexity
    growingPrefixForwardBesselPACBayesComplexity
    continuousGeometricForwardBesselPACBayesComplexity
    geometricForwardBesselPACBayesComplexity
  rw [toReal_informationTheory_klDiv_toPMF_eq_of_fullSupport
      hposterior hprior]

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The continuous dyadic envelope is exactly the finite expression. -/
theorem continuousTrajectorySleepingSuffixVarianceLILEnvelope_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (delta : Real)
    (w n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingSuffixVarianceLILEnvelope
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score delta w n x =
      finiteTrajectorySleepingSuffixVarianceLILEnvelope
        prior posterior score delta w n x := by
  unfold continuousTrajectorySleepingSuffixVarianceLILEnvelope
    finiteTrajectorySleepingSuffixVarianceLILEnvelope
  rw [continuousTrajectorySleepingSuffixVarianceGrowingPrefixComplexity_toPMF
      hprior hposterior delta w n]
  rw [continuousTrajectoryPosteriorSuffixPredictorQuadraticVariation_toPMF
      score hposterior w n x]

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The finite exact selector is bounded by the finite observable dyadic
envelope. -/
theorem finiteTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y, score h n u y ∈ Set.Icc (0 : Real) 1)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    finiteTrajectorySleepingSuffixVarianceSelectedExcess
        prior posterior score delta w n x <=
      finiteTrajectorySleepingSuffixVarianceLILEnvelope
        prior posterior score delta w n x := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let priorMeasure : Measure ι := hprior.toIsPMF.toPMF.toMeasure
  let posteriorMeasure : Measure ι := hposterior.toPMF.toMeasure
  letI : IsProbabilityMeasure posteriorMeasure := by
    unfold posteriorMeasure
    infer_instance
  have hparameter : forall k u y,
      StronglyMeasurable (fun h => score h k u y) := by
    intro k u y
    exact (measurable_of_finite _).stronglyMeasurable
  have hbound :=
    continuousTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
      priorMeasure posteriorMeasure score hscore hparameter hdelta hdelta1
        hsuffix x
  unfold priorMeasure posteriorMeasure at hbound
  rw [continuousTrajectorySleepingSuffixVarianceSelectedExcess_toPMF
      hprior hposterior score delta w n x] at hbound
  rw [continuousTrajectorySleepingSuffixVarianceLILEnvelope_toPMF
      hprior hposterior score delta w n x] at hbound
  exact hbound

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The finite selected boundary is bounded by finite empirical suffix risk
plus the finite observable dyadic envelope. -/
theorem finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le_LILEnvelope
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y, score h n u y ∈ Set.Icc (0 : Real) 1)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {w n : Nat} (hsuffix : 4 <= n - w) (x : Nat -> Z) :
    finiteTrajectorySleepingSuffixVarianceSelectedBoundary
        prior posterior score delta w n x <=
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
          score posterior w n x +
        finiteTrajectorySleepingSuffixVarianceLILEnvelope
          prior posterior score delta w n x := by
  unfold finiteTrajectorySleepingSuffixVarianceSelectedBoundary
  exact add_le_add_right
    (finiteTrajectorySleepingSuffixVarianceSelectedExcess_le_LILEnvelope
      hprior hposterior score hscore hdelta hdelta1 hsuffix x) _

/-! ### Common finite events -/

/-- One event supports the exact finite-PMF suffix-variance selector for every
path-selected posterior, wake, and reporting time. -/
theorem exists_finiteTrajectorySleepingSuffixVarianceOracle_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y, score h n u y ∈ Set.Icc (0 : Real) 1)
    {prior : ι -> Real} (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (posterior : (Nat -> Z) -> Nat -> ι -> Real)
    (hposterior : forall x n, IsPMF (posterior x n))
    (wake : (Nat -> Z) -> Nat -> Nat) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent -> forall n : Nat,
          4 <= n - wake x n ->
            let rho := posterior x n
            let w := wake x n
            let selected :=
              finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
                prior rho score delta w n x
            selected ∈ Finset.range
                (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1) ∧
              finiteTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score rho w n x <
                finiteTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x ∧
              finiteTrajectorySleepingSuffixVarianceSelectedExcess
                  prior rho score delta w n x <=
                finiteTrajectorySleepingSuffixVarianceLILEnvelope
                  prior rho score delta w n x ∧
              finiteTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x <=
                finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
                    score rho w n x +
                  finiteTrajectorySleepingSuffixVarianceLILEnvelope
                    prior rho score delta w n x := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let priorMeasure : Measure ι := hprior.toIsPMF.toPMF.toMeasure
  let posteriorMeasure : (Nat -> Z) -> Nat -> Measure ι :=
    fun x n => (hposterior x n).toPMF.toMeasure
  haveI : IsProbabilityMeasure priorMeasure := by
    unfold priorMeasure
    infer_instance
  have hparameter : forall k u y,
      StronglyMeasurable (fun h => score h k u y) := by
    intro k u y
    exact (measurable_of_finite _).stronglyMeasurable
  have hposterior_probability : forall x n,
      IsProbabilityMeasure (posteriorMeasure x n) := by
    intro x n
    unfold posteriorMeasure
    infer_instance
  have hposterior_prior : forall x n,
      posteriorMeasure x n ≪ priorMeasure := by
    intro x n
    unfold posteriorMeasure priorMeasure
    exact toPMF_toMeasure_absolutelyContinuous_of_fullSupport
      (hposterior x n) hprior
  have hllr : forall x n,
      Integrable (llr (posteriorMeasure x n) priorMeasure)
        (posteriorMeasure x n) := by
    intro x n
    exact Integrable.of_finite
  rcases
      exists_continuousTrajectorySleepingSuffixVarianceOracle_event
        K x0 score hscore hparameter priorMeasure hdelta hdelta1
        posteriorMeasure hposterior_probability hposterior_prior hllr wake with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hsuffix
  let rho := posterior x n
  let w := wake x n
  have hcontinuous := hgood x hx n hsuffix
  have hselected_mem :
      finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
          prior rho score delta w n x ∈
        Finset.range
          (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1) :=
    finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin_mem
      prior rho score delta w n x
  have hrisk := hcontinuous.2.1
  have hLIL := hcontinuous.2.2.1
  have hboundary := hcontinuous.2.2.2
  unfold posteriorMeasure priorMeasure at hrisk hLIL hboundary
  rw [continuousTrajectoryPosteriorAverageConditionalSuffixRisk_toPMF
      K score (hposterior x n) w n x] at hrisk
  rw [continuousTrajectorySleepingSuffixVarianceSelectedBoundary_toPMF
      hprior (hposterior x n) score delta w n x] at hrisk
  rw [continuousTrajectorySleepingSuffixVarianceSelectedExcess_toPMF
      hprior (hposterior x n) score delta w n x] at hLIL
  rw [continuousTrajectorySleepingSuffixVarianceLILEnvelope_toPMF
      hprior (hposterior x n) score delta w n x] at hLIL
  rw [continuousTrajectorySleepingSuffixVarianceSelectedBoundary_toPMF
      hprior (hposterior x n) score delta w n x] at hboundary
  rw [continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_toPMF
      score (hposterior x n) w n x] at hboundary
  rw [continuousTrajectorySleepingSuffixVarianceLILEnvelope_toPMF
      hprior (hposterior x n) score delta w n x] at hboundary
  dsimp only
  exact ⟨hselected_mem, hrisk, hLIL, hboundary⟩

/-- Fully finite specialization: posterior quantities and every conditional
transition risk are explicit finite sums. -/
theorem exists_finitePMFTrajectorySleepingSuffixVarianceOracle_event
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u)) (x0 : Z)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y, score h n u y ∈ Set.Icc (0 : Real) 1)
    {prior : ι -> Real} (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (posterior : (Nat -> Z) -> Nat -> ι -> Real)
    (hposterior : forall x n, IsPMF (posterior x n))
    (wake : (Nat -> Z) -> Nat -> Nat) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure (finiteTrajectoryKernel P hP) x0).real
          goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent -> forall n : Nat,
          4 <= n - wake x n ->
            let rho := posterior x n
            let w := wake x n
            let selected :=
              finiteTrajectorySleepingSuffixVarianceFinitePrefixArgmin
                prior rho score delta w n x
            selected ∈ Finset.range
                (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1) ∧
              finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
                  P score rho w n x <
                finiteTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x ∧
              finiteTrajectorySleepingSuffixVarianceSelectedExcess
                  prior rho score delta w n x <=
                finiteTrajectorySleepingSuffixVarianceLILEnvelope
                  prior rho score delta w n x ∧
              finiteTrajectorySleepingSuffixVarianceSelectedBoundary
                  prior rho score delta w n x <=
                finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
                    score rho w n x +
                  finiteTrajectorySleepingSuffixVarianceLILEnvelope
                    prior rho score delta w n x := by
  rcases
      exists_finiteTrajectorySleepingSuffixVarianceOracle_event
        (finiteTrajectoryKernel P hP) x0 score hscore hprior hdelta hdelta1
        posterior hposterior wake with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hsuffix
  have hbound := hgood x hx n hsuffix
  dsimp only at hbound
  rw [finiteTrajectoryPosteriorAverageConditionalSuffixRisk_finiteTrajectoryKernel
      P hP score (posterior x n) (wake x n) n x] at hbound
  exact hbound

end

end FormalSLT.StochasticDynamics
