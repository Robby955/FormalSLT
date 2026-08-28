/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FinitePMFBridge
import FormalSLT.StochasticDynamics.ContinuousTrajectorySleepingOrdinaryRiskPACBayes

/-!
# Finite certificates for wake-selected trajectory suffix risk

This module turns the measure-valued sleeping trajectory theorem into an
explicit finite-hypothesis certificate.  Posterior integrals become finite
posterior averages and the measure-theoretic relative entropy becomes
`PACBayesKL.klDiv` under a full-support finite prior.

One outer-mass event permits the reporting time, suffix start, and finite
posterior PMF to be selected from the observed path.  The target remains the
posterior-averaged conditional risk encountered on that suffix.  It is not a
future, stationary, population, or deployment-risk guarantee without an
additional bridge.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {ι Z : Type*}
  [Fintype ι]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ### Explicit finite trajectory kernels -/

/-- Convert prefix-dependent finite transition tables into the trajectory
kernel API.  Each supplied row is checked by `IsPMF`. -/
def finiteTrajectoryKernel
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u)) (n : Nat) :
    Kernel ((i : Finset.Iic n) -> Z) Z :=
  Kernel.ofFunOfCountable fun u => (hP n u).toPMF.toMeasure

instance finiteTrajectoryKernel.instIsMarkovKernel
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u)) (n : Nat) :
    IsMarkovKernel (finiteTrajectoryKernel P hP n) :=
  ⟨fun u => by
    change IsProbabilityMeasure (hP n u).toPMF.toMeasure
    infer_instance⟩

/-- Conditional trajectory risk under an explicit finite transition table is
the corresponding weighted finite sum. -/
theorem conditionalTrajectoryRisk_finiteTrajectoryKernel_eq_sum
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u))
    (score : TrajectoryScore Z) (n : Nat) (x : Nat -> Z) :
    conditionalTrajectoryRisk (finiteTrajectoryKernel P hP) score n x =
      ∑ y, P n (Preorder.frestrictLe n x) y *
        score n (Preorder.frestrictLe n x) y := by
  unfold conditionalTrajectoryRisk finiteTrajectoryKernel
  exact (hP n (Preorder.frestrictLe n x)).integral_toPMF_eq_sum _

/-! ### Explicit finite posterior quantities -/

/-- Finite-posterior conditional risk averaged over the monitored suffix
`[j,n)`. Division is total; theorem endpoints assume `j < n`. -/
def finiteTrajectoryPosteriorAverageConditionalSuffixRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (j n : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage posterior fun h =>
    (∑ k ∈ Finset.Ico j n,
      conditionalTrajectoryRisk K (score h) k x) / (n - j : Nat)

/-- The same conditional suffix risk with every transition integral expanded
to a finite sum.  This is the directly evaluable target for finite
certificates. -/
def finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (j n : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage posterior fun h =>
    (∑ k ∈ Finset.Ico j n,
      ∑ y, P k (Preorder.frestrictLe k x) y *
        score h k (Preorder.frestrictLe k x) y) / (n - j : Nat)

/-- Expanding the finite-row kernel changes no conditional suffix risk. -/
theorem
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk_finiteTrajectoryKernel
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u))
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (j n : Nat) (x : Nat -> Z) :
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk
        (finiteTrajectoryKernel P hP) score posterior j n x =
      finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
        P score posterior j n x := by
  unfold finiteTrajectoryPosteriorAverageConditionalSuffixRisk
    finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
  apply congrArg (posteriorAverage posterior)
  funext h
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact conditionalTrajectoryRisk_finiteTrajectoryKernel_eq_sum
    P hP (score h) k x

/-- Finite-posterior empirical score averaged over the monitored suffix
`[j,n)`. -/
def finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (j n : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage posterior fun h =>
    (∑ k ∈ Finset.Ico j n,
      observedTrajectoryScore (score h) k x) / (n - j : Nat)

/-- Finite-posterior observable forward-prediction residual penalty on
`[j,n)`. -/
def finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    (score : ι -> TrajectoryScore Z) (posterior : ι -> Real)
    (eta : Nat -> Real) (j n : Nat) (x : Nat -> Z) : Real :=
  posteriorAverage posterior fun h =>
    ∑ k ∈ Finset.Ico j n,
      forwardEmpiricalBernsteinPsi (eta j) *
        (observedTrajectoryScore (score h) k x -
          forwardPredictorProcess
            (observedTrajectoryScore (score h)) k x) ^ 2

/-- Fully explicit finite upper boundary for the ordinary encountered suffix
risk.  `klDiv posterior prior` charges for post-data model selection, while
`-log (polynomialEpochWeight j)` charges for selecting the wake-time atom. -/
def finiteTrajectorySleepingConstantTiltSuffixBoundary
    (prior posterior : ι -> Real)
    (score : ι -> TrajectoryScore Z) (eta : Nat -> Real)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score posterior j n x +
    (klDiv posterior prior +
        Real.log (1 / delta) - Real.log (polynomialEpochWeight j) +
        finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
          score posterior eta j n x) /
      (((n - j : Nat) : Real) * eta j)

omit [Fintype Z]
  [MeasurableSingletonClass Z] in
/-- The measure-valued conditional suffix risk is exactly its finite-sum
counterpart after converting a FormalSLT PMF to a mathlib measure. -/
theorem continuousTrajectoryPosteriorAverageConditionalSuffixRisk_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : ι -> TrajectoryScore Z) {posterior : ι -> Real}
    (hposterior : IsPMF posterior) (j n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorAverageConditionalSuffixRisk
        K score hposterior.toPMF.toMeasure j n x =
      finiteTrajectoryPosteriorAverageConditionalSuffixRisk
        K score posterior j n x := by
  unfold continuousTrajectoryPosteriorAverageConditionalSuffixRisk
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk
  exact integral_toPMF_eq_posteriorAverage hposterior _

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The measure-valued empirical suffix risk is exactly its finite-sum
counterpart. -/
theorem continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (score : ι -> TrajectoryScore Z) {posterior : ι -> Real}
    (hposterior : IsPMF posterior) (j n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        score hposterior.toPMF.toMeasure j n x =
      finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        score posterior j n x := by
  unfold continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
  exact integral_toPMF_eq_posteriorAverage hposterior _

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The measure-valued residual penalty is exactly its finite posterior
average. -/
theorem
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (score : ι -> TrajectoryScore Z) {posterior : ι -> Real}
    (hposterior : IsPMF posterior) (eta : Nat -> Real)
    (j n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score hposterior.toPMF.toMeasure eta j n x =
      finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        score posterior eta j n x := by
  unfold continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
  exact integral_toPMF_eq_posteriorAverage hposterior _

omit [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- The continuous-measure boundary reduces exactly to the explicit finite
boundary under a full-support finite prior. -/
theorem continuousTrajectorySleepingConstantTiltSuffixBoundary_toPMF
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {prior posterior : ι -> Real}
    (hprior : IsFullSupportPMF prior) (hposterior : IsPMF posterior)
    (score : ι -> TrajectoryScore Z) (eta : Nat -> Real)
    (delta : Real) (j n : Nat) (x : Nat -> Z) :
    continuousTrajectorySleepingConstantTiltSuffixBoundary
        hprior.toIsPMF.toPMF.toMeasure hposterior.toPMF.toMeasure
        score eta delta j n x =
      finiteTrajectorySleepingConstantTiltSuffixBoundary
        prior posterior score eta delta j n x := by
  unfold continuousTrajectorySleepingConstantTiltSuffixBoundary
    finiteTrajectorySleepingConstantTiltSuffixBoundary
  rw [continuousTrajectoryPosteriorEmpiricalPrequentialSuffixRisk_toPMF
      score hposterior j n x,
    toReal_informationTheory_klDiv_toPMF_eq_of_fullSupport
      hposterior hprior,
    continuousTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty_toPMF
      score hposterior eta j n x]

/-- One outer-mass event controls every finite posterior PMF, reporting time,
and nonempty wake-selected suffix.  All quantities in the conclusion are
in finite-sum form, so the endpoint can be instantiated without exposing
measure-valued posterior terms. Numerical replay of logarithmic terms still
requires proved evaluations or certified bounds. -/
theorem exists_finiteTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y,
      score h n u y ∈ Set.Icc (0 : Real) 1)
    (eta : Nat -> Real) {L : Real}
    (heta_pos : forall j, 0 < eta j)
    (heta_upper : forall j, eta j <= L) (hL1 : L < 1)
    {prior : ι -> Real} (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : ι -> Real, IsPMF posterior ->
            forall j n : Nat, j < n ->
              finiteTrajectoryPosteriorAverageConditionalSuffixRisk
                  K score posterior j n x <
                finiteTrajectorySleepingConstantTiltSuffixBoundary
                  prior posterior score eta delta j n x := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let priorMeasure : Measure ι := hprior.toIsPMF.toPMF.toMeasure
  haveI : IsProbabilityMeasure priorMeasure := by
    unfold priorMeasure
    infer_instance
  have hparameter : forall n u y,
      StronglyMeasurable (fun h => score h n u y) := by
    intro n u y
    exact (measurable_of_finite _).stronglyMeasurable
  rcases
      exists_continuousTrajectorySleepingConstantTiltPACBayes_suffixRisk_event_of_parameterMeasurable
        K x0 score hscore hparameter eta heta_pos heta_upper hL1
        priorMeasure hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior j n hjn
  let posteriorMeasure : Measure ι := hposterior.toPMF.toMeasure
  have hposteriorProbability : IsProbabilityMeasure posteriorMeasure := by
    unfold posteriorMeasure
    infer_instance
  have hposteriorPrior : posteriorMeasure ≪ priorMeasure := by
    unfold posteriorMeasure priorMeasure
    exact toPMF_toMeasure_absolutelyContinuous_of_fullSupport
      hposterior hprior
  have hllr : Integrable (llr posteriorMeasure priorMeasure) posteriorMeasure :=
    Integrable.of_finite
  have hbound := hgood x hx posteriorMeasure hposteriorProbability
    hposteriorPrior hllr j n hjn
  unfold posteriorMeasure priorMeasure at hbound
  rw [continuousTrajectoryPosteriorAverageConditionalSuffixRisk_toPMF
        K score hposterior j n x,
      continuousTrajectorySleepingConstantTiltSuffixBoundary_toPMF
        hprior hposterior score eta delta j n x] at hbound
  exact hbound

/-- Fully finite specialization: both the hypothesis posterior and every
prefix-dependent transition row are real-valued finite PMFs.  The left side
is therefore an explicit nested finite sum. -/
theorem exists_finitePMFTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
    (P : (n : Nat) -> ((i : Finset.Iic n) -> Z) -> Z -> Real)
    (hP : forall n u, IsPMF (P n u)) (x0 : Z)
    (score : ι -> TrajectoryScore Z)
    (hscore : forall h n u y,
      score h n u y ∈ Set.Icc (0 : Real) 1)
    (eta : Nat -> Real) {L : Real}
    (heta_pos : forall j, 0 < eta j)
    (heta_upper : forall j, eta j <= L) (hL1 : L < 1)
    {prior : ι -> Real} (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure (finiteTrajectoryKernel P hP) x0).real
          goodEventᶜ <= delta ∧
        forall x, x ∈ goodEvent ->
          forall posterior : ι -> Real, IsPMF posterior ->
            forall j n : Nat, j < n ->
              finitePMFTrajectoryPosteriorAverageConditionalSuffixRisk
                  P score posterior j n x <
                finiteTrajectorySleepingConstantTiltSuffixBoundary
                  prior posterior score eta delta j n x := by
  rcases
      exists_finiteTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
        (finiteTrajectoryKernel P hP) x0 score hscore eta
        heta_pos heta_upper hL1 hprior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior j n hjn
  rw [←
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk_finiteTrajectoryKernel
      P hP score posterior j n x]
  exact hgood x hx posterior hposterior j n hjn

end

end FormalSLT.StochasticDynamics
