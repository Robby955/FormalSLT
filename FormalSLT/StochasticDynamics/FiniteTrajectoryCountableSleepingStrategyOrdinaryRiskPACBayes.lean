/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingStrategyOrdinaryRiskPACBayes

/-!
# Ordinary trajectory risk for countable sleeping-strategy posteriors

This module specializes the generic polynomial sleeping e-process posterior
to the observable forward-predictor empirical-Bernstein process on bounded
prefix-dependent trajectories.  One event permits post-data selection of the
reporting time, a finite model posterior, and a posterior over every strategy
atom active before that time.  Model and strategy selection pay separate KL
costs.

The selected strategy posterior induces one realized time-weight vector.
Two finite total-variation comparisons convert the weighted result to ordinary
encountered prefix risk.  The conclusion is not future, stationary,
population, or deployment risk.  The countable catalog is fixed in advance;
this remains confidence allocation rather than coin betting.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
open scoped BigOperators

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Iota Z : Type*}
  [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Active trajectory catalog and observable score -/

/-- The `j`th declared trajectory strategy, asleep before time `j`. -/
def countableSleepingTrajectoryStrategy
    (strategy : Nat -> TrajectoryPredictableTilt Z) (j : Nat) :
    TrajectoryPredictableTilt Z :=
  fun k u => if j <= k then strategy j k u else 0

/-- Restrict the countable sleeping catalog to the atoms active before the
reporting time `n`, in the finite model--strategy interface. -/
def finiteTrajectoryActiveSleepingStrategyCatalog
    (strategy : Nat -> TrajectoryPredictableTilt Z) (n : Nat) :
    Fin n -> Iota -> TrajectoryPredictableTilt Z :=
  fun j _i => countableSleepingTrajectoryStrategy strategy j.1

/-- Evaluation of the active trajectory catalog on the observed full path. -/
def observedFiniteTrajectoryActiveSleepingStrategyCatalog
    (strategy : Nat -> TrajectoryPredictableTilt Z) (n : Nat) :
    Fin n -> Iota -> Nat -> (Nat -> Z) -> Real :=
  fun j i => observedTrajectoryPredictableTilt
    (finiteTrajectoryActiveSleepingStrategyCatalog strategy n j i)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Adding a common wake at zero does not change the already-sleeping active
catalog. -/
theorem finiteTrajectoryActiveSleepingStrategyCatalog_eq_commonWake
    (strategy : Nat -> TrajectoryPredictableTilt Z) (n : Nat) :
    finiteTrajectoryActiveSleepingStrategyCatalog (Iota := Iota) strategy n =
      sleepingTrajectoryStrategyCatalog (fun _ : Fin n => 0)
        (fun j : Fin n =>
          countableSleepingTrajectoryStrategy strategy j.1) := by
  funext j i k u
  simp [finiteTrajectoryActiveSleepingStrategyCatalog,
    sleepingTrajectoryStrategyCatalog]

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
theorem observed_countableSleepingTrajectoryStrategy
    (strategy : Nat -> TrajectoryPredictableTilt Z) (j : Nat) :
    observedTrajectoryPredictableTilt
        (countableSleepingTrajectoryStrategy strategy j) =
      sleepingStrategy
        (observedTrajectoryPredictableStrategyCatalog strategy) j := by
  rfl

/-- Per-model, per-wake observable empirical-Bernstein e-process. -/
def finiteTrajectoryCountableSleepingEBComponent
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Iota -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (i : Iota) (j : Nat) : Nat -> (Nat -> Z) -> Real :=
  forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
    (observedTrajectoryScore (score i))
    (conditionalTrajectoryRisk K (score i))
    (sleepingStrategy
      (observedTrajectoryPredictableStrategyCatalog strategy) j)

/-- Observable quadratic penalty for a factorized model posterior and active
sleeping-strategy posterior. -/
def finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
    (score : Iota -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Iota -> Real)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  trajectoryPredictableStrategyPosteriorQuadraticPenalty score
    (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
    (modelStrategyProductPrior modelPosterior strategyPosterior) n x

/-- Effective exposure of the selected active-prefix strategy posterior. -/
def finiteTrajectoryCountableSleepingStrategyExposure
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  finiteStrategyPosteriorSleepingExposure strategyPosterior
    (fun j : Fin n => countableSleepingTrajectoryStrategy strategy j.1)
    0 n x

/-- Total-variation discrepancy between uniform prefix weights and the
selected active-prefix strategy posterior's effective weights. -/
def finiteTrajectoryCountableSleepingStrategyUniformDiscrepancy
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) : Real :=
  finiteStrategyPosteriorSleepingUniformDiscrepancy strategyPosterior
    (fun j : Fin n => countableSleepingTrajectoryStrategy strategy j.1)
    0 n x

omit [DecidableEq Iota] [Nonempty Iota]
  [Fintype Z] [MeasurableSingletonClass Z] in
private theorem nested_logComponent_eq_scoreAverage
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Iota -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Iota -> Real)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) :
    posteriorAverage modelPosterior (fun i =>
        posteriorAverage strategyPosterior (fun j =>
          Real.log (finiteTrajectoryCountableSleepingEBComponent
            K score strategy i j.1 n x))) =
      posteriorAverage
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (fun p : Iota × Fin n =>
          forwardPredictableTiltPACBayesScore
            (modelStrategyProcess
              (fun i => observedTrajectoryScore (score i)))
            (modelStrategyProcess
              (fun i => conditionalTrajectoryRisk K (score i)))
            (modelStrategyPredictableTilt
              (observedFiniteTrajectoryActiveSleepingStrategyCatalog
                strategy n))
            p n x) := by
  unfold posteriorAverage modelStrategyProductPrior
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hprocess :=
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq
      (observedTrajectoryScore (score i))
      (conditionalTrajectoryRisk K (score i))
      (sleepingStrategy
        (observedTrajectoryPredictableStrategyCatalog strategy) j.1)
      n x
  have hlog :
      Real.log (finiteTrajectoryCountableSleepingEBComponent
          K score strategy i j.1 n x) =
        forwardPredictableTiltPACBayesScore
          (modelStrategyProcess
            (fun i => observedTrajectoryScore (score i)))
          (modelStrategyProcess
            (fun i => conditionalTrajectoryRisk K (score i)))
          (modelStrategyPredictableTilt
            (observedFiniteTrajectoryActiveSleepingStrategyCatalog
              strategy n))
          (i, j) n x := by
    rw [show finiteTrajectoryCountableSleepingEBComponent
        K score strategy i j.1 n x =
      Real.exp
        (forwardPredictableTiltPACBayesScore
          (modelStrategyProcess
            (fun i => observedTrajectoryScore (score i)))
          (modelStrategyProcess
            (fun i => conditionalTrajectoryRisk K (score i)))
          (modelStrategyPredictableTilt
            (observedFiniteTrajectoryActiveSleepingStrategyCatalog
              strategy n))
          (i, j) n x) by
      unfold finiteTrajectoryCountableSleepingEBComponent
      rw [hprocess]
      rfl]
    exact Real.log_exp _
  simp only
  rw [hlog]
  ring

/-! ## Raw countable posterior event -/

/-- One trajectory event controls the observable weighted mean gap for every
time, finite model posterior, and posterior on the active prefix of the
predeclared countable sleeping strategy catalog. -/
theorem exists_finiteTrajectoryCountableSleepingStrategyPACBayes_raw_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    {score : Iota -> TrajectoryScore Z}
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    {strategy : Nat -> TrajectoryPredictableTilt Z}
    {L : Real} (hL1 : L < 1)
    (hstrategy : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    {modelPrior : Iota -> Real}
    (hmodelPrior : IsFullSupportPMF modelPrior)
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta /\
        forall x, x ∈ goodEvent -> forall n : Nat,
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin n -> Real,
            IsPMF strategyPosterior ->
          trajectoryPredictableStrategyPosteriorMeanGap K score
              (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
              (modelStrategyProductPrior
                modelPosterior strategyPosterior) n x <
            (klDiv modelPosterior modelPrior +
                klDiv (liftPolynomialActivePosterior strategyPosterior)
                  (polynomialActiveTailPrior n)) +
              Real.log (1 / delta) +
                finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
                  score strategy modelPosterior strategyPosterior x := by
  let E : Iota -> Nat -> Nat -> (Nat -> Z) -> Real :=
    finiteTrajectoryCountableSleepingEBComponent K score strategy
  have hE : forall i j, EProcess (trajectoryMeasure K x0)
      (Filtration.piLE (X := fun _ : Nat => Z)) (E i j) := by
    intro i j
    unfold E finiteTrajectoryCountableSleepingEBComponent
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
        hL1
        (observedTrajectoryScore_incrementAdapted (score i))
        (conditionalTrajectoryRisk_stronglyAdapted K (score i))
        (sleepingStrategy_stronglyAdapted
          (observedTrajectoryPredictableStrategyCatalog strategy)
          (fun a => observedTrajectoryPredictableTilt_stronglyAdapted
            (strategy a)) j)
        (fun k x => observedTrajectoryScore_mem_Icc (hscore i) k x)
        (fun k x => sleepingStrategy_mem_Icc
          (strategy := observedTrajectoryPredictableStrategyCatalog strategy)
          (fun a r y => hstrategy a r (Preorder.frestrictLe r y))
          j k x)
        (fun k => observedTrajectoryScore_condExp
          K x0 (score i) (hscore i) k)
  have hsleep : forall i j n x, n <= j -> E i j n x = 1 := by
    intro i j n x hnj
    unfold E finiteTrajectoryCountableSleepingEBComponent
    exact
      forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_sleeping_of_time_le
        (observedTrajectoryScore (score i))
        (conditionalTrajectoryRisk K (score i))
        (observedTrajectoryPredictableStrategyCatalog strategy)
        hnj x
  have hEpos : forall i j n x, 0 < E i j n x := by
    intro i j n x
    unfold E finiteTrajectoryCountableSleepingEBComponent
    exact Real.exp_pos _
  rcases exists_finiteModelCountableSleepingEProcessPACBayes_event
      hmodelPrior E hE hsleep hEpos hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior
  have hlog := hgood x hx n modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior
  rw [nested_logComponent_eq_scoreAverage
    K score strategy modelPosterior strategyPosterior x] at hlog
  rw [posteriorAverage_forwardPredictableTiltPACBayesScore] at hlog
  change
    trajectoryPredictableStrategyPosteriorMeanGap K score
          (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x -
        finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
          score strategy modelPosterior strategyPosterior x <
      (klDiv modelPosterior modelPrior +
          klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n)) +
        Real.log (1 / delta) at hlog
  linarith

/-! ## Ordinary encountered-prefix endpoint -/

/-- Fully observable boundary for ordinary encountered prefix risk. -/
def finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
    (modelPrior modelPosterior : Iota -> Real)
    (score : Iota -> TrajectoryScore Z)
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (delta : Real) (x : Nat -> Z) : Real :=
  finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
      score modelPosterior 0 n x +
    ((klDiv modelPosterior modelPrior +
          klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n)) +
        Real.log (1 / delta) +
        finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
          score strategy modelPosterior strategyPosterior x) /
      finiteTrajectoryCountableSleepingStrategyExposure
        strategy strategyPosterior x +
    2 * finiteTrajectoryCountableSleepingStrategyUniformDiscrepancy
      strategy strategyPosterior x

omit [DecidableEq Iota] [Nonempty Iota]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private theorem activeSleeping_totalWeight_eq_exposure
    (strategy : Nat -> TrajectoryPredictableTilt Z)
    (modelPosterior : Iota -> Real) (hmodelPosterior : IsPMF modelPosterior)
    {n : Nat} (strategyPosterior : Fin n -> Real)
    (x : Nat -> Z) :
    trajectoryPredictableStrategyPosteriorTotalWeight
        (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
        (modelStrategyProductPrior modelPosterior strategyPosterior) n x =
      finiteTrajectoryCountableSleepingStrategyExposure
        strategy strategyPosterior x := by
  have h := trajectorySleepingStrategyPosteriorTotalWeight_commonWake_factorized
    (strategy := fun j : Fin n =>
      countableSleepingTrajectoryStrategy strategy j.1)
    modelPosterior strategyPosterior hmodelPosterior (w := 0) (n := n)
    (Nat.zero_le n) x
  rw [finiteTrajectoryActiveSleepingStrategyCatalog_eq_commonWake]
  exact h

/-- One common event controls ordinary encountered prefix risk after selecting
both the model posterior and the active-prefix strategy posterior from the
observed path and reporting time. -/
theorem
    exists_finiteTrajectoryCountableSleepingStrategyPACBayes_ordinaryPrefixRisk_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    {score : Iota -> TrajectoryScore Z}
    (hscore : forall i n u y, score i n u y ∈ Set.Icc (0 : Real) 1)
    {strategy : Nat -> TrajectoryPredictableTilt Z}
    {L : Real} (hL1 : L < 1)
    (hstrategy : forall j n u,
      strategy j n u ∈ Set.Icc (0 : Real) L)
    {modelPrior : Iota -> Real}
    (hmodelPrior : IsFullSupportPMF modelPrior)
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta /\
        forall x, x ∈ goodEvent -> forall n : Nat, 0 < n ->
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin n -> Real,
            IsPMF strategyPosterior ->
          0 < finiteTrajectoryCountableSleepingStrategyExposure
              strategy strategyPosterior x ->
          finiteTrajectoryPosteriorAverageConditionalSuffixRisk
              K score modelPosterior 0 n x <
            finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary
              modelPrior modelPosterior score strategy strategyPosterior
              delta x := by
  rcases exists_finiteTrajectoryCountableSleepingStrategyPACBayes_raw_event
      K x0 hscore hL1 hstrategy hmodelPrior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx n hn modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior hexposure
  have hraw := hgood x hx n modelPosterior hmodelPosterior
    strategyPosterior hstrategyPosterior
  have htotal := activeSleeping_totalWeight_eq_exposure
    strategy modelPosterior hmodelPosterior strategyPosterior x
  have hgap :
      trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
          K score (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x <
        trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
            score (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
            (modelStrategyProductPrior modelPosterior strategyPosterior) n x +
          ((klDiv modelPosterior modelPrior +
                klDiv (liftPolynomialActivePosterior strategyPosterior)
                  (polynomialActiveTailPrior n)) +
              Real.log (1 / delta) +
              finiteTrajectoryCountableSleepingStrategyQuadraticPenalty
                score strategy modelPosterior strategyPosterior x) /
            finiteTrajectoryCountableSleepingStrategyExposure
              strategy strategyPosterior x := by
    have hdiv := (div_lt_div_iff_of_pos_right hexposure).2 hraw
    have hnormalized :=
      forwardPredictableTiltPosteriorNormalizedMean_sub_observation
        (modelStrategyProductPrior modelPosterior strategyPosterior)
        (modelStrategyProcess
          (fun i => observedTrajectoryScore (score i)))
        (modelStrategyProcess
          (fun i => conditionalTrajectoryRisk K (score i)))
        (modelStrategyPredictableTilt
          (observedFiniteTrajectoryActiveSleepingStrategyCatalog
            strategy n)) n x
    change
      trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
            K score
            (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
            (modelStrategyProductPrior modelPosterior strategyPosterior)
            n x -
          trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
            score
            (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
            (modelStrategyProductPrior modelPosterior strategyPosterior)
            n x =
        trajectoryPredictableStrategyPosteriorMeanGap K score
            (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
            (modelStrategyProductPrior modelPosterior strategyPosterior)
            n x /
          trajectoryPredictableStrategyPosteriorTotalWeight
            (finiteTrajectoryActiveSleepingStrategyCatalog strategy n)
            (modelStrategyProductPrior modelPosterior strategyPosterior)
            n x at hnormalized
    rw [htotal] at hnormalized
    linarith
  have hweighted :
      trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk
          K score
          (sleepingTrajectoryStrategyCatalog (fun _ : Fin n => 0)
            (fun j : Fin n =>
              countableSleepingTrajectoryStrategy strategy j.1))
          (modelStrategyProductPrior modelPosterior strategyPosterior) n x <
        trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk
            score
            (sleepingTrajectoryStrategyCatalog (fun _ : Fin n => 0)
              (fun j : Fin n =>
                countableSleepingTrajectoryStrategy strategy j.1))
            (modelStrategyProductPrior modelPosterior strategyPosterior) n x +
          ((klDiv modelPosterior modelPrior +
                klDiv strategyPosterior
                  (fun j : Fin n => polynomialEpochWeight j.1)) +
              Real.log (1 / delta) +
              trajectoryPredictableStrategyPosteriorQuadraticPenalty score
                (sleepingTrajectoryStrategyCatalog (fun _ : Fin n => 0)
                  (fun j : Fin n =>
                    countableSleepingTrajectoryStrategy strategy j.1))
                (modelStrategyProductPrior
                  modelPosterior strategyPosterior) n x) /
            finiteStrategyPosteriorSleepingExposure strategyPosterior
              (fun j : Fin n =>
                countableSleepingTrajectoryStrategy strategy j.1)
              0 n x := by
    rw [← finiteTrajectoryActiveSleepingStrategyCatalog_eq_commonWake]
    simpa [finiteTrajectoryActiveSleepingStrategyCatalog,
      finiteTrajectoryCountableSleepingStrategyQuadraticPenalty,
      finiteTrajectoryCountableSleepingStrategyExposure,
      klDiv_liftPolynomialActivePosterior_eq_active,
      sleepingTrajectoryStrategyCatalog] using hgap
  have hord := finiteTrajectorySleepingStrategyPosterior_ordinaryRisk_of_weighted
    K score hscore modelPrior modelPosterior hmodelPosterior
    (fun j : Fin n => polynomialEpochWeight j.1) strategyPosterior
    (fun j : Fin n => countableSleepingTrajectoryStrategy strategy j.1)
    delta (w := 0) (n := n) hn x hexposure hweighted
  simpa [finiteTrajectoryCountableSleepingStrategyOrdinaryPrefixBoundary,
    finiteTrajectorySleepingStrategyPosteriorOrdinarySuffixBoundary,
    finiteTrajectorySleepingStrategyPosteriorExcess,
    finiteTrajectoryCountableSleepingStrategyQuadraticPenalty,
    finiteTrajectoryCountableSleepingStrategyExposure,
    finiteTrajectoryCountableSleepingStrategyUniformDiscrepancy,
    finiteTrajectoryActiveSleepingStrategyCatalog_eq_commonWake,
    klDiv_liftPolynomialActivePosterior_eq_active,
    sleepingTrajectoryStrategyCatalog] using hord

end

end FormalSLT.StochasticDynamics
