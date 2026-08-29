/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingPosterior
import FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes

/-!
# Finite-model PAC-Bayes with a countable sleeping strategy posterior

This module combines two existing exact constructions.  For each model, the
countable sleeping betting master mixes a predeclared strategy catalog with
dyadic weights and evaluates its finite active prefix plus a closed-form
sleeping tail.  A finite model prior then mixes those model-specific masters.

The resulting single e-process gives one Ville event on which the reporting
time, finite model posterior, and posterior over all strategies active at that
time may be selected after observing the path.  For factorized reporting
posteriors, model and strategy selection pay the separate costs

`klDiv modelPosterior modelPrior`

and

`klDiv (liftSleepingActivePosterior strategyPosterior)
  (sleepingActiveDyadicPrior n)`.

The countable strategy family is fixed before observation, every catalog
member must be predictable, and every component wealth process must satisfy
the e-process premise.  This is not unrestricted post-data strategy invention
or a continuum coin-betting result.  The conclusion controls posterior-average
log wealth; a score-to-risk theorem is required before it can be described as
an ordinary-risk certificate.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open scoped BigOperators

namespace FormalSLT.PACBayes.FiniteModelCountableStrategyPACBayes

noncomputable section

variable {Iota Omega : Type*}
  [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

/-- The exact countable sleeping-strategy master attached to one model. -/
def modelCountableSleepingMasterProcess
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (i : Iota) : Nat -> Omega -> Real :=
  bettingWealthProcess (X i)
    (countableSleepingMasterBet
      (fun k omega => X i k omega - mean i) (strategy i))
    (mean i)

/-- The finite model-prior mixture of exact countable sleeping masters. -/
def finiteModelCountableSleepingMasterProcess
    (modelPrior : Iota -> Real)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real) :
    Nat -> Omega -> Real :=
  finiteWeightedProcess modelPrior
    (modelCountableSleepingMasterProcess X mean strategy)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
/-- Each model-specific exact sleeping master remains an e-process. -/
theorem modelCountableSleepingMasterProcess_eProcess
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (i : Iota) :
    EProcess mu F (modelCountableSleepingMasterProcess X mean strategy i) := by
  exact countableSleepingMasterBet_eProcess
    (X i) (mean i) (strategy i) (hX_adapted i)
      (hstrategy_adapted i) (hcomponent i)

omit [Nonempty Iota] in
/-- A normalized finite model mixture of the countable masters is one
e-process. -/
theorem finiteModelCountableSleepingMasterProcess_eProcess
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i))) :
    EProcess mu F
      (finiteModelCountableSleepingMasterProcess
        modelPrior X mean strategy) := by
  unfold finiteModelCountableSleepingMasterProcess
  exact finiteWeightedProcess_eProcess
    hmodelPrior.nonneg hmodelPrior.sum_one
      (modelCountableSleepingMasterProcess_eProcess
        X mean strategy hX_adapted hstrategy_adapted hcomponent)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
/-- The recursive master wealth equals the exact finite active-prefix plus
closed-form sleeping-tail mixture. -/
theorem modelCountableSleepingMasterProcess_eq_mixture
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (i : Iota) (n : Nat) (omega : Omega) :
    modelCountableSleepingMasterProcess X mean strategy i n omega =
      countableSleepingMixtureWealth
        (fun k xi => X i k xi - mean i) (strategy i) n omega := by
  have hwealth_nonneg : forall j k xi,
      0 <= algebraicBettingWealth
        (fun t eta => X i t eta - mean i)
        (sleepingStrategy (strategy i) j) k xi := by
    intro j k xi
    simpa only [algebraicBettingWealth_eq_bettingWealthProcess,
      Pi.zero_apply] using
      (hcomponent i j).nonneg k xi
  rw [show modelCountableSleepingMasterProcess X mean strategy i n omega =
      algebraicBettingWealth
        (fun k xi => X i k xi - mean i)
        (countableSleepingMasterBet
          (fun k xi => X i k xi - mean i) (strategy i)) n omega by
    simp only [modelCountableSleepingMasterProcess,
      algebraicBettingWealth_eq_bettingWealthProcess]]
  exact countableSleepingMasterWealth_eq_mixture
    (fun k xi => X i k xi - mean i) (strategy i)
      (fun k xi =>
        (countableSleepingMixtureWealth_pos hwealth_nonneg k xi).ne')
      n omega

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
/-- Every model-specific master is strictly positive.  The closed-form mass
of the still-sleeping tail supplies strict positivity even when all active
component wealths are zero. -/
theorem modelCountableSleepingMasterProcess_pos
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (i : Iota) (n : Nat) (omega : Omega) :
    0 < modelCountableSleepingMasterProcess X mean strategy i n omega := by
  have hwealth_nonneg : forall j k xi,
      0 <= algebraicBettingWealth
        (fun t eta => X i t eta - mean i)
        (sleepingStrategy (strategy i) j) k xi := by
    intro j k xi
    simpa only [algebraicBettingWealth_eq_bettingWealthProcess,
      Pi.zero_apply] using
      (hcomponent i j).nonneg k xi
  rw [modelCountableSleepingMasterProcess_eq_mixture
    X mean strategy hcomponent i n omega]
  exact countableSleepingMixtureWealth_pos hwealth_nonneg n omega

omit [DecidableEq Iota] in
/-- The finite model master is strictly positive under a full-support model
prior. -/
theorem finiteModelCountableSleepingMasterProcess_pos
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (n : Nat) (omega : Omega) :
    0 < finiteModelCountableSleepingMasterProcess
      modelPrior X mean strategy n omega := by
  unfold finiteModelCountableSleepingMasterProcess finiteWeightedProcess
  exact Finset.sum_pos
    (fun i _hi => mul_pos (hmodelPrior.pos i)
      (modelCountableSleepingMasterProcess_pos
        X mean strategy hcomponent i n omega))
    Finset.univ_nonempty

/-- Product prior on a finite model and the active-prefix compression of the
countable sleeping strategy catalog. -/
def finiteModelActiveStrategyPrior
    (modelPrior : Iota -> Real) (n : Nat) :
    Iota × Option (Fin (n + 1)) -> Real :=
  modelStrategyProductPrior modelPrior (sleepingActiveDyadicPrior n)

/-- Wealth of a model and one active-or-sleeping-tail compressed cell at a
fixed reporting time.  The `none` cell aggregates the unit-wealth sleeping
tail; it is not an additional selectable strategy. -/
def finiteModelActiveStrategyWealth
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega)
    (p : Iota × Option (Fin (n + 1))) : Real :=
  sleepingActiveWealth
    (fun k xi => X p.1 k xi - mean p.1) (strategy p.1) n omega p.2

omit [DecidableEq Iota] [Nonempty Iota] in
/-- The active model--strategy product prior has full support. -/
theorem finiteModelActiveStrategyPrior_isFullSupportPMF
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (n : Nat) :
    IsFullSupportPMF (finiteModelActiveStrategyPrior modelPrior n) := by
  exact modelStrategyProductPrior_isFullSupportPMF hmodelPrior
    (sleepingActiveDyadicPrior_isFullSupportPMF n)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
/-- Every active model--strategy cell has positive wealth under the usual
legal-betting factor premise. -/
theorem finiteModelActiveStrategyWealth_pos
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    (n : Nat) (omega : Omega)
    (p : Iota × Option (Fin (n + 1))) :
    0 < finiteModelActiveStrategyWealth X mean strategy n omega p := by
  rcases p with ⟨i, a⟩
  cases a with
  | none => simp [finiteModelActiveStrategyWealth, sleepingActiveWealth]
  | some j =>
      exact algebraicBettingWealth_pos
        (fun k xi => hfactor_pos i j.1 k xi) n omega

omit [DecidableEq Iota] [Nonempty Iota] in
/-- The product-prior average of the active-or-tail compressed wealth is
exactly the single finite-model countable-strategy master. -/
theorem finiteModelActiveStrategyPriorMoment_eq_master
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {modelPrior : Iota -> Real}
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (n : Nat) (omega : Omega) :
    (∑ p : Iota × Option (Fin (n + 1)),
        finiteModelActiveStrategyPrior modelPrior n p *
          finiteModelActiveStrategyWealth X mean strategy n omega p) =
      finiteModelCountableSleepingMasterProcess
        modelPrior X mean strategy n omega := by
  rw [Fintype.sum_prod_type]
  unfold finiteModelActiveStrategyPrior modelStrategyProductPrior
    finiteModelCountableSleepingMasterProcess finiteWeightedProcess
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show (∑ a : Option (Fin (n + 1)),
      modelPrior i * sleepingActiveDyadicPrior n a *
        finiteModelActiveStrategyWealth X mean strategy n omega (i, a)) =
      modelPrior i * (∑ a : Option (Fin (n + 1)),
        sleepingActiveDyadicPrior n a *
          finiteModelActiveStrategyWealth X mean strategy n omega (i, a)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring]
  congr 1
  rw [show (∑ a : Option (Fin (n + 1)),
      sleepingActiveDyadicPrior n a *
        finiteModelActiveStrategyWealth X mean strategy n omega (i, a)) =
      countableSleepingMixtureWealth
        (fun k xi => X i k xi - mean i) (strategy i) n omega by
    simpa only [finiteModelActiveStrategyWealth] using
      sleepingActivePriorMoment_eq_countableSleepingMixtureWealth
        (fun k xi => X i k xi - mean i) (strategy i) n omega]
  exact (modelCountableSleepingMasterProcess_eq_mixture
    X mean strategy hcomponent i n omega).symm

omit [DecidableEq Iota] in
/-- The stronger correlated-posterior oracle.  A reporting posterior may
couple models with active-or-tail compressed cells arbitrarily; it pays the
full KL to the product prior.  The `none` cell aggregates the unit-wealth
sleeping tail rather than naming one selectable strategy. -/
theorem finiteModelCountableSleepingJointPosterior_logWealth_le
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    (n : Nat)
    (jointPosterior : Iota × Option (Fin (n + 1)) -> Real)
    (hjointPosterior : IsPMF jointPosterior) (omega : Omega) :
    posteriorAverage jointPosterior (fun p =>
        Real.log (finiteModelActiveStrategyWealth
          X mean strategy n omega p)) <=
      klDiv jointPosterior (finiteModelActiveStrategyPrior modelPrior n) +
        Real.log (finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega) := by
  have hchange := posterior_change_of_measure hjointPosterior
    (finiteModelActiveStrategyPrior_isFullSupportPMF hmodelPrior n)
    (fun p => Real.log
      (finiteModelActiveStrategyWealth X mean strategy n omega p))
  have hmoment :
      (∑ p : Iota × Option (Fin (n + 1)),
          finiteModelActiveStrategyPrior modelPrior n p *
            Real.exp (Real.log (finiteModelActiveStrategyWealth
              X mean strategy n omega p))) =
        finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega := by
    rw [show (∑ p : Iota × Option (Fin (n + 1)),
        finiteModelActiveStrategyPrior modelPrior n p *
          Real.exp (Real.log (finiteModelActiveStrategyWealth
            X mean strategy n omega p))) =
      ∑ p : Iota × Option (Fin (n + 1)),
        finiteModelActiveStrategyPrior modelPrior n p *
          finiteModelActiveStrategyWealth X mean strategy n omega p by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Real.exp_log (finiteModelActiveStrategyWealth_pos
        X mean strategy hfactor_pos n omega p)]]
    exact finiteModelActiveStrategyPriorMoment_eq_master
      X mean strategy hcomponent n omega
  simpa [hmoment] using hchange

omit [DecidableEq Iota] in
/-- A factorized posterior over models and the active countable strategy
prefix pays separate model and strategy KL costs against the single master.
Both posteriors may be chosen from the observed path. -/
theorem finiteModelCountableSleepingStrategyPosterior_logWealth_le
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega}
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    (n : Nat) (modelPosterior : Iota -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategyPosterior : Fin (n + 1) -> Real)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (omega : Omega) :
    posteriorAverage modelPosterior (fun i =>
        posteriorAverage strategyPosterior (fun j =>
          Real.log (algebraicBettingWealth
            (fun k xi => X i k xi - mean i)
            (sleepingStrategy (strategy i) j.1) n omega))) <=
      (klDiv modelPosterior modelPrior +
          klDiv (liftSleepingActivePosterior strategyPosterior)
            (sleepingActiveDyadicPrior n)) +
        Real.log (finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega) := by
  have hinner : forall i,
      posteriorAverage strategyPosterior (fun j =>
          Real.log (algebraicBettingWealth
            (fun k xi => X i k xi - mean i)
            (sleepingStrategy (strategy i) j.1) n omega)) <=
        klDiv (liftSleepingActivePosterior strategyPosterior)
            (sleepingActiveDyadicPrior n) +
          Real.log (modelCountableSleepingMasterProcess
            X mean strategy i n omega) := by
    intro i
    have h := countableSleepingStrategyPosterior_logWealth_le
      (hfactor_pos i) n strategyPosterior hstrategyPosterior omega
    simpa only [modelCountableSleepingMasterProcess,
      algebraicBettingWealth_eq_bettingWealthProcess] using h
  have haverage :
      posteriorAverage modelPosterior (fun i =>
          posteriorAverage strategyPosterior (fun j =>
            Real.log (algebraicBettingWealth
              (fun k xi => X i k xi - mean i)
              (sleepingStrategy (strategy i) j.1) n omega))) <=
        posteriorAverage modelPosterior (fun i =>
          klDiv (liftSleepingActivePosterior strategyPosterior)
              (sleepingActiveDyadicPrior n) +
            Real.log (modelCountableSleepingMasterProcess
              X mean strategy i n omega)) := by
    unfold posteriorAverage
    exact Finset.sum_le_sum fun i _hi =>
      mul_le_mul_of_nonneg_left (hinner i) (hmodelPosterior.nonneg i)
  have houter := posterior_change_of_measure hmodelPosterior hmodelPrior
    (fun i => Real.log
      (modelCountableSleepingMasterProcess X mean strategy i n omega))
  have hmoment :
      (∑ i : Iota, modelPrior i *
          Real.exp (Real.log
            (modelCountableSleepingMasterProcess
              X mean strategy i n omega))) =
        finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega := by
    unfold finiteModelCountableSleepingMasterProcess finiteWeightedProcess
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.exp_log (modelCountableSleepingMasterProcess_pos
      X mean strategy hcomponent i n omega)]
  rw [hmoment] at houter
  have hsplit :
      posteriorAverage modelPosterior (fun i =>
          klDiv (liftSleepingActivePosterior strategyPosterior)
              (sleepingActiveDyadicPrior n) +
            Real.log (modelCountableSleepingMasterProcess
              X mean strategy i n omega)) =
        klDiv (liftSleepingActivePosterior strategyPosterior)
            (sleepingActiveDyadicPrior n) +
          posteriorAverage modelPosterior (fun i =>
            Real.log (modelCountableSleepingMasterProcess
              X mean strategy i n omega)) := by
    unfold posteriorAverage
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      hmodelPosterior.sum_one, one_mul]
  rw [hsplit] at haverage
  linarith

/-- The single crossing event of the finite-model, countable-strategy
master. -/
def finiteModelCountableSleepingStrategyGoodEvent
    (modelPrior : Iota -> Real)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (delta : Real) : Set Omega :=
  (atTopCrossingEvent
    (finiteModelCountableSleepingMasterProcess
      modelPrior X mean strategy) (1 / delta))ᶜ

/-- One Ville event controls all times, all finite model posteriors, and all
posteriors over the active prefix of the predeclared countable strategy
catalog. -/
theorem finiteModelCountableSleepingStrategyGoodEvent_spec
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    {delta : Real} (hdelta : 0 < delta) :
    mu.real (finiteModelCountableSleepingStrategyGoodEvent
        modelPrior X mean strategy delta)ᶜ <= delta ∧
      forall omega, omega ∈ finiteModelCountableSleepingStrategyGoodEvent
          modelPrior X mean strategy delta ->
        forall n : Nat,
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin (n + 1) -> Real,
            IsPMF strategyPosterior ->
          posteriorAverage modelPosterior (fun i =>
              posteriorAverage strategyPosterior (fun j =>
                Real.log (algebraicBettingWealth
                  (fun k xi => X i k xi - mean i)
                  (sleepingStrategy (strategy i) j.1) n omega))) <=
            (klDiv modelPosterior modelPrior +
                klDiv (liftSleepingActivePosterior strategyPosterior)
                  (sleepingActiveDyadicPrior n)) +
              Real.log (1 / delta) := by
  have hE := finiteModelCountableSleepingMasterProcess_eProcess
    hmodelPrior.toIsPMF X mean strategy hX_adapted
      hstrategy_adapted hcomponent
  have hthreshold : 0 < (1 : Real) / delta := one_div_pos.mpr hdelta
  have hville := ville_atTop_maximal_ineq
    hE.supermartingale hE.nonneg hthreshold
  rw [hE.integral_start_eq_one] at hville
  have hcrossing :
      mu.real (atTopCrossingEvent
        (finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy) (1 / delta)) <= delta := by
    calc
      mu.real (atTopCrossingEvent
          (finiteModelCountableSleepingMasterProcess
            modelPrior X mean strategy) (1 / delta)) =
          delta * ((1 / delta) *
            mu.real (atTopCrossingEvent
              (finiteModelCountableSleepingMasterProcess
                modelPrior X mean strategy) (1 / delta))) := by
              field_simp [hdelta.ne']
      _ <= delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  constructor
  · simpa [finiteModelCountableSleepingStrategyGoodEvent] using hcrossing
  · intro omega homega n modelPosterior hmodelPosterior
      strategyPosterior hstrategyPosterior
    have hnot_crossing :
        omega ∉ atTopCrossingEvent
          (finiteModelCountableSleepingMasterProcess
            modelPrior X mean strategy) (1 / delta) := by
      simpa [finiteModelCountableSleepingStrategyGoodEvent] using homega
    have hmaster_lt :
        finiteModelCountableSleepingMasterProcess
            modelPrior X mean strategy n omega < 1 / delta := by
      exact lt_of_not_ge fun hcross => hnot_crossing ⟨n, hcross⟩
    have hmaster_pos :=
      finiteModelCountableSleepingMasterProcess_pos
        hmodelPrior X mean strategy hcomponent n omega
    have hlog :
        Real.log (finiteModelCountableSleepingMasterProcess
            modelPrior X mean strategy n omega) <= Real.log (1 / delta) :=
      (Real.log_lt_log hmaster_pos hmaster_lt).le
    have horacle :=
      finiteModelCountableSleepingStrategyPosterior_logWealth_le
        hmodelPrior X mean strategy hcomponent hfactor_pos n
          modelPosterior hmodelPosterior strategyPosterior
            hstrategyPosterior omega
    exact horacle.trans (add_le_add (le_refl _) hlog)

/-- The same common event controls arbitrary correlated post-data posteriors
on the finite model crossed with the active-or-tail countable-strategy
compression.  The `none` cell represents the aggregate unit-wealth sleeping
tail rather than one selectable strategy.  The price is the full joint KL to
the independent product prior. -/
theorem finiteModelCountableSleepingStrategyJointGoodEvent_spec
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    {delta : Real} (hdelta : 0 < delta) :
    mu.real (finiteModelCountableSleepingStrategyGoodEvent
        modelPrior X mean strategy delta)ᶜ <= delta ∧
      forall omega, omega ∈ finiteModelCountableSleepingStrategyGoodEvent
          modelPrior X mean strategy delta ->
        forall n : Nat,
          forall jointPosterior :
              Iota × Option (Fin (n + 1)) -> Real,
            IsPMF jointPosterior ->
          posteriorAverage jointPosterior (fun p =>
              Real.log (finiteModelActiveStrategyWealth
                X mean strategy n omega p)) <=
            klDiv jointPosterior
                (finiteModelActiveStrategyPrior modelPrior n) +
              Real.log (1 / delta) := by
  have hfactorized :=
    finiteModelCountableSleepingStrategyGoodEvent_spec
      hmodelPrior X mean strategy hX_adapted hstrategy_adapted
        hcomponent hfactor_pos hdelta
  refine ⟨hfactorized.1, ?_⟩
  intro omega homega n jointPosterior hjointPosterior
  have hnot_crossing :
      omega ∉ atTopCrossingEvent
        (finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy) (1 / delta) := by
    simpa [finiteModelCountableSleepingStrategyGoodEvent] using homega
  have hmaster_lt :
      finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega < 1 / delta := by
    exact lt_of_not_ge fun hcross => hnot_crossing ⟨n, hcross⟩
  have hmaster_pos := finiteModelCountableSleepingMasterProcess_pos
    hmodelPrior X mean strategy hcomponent n omega
  have hlog :
      Real.log (finiteModelCountableSleepingMasterProcess
          modelPrior X mean strategy n omega) <= Real.log (1 / delta) :=
    (Real.log_lt_log hmaster_pos hmaster_lt).le
  have horacle := finiteModelCountableSleepingJointPosterior_logWealth_le
    hmodelPrior X mean strategy hcomponent hfactor_pos n
      jointPosterior hjointPosterior omega
  exact horacle.trans (add_le_add (le_refl _) hlog)

/-- Existential packaging of the correlated joint-posterior common event. -/
theorem exists_finiteModelCountableSleepingJointPACBayes_event
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        forall omega, omega ∈ goodEvent -> forall n : Nat,
          forall jointPosterior :
              Iota × Option (Fin (n + 1)) -> Real,
            IsPMF jointPosterior ->
          posteriorAverage jointPosterior (fun p =>
              Real.log (finiteModelActiveStrategyWealth
                X mean strategy n omega p)) <=
            klDiv jointPosterior
                (finiteModelActiveStrategyPrior modelPrior n) +
              Real.log (1 / delta) := by
  refine ⟨finiteModelCountableSleepingStrategyGoodEvent
    modelPrior X mean strategy delta, ?_⟩
  exact finiteModelCountableSleepingStrategyJointGoodEvent_spec
    hmodelPrior X mean strategy hX_adapted hstrategy_adapted
      hcomponent hfactor_pos hdelta

/-- Existential packaging of the common event, preserving the quantifier
order over time and both reporting posteriors. -/
theorem exists_finiteModelCountableSleepingStrategyPACBayes_event
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (X : Iota -> Nat -> Omega -> Real) (mean : Iota -> Real)
    (strategy : Iota -> Nat -> Nat -> Omega -> Real)
    (hX_adapted : forall i, IncrementAdapted F (X i))
    (hstrategy_adapted : forall i j, StronglyAdapted F (strategy i j))
    (hcomponent : forall i j,
      EProcess mu F
        (bettingWealthProcess (X i)
          (sleepingStrategy (strategy i) j) (mean i)))
    (hfactor_pos : forall i j k xi,
      0 < 1 + sleepingStrategy (strategy i) j k xi *
        (X i k xi - mean i))
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        forall omega, omega ∈ goodEvent -> forall n : Nat,
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin (n + 1) -> Real,
            IsPMF strategyPosterior ->
          posteriorAverage modelPosterior (fun i =>
              posteriorAverage strategyPosterior (fun j =>
                Real.log (algebraicBettingWealth
                  (fun k xi => X i k xi - mean i)
                  (sleepingStrategy (strategy i) j.1) n omega))) <=
            (klDiv modelPosterior modelPrior +
                klDiv (liftSleepingActivePosterior strategyPosterior)
                  (sleepingActiveDyadicPrior n)) +
              Real.log (1 / delta) := by
  refine ⟨finiteModelCountableSleepingStrategyGoodEvent
    modelPrior X mean strategy delta, ?_⟩
  exact finiteModelCountableSleepingStrategyGoodEvent_spec
    hmodelPrior X mean strategy hX_adapted hstrategy_adapted
      hcomponent hfactor_pos hdelta

end

end FormalSLT.PACBayes.FiniteModelCountableStrategyPACBayes
