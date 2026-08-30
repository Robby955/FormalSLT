/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingEProcessMixture
import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingPosterior
import FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes

/-!
# Finite-model PAC-Bayes for countable sleeping e-process strategies

This module gives the generic polynomial sleeping e-process master a finite
model layer and a post-data posterior over the strategy prefix active at the
reporting time.  One Ville event is simultaneous over time, the finite model
posterior, and the active-prefix strategy posterior.  A factorized reporting
posterior pays separate model and strategy KL costs.

The countable strategy catalog and every component e-process are fixed before
observation.  This is confidence allocation over a predeclared catalog, not a
coin-betting theorem or unrestricted post-data strategy construction.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes

noncomputable section

variable {Iota Omega : Type*}
  [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

/-! ## Exact active-prefix compression -/

/-- Polynomial prior on the strategies active before time `n`, plus one atom
carrying the exact mass of the still-sleeping tail. -/
def polynomialActiveTailPrior (n : Nat) : Option (Fin n) -> Real
  | none => polynomialSleepingTail n
  | some j => polynomialEpochWeight j.1

/-- Lift a posterior on the active prefix to the compressed active-or-tail
space.  The still-sleeping tail receives zero reporting mass. -/
def liftPolynomialActivePosterior {n : Nat}
    (q : Fin n -> Real) : Option (Fin n) -> Real
  | none => 0
  | some j => q j

/-- Value of one active component, or unit value for the compressed sleeping
tail. -/
def activeSleepingEProcessValue
    (E : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Option (Fin n) -> Real
  | none => 1
  | some j => E j.1 n omega

/-- The compressed polynomial prior is an exact full-support PMF. -/
theorem polynomialActiveTailPrior_isFullSupportPMF (n : Nat) :
    IsFullSupportPMF (polynomialActiveTailPrior n) := by
  refine
    { nonneg := ?_
      sum_one := ?_
      pos := ?_ }
  · intro a
    cases a with
    | none => exact (polynomialSleepingTail_pos n).le
    | some j => exact (polynomialEpochWeight_pos j.1).le
  · rw [Fintype.sum_option]
    simp only [polynomialActiveTailPrior]
    rw [Fin.sum_univ_eq_sum_range
      (fun j => polynomialEpochWeight j) n,
      polynomialEpochWeight_sum_range]
    unfold polynomialSleepingTail
    ring
  · intro a
    cases a with
    | none => exact polynomialSleepingTail_pos n
    | some j => exact polynomialEpochWeight_pos j.1

/-- Zero mass on the sleeping tail preserves the PMF property. -/
theorem liftPolynomialActivePosterior_isPMF {n : Nat}
    {q : Fin n -> Real} (hq : IsPMF q) :
    IsPMF (liftPolynomialActivePosterior q) := by
  refine
    { nonneg := ?_
      sum_one := ?_ }
  · intro a
    cases a with
    | none => simp [liftPolynomialActivePosterior]
    | some j => exact hq.nonneg j
  · rw [Fintype.sum_option]
    simpa [liftPolynomialActivePosterior] using hq.sum_one

/-- Lifting does not change an average over active atoms. -/
theorem posteriorAverage_liftPolynomialActivePosterior {n : Nat}
    (q : Fin n -> Real) (f : Option (Fin n) -> Real) :
    posteriorAverage (liftPolynomialActivePosterior q) f =
      posteriorAverage q (fun j => f (some j)) := by
  simp [posteriorAverage, liftPolynomialActivePosterior,
    Fintype.sum_option]

/-- The lifted KL is the explicit polynomial active-prefix selection cost. -/
theorem klDiv_liftPolynomialActivePosterior (n : Nat)
    (q : Fin n -> Real) :
    klDiv (liftPolynomialActivePosterior q)
        (polynomialActiveTailPrior n) =
      ∑ j : Fin n,
        q j * Real.log (q j / polynomialEpochWeight j.1) := by
  simp [klDiv, liftPolynomialActivePosterior,
    polynomialActiveTailPrior, Fintype.sum_option]

/-- The compressed-tail KL is the same finite KL obtained by restricting the
polynomial weights to the active prefix.  The restricted weights need not sum
to one; the missing mass is exactly the zero-posterior tail atom. -/
theorem klDiv_liftPolynomialActivePosterior_eq_active
    (n : Nat) (q : Fin n -> Real) :
    klDiv (liftPolynomialActivePosterior q)
        (polynomialActiveTailPrior n) =
      klDiv q (fun j : Fin n => polynomialEpochWeight j.1) := by
  rw [klDiv_liftPolynomialActivePosterior]
  rfl

/-- The compressed prior moment is exactly the finite-prefix representation
of the countable sleeping process mixture. -/
theorem polynomialActiveTailPriorMoment_eq_countableSleepingProcessMixture
    (E : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    (∑ a : Option (Fin n),
        polynomialActiveTailPrior n a *
          activeSleepingEProcessValue E n omega a) =
      countableSleepingProcessMixture E n omega := by
  rw [Fintype.sum_option]
  simp only [polynomialActiveTailPrior, activeSleepingEProcessValue,
    mul_one]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => polynomialEpochWeight j * E j n omega) n]
  rfl

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
/-- A posterior over the active strategy prefix pays its KL to the exact
polynomial active-or-tail prior. -/
theorem countableSleepingEProcessStrategyPosterior_logValue_le
    (E : Nat -> Nat -> Omega -> Real)
    (hEpos : forall j k omega, 0 < E j k omega)
    (n : Nat) (q : Fin n -> Real) (hq : IsPMF q)
    (omega : Omega) :
    posteriorAverage q (fun j => Real.log (E j.1 n omega)) <=
      klDiv (liftPolynomialActivePosterior q)
          (polynomialActiveTailPrior n) +
        Real.log (countableSleepingProcessMixture E n omega) := by
  let f : Option (Fin n) -> Real := fun a =>
    Real.log (activeSleepingEProcessValue E n omega a)
  have hvalue_pos (a : Option (Fin n)) :
      0 < activeSleepingEProcessValue E n omega a := by
    cases a with
    | none => simp [activeSleepingEProcessValue]
    | some j => exact hEpos j.1 n omega
  have hchange := posterior_change_of_measure
    (liftPolynomialActivePosterior_isPMF hq)
    (polynomialActiveTailPrior_isFullSupportPMF n) f
  have hmoment :
      (∑ a : Option (Fin n),
          polynomialActiveTailPrior n a * Real.exp (f a)) =
        countableSleepingProcessMixture E n omega := by
    rw [show (∑ a : Option (Fin n),
        polynomialActiveTailPrior n a * Real.exp (f a)) =
      ∑ a : Option (Fin n),
        polynomialActiveTailPrior n a *
          activeSleepingEProcessValue E n omega a by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [show Real.exp (f a) =
          activeSleepingEProcessValue E n omega a by
        unfold f
        exact Real.exp_log (hvalue_pos a)]]
    exact polynomialActiveTailPriorMoment_eq_countableSleepingProcessMixture
      E n omega
  rw [posteriorAverage_liftPolynomialActivePosterior, hmoment] at hchange
  exact hchange

/-! ## Finite model mixture and one common event -/

/-- The polynomial sleeping master attached to one finite model. -/
def modelCountableSleepingEProcessMaster
    (E : Iota -> Nat -> Nat -> Omega -> Real) (i : Iota) :
    Nat -> Omega -> Real :=
  countableSleepingProcessMixture (E i)

/-- Finite model-prior mixture of countable sleeping e-process masters. -/
def finiteModelCountableSleepingEProcessMaster
    (modelPrior : Iota -> Real)
    (E : Iota -> Nat -> Nat -> Omega -> Real) : Nat -> Omega -> Real :=
  finiteWeightedProcess modelPrior (modelCountableSleepingEProcessMaster E)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
theorem modelCountableSleepingEProcessMaster_eProcess
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hE : forall i j, EProcess mu F (E i j))
    (hsleep : forall i j n omega, n <= j -> E i j n omega = 1)
    (i : Iota) :
    EProcess mu F (modelCountableSleepingEProcessMaster E i) := by
  exact countableSleepingProcessMixture_eProcess (hE i) (hsleep i)

omit [Nonempty Iota] in
theorem finiteModelCountableSleepingEProcessMaster_eProcess
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsPMF modelPrior)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hE : forall i j, EProcess mu F (E i j))
    (hsleep : forall i j n omega, n <= j -> E i j n omega = 1) :
    EProcess mu F
      (finiteModelCountableSleepingEProcessMaster modelPrior E) := by
  unfold finiteModelCountableSleepingEProcessMaster
  exact finiteWeightedProcess_eProcess
    hmodelPrior.nonneg hmodelPrior.sum_one
      (modelCountableSleepingEProcessMaster_eProcess E hE hsleep)

omit [Fintype Iota] [DecidableEq Iota] [Nonempty Iota] in
theorem modelCountableSleepingEProcessMaster_pos
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hEnonneg : forall i j n omega, 0 <= E i j n omega)
    (i : Iota) (n : Nat) (omega : Omega) :
    0 < modelCountableSleepingEProcessMaster E i n omega := by
  exact countableSleepingProcessMixture_pos (hEnonneg i) n omega

omit [DecidableEq Iota] in
theorem finiteModelCountableSleepingEProcessMaster_pos
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hEnonneg : forall i j n omega, 0 <= E i j n omega)
    (n : Nat) (omega : Omega) :
    0 < finiteModelCountableSleepingEProcessMaster
      modelPrior E n omega := by
  unfold finiteModelCountableSleepingEProcessMaster finiteWeightedProcess
  exact Finset.sum_pos
    (fun i _hi => mul_pos (hmodelPrior.pos i)
      (modelCountableSleepingEProcessMaster_pos E hEnonneg i n omega))
    Finset.univ_nonempty

omit [DecidableEq Iota] in
/-- Separate-KL oracle for a factorized finite model posterior and active
countable-strategy posterior. -/
theorem finiteModelCountableSleepingEProcessPosterior_logValue_le
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hEpos : forall i j n omega, 0 < E i j n omega)
    (n : Nat) (modelPosterior : Iota -> Real)
    (hmodelPosterior : IsPMF modelPosterior)
    (strategyPosterior : Fin n -> Real)
    (hstrategyPosterior : IsPMF strategyPosterior)
    (omega : Omega) :
    posteriorAverage modelPosterior (fun i =>
        posteriorAverage strategyPosterior (fun j =>
          Real.log (E i j.1 n omega))) <=
      (klDiv modelPosterior modelPrior +
          klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n)) +
        Real.log (finiteModelCountableSleepingEProcessMaster
          modelPrior E n omega) := by
  have hinner : forall i,
      posteriorAverage strategyPosterior (fun j =>
          Real.log (E i j.1 n omega)) <=
        klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n) +
          Real.log (modelCountableSleepingEProcessMaster E i n omega) := by
    intro i
    exact countableSleepingEProcessStrategyPosterior_logValue_le
      (E i) (hEpos i) n strategyPosterior hstrategyPosterior omega
  have haverage :
      posteriorAverage modelPosterior (fun i =>
          posteriorAverage strategyPosterior (fun j =>
            Real.log (E i j.1 n omega))) <=
        posteriorAverage modelPosterior (fun i =>
          klDiv (liftPolynomialActivePosterior strategyPosterior)
              (polynomialActiveTailPrior n) +
            Real.log (modelCountableSleepingEProcessMaster E i n omega)) := by
    unfold posteriorAverage
    exact Finset.sum_le_sum fun i _hi =>
      mul_le_mul_of_nonneg_left (hinner i) (hmodelPosterior.nonneg i)
  have houter := posterior_change_of_measure hmodelPosterior hmodelPrior
    (fun i => Real.log (modelCountableSleepingEProcessMaster E i n omega))
  have hmoment :
      (∑ i : Iota, modelPrior i *
          Real.exp (Real.log
            (modelCountableSleepingEProcessMaster E i n omega))) =
        finiteModelCountableSleepingEProcessMaster
          modelPrior E n omega := by
    unfold finiteModelCountableSleepingEProcessMaster finiteWeightedProcess
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.exp_log (modelCountableSleepingEProcessMaster_pos E
      (fun i j k xi => (hEpos i j k xi).le) i n omega)]
  rw [hmoment] at houter
  have hsplit :
      posteriorAverage modelPosterior (fun i =>
          klDiv (liftPolynomialActivePosterior strategyPosterior)
              (polynomialActiveTailPrior n) +
            Real.log (modelCountableSleepingEProcessMaster E i n omega)) =
        klDiv (liftPolynomialActivePosterior strategyPosterior)
            (polynomialActiveTailPrior n) +
          posteriorAverage modelPosterior (fun i =>
            Real.log (modelCountableSleepingEProcessMaster E i n omega)) := by
    unfold posteriorAverage
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      hmodelPosterior.sum_one, one_mul]
  rw [hsplit] at haverage
  linarith

/-- Complement of the one Ville crossing event for the finite-model master. -/
def finiteModelCountableSleepingEProcessGoodEvent
    (modelPrior : Iota -> Real)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (delta : Real) : Set Omega :=
  (atTopCrossingEvent
    (finiteModelCountableSleepingEProcessMaster modelPrior E)
    (1 / delta))ᶜ

/-- One event controls every time, finite model posterior, and posterior over
the active prefix of the predeclared countable strategy catalog. -/
theorem finiteModelCountableSleepingEProcessGoodEvent_spec
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hE : forall i j, EProcess mu F (E i j))
    (hsleep : forall i j n omega, n <= j -> E i j n omega = 1)
    (hEpos : forall i j n omega, 0 < E i j n omega)
    {delta : Real} (hdelta : 0 < delta) :
    mu.real (finiteModelCountableSleepingEProcessGoodEvent
        modelPrior E delta)ᶜ <= delta /\
      forall omega, omega ∈ finiteModelCountableSleepingEProcessGoodEvent
          modelPrior E delta ->
        forall n : Nat,
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin n -> Real,
            IsPMF strategyPosterior ->
          posteriorAverage modelPosterior (fun i =>
              posteriorAverage strategyPosterior (fun j =>
                Real.log (E i j.1 n omega))) <
            (klDiv modelPosterior modelPrior +
                klDiv (liftPolynomialActivePosterior strategyPosterior)
                  (polynomialActiveTailPrior n)) +
              Real.log (1 / delta) := by
  have hmasterE := finiteModelCountableSleepingEProcessMaster_eProcess
    hmodelPrior.toIsPMF E hE hsleep
  have hthreshold : 0 < (1 : Real) / delta := one_div_pos.mpr hdelta
  have hville := ville_atTop_maximal_ineq
    hmasterE.supermartingale hmasterE.nonneg hthreshold
  rw [hmasterE.integral_start_eq_one] at hville
  have hcrossing :
      mu.real (atTopCrossingEvent
        (finiteModelCountableSleepingEProcessMaster modelPrior E)
        (1 / delta)) <= delta := by
    calc
      mu.real (atTopCrossingEvent
          (finiteModelCountableSleepingEProcessMaster modelPrior E)
          (1 / delta)) =
          delta * ((1 / delta) *
            mu.real (atTopCrossingEvent
              (finiteModelCountableSleepingEProcessMaster modelPrior E)
              (1 / delta))) := by
              field_simp [hdelta.ne']
      _ <= delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  constructor
  · simpa [finiteModelCountableSleepingEProcessGoodEvent] using hcrossing
  · intro omega homega n modelPosterior hmodelPosterior
      strategyPosterior hstrategyPosterior
    have hnot_crossing :
        omega ∉ atTopCrossingEvent
          (finiteModelCountableSleepingEProcessMaster modelPrior E)
          (1 / delta) := by
      simpa [finiteModelCountableSleepingEProcessGoodEvent] using homega
    have hmaster_lt :
        finiteModelCountableSleepingEProcessMaster
            modelPrior E n omega < 1 / delta := by
      exact lt_of_not_ge fun hcross => hnot_crossing ⟨n, hcross⟩
    have hmaster_pos := finiteModelCountableSleepingEProcessMaster_pos
      hmodelPrior E (fun i j k xi => (hEpos i j k xi).le) n omega
    have hlog :
        Real.log (finiteModelCountableSleepingEProcessMaster
            modelPrior E n omega) < Real.log (1 / delta) :=
      Real.log_lt_log hmaster_pos hmaster_lt
    have horacle :=
      finiteModelCountableSleepingEProcessPosterior_logValue_le
        hmodelPrior E hEpos n modelPosterior hmodelPosterior
          strategyPosterior hstrategyPosterior omega
    exact horacle.trans_lt (add_lt_add_right hlog _)

/-- Existential packaging with the reporting time and both posteriors inside
the common event. -/
theorem exists_finiteModelCountableSleepingEProcessPACBayes_event
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    {modelPrior : Iota -> Real} (hmodelPrior : IsFullSupportPMF modelPrior)
    (E : Iota -> Nat -> Nat -> Omega -> Real)
    (hE : forall i j, EProcess mu F (E i j))
    (hsleep : forall i j n omega, n <= j -> E i j n omega = 1)
    (hEpos : forall i j n omega, 0 < E i j n omega)
    {delta : Real} (hdelta : 0 < delta) :
    exists goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta /\
        forall omega, omega ∈ goodEvent -> forall n : Nat,
          forall modelPosterior : Iota -> Real,
            IsPMF modelPosterior ->
          forall strategyPosterior : Fin n -> Real,
            IsPMF strategyPosterior ->
          posteriorAverage modelPosterior (fun i =>
              posteriorAverage strategyPosterior (fun j =>
                Real.log (E i j.1 n omega))) <
            (klDiv modelPosterior modelPrior +
                klDiv (liftPolynomialActivePosterior strategyPosterior)
                  (polynomialActiveTailPrior n)) +
              Real.log (1 / delta) := by
  refine ⟨finiteModelCountableSleepingEProcessGoodEvent
    modelPrior E delta, ?_⟩
  exact finiteModelCountableSleepingEProcessGoodEvent_spec
    hmodelPrior E hE hsleep hEpos hdelta

end

end FormalSLT.PACBayes.FiniteModelCountableSleepingEProcessPACBayes
