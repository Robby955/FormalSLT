/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingMixture
import FormalSLT.PACBayesKL

/-!
# Posterior interpretation of the countable sleeping betting master

At time `n`, the countable sleeping master has only `n + 1` strategies that
can affect its current bet. This module packages those strategies as
`some j : Option (Fin (n + 1))` and packages every later, still-sleeping
strategy as one `none` atom. The latter has its exact dyadic tail mass and
unit wealth.

This compression gives a finite full-support prior whose wealth moment is
exactly the existing countable master. Normalizing prior mass by current
wealth gives an operational posterior, and the master's current bet is the
posterior average of the active strategy bets. A finite KL
change-of-measure inequality then charges explicitly for selecting an active
strategy posterior after observing the path.

The result is a posterior interpretation of the existing countable catalog.
It is not a continuum strategy mixture or a parameter-free coin-betting
theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

open FormalSLT.PACBayesKL

section Compression

variable {Omega : Type*}

/-- The exact dyadic prior on the active prefix plus one compressed sleeping
tail atom. -/
noncomputable def sleepingActiveDyadicPrior
    (n : Nat) : Option (Fin (n + 1)) -> Real
  | none => dyadicSleepingTail (n + 1)
  | some j => dyadicExpertWeight j.1

/-- Lift a posterior on currently active strategies to the compressed space.
The sleeping tail receives no posterior mass. -/
def liftSleepingActivePosterior {n : Nat}
    (rho : Fin (n + 1) -> Real) : Option (Fin (n + 1)) -> Real
  | none => 0
  | some j => rho j

/-- Wealth attached to an atom of the compressed active-strategy space. -/
def sleepingActiveWealth
    (residual : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Option (Fin (n + 1)) -> Real
  | none => 1
  | some j =>
      algebraicBettingWealth residual
        (sleepingStrategy strategy j.1) n omega

/-- Current bet attached to an atom of the compressed active-strategy space.
The compressed sleeping tail cannot bet at time `n`. -/
def sleepingActiveBet
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Option (Fin (n + 1)) -> Real
  | none => 0
  | some j => strategy j.1 n omega

/-- Prior-weighted current wealth, normalized by the exact countable master
wealth. -/
noncomputable def countableSleepingMasterPosterior
    (residual : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Option (Fin (n + 1)) -> Real :=
  fun a =>
    sleepingActiveDyadicPrior n a *
        sleepingActiveWealth residual strategy n omega a /
      countableSleepingMixtureWealth residual strategy n omega

/-- The dyadic active prefix and the exact sleeping tail have total mass one. -/
theorem sum_range_dyadicExpertWeight_add_tail (n : Nat) :
    (∑ j ∈ Finset.range n, dyadicExpertWeight (R := Real) j) +
        dyadicSleepingTail (R := Real) n = 1 := by
  induction n with
  | zero => simp [dyadicSleepingTail]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range n, dyadicExpertWeight (R := Real) j) +
              dyadicExpertWeight (R := Real) n +
              dyadicSleepingTail (R := Real) (n + 1) =
            (∑ j ∈ Finset.range n, dyadicExpertWeight (R := Real) j) +
              (dyadicSleepingTail (R := Real) (n + 1) +
                dyadicExpertWeight (R := Real) n) := by ring
        _ = (∑ j ∈ Finset.range n, dyadicExpertWeight (R := Real) j) +
              dyadicSleepingTail (R := Real) n := by
              rw [dyadicSleepingTail_succ_add_weight]
        _ = 1 := ih

/-- The compressed dyadic prior is a full-support probability mass function. -/
theorem sleepingActiveDyadicPrior_isFullSupportPMF (n : Nat) :
    IsFullSupportPMF (sleepingActiveDyadicPrior n) := by
  refine
    { nonneg := ?_
      sum_one := ?_
      pos := ?_ }
  · intro a
    cases a with
    | none => exact (dyadicSleepingTail_pos (R := Real) (n + 1)).le
    | some j => exact (dyadicExpertWeight_pos (R := Real) j.1).le
  · rw [Fintype.sum_option]
    simp only [sleepingActiveDyadicPrior]
    rw [Fin.sum_univ_eq_sum_range
      (fun j => dyadicExpertWeight (R := Real) j) (n + 1)]
    simpa [add_comm] using sum_range_dyadicExpertWeight_add_tail (n + 1)
  · intro a
    cases a with
    | none => exact dyadicSleepingTail_pos (R := Real) (n + 1)
    | some j => exact dyadicExpertWeight_pos (R := Real) j.1

/-- Lifting an active-strategy posterior and assigning zero mass to the
sleeping tail preserves the PMF property. -/
theorem liftSleepingActivePosterior_isPMF {n : Nat}
    {rho : Fin (n + 1) -> Real} (hrho : IsPMF rho) :
    IsPMF (liftSleepingActivePosterior rho) := by
  refine
    { nonneg := ?_
      sum_one := ?_ }
  · intro a
    cases a with
    | none => simp [liftSleepingActivePosterior]
    | some j => exact hrho.nonneg j
  · rw [Fintype.sum_option]
    simpa [liftSleepingActivePosterior] using hrho.sum_one

/-- Lifting the posterior does not change posterior averages over active
atoms. -/
theorem posteriorAverage_liftSleepingActivePosterior {n : Nat}
    (rho : Fin (n + 1) -> Real)
    (score : Option (Fin (n + 1)) -> Real) :
    posteriorAverage (liftSleepingActivePosterior rho) score =
      posteriorAverage rho (fun j => score (some j)) := by
  simp [posteriorAverage, liftSleepingActivePosterior, Fintype.sum_option]

/-- The KL cost of a lifted posterior is exactly the active-strategy KL sum;
the zero-mass tail contributes nothing. -/
theorem klDiv_liftSleepingActivePosterior (n : Nat)
    (rho : Fin (n + 1) -> Real) :
    klDiv (liftSleepingActivePosterior rho) (sleepingActiveDyadicPrior n) =
      ∑ j : Fin (n + 1),
        rho j * Real.log (rho j / dyadicExpertWeight j.1) := by
  simp [klDiv, liftSleepingActivePosterior, sleepingActiveDyadicPrior,
    Fintype.sum_option]

/-- The prior moment on the compressed space is the existing exact
countable sleeping-mixture wealth. -/
theorem sleepingActivePriorMoment_eq_countableSleepingMixtureWealth
    (residual : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    (∑ a : Option (Fin (n + 1)),
        sleepingActiveDyadicPrior n a *
          sleepingActiveWealth residual strategy n omega a) =
      countableSleepingMixtureWealth residual strategy n omega := by
  rw [Fintype.sum_option]
  simp only [sleepingActiveDyadicPrior, sleepingActiveWealth]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => dyadicExpertWeight (R := Real) j *
      algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega) (n + 1),
    Finset.sum_range_succ]
  have hnew :
      algebraicBettingWealth residual (sleepingStrategy strategy n) n omega = 1 :=
    algebraicBettingWealth_sleeping_of_time_le
      residual strategy le_rfl omega
  rw [hnew]
  unfold countableSleepingMixtureWealth
  rw [show dyadicExpertWeight (R := Real) n * 1 =
      dyadicExpertWeight (R := Real) n by ring]
  rw [← dyadicSleepingTail_succ_add_weight (R := Real) n]
  ring

/-- The current prior-times-wealth normalization is an honest PMF whenever
component wealth is nonnegative. -/
theorem countableSleepingMasterPosterior_isPMF
    {residual : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hwealth_nonneg : forall j k xi,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) k xi)
    (n : Nat) (omega : Omega) :
    IsPMF (countableSleepingMasterPosterior
      residual strategy n omega) := by
  have hmix := countableSleepingMixtureWealth_pos
    hwealth_nonneg n omega
  refine
    { nonneg := ?_
      sum_one := ?_ }
  · intro a
    unfold countableSleepingMasterPosterior
    apply div_nonneg
    · cases a with
      | none =>
          exact mul_nonneg
            (dyadicSleepingTail_pos (R := Real) (n + 1)).le zero_le_one
      | some j =>
          exact mul_nonneg
            (dyadicExpertWeight_pos (R := Real) j.1).le
            (hwealth_nonneg j.1 n omega)
    · exact hmix.le
  · unfold countableSleepingMasterPosterior
    rw [show (∑ a : Option (Fin (n + 1)),
          sleepingActiveDyadicPrior n a *
              sleepingActiveWealth residual strategy n omega a /
            countableSleepingMixtureWealth residual strategy n omega) =
        (∑ a : Option (Fin (n + 1)),
          sleepingActiveDyadicPrior n a *
            sleepingActiveWealth residual strategy n omega a) /
          countableSleepingMixtureWealth residual strategy n omega by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]]
    rw [sleepingActivePriorMoment_eq_countableSleepingMixtureWealth]
    exact div_self hmix.ne'

/-- The executable master's current bet is the posterior average under its
prior-times-wealth posterior. -/
theorem countableSleepingMasterBet_eq_posteriorAverage
    (residual : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    countableSleepingMasterBet residual strategy n omega =
      posteriorAverage
        (countableSleepingMasterPosterior residual strategy n omega)
        (sleepingActiveBet strategy n omega) := by
  unfold posteriorAverage countableSleepingMasterPosterior
  rw [Fintype.sum_option]
  simp only [sleepingActiveDyadicPrior, sleepingActiveWealth,
    sleepingActiveBet, mul_zero, zero_add]
  rw [Fin.sum_univ_eq_sum_range
    (fun j =>
      dyadicExpertWeight (R := Real) j *
          algebraicBettingWealth residual
            (sleepingStrategy strategy j) n omega /
        countableSleepingMixtureWealth residual strategy n omega *
          strategy j n omega) (n + 1)]
  unfold countableSleepingMasterBet countableSleepingBetNumerator
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

end Compression

section StrategySelection

variable {Omega : Type*}

/-- Selecting a posterior over the strategies active at time `n` costs its
explicit KL divergence to the compressed dyadic prior. The score is the log
wealth of each strategy on the observed path, and the comparator on the right
is the wealth of the existing executable sleeping master.

The positivity premise is the standard legal-betting condition needed to
take logarithms. It is stated for every strategy, time, and path because the
master-wealth identity is recursive. -/
theorem countableSleepingStrategyPosterior_logWealth_le
    {residual : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hfactor_pos : forall j k xi,
      0 < 1 + sleepingStrategy strategy j k xi * residual k xi)
    (n : Nat) (rho : Fin (n + 1) -> Real) (hrho : IsPMF rho)
    (omega : Omega) :
    posteriorAverage rho (fun j =>
        Real.log (algebraicBettingWealth residual
          (sleepingStrategy strategy j.1) n omega)) <=
      klDiv (liftSleepingActivePosterior rho)
          (sleepingActiveDyadicPrior n) +
        Real.log (algebraicBettingWealth residual
          (countableSleepingMasterBet residual strategy) n omega) := by
  let score : Option (Fin (n + 1)) -> Real := fun a =>
    Real.log (sleepingActiveWealth residual strategy n omega a)
  have hactive_pos (a : Option (Fin (n + 1))) :
      0 < sleepingActiveWealth residual strategy n omega a := by
    cases a with
    | none => simp [sleepingActiveWealth]
    | some j =>
        exact algebraicBettingWealth_pos
          (fun k xi => hfactor_pos j.1 k xi) n omega
  have hchange := posterior_change_of_measure
    (liftSleepingActivePosterior_isPMF hrho)
    (sleepingActiveDyadicPrior_isFullSupportPMF n) score
  have hlhs :
      posteriorAverage (liftSleepingActivePosterior rho) score =
        posteriorAverage rho (fun j =>
          Real.log (algebraicBettingWealth residual
            (sleepingStrategy strategy j.1) n omega)) := by
    rw [posteriorAverage_liftSleepingActivePosterior]
    rfl
  have hmoment :
      (∑ a : Option (Fin (n + 1)),
          sleepingActiveDyadicPrior n a * Real.exp (score a)) =
        countableSleepingMixtureWealth residual strategy n omega := by
    rw [show (∑ a : Option (Fin (n + 1)),
          sleepingActiveDyadicPrior n a * Real.exp (score a)) =
        ∑ a : Option (Fin (n + 1)),
          sleepingActiveDyadicPrior n a *
            sleepingActiveWealth residual strategy n omega a by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [show Real.exp (score a) =
          sleepingActiveWealth residual strategy n omega a by
        unfold score
        exact Real.exp_log (hactive_pos a)]]
    exact sleepingActivePriorMoment_eq_countableSleepingMixtureWealth
      residual strategy n omega
  have hwealth_nonneg : forall j k xi,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) k xi := fun j k xi =>
    (algebraicBettingWealth_pos
      (fun t eta => hfactor_pos j t eta) k xi).le
  have hmaster :
      algebraicBettingWealth residual
          (countableSleepingMasterBet residual strategy) n omega =
        countableSleepingMixtureWealth residual strategy n omega :=
    countableSleepingMasterWealth_eq_mixture residual strategy
      (fun k xi =>
        (countableSleepingMixtureWealth_pos
          hwealth_nonneg k xi).ne') n omega
  rw [hlhs, hmoment, ← hmaster] at hchange
  exact hchange

/-- The same oracle inequality with the strategy-selection cost expanded
term by term against the dyadic catalog prior. -/
theorem countableSleepingStrategyPosterior_logWealth_le_explicit
    {residual : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hfactor_pos : forall j k xi,
      0 < 1 + sleepingStrategy strategy j k xi * residual k xi)
    (n : Nat) (rho : Fin (n + 1) -> Real) (hrho : IsPMF rho)
    (omega : Omega) :
    posteriorAverage rho (fun j =>
        Real.log (algebraicBettingWealth residual
          (sleepingStrategy strategy j.1) n omega)) <=
      (∑ j : Fin (n + 1),
          rho j * Real.log (rho j / dyadicExpertWeight j.1)) +
        Real.log (algebraicBettingWealth residual
          (countableSleepingMasterBet residual strategy) n omega) := by
  rw [← klDiv_liftSleepingActivePosterior n rho]
  exact countableSleepingStrategyPosterior_logWealth_le
    hfactor_pos n rho hrho omega

end StrategySelection

section TimeUniformEvent

variable {Omega : Type*}

/-- The single path event on which the executable countable master never
crosses its Ville threshold. This event is fixed before choosing either the
reporting time or the posterior over the currently active strategies. -/
def countableSleepingStrategyPosteriorGoodEvent
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real) (delta : Real) : Set Omega :=
  (atTopCrossingEvent
    (bettingWealthProcess X
      (countableSleepingMasterBet
        (fun k omega => X k omega - m) strategy) m)
    (1 / delta))ᶜ

/-- One Ville event controls every time and every posterior on the active
strategy prefix. The strategy catalog itself is fixed in advance and
countable; this theorem does not permit newly invented post-data strategies
and does not assert a continuum or parameter-free coin-betting result. -/
theorem countableSleepingStrategyPosteriorGoodEvent_spec
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall j,
      EProcess mu F
        (bettingWealthProcess X (sleepingStrategy strategy j) m))
    (hfactor_pos : forall j k omega,
      0 < 1 + sleepingStrategy strategy j k omega * (X k omega - m))
    {delta : Real} (hdelta : 0 < delta) :
    mu.real
        (countableSleepingStrategyPosteriorGoodEvent
          X m strategy delta)ᶜ <= delta ∧
      ∀ omega ∈
          countableSleepingStrategyPosteriorGoodEvent X m strategy delta,
        ∀ n : Nat, ∀ rho : Fin (n + 1) -> Real,
          IsPMF rho ->
            posteriorAverage rho (fun j =>
                Real.log (algebraicBettingWealth
                  (fun k xi => X k xi - m)
                  (sleepingStrategy strategy j.1) n omega)) <=
              klDiv (liftSleepingActivePosterior rho)
                  (sleepingActiveDyadicPrior n) +
                Real.log (1 / delta) := by
  let masterBet := countableSleepingMasterBet
    (fun k omega => X k omega - m) strategy
  let masterWealth := bettingWealthProcess X masterBet m
  have hE : EProcess mu F masterWealth := by
    dsimp only [masterWealth, masterBet]
    exact countableSleepingMasterBet_eProcess X m strategy
      hX_adapted hstrategy_adapted hcomponent
  have hthreshold : 0 < (1 : Real) / delta := one_div_pos.mpr hdelta
  have hville := ville_atTop_maximal_ineq
    hE.supermartingale hE.nonneg hthreshold
  rw [hE.integral_start_eq_one] at hville
  have hcrossing :
      mu.real (atTopCrossingEvent masterWealth (1 / delta)) <= delta := by
    calc
      mu.real (atTopCrossingEvent masterWealth (1 / delta)) =
          delta * ((1 / delta) *
            mu.real (atTopCrossingEvent masterWealth (1 / delta))) := by
              field_simp [hdelta.ne']
      _ <= delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  constructor
  · simpa [countableSleepingStrategyPosteriorGoodEvent,
      masterWealth, masterBet] using hcrossing
  · intro omega homega n rho hrho
    have hnot_crossing :
        omega ∉ atTopCrossingEvent masterWealth (1 / delta) := by
      simpa [countableSleepingStrategyPosteriorGoodEvent,
        masterWealth, masterBet] using homega
    have hmaster_lt : masterWealth n omega < 1 / delta := by
      exact lt_of_not_ge fun hcross => hnot_crossing ⟨n, hcross⟩
    have hwealth_nonneg : forall j k xi,
        0 <= algebraicBettingWealth (fun t eta => X t eta - m)
          (sleepingStrategy strategy j) k xi := fun j k xi =>
      (algebraicBettingWealth_pos
        (fun t eta => hfactor_pos j t eta) k xi).le
    have hmaster_pos :
        0 < algebraicBettingWealth (fun k xi => X k xi - m)
          (countableSleepingMasterBet
            (fun k xi => X k xi - m) strategy) n omega := by
      rw [countableSleepingMasterWealth_eq_mixture
        (fun k xi => X k xi - m) strategy
        (fun k xi =>
          (countableSleepingMixtureWealth_pos
            hwealth_nonneg k xi).ne') n omega]
      exact countableSleepingMixtureWealth_pos hwealth_nonneg n omega
    have hmaster_lt' :
        algebraicBettingWealth (fun k xi => X k xi - m)
            (countableSleepingMasterBet
              (fun k xi => X k xi - m) strategy) n omega <
          1 / delta := by
      simpa only [algebraicBettingWealth_eq_bettingWealthProcess,
        masterWealth, masterBet] using hmaster_lt
    have hlog :
        Real.log (algebraicBettingWealth (fun k xi => X k xi - m)
            (countableSleepingMasterBet
              (fun k xi => X k xi - m) strategy) n omega) <=
          Real.log (1 / delta) :=
      (Real.log_lt_log hmaster_pos hmaster_lt').le
    have horacle := countableSleepingStrategyPosterior_logWealth_le
      hfactor_pos n rho hrho omega
    exact horacle.trans (add_le_add (le_refl _) hlog)

/-- Existential packaging of the named common good event. The quantifiers over
time and posterior remain inside the event guarantee. -/
theorem exists_countableSleepingStrategyPosteriorGoodEvent
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsProbabilityMeasure mu]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall j,
      EProcess mu F
        (bettingWealthProcess X (sleepingStrategy strategy j) m))
    (hfactor_pos : forall j k omega,
      0 < 1 + sleepingStrategy strategy j k omega * (X k omega - m))
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        ∀ omega ∈ goodEvent, ∀ n : Nat,
          ∀ rho : Fin (n + 1) -> Real, IsPMF rho ->
            posteriorAverage rho (fun j =>
                Real.log (algebraicBettingWealth
                  (fun k xi => X k xi - m)
                  (sleepingStrategy strategy j.1) n omega)) <=
              klDiv (liftSleepingActivePosterior rho)
                  (sleepingActiveDyadicPrior n) +
                Real.log (1 / delta) := by
  refine ⟨countableSleepingStrategyPosteriorGoodEvent
    X m strategy delta, ?_⟩
  exact countableSleepingStrategyPosteriorGoodEvent_spec
    X m strategy hX_adapted hstrategy_adapted hcomponent
      hfactor_pos hdelta

end TimeUniformEvent

end FormalSLT.AnytimeValid
