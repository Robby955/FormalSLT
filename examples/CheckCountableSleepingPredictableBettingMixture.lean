import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingMixture

/-!
# Exact countable sleeping-expert betting-mixture receipt

The countable catalog uses dyadic prior mass. At each time only a finite
prefix can bet, while the still-sleeping infinite tail is represented exactly
by one rational number. The receipt checks that the master adapts, its wealth
obeys the countable-mixture identity, and it competes with active experts.
-/

open FormalSLT.AnytimeValid

def countableReceiptResidual (n : Nat) (_omega : Unit) : Rat :=
  if n = 0 then 1 / 2 else if n = 1 then -1 / 4 else 0

def countableReceiptStrategy (j : Nat) (_n : Nat) (_omega : Unit) : Rat :=
  if j = 0 then 1 / 2 else if j = 1 then 1 / 4 else 1 / 8

#eval countableSleepingMasterBet
  countableReceiptResidual countableReceiptStrategy 0 ()
#eval countableSleepingMasterBet
  countableReceiptResidual countableReceiptStrategy 1 ()
#eval countableSleepingMasterBet
  countableReceiptResidual countableReceiptStrategy 2 ()
#eval countableSleepingMixtureWealth
  countableReceiptResidual countableReceiptStrategy 2 ()

theorem countableReceiptFactor_positive (j k : Nat) :
    0 < 1 +
      sleepingStrategy countableReceiptStrategy j k () *
        countableReceiptResidual k () := by
  unfold sleepingStrategy countableReceiptStrategy countableReceiptResidual
  split_ifs <;> norm_num

theorem countableReceiptExpertWealth_positive (j n : Nat) :
    0 < algebraicBettingWealth countableReceiptResidual
      (sleepingStrategy countableReceiptStrategy j) n () := by
  exact algebraicBettingWealth_pos
    (fun k _omega => countableReceiptFactor_positive j k) n ()

theorem countableReceiptMixture_positive (n : Nat) :
    0 < countableSleepingMixtureWealth
      countableReceiptResidual countableReceiptStrategy n () := by
  exact countableSleepingMixtureWealth_pos
    (fun j n _omega => (countableReceiptExpertWealth_positive j n).le) n ()

theorem countableReceiptMasterBet_zero :
    countableSleepingMasterBet
      countableReceiptResidual countableReceiptStrategy 0 () = 1 / 4 := by
  norm_num [countableSleepingMasterBet, countableSleepingBetNumerator,
    countableSleepingMixtureWealth, dyadicSleepingTail, dyadicExpertWeight,
    algebraicBettingWealth, sleepingStrategy, countableReceiptStrategy]

theorem countableReceiptMasterBet_one :
    countableSleepingMasterBet
      countableReceiptResidual countableReceiptStrategy 1 () = 1 / 3 := by
  simp only [countableSleepingMasterBet, countableSleepingBetNumerator,
    countableSleepingMixtureWealth, dyadicSleepingTail, dyadicExpertWeight,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [algebraicBettingWealth, sleepingStrategy,
    countableReceiptResidual, countableReceiptStrategy,
    Finset.prod_range_succ]

theorem countableReceiptMasterBet_two :
    countableSleepingMasterBet
      countableReceiptResidual countableReceiptStrategy 2 () = 89 / 264 := by
  simp only [countableSleepingMasterBet, countableSleepingBetNumerator,
    countableSleepingMixtureWealth, dyadicSleepingTail, dyadicExpertWeight,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [algebraicBettingWealth, sleepingStrategy,
    countableReceiptResidual, countableReceiptStrategy,
    Finset.prod_range_succ]

theorem countableReceiptMaster_adapts :
    countableSleepingMasterBet
        countableReceiptResidual countableReceiptStrategy 0 () ≠
      countableSleepingMasterBet
        countableReceiptResidual countableReceiptStrategy 1 () := by
  rw [countableReceiptMasterBet_zero, countableReceiptMasterBet_one]
  norm_num

theorem countableReceiptMixtureWealth_two :
    countableSleepingMixtureWealth
      countableReceiptResidual countableReceiptStrategy 2 () = 33 / 32 := by
  simp only [countableSleepingMixtureWealth, dyadicSleepingTail,
    dyadicExpertWeight, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [algebraicBettingWealth, sleepingStrategy,
    countableReceiptResidual, countableReceiptStrategy,
    Finset.prod_range_succ]

theorem countableReceiptMasterWealth_two :
    algebraicBettingWealth countableReceiptResidual
        (countableSleepingMasterBet
          countableReceiptResidual countableReceiptStrategy) 2 () =
      33 / 32 := by
  rw [countableSleepingMasterWealth_eq_mixture
    countableReceiptResidual countableReceiptStrategy
      (fun n _omega => (countableReceiptMixture_positive n).ne') 2 ()]
  exact countableReceiptMixtureWealth_two

theorem countableReceiptCompetesExpert_zero :
    dyadicExpertWeight 0 *
        algebraicBettingWealth countableReceiptResidual
          (sleepingStrategy countableReceiptStrategy 0) 2 () <=
      algebraicBettingWealth countableReceiptResidual
        (countableSleepingMasterBet
          countableReceiptResidual countableReceiptStrategy) 2 () := by
  exact countableSleepingMasterWealth_competes_of_lt
    (fun j n _omega => (countableReceiptExpertWealth_positive j n).le)
    (by norm_num) ()

theorem countableReceipt_rational_real_pin :
    ((countableSleepingMixtureWealth
      countableReceiptResidual countableReceiptStrategy 2 () : Rat) : Real) =
      33 / 32 := by
  norm_num [countableReceiptMixtureWealth_two]

#check countableSleepingMixtureWealth_succ
#check hasSum_dyadicExpertWeight
#check countableSleepingMixtureWealth_eq_tsum
#check countableSleepingActiveMass_le_mixture
#check countableSleepingMasterBet_mem_Icc
#check countableSleepingMasterWealth_eq_mixture
#check countableSleepingMasterWealth_competes_of_lt
#check ratCast_countableSleepingMasterBet
#check countableSleepingMasterBet_stronglyAdapted
#check countableSleepingMasterBet_eProcess
#check countableSleepingMaster_logWealth_regret_le

#print axioms countableSleepingMixtureWealth_succ
#print axioms hasSum_dyadicExpertWeight
#print axioms countableSleepingMixtureWealth_eq_tsum
#print axioms countableSleepingActiveMass_le_mixture
#print axioms countableSleepingMasterBet_mem_Icc
#print axioms countableSleepingMasterWealth_eq_mixture
#print axioms countableSleepingMasterWealth_competes_of_lt
#print axioms ratCast_countableSleepingMasterBet
#print axioms countableSleepingMasterBet_stronglyAdapted
#print axioms countableSleepingMasterBet_eProcess
#print axioms countableSleepingMaster_logWealth_regret_le
#print axioms countableReceiptMasterWealth_two
#print axioms countableReceipt_rational_real_pin
