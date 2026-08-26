import FormalSLT.AnytimeValid.ComputablePredictableBettingMixture

/-!
# Exact executable predictable betting-mixture receipt

Two rational betting strategies start with equal prior weight. The master bet
is computed from their wealth before the current residual is revealed. Exact
rational checks show that the master changes its bet after the first residual,
that its recursively generated wealth equals the fixed mixture wealth, and
that the mixture dominates both prior-weighted expert wealths.
-/

open FormalSLT.AnytimeValid

def receiptWeight (_j : Fin 2) : Rat := 1 / 2

def receiptResidual (n : Nat) (_omega : Unit) : Rat :=
  if n = 0 then 1 / 2 else -1 / 4

def receiptStrategy (j : Fin 2) (_n : Nat) (_omega : Unit) : Rat :=
  if j = 0 then 1 / 2 else 1 / 4

#eval wealthWeightedBet receiptWeight receiptResidual receiptStrategy 0 ()
#eval wealthWeightedBet receiptWeight receiptResidual receiptStrategy 1 ()
#eval finiteExpertMixtureWealth receiptWeight receiptResidual receiptStrategy 2 ()

theorem receiptWeight_sum_one :
    ∑ j : Fin 2, receiptWeight j = 1 := by
  norm_num [receiptWeight, Fin.sum_univ_two]

lemma receiptWeight_nonneg (j : Fin 2) : 0 <= receiptWeight j := by
  norm_num [receiptWeight]

lemma receiptFactor_positive (j : Fin 2) (n : Nat) :
    0 < 1 + receiptStrategy j n () * receiptResidual n () := by
  unfold receiptStrategy receiptResidual
  split_ifs <;> norm_num

lemma receiptExpertWealth_positive (j : Fin 2) (n : Nat) :
    0 < algebraicBettingWealth receiptResidual (receiptStrategy j) n () := by
  unfold algebraicBettingWealth
  exact Finset.prod_pos fun k _hk => receiptFactor_positive j k

theorem receiptMixture_positive (n : Nat) :
    0 < finiteExpertMixtureWealth
      receiptWeight receiptResidual receiptStrategy n () := by
  unfold finiteExpertMixtureWealth
  rw [Fin.sum_univ_two]
  exact add_pos
    (mul_pos (by norm_num [receiptWeight]) (receiptExpertWealth_positive 0 n))
    (mul_pos (by norm_num [receiptWeight]) (receiptExpertWealth_positive 1 n))

theorem receipt_masterBet_zero :
    wealthWeightedBet receiptWeight receiptResidual receiptStrategy 0 () =
      3 / 8 := by
  norm_num [wealthWeightedBet, finiteExpertMixtureWealth,
    algebraicBettingWealth, receiptWeight, receiptStrategy, Fin.sum_univ_two]

theorem receipt_masterBet_one :
    wealthWeightedBet receiptWeight receiptResidual receiptStrategy 1 () =
      29 / 76 := by
  norm_num [wealthWeightedBet, finiteExpertMixtureWealth,
    algebraicBettingWealth, receiptWeight, receiptResidual, receiptStrategy,
    Fin.sum_univ_two]

theorem receipt_master_adapts :
    wealthWeightedBet receiptWeight receiptResidual receiptStrategy 0 () ≠
      wealthWeightedBet receiptWeight receiptResidual receiptStrategy 1 () := by
  rw [receipt_masterBet_zero, receipt_masterBet_one]
  norm_num

theorem receipt_mixtureWealth_two :
    finiteExpertMixtureWealth receiptWeight receiptResidual receiptStrategy 2 () =
      275 / 256 := by
  norm_num [finiteExpertMixtureWealth, algebraicBettingWealth,
    receiptWeight, receiptResidual, receiptStrategy, Fin.sum_univ_two,
    Finset.prod_range_succ]

theorem receipt_aggregateWealth_two :
    algebraicBettingWealth receiptResidual
        (wealthWeightedBet receiptWeight receiptResidual receiptStrategy) 2 () =
      275 / 256 := by
  rw [aggregateWealth_eq_finiteExpertMixtureWealth
    receiptWeight receiptResidual receiptStrategy receiptWeight_sum_one
      (fun n _omega => (receiptMixture_positive n).ne') 2 ()]
  exact receipt_mixtureWealth_two

theorem receipt_competes_strategy_zero :
    receiptWeight 0 *
        algebraicBettingWealth receiptResidual (receiptStrategy 0) 2 () <=
      algebraicBettingWealth receiptResidual
        (wealthWeightedBet receiptWeight receiptResidual receiptStrategy) 2 () := by
  exact aggregateWealth_competes_with_every_strategy
    receiptWeight_sum_one receiptWeight_nonneg
      (fun j n _omega => (receiptExpertWealth_positive j n).le)
      (fun n _omega => receiptMixture_positive n) 0 2 ()

theorem receipt_competes_strategy_one :
    receiptWeight 1 *
        algebraicBettingWealth receiptResidual (receiptStrategy 1) 2 () <=
      algebraicBettingWealth receiptResidual
        (wealthWeightedBet receiptWeight receiptResidual receiptStrategy) 2 () := by
  exact aggregateWealth_competes_with_every_strategy
    receiptWeight_sum_one receiptWeight_nonneg
      (fun j n _omega => (receiptExpertWealth_positive j n).le)
      (fun n _omega => receiptMixture_positive n) 1 2 ()

theorem receipt_rational_real_pin :
    ((finiteExpertMixtureWealth receiptWeight receiptResidual
        receiptStrategy 2 () : Rat) : Real) = 275 / 256 := by
  norm_num [receipt_mixtureWealth_two]

#check algebraicBettingWealth
#check finiteExpertMixtureWealth
#check wealthWeightedBet
#check aggregateWealth_eq_finiteExpertMixtureWealth
#check algebraicBettingWealth_pos
#check finiteExpertMixtureWealth_pos
#check wealthWeightedBet_mem_Icc
#check aggregateWealth_competes_with_every_strategy
#check ratCast_wealthWeightedBet
#check wealthWeightedBet_stronglyAdapted
#check wealthWeightedBet_eProcess
#check wealthWeightedBet_eProcess_of_positive_factors
#check aggregate_logWealth_regret_le

#print axioms aggregateWealth_eq_finiteExpertMixtureWealth
#print axioms algebraicBettingWealth_pos
#print axioms finiteExpertMixtureWealth_pos
#print axioms wealthWeightedBet_mem_Icc
#print axioms aggregateWealth_competes_with_every_strategy
#print axioms ratCast_wealthWeightedBet
#print axioms wealthWeightedBet_stronglyAdapted
#print axioms wealthWeightedBet_eProcess
#print axioms wealthWeightedBet_eProcess_of_positive_factors
#print axioms aggregate_logWealth_regret_le
#print axioms receipt_aggregateWealth_two
#print axioms receipt_rational_real_pin
