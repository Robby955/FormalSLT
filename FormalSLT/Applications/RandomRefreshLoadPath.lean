/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.RandomRefreshLoadModel
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence

/-!
# A periodic balanced path for the random-refresh load model

This module gives a fully deterministic arithmetic receipt for the empirical
transition table used by the twenty-state application.  One length-`1,600`
period consists of three length-`400` order-two de Bruijn circuits followed by
twenty complete turns around the deterministic length-`20` successor cycle.
The entire block repeats, so the path has no eventually homogeneous tail.

Every complete block gives each state exactly `80` departures, each successor
edge multiplicity `23`, and every other edge multiplicity `3`.  Consequently
the first `200,000 = 125 * 1,600` transitions retain the original exact table:
`10,000` departures per state, successor-edge multiplicity `2,875`, and every
other edge multiplicity `375`.  These statements concern this named
arithmetic witness only; they make no claim that the witness belongs to a
statistical good event.
-/

open Finset
open scoped BigOperators

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadPath

open RandomRefreshLoadModel

noncomputable section

attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- Block of the lexicographically concatenated length-one and length-two
Lyndon words.  The thresholds are the exact block starts
`a * (40 - a)` for `0 < a ≤ 20`. -/
private def deBruijnBlock (k : ℕ) : ℕ :=
  let r := k % 400
  if r < 39 then 0
  else if r < 76 then 1
  else if r < 111 then 2
  else if r < 144 then 3
  else if r < 175 then 4
  else if r < 204 then 5
  else if r < 231 then 6
  else if r < 256 then 7
  else if r < 279 then 8
  else if r < 300 then 9
  else if r < 319 then 10
  else if r < 336 then 11
  else if r < 351 then 12
  else if r < 364 then 13
  else if r < 375 then 14
  else if r < 384 then 15
  else if r < 391 then 16
  else if r < 396 then 17
  else if r < 399 then 18
  else 19

/-- Offset inside the current Lyndon block. -/
private def deBruijnOffset (k : ℕ) : ℕ :=
  let r := k % 400
  let a := deBruijnBlock k
  r - a * (40 - a)

/-- Cyclic order-two de Bruijn word on twenty symbols.  Within block `a`,
the word is `a, a, a+1, a, a+2, ..., a, 19`. -/
def deBruijnVertex (k : ℕ) : State :=
  let a := deBruijnBlock k
  let t := deBruijnOffset k
  let v := if t % 2 = 0 then a + t / 2 else a
  ⟨v % 20, Nat.mod_lt _ (by norm_num)⟩

/-- The deterministic twenty-cycle, starting at state zero. -/
def successorCycleVertex (k : ℕ) : State :=
  ⟨k % 20, Nat.mod_lt _ (by norm_num)⟩

/-- The balanced arithmetic witness.  Each `1,600`-edge period contains three
de Bruijn circuits followed by twenty successor cycles. -/
def balancedPath (k : ℕ) : State :=
  let r := k % 1600
  if r < 1200 then deBruijnVertex r
  else successorCycleVertex (r - 1200)

private theorem sum_range_mul_of_periodic {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (p r : ℕ) (hperiod : Function.Periodic f p) :
    (∑ k ∈ Finset.range (p * r), f k) =
      r • (∑ k ∈ Finset.range p, f k) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro k _hk
      have hp := hperiod.nsmul r k
      simpa [nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using hp

theorem deBruijnVertex_periodic : Function.Periodic deBruijnVertex 400 := by
  intro k
  simp [deBruijnVertex, deBruijnOffset, deBruijnBlock, Nat.add_mod_right]

theorem successorCycleVertex_periodic :
    Function.Periodic successorCycleVertex 20 := by
  intro k
  apply Fin.ext
  simp [successorCycleVertex, Nat.add_mod_right]

private theorem deBruijnVertex_1200 : deBruijnVertex 1200 = 0 := by decide

private theorem balancedPath_first (k : ℕ) (hk : k < 1200) :
    balancedPath k = deBruijnVertex k := by
  have hk1600 : k < 1600 := hk.trans (by norm_num)
  simp [balancedPath, Nat.mod_eq_of_lt hk1600, hk]

private theorem balancedPath_boundary : balancedPath 1200 = 0 := by
  simp [balancedPath, successorCycleVertex]

private theorem balancedPath_first_next (k : ℕ) (hk : k < 1200) :
    balancedPath (k + 1) = deBruijnVertex (k + 1) := by
  by_cases hnext : k + 1 < 1200
  · exact balancedPath_first (k + 1) hnext
  · have hkEq : k + 1 = 1200 := by omega
    rw [hkEq, balancedPath_boundary, deBruijnVertex_1200]

private theorem balancedPath_second (k : ℕ) (hk : k < 400) :
    balancedPath (1200 + k) = successorCycleVertex k := by
  have hlt : 1200 + k < 1600 := by omega
  simp [balancedPath, Nat.mod_eq_of_lt hlt]

private theorem balancedPath_second_next (k : ℕ) (hk : k < 400) :
    balancedPath (1200 + k + 1) = successorCycleVertex (k + 1) := by
  by_cases hnext : k + 1 < 400
  · simpa [Nat.add_assoc] using balancedPath_second (k + 1) hnext
  · have hkEq : k = 399 := by omega
    subst k
    norm_num [balancedPath, successorCycleVertex, deBruijnVertex,
      deBruijnOffset, deBruijnBlock]

/-- The balanced path repeats after every `1,600` transitions. -/
theorem balancedPath_periodic : Function.Periodic balancedPath 1600 := by
  intro k
  simp [balancedPath, Nat.add_mod_right]

private def balancedPathVisitIndicator (z : State) (k : ℕ) : ℝ :=
  if (balancedPath k).val = z.val then 1 else 0

private theorem successor_visit_card : ∀ z : State,
    ((Finset.range 20).filter (fun k ↦ successorCycleVertex k = z)).card = 1 := by
  decide

private theorem successor_edge_card : ∀ z y : State,
    ((Finset.range 20).filter (fun k ↦
      successorCycleVertex k = z ∧ successorCycleVertex (k + 1) = y)).card =
        if y = successor z then 1 else 0 := by
  decide

/-- Closed-form location of the edge `z → y` in one de Bruijn period. -/
private def deBruijnEdgeIndexNat (z y : State) : ℕ :=
  let zv := z.val
  let yv := y.val
  let start (a : ℕ) := a * (40 - a)
  if zv < 19 then
    if zv ≤ yv then
      if zv = yv then start zv else start zv + 2 * (yv - zv) - 1
    else start yv + 2 * (zv - yv)
  else if yv = 0 then 399 else start yv - 1

private def deBruijnEdgeIndex (p : State × State) : Fin 400 :=
  ⟨deBruijnEdgeIndexNat p.1 p.2 % 400, Nat.mod_lt _ (by norm_num)⟩

private def deBruijnEdgeMap (k : Fin 400) : State × State :=
  (deBruijnVertex k, deBruijnVertex (k + 1))

private theorem deBruijnEdgeMap_index_0 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (0, y)) = (0, y) := by decide

private theorem deBruijnEdgeMap_index_1 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (1, y)) = (1, y) := by decide

private theorem deBruijnEdgeMap_index_2 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (2, y)) = (2, y) := by decide

private theorem deBruijnEdgeMap_index_3 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (3, y)) = (3, y) := by decide

private theorem deBruijnEdgeMap_index_4 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (4, y)) = (4, y) := by decide

private theorem deBruijnEdgeMap_index_5 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (5, y)) = (5, y) := by decide

private theorem deBruijnEdgeMap_index_6 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (6, y)) = (6, y) := by decide

private theorem deBruijnEdgeMap_index_7 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (7, y)) = (7, y) := by decide

private theorem deBruijnEdgeMap_index_8 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (8, y)) = (8, y) := by decide

private theorem deBruijnEdgeMap_index_9 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (9, y)) = (9, y) := by decide

private theorem deBruijnEdgeMap_index_10 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (10, y)) = (10, y) := by decide

private theorem deBruijnEdgeMap_index_11 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (11, y)) = (11, y) := by decide

private theorem deBruijnEdgeMap_index_12 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (12, y)) = (12, y) := by decide

private theorem deBruijnEdgeMap_index_13 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (13, y)) = (13, y) := by decide

private theorem deBruijnEdgeMap_index_14 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (14, y)) = (14, y) := by decide

private theorem deBruijnEdgeMap_index_15 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (15, y)) = (15, y) := by decide

private theorem deBruijnEdgeMap_index_16 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (16, y)) = (16, y) := by decide

private theorem deBruijnEdgeMap_index_17 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (17, y)) = (17, y) := by decide

private theorem deBruijnEdgeMap_index_18 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (18, y)) = (18, y) := by decide

private theorem deBruijnEdgeMap_index_19 : ∀ y : State,
    deBruijnEdgeMap (deBruijnEdgeIndex (19, y)) = (19, y) := by decide

private theorem deBruijnEdgeMap_index (z y : State) :
    deBruijnEdgeMap (deBruijnEdgeIndex (z, y)) = (z, y) := by
  fin_cases z
  · exact deBruijnEdgeMap_index_0 y
  · exact deBruijnEdgeMap_index_1 y
  · exact deBruijnEdgeMap_index_2 y
  · exact deBruijnEdgeMap_index_3 y
  · exact deBruijnEdgeMap_index_4 y
  · exact deBruijnEdgeMap_index_5 y
  · exact deBruijnEdgeMap_index_6 y
  · exact deBruijnEdgeMap_index_7 y
  · exact deBruijnEdgeMap_index_8 y
  · exact deBruijnEdgeMap_index_9 y
  · exact deBruijnEdgeMap_index_10 y
  · exact deBruijnEdgeMap_index_11 y
  · exact deBruijnEdgeMap_index_12 y
  · exact deBruijnEdgeMap_index_13 y
  · exact deBruijnEdgeMap_index_14 y
  · exact deBruijnEdgeMap_index_15 y
  · exact deBruijnEdgeMap_index_16 y
  · exact deBruijnEdgeMap_index_17 y
  · exact deBruijnEdgeMap_index_18 y
  · exact deBruijnEdgeMap_index_19 y

private theorem deBruijnEdgeMap_surjective :
    Function.Surjective deBruijnEdgeMap := by
  rintro ⟨z, y⟩
  exact ⟨deBruijnEdgeIndex (z, y), deBruijnEdgeMap_index z y⟩

/-- The cyclic adjacent-pair map is a bijection from one period to all
ordered state pairs.  Downstream counting uses this equivalence algebraically. -/
private def deBruijnEdgeEquiv : Fin 400 ≃ State × State :=
  Equiv.ofBijective deBruijnEdgeMap
    ((Fintype.bijective_iff_surjective_and_card deBruijnEdgeMap).2
      ⟨deBruijnEdgeMap_surjective, by decide⟩)

private theorem deBruijn_visit_sum (z : State) :
    (∑ k ∈ Finset.range 400,
      if deBruijnVertex k = z then (1 : ℝ) else 0) = 20 := by
  rw [← Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin 400,
    if (deBruijnEdgeEquiv k).1 = z then (1 : ℝ) else 0) = 20
  rw [Equiv.sum_comp deBruijnEdgeEquiv
    (fun p : State × State ↦ if p.1 = z then (1 : ℝ) else 0)]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single z]
  · norm_num [Finset.card_univ, nsmul_eq_mul]
  · intro x hx
    simp [hx]

private theorem deBruijn_edge_sum (z y : State) :
    (∑ k ∈ Finset.range 400,
      if deBruijnVertex k = z ∧ deBruijnVertex (k + 1) = y
      then (1 : ℝ) else 0) = 1 := by
  rw [← Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin 400,
    if (deBruijnEdgeEquiv k).1 = z ∧ (deBruijnEdgeEquiv k).2 = y
    then (1 : ℝ) else 0) = 1
  rw [Equiv.sum_comp deBruijnEdgeEquiv
    (fun p : State × State ↦
      if p.1 = z ∧ p.2 = y then (1 : ℝ) else 0)]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single z]
  · rw [Fintype.sum_eq_single y]
    · simp
    · intro y' hy'
      simp [hy']
  · intro x hx
    simp [hx]

private theorem successor_visit_sum (z : State) :
    (∑ k ∈ Finset.range 20,
      if successorCycleVertex k = z then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_boole]
  norm_num [successor_visit_card z]

private theorem successor_edge_sum (z y : State) :
    (∑ k ∈ Finset.range 20,
      if successorCycleVertex k = z ∧ successorCycleVertex (k + 1) = y
      then (1 : ℝ) else 0) = if y = successor z then 1 else 0 := by
  rw [Finset.sum_boole]
  exact_mod_cast successor_edge_card z y

private theorem deBruijn_visit_indicator_periodic (z : State) :
    Function.Periodic
      (fun k ↦ if deBruijnVertex k = z then (1 : ℝ) else 0) 400 := by
  intro k
  change (if deBruijnVertex (k + 400) = z then (1 : ℝ) else 0) = _
  rw [deBruijnVertex_periodic k]

private theorem deBruijn_edge_indicator_periodic (z y : State) :
    Function.Periodic
      (fun k ↦ if deBruijnVertex k = z ∧ deBruijnVertex (k + 1) = y
        then (1 : ℝ) else 0) 400 := by
  intro k
  change (if deBruijnVertex (k + 400) = z ∧
      deBruijnVertex (k + 400 + 1) = y then (1 : ℝ) else 0) = _
  rw [deBruijnVertex_periodic k]
  have hnext := deBruijnVertex_periodic (k + 1)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg
    (fun v ↦ if deBruijnVertex k = z ∧ v = y then (1 : ℝ) else 0) hnext

private theorem successor_visit_indicator_periodic (z : State) :
    Function.Periodic
      (fun k ↦ if successorCycleVertex k = z then (1 : ℝ) else 0) 20 := by
  intro k
  change (if successorCycleVertex (k + 20) = z then (1 : ℝ) else 0) = _
  rw [successorCycleVertex_periodic k]

private theorem successor_edge_indicator_periodic (z y : State) :
    Function.Periodic
      (fun k ↦ if successorCycleVertex k = z ∧
          successorCycleVertex (k + 1) = y then (1 : ℝ) else 0) 20 := by
  intro k
  change (if successorCycleVertex (k + 20) = z ∧
      successorCycleVertex (k + 20 + 1) = y then (1 : ℝ) else 0) = _
  rw [successorCycleVertex_periodic k]
  have hnext := successorCycleVertex_periodic (k + 1)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg
    (fun v ↦ if successorCycleVertex k = z ∧ v = y then (1 : ℝ) else 0) hnext

private theorem balancedPath_visit_sum (z : State) :
    (∑ k ∈ Finset.range 1600,
      if balancedPath k = z then (1 : ℝ) else 0) = 80 := by
  rw [show 1600 = 1200 + 400 by norm_num, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range 1200,
        if balancedPath k = z then (1 : ℝ) else 0) = 60 := by
    calc
      (∑ k ∈ Finset.range 1200,
          if balancedPath k = z then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range (400 * 3),
            if deBruijnVertex k = z then (1 : ℝ) else 0 := by
              apply Finset.sum_congr
              · norm_num
              · intro k hk
                rw [balancedPath_first k (Finset.mem_range.mp hk)]
      _ = 3 • (∑ k ∈ Finset.range 400,
            if deBruijnVertex k = z then (1 : ℝ) else 0) :=
          sum_range_mul_of_periodic _ 400 3
            (deBruijn_visit_indicator_periodic z)
      _ = 60 := by rw [deBruijn_visit_sum]; norm_num
  have hsecond :
      (∑ k ∈ Finset.range 400,
        if balancedPath (1200 + k) = z then (1 : ℝ) else 0) = 20 := by
    calc
      (∑ k ∈ Finset.range 400,
          if balancedPath (1200 + k) = z then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range (20 * 20),
            if successorCycleVertex k = z then (1 : ℝ) else 0 := by
              apply Finset.sum_congr
              · norm_num
              · intro k hk
                rw [balancedPath_second k (Finset.mem_range.mp hk)]
      _ = 20 • (∑ k ∈ Finset.range 20,
            if successorCycleVertex k = z then (1 : ℝ) else 0) :=
          sum_range_mul_of_periodic _ 20 20
            (successor_visit_indicator_periodic z)
      _ = 20 := by rw [successor_visit_sum]; norm_num
  rw [hfirst, hsecond]
  norm_num

private theorem balancedPath_edge_sum (z y : State) :
    (∑ k ∈ Finset.range 1600,
      if balancedPath k = z ∧ balancedPath (k + 1) = y
      then (1 : ℝ) else 0) =
        if y = successor z then 23 else 3 := by
  rw [show 1600 = 1200 + 400 by norm_num, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range 1200,
        if balancedPath k = z ∧ balancedPath (k + 1) = y
        then (1 : ℝ) else 0) = 3 := by
    calc
      (∑ k ∈ Finset.range 1200,
          if balancedPath k = z ∧ balancedPath (k + 1) = y
          then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range (400 * 3),
            if deBruijnVertex k = z ∧ deBruijnVertex (k + 1) = y
            then (1 : ℝ) else 0 := by
              apply Finset.sum_congr
              · norm_num
              · intro k hk
                have hklt := Finset.mem_range.mp hk
                rw [balancedPath_first k hklt,
                  balancedPath_first_next k hklt]
      _ = 3 • (∑ k ∈ Finset.range 400,
            if deBruijnVertex k = z ∧ deBruijnVertex (k + 1) = y
            then (1 : ℝ) else 0) :=
          sum_range_mul_of_periodic _ 400 3
            (deBruijn_edge_indicator_periodic z y)
      _ = 3 := by rw [deBruijn_edge_sum]; norm_num
  have hsecond :
      (∑ k ∈ Finset.range 400,
        if balancedPath (1200 + k) = z ∧
            balancedPath (1200 + k + 1) = y
        then (1 : ℝ) else 0) =
          if y = successor z then 20 else 0 := by
    calc
      (∑ k ∈ Finset.range 400,
          if balancedPath (1200 + k) = z ∧
              balancedPath (1200 + k + 1) = y
          then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range (20 * 20),
            if successorCycleVertex k = z ∧
                successorCycleVertex (k + 1) = y
            then (1 : ℝ) else 0 := by
              apply Finset.sum_congr
              · norm_num
              · intro k hk
                have hklt := Finset.mem_range.mp hk
                rw [balancedPath_second k hklt,
                  balancedPath_second_next k hklt]
      _ = 20 • (∑ k ∈ Finset.range 20,
            if successorCycleVertex k = z ∧
                successorCycleVertex (k + 1) = y
            then (1 : ℝ) else 0) :=
          sum_range_mul_of_periodic _ 20 20
            (successor_edge_indicator_periodic z y)
      _ = if y = successor z then 20 else 0 := by
        rw [successor_edge_sum]
        split_ifs <;> norm_num
  rw [hfirst, hsecond]
  split_ifs <;> norm_num

private theorem balancedPath_visit_indicator_periodic (z : State) :
    Function.Periodic (balancedPathVisitIndicator z) 1600 := by
  intro k
  unfold balancedPathVisitIndicator
  rw [balancedPath_periodic k]

private theorem balancedPath_transitionIndicator_sum (z y : State) :
    (∑ k ∈ Finset.range 1600,
      transitionIndicatorScore z y (balancedPath k) (balancedPath (k + 1))) =
        if y = successor z then 23 else 3 := by
  refine Eq.trans ?_ (balancedPath_edge_sum z y)
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hz : balancedPath k = z <;>
    by_cases hy : balancedPath (k + 1) = y <;>
      simp [transitionIndicatorScore, hz, hy]

private theorem balancedPath_transitionIndicator_periodic (z y : State) :
    Function.Periodic
      (fun k ↦ transitionIndicatorScore z y
        (balancedPath k) (balancedPath (k + 1))) 1600 := by
  intro k
  change transitionIndicatorScore z y (balancedPath (k + 1600))
      (balancedPath (k + 1600 + 1)) =
    transitionIndicatorScore z y (balancedPath k) (balancedPath (k + 1))
  rw [balancedPath_periodic k]
  have hnext := balancedPath_periodic (k + 1)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg
    (fun v ↦ transitionIndicatorScore z y (balancedPath k) v) hnext

/-- Every complete `1,600`-edge block gives each state exactly `80`
departures. -/
theorem balancedPath_transitionVisitMass_mul_period (z : State) (r : ℕ) :
    transitionVisitMass z (1600 * r) balancedPath = 80 * (r : ℝ) := by
  unfold transitionVisitMass
  simp only [Fin.ext_iff]
  change (∑ k ∈ Finset.range (1600 * r),
    balancedPathVisitIndicator z k) = 80 * (r : ℝ)
  calc
    _ = r • _ :=
      sum_range_mul_of_periodic _ 1600 r
        (balancedPath_visit_indicator_periodic z)
    _ = r • (80 : ℝ) := congrArg (fun q : ℝ ↦ r • q)
      (by simpa [balancedPathVisitIndicator, Fin.ext_iff] using
        balancedPath_visit_sum z)
    _ = 80 * (r : ℝ) := by
      simp [nsmul_eq_mul]
      ring

/-- Every complete `1,600`-edge block gives each successor edge multiplicity
`23` and every other edge multiplicity `3`. -/
theorem balancedPath_transitionEdgeMass_mul_period
    (z y : State) (r : ℕ) :
    transitionEdgeMass z y (1600 * r) balancedPath =
      if y = successor z then 23 * (r : ℝ) else 3 * (r : ℝ) := by
  unfold transitionEdgeMass
  calc
    _ = r • _ :=
      sum_range_mul_of_periodic _ 1600 r
        (balancedPath_transitionIndicator_periodic z y)
    _ = r • (if y = successor z then (23 : ℝ) else 3) :=
      congrArg (fun q : ℝ ↦ r • q)
        (balancedPath_transitionIndicator_sum z y)
    _ = if y = successor z then 23 * (r : ℝ) else 3 * (r : ℝ) := by
      split_ifs <;> simp [nsmul_eq_mul] <;> ring

/-- At every positive complete-block horizon, the empirical transition
frequencies equal the nominal refresh-kernel row probabilities exactly. -/
theorem balancedPath_empiricalTransitionFrequency_mul_period
    (z y : State) (r : ℕ) (hr : 0 < r) :
    empiricalTransitionFrequency z y (1600 * r) balancedPath =
      if y = successor z then 23 / 80 else 3 / 80 := by
  rw [empiricalTransitionFrequency,
    balancedPath_transitionEdgeMass_mul_period,
    balancedPath_transitionVisitMass_mul_period]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  split_ifs <;> field_simp [hr0]

/-- Every state is the source of exactly `10,000` of the first `200,000`
transitions of the named path. -/
theorem balancedPath_transitionVisitMass (z : State) :
    transitionVisitMass z 200000 balancedPath = 10000 := by
  have h := balancedPath_transitionVisitMass_mul_period z 125
  norm_num at h ⊢
  exact h

/-- Exact transition table of the named `200,000`-edge path. -/
theorem balancedPath_transitionEdgeMass (z y : State) :
    transitionEdgeMass z y 200000 balancedPath =
      if y = successor z then 2875 else 375 := by
  have h := balancedPath_transitionEdgeMass_mul_period z y 125
  norm_num at h ⊢
  exact h

/-- The empirical transition frequencies at the receipt horizon are exactly
the nominal refresh-kernel row probabilities. -/
theorem balancedPath_empiricalTransitionFrequency (z y : State) :
    empiricalTransitionFrequency z y 200000 balancedPath =
      if y = successor z then 23 / 80 else 3 / 80 := by
  simpa using balancedPath_empiricalTransitionFrequency_mul_period
    z y 125 (by norm_num)

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadPath
