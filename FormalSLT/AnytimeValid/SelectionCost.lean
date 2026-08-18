/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Tactic
import FormalSLT.PACBayesKL

/-!
# Adaptive selection costs for finite e-value catalogs

This file records the elementary guardrail behind post-data selection from a
finite catalog of e-values.  If each nonnegative score has expectation at most
one, then a selector may inspect the observation and retain an index only after
the selected score is multiplied by its predeclared weight.  Equivalently, a
simultaneous threshold for index `i` pays the reciprocal of that weight.

The results are finite weighted-sum statements.  They do not assert a new
concentration inequality or a new e-process construction.  Their purpose is to
make the standard union/Kraft cost explicit and reusable at the formal API
boundary.

The diagonal-spike construction proves sharpness: for any full-support finite
law `p`, score `i` pays out `1 / p i` only on observation `i`.  Every coordinate
has expectation exactly one, adaptive selection of the observed coordinate has
unweighted expectation equal to the catalog size, and multiplying by its
predeclared weight `p i` restores expectation one exactly.

Mathematical sources: Markov's inequality, the finite union bound, and the
weighted Bonferroni/Kraft allocation principle.
-/

namespace FormalSLT.AnytimeValid.SelectionCost

open Finset BigOperators
open FormalSLT.PACBayesKL

noncomputable section

variable {Omega I : Type*}

/-- Expectation under a finite real-valued probability mass function. -/
def finiteExpectation [Fintype Omega] (p : Omega -> Real) (X : Omega -> Real) : Real :=
  ∑ omega, p omega * X omega

/-- Mass of a decidable event under a finite real-valued probability mass function. -/
def finiteEventMass [Fintype Omega]
    (p : Omega -> Real) (event : Omega -> Prop) : Real := by
  classical
  exact ∑ omega, if event omega then p omega else 0

/-- A fixed weighted mixture of a finite score catalog. -/
def finiteScoreMixture [Fintype I]
    (weight : I -> Real) (score : I -> Omega -> Real) (omega : Omega) : Real :=
  ∑ i, weight i * score i omega

/-- The predeclared-weight correction applied to a data-selected score. -/
def selectedWeightedScore
    (weight : I -> Real) (score : I -> Omega -> Real)
    (select : Omega -> I) (omega : Omega) : Real :=
  weight (select omega) * score (select omega) omega

/-- Finite Markov inequality in weighted-sum form. -/
theorem finiteEventMass_upperTail_le_expectation_div
    [Fintype Omega]
    (p X : Omega -> Real)
    (hp_nonneg : forall omega, 0 <= p omega)
    (hX_nonneg : forall omega, 0 <= X omega)
    {threshold : Real} (hthreshold : 0 < threshold) :
    finiteEventMass p (fun omega => threshold <= X omega) <=
      finiteExpectation p X / threshold := by
  classical
  unfold finiteEventMass finiteExpectation
  rw [le_div_iff₀ hthreshold]
  calc
    (∑ omega, if threshold <= X omega then p omega else 0) * threshold =
        ∑ omega, (if threshold <= X omega then p omega else 0) * threshold := by
      rw [Finset.sum_mul]
    _ <= ∑ omega, p omega * X omega := by
      refine Finset.sum_le_sum (fun omega _ => ?_)
      by_cases hcross : threshold <= X omega
      · simp only [if_pos hcross]
        exact mul_le_mul_of_nonneg_left hcross (hp_nonneg omega)
      · simp only [if_neg hcross, zero_mul]
        exact mul_nonneg (hp_nonneg omega) (hX_nonneg omega)

/-- A nonnegative finite score with expectation at most one crosses `1 / alpha`
with mass at most `alpha`. -/
theorem finiteEventMass_upperTail_le_alpha
    [Fintype Omega]
    (p X : Omega -> Real) (hp : IsPMF p)
    (hX_nonneg : forall omega, 0 <= X omega)
    (hX_mean : finiteExpectation p X <= 1)
    {alpha : Real} (halpha : 0 < alpha) :
    finiteEventMass p (fun omega => 1 / alpha <= X omega) <= alpha := by
  have hthreshold : (0 : Real) < 1 / alpha := by positivity
  calc
    finiteEventMass p (fun omega => 1 / alpha <= X omega) <=
        finiteExpectation p X / (1 / alpha) :=
      finiteEventMass_upperTail_le_expectation_div
        p X hp.nonneg hX_nonneg hthreshold
    _ <= 1 / (1 / alpha) := div_le_div_of_nonneg_right hX_mean hthreshold.le
    _ = alpha := by field_simp

/-- Monotonicity of finite event mass under event inclusion. -/
theorem finiteEventMass_mono
    [Fintype Omega]
    (p : Omega -> Real) (hp_nonneg : forall omega, 0 <= p omega)
    {event event' : Omega -> Prop}
    (hsub : forall omega, event omega -> event' omega) :
    finiteEventMass p event <= finiteEventMass p event' := by
  classical
  unfold finiteEventMass
  refine Finset.sum_le_sum (fun omega _ => ?_)
  by_cases hevent : event omega
  · have hevent' := hsub omega hevent
    simp [hevent, hevent']
  · by_cases hevent' : event' omega
    · simp [hevent, hevent', hp_nonneg omega]
    · simp [hevent, hevent']

/-- A nonnegative mixture with total predeclared weight at most one has
expectation at most one whenever every component does. -/
theorem finiteScoreMixture_expectation_le_one
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (_hp : IsPMF p)
    (weight : I -> Real)
    (hweight_nonneg : forall i, 0 <= weight i)
    (hweight_sum : ∑ i, weight i <= 1)
    (score : I -> Omega -> Real)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1) :
    finiteExpectation p (finiteScoreMixture weight score) <= 1 := by
  classical
  unfold finiteExpectation finiteScoreMixture
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : I, ∑ omega : Omega, p omega * (weight i * score i omega)) =
        ∑ i : I, weight i * ∑ omega : Omega, p omega * score i omega := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun omega _ => ?_)
      ring
    _ <= ∑ i : I, weight i * 1 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_left (hscore_mean i) (hweight_nonneg i)
    _ = ∑ i, weight i := by simp
    _ <= 1 := hweight_sum

/-- A fixed nonnegative score mixture is pointwise nonnegative. -/
theorem finiteScoreMixture_nonneg
    [Fintype I]
    (weight : I -> Real) (hweight_nonneg : forall i, 0 <= weight i)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega) :
    forall omega, 0 <= finiteScoreMixture weight score omega := by
  intro omega
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hweight_nonneg i) (hscore_nonneg i omega)

/-- **Weighted adaptive-selection guardrail.** A selector may inspect the
observation, but the selected score must retain its predeclared weight. -/
theorem selectedWeightedScore_expectation_le_one
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (hp : IsPMF p)
    (weight : I -> Real)
    (hweight_nonneg : forall i, 0 <= weight i)
    (hweight_sum : ∑ i, weight i <= 1)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (select : Omega -> I) :
    finiteExpectation p (selectedWeightedScore weight score select) <= 1 := by
  classical
  calc
    finiteExpectation p (selectedWeightedScore weight score select) <=
        finiteExpectation p (finiteScoreMixture weight score) := by
      unfold finiteExpectation
      refine Finset.sum_le_sum (fun omega _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg omega)
      unfold selectedWeightedScore finiteScoreMixture
      exact Finset.single_le_sum
        (f := fun i => weight i * score i omega)
        (fun i _ => mul_nonneg (hweight_nonneg i) (hscore_nonneg i omega))
        (Finset.mem_univ (select omega))
    _ <= 1 := finiteScoreMixture_expectation_le_one
      p hp weight hweight_nonneg hweight_sum score hscore_mean

/-- PMF-weighted specialization of the adaptive-selection guardrail. -/
theorem selectedWeightedScore_expectation_le_one_of_pmf
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (hp : IsPMF p)
    (weight : I -> Real) (hweight : IsPMF weight)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (select : Omega -> I) :
    finiteExpectation p (selectedWeightedScore weight score select) <= 1 :=
  selectedWeightedScore_expectation_le_one p hp weight hweight.nonneg
    hweight.sum_one.le score hscore_nonneg hscore_mean select

/-- Exact finite weighted union/Markov bound.  Threshold `cost i` spends
reciprocal budget `1 / cost i`; summing these budgets is the Kraft condition. -/
theorem simultaneous_upperTail_mass_le_sum_reciprocal
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (hp : IsPMF p)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (cost : I -> Real) (hcost_pos : forall i, 0 < cost i) :
    finiteEventMass p (fun omega => exists i, cost i <= score i omega) <=
      ∑ i : I, 1 / cost i := by
  classical
  letI : DecidablePred (fun omega : Omega => exists i, cost i <= score i omega) :=
    fun _ => Classical.propDecidable _
  calc
    finiteEventMass p (fun omega => exists i, cost i <= score i omega) <=
        ∑ omega : Omega, ∑ i : I,
          if cost i <= score i omega then p omega else 0 := by
      unfold finiteEventMass
      refine Finset.sum_le_sum (fun omega _ => ?_)
      change (if (exists i, cost i <= score i omega) then p omega else 0) <=
        ∑ i : I, if cost i <= score i omega then p omega else 0
      by_cases hcross : exists i, cost i <= score i omega
      · have hexists := hcross
        obtain ⟨i, hi⟩ := hcross
        have hnonneg : forall j, j ∈ (univ : Finset I) ->
            0 <= (if cost j <= score j omega then p omega else 0) := by
          intro j _hj
          by_cases hj : cost j <= score j omega
          · simp [hj, hp.nonneg omega]
          · simp [hj]
        have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
        simpa [hexists, hi] using hsingle
      · have hsum_nonneg : 0 <= ∑ i : I,
            if cost i <= score i omega then p omega else 0 := by
          exact Finset.sum_nonneg fun i _ => by
            by_cases hi : cost i <= score i omega
            · simp [hi, hp.nonneg omega]
            · simp [hi]
        simpa [hcross] using hsum_nonneg
    _ = ∑ i : I, finiteEventMass p (fun omega => cost i <= score i omega) := by
      unfold finiteEventMass
      rw [Finset.sum_comm]
    _ <= ∑ i : I, 1 / cost i := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      calc
        finiteEventMass p (fun omega => cost i <= score i omega) <=
            finiteExpectation p (score i) / cost i :=
          finiteEventMass_upperTail_le_expectation_div
            p (score i) hp.nonneg (hscore_nonneg i) (hcost_pos i)
        _ <= 1 / cost i :=
          div_le_div_of_nonneg_right (hscore_mean i) (hcost_pos i).le

/-- **Kraft/Bonferroni selection penalty.** If reciprocal costs sum to at most
one, then thresholds `cost i / alpha` hold simultaneously with failure mass at
most `alpha`. -/
theorem simultaneous_kraft_upperTail_mass_le_alpha
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (hp : IsPMF p)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (cost : I -> Real) (hcost_pos : forall i, 0 < cost i)
    (hcost_kraft : (∑ i : I, 1 / cost i) <= 1)
    {alpha : Real} (halpha : 0 < alpha) :
    finiteEventMass p
        (fun omega => exists i, cost i / alpha <= score i omega) <= alpha := by
  have hscaled_pos : forall i, 0 < cost i / alpha := fun i =>
    div_pos (hcost_pos i) halpha
  calc
    finiteEventMass p (fun omega => exists i, cost i / alpha <= score i omega) <=
        ∑ i : I, 1 / (cost i / alpha) :=
      simultaneous_upperTail_mass_le_sum_reciprocal
        p hp score hscore_nonneg hscore_mean (fun i => cost i / alpha) hscaled_pos
    _ = alpha * ∑ i : I, 1 / cost i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      field_simp [(hcost_pos i).ne', halpha.ne']
    _ <= alpha * 1 := mul_le_mul_of_nonneg_left hcost_kraft halpha.le
    _ = alpha := mul_one alpha

/-- Selector form of the Kraft bound.  The selector may depend arbitrarily on
the observation because the event above is simultaneous over the catalog. -/
theorem selected_kraft_upperTail_mass_le_alpha
    [Fintype Omega] [Fintype I]
    (p : Omega -> Real) (hp : IsPMF p)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (cost : I -> Real) (hcost_pos : forall i, 0 < cost i)
    (hcost_kraft : (∑ i : I, 1 / cost i) <= 1)
    (select : Omega -> I)
    {alpha : Real} (halpha : 0 < alpha) :
    finiteEventMass p
        (fun omega => cost (select omega) / alpha <= score (select omega) omega) <= alpha := by
  classical
  calc
    finiteEventMass p
        (fun omega => cost (select omega) / alpha <= score (select omega) omega) <=
        finiteEventMass p
          (fun omega => exists i, cost i / alpha <= score i omega) := by
      exact finiteEventMass_mono p hp.nonneg fun omega hselected =>
        ⟨select omega, hselected⟩
    _ <= alpha := simultaneous_kraft_upperTail_mass_le_alpha
      p hp score hscore_nonneg hscore_mean cost hcost_pos hcost_kraft halpha

/-! ## Sharp diagonal construction -/

/-- Coordinate `i` pays `1 / p i` only when observation `i` occurs. -/
def diagonalSpike [DecidableEq Omega]
    (p : Omega -> Real) (i omega : Omega) : Real :=
  if i = omega then 1 / p omega else 0

/-- Every diagonal spike is nonnegative under a full-support law. -/
theorem diagonalSpike_nonneg
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) :
    forall i omega, 0 <= diagonalSpike p i omega := by
  intro i omega
  by_cases h : i = omega
  · subst i
    simp [diagonalSpike, (hp.pos omega).le]
  · simp [diagonalSpike, h]

/-- Every coordinate of the diagonal construction has expectation exactly one. -/
theorem diagonalSpike_expectation_eq_one
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) (i : Omega) :
    finiteExpectation p (diagonalSpike p i) = 1 := by
  unfold finiteExpectation diagonalSpike
  simp [(hp.pos i).ne']

/-- The weighted selected diagonal spike is exactly one on every observation. -/
theorem diagonalSpike_selectedWeightedScore_eq_one
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) (omega : Omega) :
    selectedWeightedScore p (diagonalSpike p) id omega = 1 := by
  simp [selectedWeightedScore, diagonalSpike, (hp.pos omega).ne']

/-- The adaptive-selection expectation bound is attained with equality by the
diagonal construction. -/
theorem diagonalSpike_selectedWeightedScore_expectation_eq_one
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) :
    finiteExpectation p (selectedWeightedScore p (diagonalSpike p) id) = 1 := by
  unfold finiteExpectation
  simp_rw [diagonalSpike_selectedWeightedScore_eq_one p hp]
  simpa using hp.toIsPMF.sum_one

/-- Without the predeclared weight, selecting the observed diagonal spike
inflates expectation from one to the exact catalog size. -/
theorem diagonalSpike_selected_expectation_eq_card
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) :
    finiteExpectation p (fun omega => diagonalSpike p omega omega) =
      Fintype.card Omega := by
  unfold finiteExpectation diagonalSpike
  calc
    (∑ omega : Omega, p omega * (if omega = omega then 1 / p omega else 0)) =
        ∑ _omega : Omega, (1 : Real) := by
      refine Finset.sum_congr rfl (fun omega _ => ?_)
      simp [(hp.pos omega).ne']
    _ = Fintype.card Omega := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp

/-- The diagonal spike makes the reciprocal-cost union bound exact: every
observation crosses its own cost `1 / p i`, and the reciprocal costs sum to one. -/
theorem diagonalSpike_reciprocal_union_sharp
    [Fintype Omega] [DecidableEq Omega]
    (p : Omega -> Real) (hp : IsFullSupportPMF p) :
    finiteEventMass p
        (fun omega => exists i, (1 / p i) <= diagonalSpike p i omega) = 1 /\
      (∑ i : Omega, 1 / (1 / p i)) = 1 := by
  letI : DecidablePred
      (fun omega : Omega => exists i, (1 / p i) <= diagonalSpike p i omega) :=
    fun _ => Classical.propDecidable _
  constructor
  · unfold finiteEventMass
    have hall : forall omega, exists i, (1 / p i) <= diagonalSpike p i omega := by
      intro omega
      exact ⟨omega, by simp [diagonalSpike]⟩
    calc
      (∑ omega : Omega,
          if exists i, (1 / p i) <= diagonalSpike p i omega then p omega else 0) =
          ∑ omega : Omega, p omega := by
        refine Finset.sum_congr rfl (fun omega _ => ?_)
        rw [if_pos (hall omega)]
      _ = 1 := hp.toIsPMF.sum_one
  · calc
      (∑ i : Omega, 1 / (1 / p i)) = ∑ i : Omega, p i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp [(hp.pos i).ne']
      _ = 1 := hp.toIsPMF.sum_one

/-! ## Symmetric finite catalogs -/

/-- With equal allocation over a nonempty catalog, the exact multiplicative
selection cost is the catalog cardinality. -/
theorem symmetric_simultaneous_upperTail_mass_le_alpha
    [Fintype Omega] [Fintype I] [Nonempty I]
    (p : Omega -> Real) (hp : IsPMF p)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    {alpha : Real} (halpha : 0 < alpha) :
    finiteEventMass p
        (fun omega => exists i,
          (Fintype.card I : Real) / alpha <= score i omega) <= alpha := by
  have hcard_pos : (0 : Real) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hkraft : (∑ _i : I, 1 / (Fintype.card I : Real)) <= 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
    norm_num
  exact simultaneous_kraft_upperTail_mass_le_alpha
    p hp score hscore_nonneg hscore_mean
    (fun _i : I => (Fintype.card I : Real)) (fun _ => hcard_pos) hkraft halpha

/-- Selector form of the symmetric catalog bound. -/
theorem symmetric_selected_upperTail_mass_le_alpha
    [Fintype Omega] [Fintype I] [Nonempty I]
    (p : Omega -> Real) (hp : IsPMF p)
    (score : I -> Omega -> Real)
    (hscore_nonneg : forall i omega, 0 <= score i omega)
    (hscore_mean : forall i, finiteExpectation p (score i) <= 1)
    (select : Omega -> I)
    {alpha : Real} (halpha : 0 < alpha) :
    finiteEventMass p
        (fun omega => (Fintype.card I : Real) / alpha <=
          score (select omega) omega) <= alpha := by
  have hcard_pos : (0 : Real) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hkraft : (∑ _i : I, 1 / (Fintype.card I : Real)) <= 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
    norm_num
  exact selected_kraft_upperTail_mass_le_alpha
    p hp score hscore_nonneg hscore_mean
    (fun _i : I => (Fintype.card I : Real)) (fun _ => hcard_pos) hkraft select halpha

/-- The symmetric multiplicative threshold contributes exactly `log |I|` on
the logarithmic scale, in addition to the confidence term `log (1 / alpha)`. -/
theorem symmetric_log_selection_penalty
    [Fintype I] [Nonempty I]
    {alpha : Real} (halpha : 0 < alpha) :
    Real.log ((Fintype.card I : Real) / alpha) =
      Real.log (Fintype.card I : Real) + Real.log (1 / alpha) := by
  have hcard_ne : (Fintype.card I : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hcard_ne halpha.ne', Real.log_div one_ne_zero halpha.ne']
  simp
  ring

end

end FormalSLT.AnytimeValid.SelectionCost
