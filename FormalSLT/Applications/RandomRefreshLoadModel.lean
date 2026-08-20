/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin

/-!
# Twenty-state random-refresh load model

This module supplies the finite model used by the multistate stationary-risk
application.  The state space is `Fin 20`, read as five load levels crossed
with four regimes.  Its deterministic component advances once around the
twenty-state cycle; with the remaining mass, the chain refreshes uniformly.

Three predeclared candidate kernels use deterministic weights `1/8`, `1/4`,
and `3/8`.  Their invariant law is uniform and their exact finite Dobrushin
coefficients are the corresponding deterministic weights.

The score catalog contains four binary Brier losses for predicting whether
the next state is in load level four: a constant predictor, a load-only
predictor, the correctly specified load--regime predictor, and a deliberately
early predictor.  Exact stationary risks and candidate-specific centered
row-risk oscillation envelopes are proved below.

This is the model layer only.  No observed path, transition-confidence
radius, selected depth, or final high-probability application claim is made
in this module.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics.RandomRefreshLoadModel

noncomputable section

/-- Five load levels crossed with four regimes.  The quotient and remainder
by four recover the two coordinates. -/
abbrev State := Fin 20

@[simp] theorem state_card : Fintype.card State = 20 := rfl

/-- Load coordinate in `{0, ..., 4}`. -/
def loadLevel (x : State) : Fin 5 :=
  ⟨x.val / 4, by omega⟩

/-- Regime coordinate in `{0, ..., 3}`. -/
def regime (x : State) : Fin 4 :=
  ⟨x.val % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The load and regime coordinates reconstruct the encoded state. -/
theorem four_mul_loadLevel_add_regime (x : State) :
    4 * (loadLevel x).val + (regime x).val = x.val := by
  simpa [loadLevel, regime, mul_comm] using Nat.div_add_mod x.val 4

/-- One step around the lexicographic load--regime cycle. -/
def successorEquiv : State ≃ State := Equiv.addRight 1

/-- The deterministic successor used by every candidate kernel. -/
def successor (x : State) : State := successorEquiv x

@[simp] theorem successorEquiv_apply (x : State) :
    successorEquiv x = successor x := rfl

@[simp] theorem successor_val (x : State) :
    (successor x).val = (x.val + 1) % 20 := rfl

/-- The three predeclared deterministic-component weights. -/
inductive Candidate where
  | low
  | nominal
  | high
deriving DecidableEq, Fintype, Repr

instance : Nonempty Candidate := ⟨Candidate.nominal⟩

/-- Deterministic-component weight as a nonnegative real. -/
def candidateGammaNN : Candidate → NNReal
  | .low => 1 / 8
  | .nominal => 1 / 4
  | .high => 3 / 8

/-- Per-state uniform-refresh mass. -/
def candidateBaseNN : Candidate → NNReal
  | .low => 7 / 160
  | .nominal => 3 / 80
  | .high => 1 / 32

/-- Deterministic-component weight as a real number. -/
def candidateGamma (c : Candidate) : ℝ := candidateGammaNN c

/-- Per-state uniform-refresh mass as a real number. -/
def candidateBase (c : Candidate) : ℝ := candidateBaseNN c

theorem twenty_mul_candidateBase_add_gamma (c : Candidate) :
    20 * candidateBase c + candidateGamma c = 1 := by
  cases c <;> norm_num [candidateBase, candidateBaseNN,
    candidateGamma, candidateGammaNN]

/-- Candidate kernel `gamma * delta_successor + (1-gamma) * uniform`. -/
def refreshKernel (c : Candidate) (x : State) : PMF State :=
  PMF.ofFintype
    (fun y ↦ (candidateBaseNN c : ENNReal) +
      if y = successor x then (candidateGammaNN c : ENNReal) else 0)
    (by
      have hmassNN :
          (20 : NNReal) * candidateBaseNN c + candidateGammaNN c = 1 := by
        cases c <;> norm_num [candidateBaseNN, candidateGammaNN]
      have hmass := congrArg (fun q : NNReal ↦ (q : ENNReal)) hmassNN
      simpa [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Finset.sum_ite_eq,
        state_card] using hmass)

@[simp] theorem refreshKernel_apply_toReal
    (c : Candidate) (x y : State) :
    (refreshKernel c x y).toReal =
      candidateBase c + if y = successor x then candidateGamma c else 0 := by
  unfold refreshKernel
  rw [PMF.ofFintype_apply]
  by_cases h : y = successor x
  · simp only [h, if_true]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp [candidateBase, candidateGamma]
  · simp only [h, if_false]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp [candidateBase]

/-- Uniform stationary law on the twenty load--regime states. -/
def uniformLaw : PMF State :=
  PMF.ofFintype (fun _ ↦ ((1 / 20 : NNReal) : ENNReal)) (by
    calc
      ∑ _x : State, ((1 / 20 : NNReal) : ENNReal) =
          (20 : ENNReal) * ((1 / 20 : NNReal) : ENNReal) := by
            simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = 1 := by
        rw [ENNReal.coe_div (by norm_num : (20 : NNReal) ≠ 0)]
        simpa [div_eq_mul_inv] using
          (ENNReal.mul_inv_cancel (a := (20 : ENNReal))
            (by norm_num) (by norm_num)))

@[simp] theorem uniformLaw_apply_toReal (x : State) :
    (uniformLaw x).toReal = 1 / 20 := by
  norm_num [uniformLaw, PMF.ofFintype_apply]

private theorem successor_indicator_sum (c : Candidate) (y : State) :
    ∑ x : State, (if y = successor x then candidateGamma c else 0) =
      candidateGamma c := by
  let f : State → ℝ := fun z ↦ if y = z then candidateGamma c else 0
  calc
    ∑ x : State, (if y = successor x then candidateGamma c else 0) =
        ∑ x : State, f (successorEquiv x) := by rfl
    _ = ∑ z : State, f z := Equiv.sum_comp successorEquiv f
    _ = candidateGamma c := by simp [f]

private theorem uniform_refresh_incoming_mass (c : Candidate) (y : State) :
    ∑ x : State,
        (uniformLaw x).toReal * (refreshKernel c x y).toReal =
      (uniformLaw y).toReal := by
  simp_rw [uniformLaw_apply_toReal, refreshKernel_apply_toReal]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, state_card,
    successor_indicator_sum]
  have hmass := twenty_mul_candidateBase_add_gamma c
  nlinarith

/-- The uniform law is invariant for every refresh candidate. -/
theorem uniformLaw_invariant (c : Candidate) :
    IsInvariantPMF (refreshKernel c) uniformLaw := by
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (uniformLaw.bind (refreshKernel c)) y)
    (PMF.apply_ne_top uniformLaw y)).mp
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro x _hx
    exact ENNReal.mul_ne_top (PMF.apply_ne_top uniformLaw x)
      (PMF.apply_ne_top (refreshKernel c x) y))]
  simpa only [ENNReal.toReal_mul] using uniform_refresh_incoming_mass c y

/-- Exact row total variation.  Distinct rows differ only at their two
permuted successor atoms. -/
theorem refreshKernel_rowTotalVariation (c : Candidate) (x y : State) :
    finitePMFTotalVariation (refreshKernel c x) (refreshKernel c y) =
      if x = y then 0 else candidateGamma c := by
  by_cases hxy : x = y
  · subst y
    simp [finitePMFTotalVariation]
  · have hsucc : successor x ≠ successor y := by
      exact fun h ↦ hxy (successorEquiv.injective h)
    have hsucc' : successor y ≠ successor x := Ne.symm hsucc
    have hgamma : 0 ≤ candidateGamma c := by
      cases c <;> norm_num [candidateGamma, candidateGammaNN]
    have hpoint : ∀ z : State,
        |(refreshKernel c x z).toReal - (refreshKernel c y z).toReal| =
          (if z = successor x then candidateGamma c else 0) +
            (if z = successor y then candidateGamma c else 0) := by
      intro z
      rw [refreshKernel_apply_toReal, refreshKernel_apply_toReal]
      by_cases hzx : z = successor x
      · have hzy : z ≠ successor y := by
          intro h
          exact hsucc (hzx.symm.trans h)
        simp [hzx, hsucc, abs_of_nonneg hgamma]
      · by_cases hzy : z = successor y
        · simp [hzy, hsucc', abs_of_nonneg hgamma]
        · simp [hzx, hzy]
    rw [if_neg hxy]
    unfold finitePMFTotalVariation
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

/-- Exact finite Dobrushin coefficient of each candidate kernel. -/
theorem refreshKernel_dobrushinCoefficient (c : Candidate) :
    finiteDobrushinCoefficient (refreshKernel c) = candidateGamma c := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    rw [refreshKernel_rowTotalVariation]
    split_ifs
    · cases c <;> norm_num [candidateGamma, candidateGammaNN]
    · exact le_rfl
  · have h := finitePMFTotalVariation_le_finiteDobrushinCoefficient
      (refreshKernel c) (0 : State) (1 : State)
    rw [refreshKernel_rowTotalVariation] at h
    norm_num at h
    exact h

/-- All three candidates are strict oscillation contractions. -/
theorem refreshKernel_dobrushinCoefficient_lt_one (c : Candidate) :
    finiteDobrushinCoefficient (refreshKernel c) < 1 := by
  rw [refreshKernel_dobrushinCoefficient]
  cases c <;> norm_num [candidateGamma, candidateGammaNN]

/-- Exact row-TV distance from the nominal kernel to each predeclared
candidate.  Both neighboring candidates are `19/160` away in every row. -/
def nominalCandidateRowTV : Candidate → ℝ
  | .low => 19 / 160
  | .nominal => 0
  | .high => 19 / 160

/-- The nominal-to-candidate row-TV certificate is independent of the row. -/
theorem refreshKernel_nominalCandidateRowTV (c : Candidate) (x : State) :
    finitePMFTotalVariation
        (refreshKernel Candidate.nominal x) (refreshKernel c x) =
      nominalCandidateRowTV c := by
  fin_cases c
  · unfold finitePMFTotalVariation
    have hpoint : ∀ z : State,
        |(refreshKernel Candidate.nominal x z).toReal -
            (refreshKernel Candidate.low x z).toReal| =
          1 / 160 + if z = successor x then 18 / 160 else 0 := by
      intro z
      rw [refreshKernel_apply_toReal, refreshKernel_apply_toReal]
      by_cases h : z = successor x <;>
        simp [h, candidateBase, candidateBaseNN,
          candidateGamma, candidateGammaNN] <;> norm_num
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp [nominalCandidateRowTV, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    norm_num
  · simp [finitePMFTotalVariation, nominalCandidateRowTV]
  · unfold finitePMFTotalVariation
    have hpoint : ∀ z : State,
        |(refreshKernel Candidate.nominal x z).toReal -
            (refreshKernel Candidate.high x z).toReal| =
          1 / 160 + if z = successor x then 18 / 160 else 0 := by
      intro z
      rw [refreshKernel_apply_toReal, refreshKernel_apply_toReal]
      by_cases h : z = successor x <;>
        simp [h, candidateBase, candidateBaseNN,
          candidateGamma, candidateGammaNN] <;> norm_num
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp [nominalCandidateRowTV, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    norm_num

/-- The four predeclared overload predictors. -/
inductive Predictor where
  | constant
  | loadOnly
  | oracle
  | early
deriving DecidableEq, Fintype, Repr

instance : Nonempty Predictor := ⟨Predictor.constant⟩

/-- Indicator that the next state is in load level four. -/
def overloadIndicator (y : State) : ℝ := if 16 ≤ y.val then 1 else 0

/-- Overload is exactly load level four. -/
theorem overloadIndicator_eq_one_iff (y : State) :
    overloadIndicator y = 1 ↔ loadLevel y = 4 := by
  simp only [overloadIndicator, loadLevel]
  constructor
  · intro h
    split at h
    · apply Fin.ext
      change y.val / 4 = 4
      omega
    · norm_num at h
  · intro h
    have hval : y.val / 4 = 4 := by
      exact Fin.ext_iff.mp h
    rw [if_pos]
    omega

/-- Predicted probability of next-step overload.  The early predictor is
`3/20 + (1/4) * 1{loadLevel (successor x) = 3}`: on this lexicographic cycle,
that indicator is exactly `11 ≤ x.val ∧ x.val ≤ 14`. -/
def predictorProbability : Predictor → State → ℝ
  | .constant, _ => 1 / 5
  | .loadOnly, x =>
      if x.val < 12 then 3 / 20
      else if x.val < 16 then 17 / 80
      else 27 / 80
  | .oracle, x =>
      if 16 ≤ (successor x).val then 2 / 5 else 3 / 20
  | .early, x =>
      if 11 ≤ x.val ∧ x.val ≤ 14 then 2 / 5 else 3 / 20

/-- Binary Brier loss for next-step overload prediction. -/
def brierScore (i : Predictor) : MarkovTransitionScore State :=
  fun x y ↦ (predictorProbability i x - overloadIndicator y) ^ 2

/-- Every overload Brier score is in the unit interval. -/
theorem brierScore_mem_Icc :
    ∀ i x y, brierScore i x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i x y
  fin_cases i <;>
    simp only [brierScore, predictorProbability, overloadIndicator] <;>
    split_ifs <;> norm_num

/-- Candidate probability of overload on the next transition. -/
def candidateOverloadProbability (c : Candidate) (x : State) : ℝ :=
  4 * candidateBase c +
    if 16 ≤ (successor x).val then candidateGamma c else 0

/-- The oracle predictor is the exact nominal one-step overload
probability. -/
theorem oracle_is_nominalOverloadProbability (x : State) :
    predictorProbability Predictor.oracle x =
      candidateOverloadProbability Candidate.nominal x := by
  simp only [predictorProbability, candidateOverloadProbability]
  split_ifs <;>
    norm_num [candidateBase, candidateBaseNN,
      candidateGamma, candidateGammaNN]

private theorem overloadIndicator_sum :
    ∑ y : State, overloadIndicator y = 4 := by
  have hcard : ((Finset.univ.filter fun y : State ↦ 16 ≤ y.val).card) = 4 := by
    decide
  simp [overloadIndicator, hcard]

private theorem refreshKernel_overloadExpectation
    (c : Candidate) (x : State) :
    ∑ y : State,
        (refreshKernel c x y).toReal * overloadIndicator y =
      candidateOverloadProbability c x := by
  simp_rw [refreshKernel_apply_toReal, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, overloadIndicator_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [candidateOverloadProbability, overloadIndicator, mul_comm]

/-- Closed-form candidate row risk of a Brier predictor. -/
def brierRowRisk (c : Candidate) (i : Predictor) (x : State) : ℝ :=
  let p := predictorProbability i x
  p ^ 2 + candidateOverloadProbability c x * (1 - 2 * p)

theorem markovRowRisk_brierScore
    (c : Candidate) (i : Predictor) (x : State) :
    markovRowRisk (refreshKernel c) (brierScore i) x =
      brierRowRisk c i x := by
  let p := predictorProbability i x
  have hscore : ∀ y : State,
      brierScore i x y = p ^ 2 + overloadIndicator y * (1 - 2 * p) := by
    intro y
    by_cases h : 16 ≤ y.val
    · simp [brierScore, overloadIndicator, p, h]
      ring
    · simp [brierScore, overloadIndicator, p, h]
  unfold markovRowRisk brierRowRisk
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  simp_rw [hscore, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, finitePMF_real_mass_sum,
    one_mul]
  conv_rhs => rw [show predictorProbability i x = p by rfl]
  congr 1
  calc
    ∑ y : State,
        (refreshKernel c x y).toReal *
          (overloadIndicator y * (1 - 2 * p)) =
        ∑ y : State,
          ((refreshKernel c x y).toReal * overloadIndicator y) *
            (1 - 2 * p) := by
              apply Finset.sum_congr rfl
              intro y _hy
              ring
    _ = (∑ y : State,
          (refreshKernel c x y).toReal * overloadIndicator y) *
            (1 - 2 * p) := by rw [Finset.sum_mul]
    _ = candidateOverloadProbability c x * (1 - 2 * p) := by
      rw [refreshKernel_overloadExpectation]

/-- Closed-form stationary-risk table for every candidate and predictor. -/
def candidateStationaryRiskValue : Candidate → Predictor → ℝ
  | .low, .constant => 4 / 25
  | .low, .loadOnly => 4 / 25
  | .low, .oracle => 4 / 25
  | .low, .early => 69 / 400
  | .nominal, .constant => 4 / 25
  | .nominal, .loadOnly => 99 / 640
  | .nominal, .oracle => 3 / 20
  | .nominal, .early => 7 / 40
  | .high, .constant => 4 / 25
  | .high, .loadOnly => 239 / 1600
  | .high, .oracle => 7 / 50
  | .high, .early => 71 / 400

/-- Exact stationary risks under the low-gamma candidate. -/
theorem low_stationaryRisk (i : Predictor) :
    stationaryMarkovRisk (refreshKernel Candidate.low) uniformLaw
        (brierScore i) =
      candidateStationaryRiskValue Candidate.low i := by
  unfold stationaryMarkovRisk
  simp_rw [markovRowRisk_brierScore]
  simp only [PMF.integral_eq_sum, smul_eq_mul, uniformLaw_apply_toReal]
  fin_cases i <;>
    norm_num [candidateStationaryRiskValue, brierRowRisk,
      predictorProbability, candidateOverloadProbability,
      candidateBase, candidateBaseNN, candidateGamma, candidateGammaNN,
      successor_val, Fin.sum_univ_succ]

/-- Exact stationary risks under the high-gamma candidate. -/
theorem high_stationaryRisk (i : Predictor) :
    stationaryMarkovRisk (refreshKernel Candidate.high) uniformLaw
        (brierScore i) =
      candidateStationaryRiskValue Candidate.high i := by
  unfold stationaryMarkovRisk
  simp_rw [markovRowRisk_brierScore]
  simp only [PMF.integral_eq_sum, smul_eq_mul, uniformLaw_apply_toReal]
  fin_cases i <;>
    norm_num [candidateStationaryRiskValue, brierRowRisk,
      predictorProbability, candidateOverloadProbability,
      candidateBase, candidateBaseNN, candidateGamma, candidateGammaNN,
      successor_val, Fin.sum_univ_succ]

/-- Exact stationary risks under the nominal kernel and uniform law. -/
theorem nominal_stationaryRisk (i : Predictor) :
    stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
        (brierScore i) =
      match i with
      | .constant => 4 / 25
      | .loadOnly => 99 / 640
      | .oracle => 3 / 20
      | .early => 7 / 40 := by
  unfold stationaryMarkovRisk
  simp_rw [markovRowRisk_brierScore]
  simp only [PMF.integral_eq_sum, smul_eq_mul, uniformLaw_apply_toReal]
  fin_cases i <;>
    norm_num [brierRowRisk, predictorProbability,
      candidateOverloadProbability, candidateBase, candidateBaseNN,
      candidateGamma, candidateGammaNN, successor_val,
      Fin.sum_univ_succ]

/-- Exact stationary risks for the complete three-kernel, four-predictor
catalog under the common uniform invariant law. -/
theorem candidate_stationaryRisk (c : Candidate) (i : Predictor) :
    stationaryMarkovRisk (refreshKernel c) uniformLaw (brierScore i) =
      candidateStationaryRiskValue c i := by
  cases c
  · exact low_stationaryRisk i
  · fin_cases i <;>
      simpa [candidateStationaryRiskValue] using nominal_stationaryRisk _
  · exact high_stationaryRisk i

/-- Sharp common row-risk oscillation envelope for each candidate. -/
def candidateOscillation : Candidate → ℝ
  | .low => 7 / 80
  | .nominal => 7 / 40
  | .high => 21 / 80

private def candidateRowRiskLower : Candidate → ℝ
  | .low => 29 / 200
  | .nominal => 51 / 400
  | .high => 11 / 100

private theorem brierRowRisk_bounds (c : Candidate) (i : Predictor) (x : State) :
    brierRowRisk c i x ∈ Set.Icc
      (candidateRowRiskLower c)
      (candidateRowRiskLower c + candidateOscillation c) := by
  fin_cases c <;> fin_cases i <;>
    simp only [brierRowRisk, predictorProbability,
      candidateOverloadProbability, candidateRowRiskLower,
      candidateOscillation, candidateBase, candidateBaseNN,
      candidateGamma, candidateGammaNN] <;>
    split_ifs <;> norm_num

/-- Candidate-specific envelope required by the stationary Poisson catalog. -/
theorem brierScore_centeredOscillation_le (c : Candidate) (i : Predictor) :
    finiteOscillation
        (centeredMarkovRowRisk (refreshKernel c) uniformLaw (brierScore i)) ≤
      candidateOscillation c := by
  apply finiteOscillation_le
  intro x y
  rw [centeredMarkovRowRisk, centeredMarkovRowRisk,
    markovRowRisk_brierScore, markovRowRisk_brierScore]
  have hx := brierRowRisk_bounds c i x
  have hy := brierRowRisk_bounds c i y
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The deliberately early predictor attains the declared common envelope,
so the candidate-specific constants are not merely loose unit bounds. -/
theorem early_centeredOscillation_eq (c : Candidate) :
    finiteOscillation
        (centeredMarkovRowRisk (refreshKernel c) uniformLaw
          (brierScore Predictor.early)) = candidateOscillation c := by
  apply le_antisymm
  · exact brierScore_centeredOscillation_le c Predictor.early
  · have h := abs_sub_le_finiteOscillation
      (centeredMarkovRowRisk (refreshKernel c) uniformLaw
        (brierScore Predictor.early)) (0 : State) (15 : State)
    rw [centeredMarkovRowRisk, centeredMarkovRowRisk,
      markovRowRisk_brierScore, markovRowRisk_brierScore] at h
    cases c <;>
      norm_num [brierRowRisk, predictorProbability,
        candidateOverloadProbability, candidateOscillation,
        candidateBase, candidateBaseNN, candidateGamma, candidateGammaNN,
        successor_val] at h ⊢ <;>
      exact h

end

end FormalSLT.StochasticDynamics.RandomRefreshLoadModel
