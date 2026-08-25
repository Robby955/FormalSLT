/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AllocationLogLog
import FormalSLT.AnytimeValid.DyadicEpochCS

/-!
# Polynomially allocated geometric-epoch sub-Gamma confidence sequence

This file closes the gap between the finite-grid optimized-tilt theorem and
the checked polynomial allocation.  Epoch `j` receives confidence weight
`1 / ((j+1)(j+2))`, uses the geometric floor `4^(j+1)`, and predeclares the
single tilt that is optimal at that floor for the allocated two-sided budget.

Countable subadditivity gives one event of mass at most `delta`.  Outside that
event, every `n >= 4` is controlled by the tilt selected from its geometric
epoch.  The exact epoch budget is

`log (2 / delta) + log (j+1) + log (j+2)`,

so the confidence price is of iterated-logarithm order when
`j = (Nat.log 4 n).pred`.  This is an allocated fixed-tilt stitch; it does not
claim that the countable union is itself an e-process.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

open AllocationLogLog

noncomputable section

/-- Lower endpoint of geometric epoch `j`. -/
def polynomialGeometricEpochFloor (j : ℕ) : ℕ :=
  4 ^ (j + 1)

/-- Exclusive upper endpoint of geometric epoch `j`. -/
def polynomialGeometricEpochHorizon (j : ℕ) : ℕ :=
  4 ^ (j + 2)

/-- Epoch selected at sample size `n >= 4`. -/
def polynomialGeometricEpochIndex (n : ℕ) : ℕ :=
  (Nat.log 4 n).pred

theorem polynomialGeometricEpochFloor_pos (j : ℕ) :
    0 < polynomialGeometricEpochFloor j := by
  unfold polynomialGeometricEpochFloor
  positivity

theorem polynomialGeometricEpochHorizon_eq_four_mul_floor (j : ℕ) :
    polynomialGeometricEpochHorizon j =
      4 * polynomialGeometricEpochFloor j := by
  unfold polynomialGeometricEpochHorizon polynomialGeometricEpochFloor
  rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
  omega

/-- Every `n >= 4` lies in the selected half-open geometric epoch. -/
theorem polynomialGeometricEpochIndex_spec {n : ℕ} (hn : 4 <= n) :
    polynomialGeometricEpochFloor (polynomialGeometricEpochIndex n) <= n ∧
      n < polynomialGeometricEpochHorizon (polynomialGeometricEpochIndex n) := by
  let r := Nat.log 4 n
  have hrpos : 0 < r := Nat.log_pos (by norm_num) hn
  have hpred : r.pred + 1 = r := Nat.succ_pred_eq_of_pos hrpos
  constructor
  · change 4 ^ (r.pred + 1) <= n
    rw [hpred]
    exact Nat.pow_log_le_self 4 (by omega)
  · have hpred' : r.pred + 2 = r + 1 := by omega
    change n < 4 ^ (r.pred + 2)
    rw [hpred']
    exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- The confidence budget for epoch `j`, including the two-sided split. -/
def polynomialGeometricEpochBudget (delta : ℝ) (j : ℕ) : ℝ :=
  Real.log (1 / ((delta * polynomialEpochWeight j) / 2))

/-- Exact decomposition of the epoch budget into confidence and allocation
costs. -/
theorem polynomialGeometricEpochBudget_eq
    {delta : ℝ} (hdelta : 0 < delta) (j : ℕ) :
    polynomialGeometricEpochBudget delta j =
      Real.log (2 / delta) + Real.log ((j : ℝ) + 1) +
        Real.log ((j : ℝ) + 2) := by
  have hreciprocal :
      1 / ((delta * polynomialEpochWeight j) / 2) =
        (2 / delta) * (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    unfold polynomialEpochWeight
    field_simp [hdelta.ne']
  unfold polynomialGeometricEpochBudget
  rw [hreciprocal, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem polynomialGeometricEpochBudget_pos
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta <= 1) (j : ℕ) :
    0 < polynomialGeometricEpochBudget delta j := by
  rw [polynomialGeometricEpochBudget_eq hdelta]
  have htwo : 1 < 2 / delta := by
    rw [lt_div_iff₀ hdelta]
    linarith
  have hfirst : 0 < Real.log (2 / delta) := Real.log_pos htwo
  have hj1 : 0 <= Real.log ((j : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hj2 : 0 <= Real.log ((j : ℝ) + 2) := by
    apply Real.log_nonneg
    have hj : (0 : ℝ) <= (j : ℝ) := Nat.cast_nonneg j
    linarith
  linarith

/-- The single predeclared tilt for epoch `j`. -/
def polynomialGeometricEpochTilt
    (sigma2 b delta : ℝ) (j : ℕ) : ℝ :=
  optTiltAtBudget sigma2 b (polynomialGeometricEpochFloor j)
    (polynomialGeometricEpochBudget delta j)

theorem polynomialGeometricEpochTilt_pos
    {sigma2 b delta : ℝ}
    (hσ : 0 < sigma2) (hb : 0 < b)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) (j : ℕ) :
    0 < polynomialGeometricEpochTilt sigma2 b delta j := by
  exact optTiltAtBudget_pos hσ hb (polynomialGeometricEpochFloor_pos j)
    (polynomialGeometricEpochBudget_pos hdelta hdelta_one j)

theorem polynomialGeometricEpochTilt_admissible
    {sigma2 b delta : ℝ}
    (hσ : 0 < sigma2) (hb : 0 < b)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) (j : ℕ) :
    b * polynomialGeometricEpochTilt sigma2 b delta j < 3 := by
  exact optTiltAtBudget_admissible hσ hb
    (polynomialGeometricEpochFloor_pos j)
    (polynomialGeometricEpochBudget_pos hdelta hdelta_one j)

/-- Fixed-tilt sub-Gamma processes are integrable under bounded increments.
This is the process-level version used by each allocated epoch atom. -/
theorem integrable_subGammaExponentialProcess_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ -> Ω -> ℝ} {sigma2 b lam : ℝ} (n : ℕ)
    (hb : 0 < b) (hσ : 0 <= sigma2) (hlam : 0 <= lam)
    (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k))
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b) :
    Integrable (subGammaExponentialProcess X sigma2 b lam n) μ := by
  refine Integrable.of_bound ?_ (Real.exp (lam * (n : ℝ) * b)) ?_
  · have hpair : Measurable (fun omega : Ω => (lam, omega)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_subGammaExponentialProcess_prod X sigma2 b n hX_meas).comp
      hpair).aestronglyMeasurable
  · have hall : ∀ᵐ omega ∂μ, ∀ k, |X k omega| <= b := ae_all_iff.2 hbound
    filter_upwards [hall] with omega homega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold subGammaExponentialProcess; positivity)]
    exact subGammaExponentialProcess_le_of_bound
      X sigma2 b lam lam n omega hb hσ hlam le_rfl hblam
      (fun i _hi => homega i)

/-- Failure event charged to one geometric epoch. -/
def polynomialStitchedLILAtomFailure {Ω : Type*}
    (X : ℕ -> Ω -> ℝ) (sigma2 b delta : ℝ) (j : ℕ) : Set Ω :=
  {omega | ∃ n : ℕ, 0 < n ∧
    subGammaBoundary sigma2 b (polynomialGeometricEpochBudget delta j) n
        (polynomialGeometricEpochTilt sigma2 b delta j) <=
      |runningMean X n omega|}

/-- Countable union of the allocated epoch failures. -/
def polynomialStitchedLILFailure {Ω : Type*}
    (X : ℕ -> Ω -> ℝ) (sigma2 b delta : ℝ) : Set Ω :=
  ⋃ j : ℕ, polynomialStitchedLILAtomFailure X sigma2 b delta j

/-- Each fixed-epoch failure event is measurable when the increments are
measurable. -/
theorem measurableSet_polynomialStitchedLILAtomFailure
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X : ℕ -> Ω -> ℝ} (hX_meas : ∀ k, Measurable (X k))
    (sigma2 b delta : ℝ) (j : ℕ) :
    MeasurableSet (polynomialStitchedLILAtomFailure X sigma2 b delta j) := by
  rw [show polynomialStitchedLILAtomFailure X sigma2 b delta j =
      ⋃ n : ℕ, if 0 < n then
        {omega |
          subGammaBoundary sigma2 b (polynomialGeometricEpochBudget delta j) n
              (polynomialGeometricEpochTilt sigma2 b delta j) <=
            |runningMean X n omega|}
      else ∅ by
    ext omega
    simp [polynomialStitchedLILAtomFailure]]
  refine MeasurableSet.iUnion fun n => ?_
  split_ifs
  · exact measurableSet_le measurable_const (by
      simpa only [Real.norm_eq_abs] using
        (measurable_runningMean hX_meas n).norm)
  · exact MeasurableSet.empty

/-- The countable stitched failure event is measurable when the increments
are measurable. -/
theorem measurableSet_polynomialStitchedLILFailure
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X : ℕ -> Ω -> ℝ} (hX_meas : ∀ k, Measurable (X k))
    (sigma2 b delta : ℝ) :
    MeasurableSet (polynomialStitchedLILFailure X sigma2 b delta) := by
  unfold polynomialStitchedLILFailure
  exact MeasurableSet.iUnion fun j =>
    measurableSet_polynomialStitchedLILAtomFailure hX_meas sigma2 b delta j

/-- Canonical good event for the polynomially stitched LIL bound. -/
def polynomialStitchedLILGoodEvent {Ω : Type*}
    (X : ℕ -> Ω -> ℝ) (sigma2 b delta : ℝ) : Set Ω :=
  (polynomialStitchedLILFailure X sigma2 b delta)ᶜ

/-- The canonical stitched-LIL good event is measurable when the increments
are measurable. -/
theorem measurableSet_polynomialStitchedLILGoodEvent
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X : ℕ -> Ω -> ℝ} (hX_meas : ∀ k, Measurable (X k))
    (sigma2 b delta : ℝ) :
    MeasurableSet (polynomialStitchedLILGoodEvent X sigma2 b delta) := by
  exact (measurableSet_polynomialStitchedLILFailure
    hX_meas sigma2 b delta).compl

/-- One epoch atom costs at most its predeclared polynomial confidence
allocation. -/
theorem polynomialStitchedLILAtomFailure_mass_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2)
    (j : ℕ) :
    μ.real (polynomialStitchedLILAtomFailure X sigma2 b delta j) <=
      delta * polynomialEpochWeight j := by
  let lam := polynomialGeometricEpochTilt sigma2 b delta j
  have hlam_pos : 0 < lam := by
    simpa [lam] using polynomialGeometricEpochTilt_pos hσ hb hδ hδ_one j
  have hlam_adm : b * lam < 3 := by
    simpa [lam] using polynomialGeometricEpochTilt_admissible hσ hb hδ hδ_one j
  have hdelta_atom : 0 < delta * polynomialEpochWeight j :=
    mul_pos hδ (polynomialEpochWeight_pos j)
  have hLam : ({lam} : Finset ℝ).Nonempty := Finset.singleton_nonempty lam
  have hLam_mem : ∀ l ∈ ({lam} : Finset ℝ), l ∈ Set.Ioo 0 (3 / b) := by
    intro l hl
    simp only [Finset.mem_singleton] at hl
    subst l
    refine ⟨hlam_pos, ?_⟩
    rw [lt_div_iff₀ hb]
    simpa [mul_comm] using hlam_adm
  have h_integrable :
      ∀ l ∈ ({lam} : Finset ℝ), ∀ n,
        Integrable (subGammaExponentialProcess X sigma2 b l n) μ := by
    intro l hl n
    simp only [Finset.mem_singleton] at hl
    subst l
    exact integrable_subGammaExponentialProcess_of_bounded n hb hσ.le
      hlam_pos.le hlam_adm hX_meas hbound
  have hbound_neg : ∀ k, ∀ᵐ omega ∂μ, |(-X k omega)| <= b := by
    intro k
    filter_upwards [hbound k] with omega homega
    simpa only [abs_neg] using homega
  have h_integrable_neg :
      ∀ l ∈ ({lam} : Finset ℝ), ∀ n,
        Integrable
          (subGammaExponentialProcess (fun k omega => -X k omega)
            sigma2 b l n) μ := by
    intro l hl n
    simp only [Finset.mem_singleton] at hl
    subst l
    exact integrable_subGammaExponentialProcess_of_bounded n hb hσ.le
      hlam_pos.le hlam_adm (fun k => (hX_meas k).neg) hbound_neg
  have hmain := optimized_lambda_two_sided_confidence_sequence
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
    (delta := delta * polynomialEpochWeight j) (Lam := ({lam} : Finset ℝ))
    hdelta_atom hb hσ.le hLam hLam_mem hX_meas hX_int hX_adapted
    h_integrable h_integrable_neg hbound hcenter hvar
  simpa [polynomialStitchedLILAtomFailure, polynomialGeometricEpochBudget,
    subGammaBoundary, lam] using hmain

/-- Countable subadditivity and the telescoping polynomial allocation bound
the full stitched failure event by `delta`. -/
theorem polynomialStitchedLILFailure_mass_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2) :
    μ.real (polynomialStitchedLILFailure X sigma2 b delta) <= delta := by
  let event : ℕ -> Set Ω := fun j =>
    polynomialStitchedLILAtomFailure X sigma2 b delta j
  have hatomReal : ∀ j, μ.real (event j) <=
      delta * polynomialEpochWeight j := by
    intro j
    exact polynomialStitchedLILAtomFailure_mass_le hδ hδ_one hb hσ
      hX_meas hX_int hX_adapted hbound hcenter hvar j
  have hatomENNReal : ∀ j, μ (event j) <=
      ENNReal.ofReal (delta * polynomialEpochWeight j) := by
    intro j
    calc
      μ (event j) = ENNReal.ofReal (μ.real (event j)) := by
        rw [ofReal_measureReal]
      _ <= ENNReal.ofReal (delta * polynomialEpochWeight j) :=
        ENNReal.ofReal_le_ofReal (hatomReal j)
  have hallocated : HasSum
      (fun j => delta * polynomialEpochWeight j) delta := by
    simpa using polynomialEpochWeight_hasSum.mul_left delta
  have hsummable : Summable (fun j => delta * polynomialEpochWeight j) :=
    hallocated.summable
  have hnonneg : ∀ j, 0 <= delta * polynomialEpochWeight j :=
    fun j => mul_nonneg hδ.le (polynomialEpochWeight_pos j).le
  have hunionENNReal : μ (⋃ j, event j) <= ENNReal.ofReal delta := by
    calc
      μ (⋃ j, event j) <= ∑' j, μ (event j) := measure_iUnion_le _
      _ <= ∑' j, ENNReal.ofReal (delta * polynomialEpochWeight j) :=
        ENNReal.tsum_le_tsum hatomENNReal
      _ = ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable,
          hallocated.tsum_eq]
  change μ.real (⋃ j, event j) <= delta
  calc
    μ.real (⋃ j, event j) <= (ENNReal.ofReal delta).toReal := by
      exact ENNReal.toReal_mono (by simp) hunionENNReal
    _ = delta := ENNReal.toReal_ofReal hδ.le

/-- The canonical measurable good event has probability at least
`1 - delta`. -/
theorem polynomialStitchedLILGoodEvent_probability_ge
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2) :
    1 - delta <= μ.real (polynomialStitchedLILGoodEvent X sigma2 b delta) := by
  rw [polynomialStitchedLILGoodEvent,
    probReal_compl_eq_one_sub
      (measurableSet_polynomialStitchedLILFailure hX_meas sigma2 b delta)]
  have hfailure := polynomialStitchedLILFailure_mass_le
    hδ hδ_one hb hσ hX_meas hX_int hX_adapted hbound hcenter hvar
  linarith

/-- The sub-Gamma line boundary decreases with the sample size when its
budget and tilt are nonnegative. -/
theorem subGammaBoundary_mono_time
    {sigma2 b budget lam : ℝ} {N n : ℕ}
    (hN : 0 < N) (hNn : N <= n) (hbudget : 0 <= budget)
    (hlam : 0 < lam) :
    subGammaBoundary sigma2 b budget n lam <=
      subGammaBoundary sigma2 b budget N lam := by
  unfold subGammaBoundary
  have hcast : (N : ℝ) <= (n : ℝ) := by exact_mod_cast hNn
  have hden_pos : 0 < (N : ℝ) * lam :=
    mul_pos (Nat.cast_pos.mpr hN) hlam
  have hden_le : (N : ℝ) * lam <= (n : ℝ) * lam :=
    mul_le_mul_of_nonneg_right hcast hlam.le
  have hfrac : budget / ((n : ℝ) * lam) <= budget / ((N : ℝ) * lam) :=
    div_le_div_of_nonneg_left hbudget hden_pos hden_le
  linarith

/-- An epoch-floor optimized width is at most a constant-factor width at any
time before four times the floor. -/
theorem subGammaWidthAtBudget_epoch_le
    {sigma2 b budget : ℝ} {N n : ℕ}
    (hσ : 0 <= sigma2) (hb : 0 <= b) (hbudget : 0 <= budget)
    (hN : 0 < N) (hNn : N <= n) (hn4N : n < 4 * N) :
    subGammaWidthAtBudget sigma2 b N budget <=
      2 * Real.sqrt (2 * sigma2 * budget / (n : ℝ)) +
        4 * b * budget / (3 * (n : ℝ)) := by
  have hn : 0 < n := hN.trans_le hNn
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn4NR : (n : ℝ) <= 4 * (N : ℝ) := by
    exact_mod_cast Nat.le_of_lt hn4N
  have hrecip : 1 / (N : ℝ) <= 4 / (n : ℝ) := by
    rw [div_le_div_iff₀ hNR hnR]
    simpa using hn4NR
  have hsarg :
      2 * sigma2 * budget / (N : ℝ) <=
        4 * (2 * sigma2 * budget / (n : ℝ)) := by
    calc
      2 * sigma2 * budget / (N : ℝ) =
          (2 * sigma2 * budget) * (1 / (N : ℝ)) := by ring
      _ <= (2 * sigma2 * budget) * (4 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 4 * (2 * sigma2 * budget / (n : ℝ)) := by ring
  have hsqrt := Real.sqrt_le_sqrt hsarg
  have hsqrt_four :
      Real.sqrt (4 * (2 * sigma2 * budget / (n : ℝ))) =
        2 * Real.sqrt (2 * sigma2 * budget / (n : ℝ)) := by
    calc
      Real.sqrt (4 * (2 * sigma2 * budget / (n : ℝ))) =
          Real.sqrt 4 * Real.sqrt (2 * sigma2 * budget / (n : ℝ)) :=
        Real.sqrt_mul (by norm_num) (2 * sigma2 * budget / (n : ℝ))
      _ = 2 * Real.sqrt (2 * sigma2 * budget / (n : ℝ)) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
        rw [hsqrt4]
  rw [hsqrt_four] at hsqrt
  have hlinear :
      b * budget / (3 * (N : ℝ)) <=
        4 * b * budget / (3 * (n : ℝ)) := by
    calc
      b * budget / (3 * (N : ℝ)) =
          (b * budget / 3) * (1 / (N : ℝ)) := by ring
      _ <= (b * budget / 3) * (4 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 4 * b * budget / (3 * (n : ℝ)) := by ring
  unfold subGammaWidthAtBudget
  linarith

/-- Outside the allocated union, every sample size at least four is bounded
by the exact optimized width at the floor of its selected epoch. -/
theorem polynomialStitchedLIL_lt_epochWidth_of_not_mem
    {Ω : Type*} {X : ℕ -> Ω -> ℝ}
    {sigma2 b delta : ℝ}
    (hσ : 0 < sigma2) (hb : 0 < b)
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    {omega : Ω}
    (homega : omega ∉ polynomialStitchedLILFailure X sigma2 b delta)
    (n : ℕ) (hn : 4 <= n) :
    |runningMean X n omega| <
      subGammaWidthAtBudget sigma2 b
        (polynomialGeometricEpochFloor (polynomialGeometricEpochIndex n))
        (polynomialGeometricEpochBudget delta
          (polynomialGeometricEpochIndex n)) := by
  let j := polynomialGeometricEpochIndex n
  let N := polynomialGeometricEpochFloor j
  let budget := polynomialGeometricEpochBudget delta j
  let lam := polynomialGeometricEpochTilt sigma2 b delta j
  have hspec := polynomialGeometricEpochIndex_spec hn
  have hN : 0 < N := by
    simpa [N, j] using polynomialGeometricEpochFloor_pos j
  have hNn : N <= n := by simpa [N, j] using hspec.1
  have hbudget : 0 < budget := by
    simpa [budget, j] using polynomialGeometricEpochBudget_pos hδ hδ_one j
  have hlam : 0 < lam := by
    simpa [lam, j] using polynomialGeometricEpochTilt_pos hσ hb hδ hδ_one j
  have hnotatom :
      omega ∉ polynomialStitchedLILAtomFailure X sigma2 b delta j := by
    intro hatom
    apply homega
    exact Set.mem_iUnion.2 ⟨j, hatom⟩
  have hline : |runningMean X n omega| <
      subGammaBoundary sigma2 b budget n lam := by
    by_contra hnot
    apply hnotatom
    exact ⟨n, by omega, le_of_not_gt hnot⟩
  calc
    |runningMean X n omega| <
        subGammaBoundary sigma2 b budget n lam := hline
    _ <= subGammaBoundary sigma2 b budget N lam :=
      subGammaBoundary_mono_time hN hNn hbudget.le hlam
    _ = subGammaWidthAtBudget sigma2 b N budget := by
      exact subGammaBoundary_eq_widthAtBudget_optTilt hσ hb hN hbudget

/-- Constant-factor form of the stitched boundary at the actual sample size.
The selected budget is explicit and grows as the logarithm of the epoch
index, hence as `log log n`. -/
theorem polynomialStitchedLIL_lt_explicit_of_not_mem
    {Ω : Type*} {X : ℕ -> Ω -> ℝ}
    {sigma2 b delta : ℝ}
    (hσ : 0 < sigma2) (hb : 0 < b)
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    {omega : Ω}
    (homega : omega ∉ polynomialStitchedLILFailure X sigma2 b delta)
    (n : ℕ) (hn : 4 <= n) :
    |runningMean X n omega| <
      2 * Real.sqrt
        (2 * sigma2 *
          polynomialGeometricEpochBudget delta
            (polynomialGeometricEpochIndex n) / (n : ℝ)) +
        4 * b *
          polynomialGeometricEpochBudget delta
            (polynomialGeometricEpochIndex n) /
          (3 * (n : ℝ)) := by
  let j := polynomialGeometricEpochIndex n
  let N := polynomialGeometricEpochFloor j
  let budget := polynomialGeometricEpochBudget delta j
  have hspec := polynomialGeometricEpochIndex_spec hn
  have hN : 0 < N := by
    simpa [N, j] using polynomialGeometricEpochFloor_pos j
  have hNn : N <= n := by simpa [N, j] using hspec.1
  have hn4N : n < 4 * N := by
    rw [← polynomialGeometricEpochHorizon_eq_four_mul_floor j]
    simpa [N, j] using hspec.2
  have hwidth := polynomialStitchedLIL_lt_epochWidth_of_not_mem
    hσ hb hδ hδ_one homega n hn
  have henvelope := subGammaWidthAtBudget_epoch_le
    hσ.le hb.le
    (polynomialGeometricEpochBudget_pos hδ hδ_one j).le
    hN hNn hn4N
  exact hwidth.trans_le (by simpa [N, budget, j] using henvelope)

/-- Standard measurable-event confidence sequence form of the explicit
polynomial stitched-LIL bound.  The canonical good event is measurable, has probability at least
`1 - delta`, and controls every sample size `n >= 4`. -/
theorem polynomialStitchedLIL_explicit_measurable_event
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2) :
    MeasurableSet (polynomialStitchedLILGoodEvent X sigma2 b delta) ∧
      1 - delta <=
        μ.real (polynomialStitchedLILGoodEvent X sigma2 b delta) ∧
      ∀ omega ∈ polynomialStitchedLILGoodEvent X sigma2 b delta,
        ∀ n : ℕ, 4 <= n ->
          |runningMean X n omega| <
            2 * Real.sqrt
              (2 * sigma2 *
                polynomialGeometricEpochBudget delta
                  (polynomialGeometricEpochIndex n) / (n : ℝ)) +
              4 * b *
                polynomialGeometricEpochBudget delta
                  (polynomialGeometricEpochIndex n) /
                (3 * (n : ℝ)) := by
  refine ⟨measurableSet_polynomialStitchedLILGoodEvent
    hX_meas sigma2 b delta, ?_, ?_⟩
  · exact polynomialStitchedLILGoodEvent_probability_ge
      hδ hδ_one hb hσ hX_meas hX_int hX_adapted hbound hcenter hvar
  · intro omega homega n hn
    apply polynomialStitchedLIL_lt_explicit_of_not_mem hσ hb hδ hδ_one
      (omega := omega) (n := n)
    · exact homega
    · exact hn

/-- User-facing all-time theorem: one good event controls every `n >= 4`
with the polynomially stitched geometric-epoch width. -/
theorem exists_polynomialStitchedLIL_event
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ <= delta ∧
        ∀ omega ∈ goodEvent, ∀ n : ℕ, 4 <= n ->
          |runningMean X n omega| <
            subGammaWidthAtBudget sigma2 b
              (polynomialGeometricEpochFloor
                (polynomialGeometricEpochIndex n))
              (polynomialGeometricEpochBudget delta
                (polynomialGeometricEpochIndex n)) := by
  let badEvent := polynomialStitchedLILFailure X sigma2 b delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using polynomialStitchedLILFailure_mass_le
      hδ hδ_one hb hσ hX_meas hX_int hX_adapted hbound hcenter hvar
  · intro omega homega n hn
    exact polynomialStitchedLIL_lt_epochWidth_of_not_mem hσ hb hδ hδ_one
      homega n hn

/-- Explicit constant-factor iterated-logarithm endpoint at the actual sample
size. -/
theorem exists_polynomialStitchedLIL_explicit_event
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ -> Ω -> ℝ} {sigma2 b delta : ℝ}
    (hδ : 0 < delta) (hδ_one : delta <= 1)
    (hb : 0 < b) (hσ : 0 < sigma2)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ omega ∂μ, |X k omega| <= b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun omega => (X k omega) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun _ => sigma2) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ <= delta ∧
        ∀ omega ∈ goodEvent, ∀ n : ℕ, 4 <= n ->
          |runningMean X n omega| <
            2 * Real.sqrt
              (2 * sigma2 *
                polynomialGeometricEpochBudget delta
                  (polynomialGeometricEpochIndex n) / (n : ℝ)) +
              4 * b *
                polynomialGeometricEpochBudget delta
                  (polynomialGeometricEpochIndex n) /
                (3 * (n : ℝ)) := by
  let badEvent := polynomialStitchedLILFailure X sigma2 b delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using polynomialStitchedLILFailure_mass_le
      hδ hδ_one hb hσ hX_meas hX_int hX_adapted hbound hcenter hvar
  · intro omega homega n hn
    exact polynomialStitchedLIL_lt_explicit_of_not_mem hσ hb hδ hδ_one
      homega n hn

end

end FormalSLT.AnytimeValid
