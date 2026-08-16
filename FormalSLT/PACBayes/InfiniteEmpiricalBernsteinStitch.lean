/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.InfiniteProductMeasureBridge
import FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt
import Mathlib.Data.Nat.Log

/-!
# Dyadically stitched empirical-Bernstein PAC-Bayes bounds

This module pulls the finite reverse-epoch empirical-Bernstein events onto one
countably infinite iid product space and stitches them over dyadic epochs.  The
confidence allocation is polynomial in the epoch index, so the resulting
complexity pays a logarithmic-in-the-epoch overhead rather than a linear one.

The result is an all-sample-size statement on one infinite iid path.  Its proof
uses offline reverse-epoch maximal inequalities and countable stitching; it is
not a forward e-process or an optional-stopping theorem.
-/

namespace FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

open Finset BigOperators MeasureTheory
open Filter Topology
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinReverseSqrt
open FormalSLT.PACBayes.InfiniteProductMeasureBridge

noncomputable section

variable {ι Z : Type*} [MeasurableSpace Z]

/-- Floor of dyadic epoch `q`.  Epoch zero covers sample sizes `[2,4)`. -/
def reverseDyadicEpochFloor (q : ℕ) : ℕ :=
  2 ^ (q + 1)

/-- Exclusive horizon of dyadic epoch `q`. -/
def reverseDyadicEpochHorizon (q : ℕ) : ℕ :=
  2 ^ (q + 2)

/-- Epoch selected for sample size `n ≥ 2`. -/
def reverseDyadicEpochIndex (n : ℕ) : ℕ :=
  (Nat.log 2 n).pred

/-- Telescoping confidence weight for epoch `q`. -/
def reverseDyadicEpochWeight (q : ℕ) : ℝ :=
  1 / (((q : ℝ) + 1) * ((q : ℝ) + 2))

/-- Confidence level assigned to epoch `q`. -/
def reverseDyadicEpochConfidence (delta : ℝ) (q : ℕ) : ℝ :=
  delta * reverseDyadicEpochWeight q

theorem reverseDyadicEpochFloor_two_le (q : ℕ) :
    2 ≤ reverseDyadicEpochFloor q := by
  unfold reverseDyadicEpochFloor
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (q + 1) := by
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem reverseDyadicEpochFloor_le_horizon (q : ℕ) :
    reverseDyadicEpochFloor q ≤ reverseDyadicEpochHorizon q := by
  unfold reverseDyadicEpochFloor reverseDyadicEpochHorizon
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem reverseDyadicEpochHorizon_two_le (q : ℕ) :
    2 ≤ reverseDyadicEpochHorizon q :=
  (reverseDyadicEpochFloor_two_le q).trans
    (reverseDyadicEpochFloor_le_horizon q)

theorem reverseDyadicEpochHorizon_eq_two_mul_floor (q : ℕ) :
    reverseDyadicEpochHorizon q = 2 * reverseDyadicEpochFloor q := by
  unfold reverseDyadicEpochHorizon reverseDyadicEpochFloor
  rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
  omega

/-- Every sample size at least two lies in its selected half-open dyadic
epoch. -/
theorem reverseDyadicEpochIndex_spec {n : ℕ} (hn : 2 ≤ n) :
    reverseDyadicEpochFloor (reverseDyadicEpochIndex n) ≤ n ∧
      n < reverseDyadicEpochHorizon (reverseDyadicEpochIndex n) := by
  let r := Nat.log 2 n
  have hrpos : 0 < r := Nat.log_pos (by norm_num) hn
  have hpred : r.pred + 1 = r := Nat.succ_pred_eq_of_pos hrpos
  constructor
  · change 2 ^ (r.pred + 1) ≤ n
    rw [hpred]
    exact Nat.pow_log_le_self 2 (by omega)
  · have hpred' : r.pred + 2 = r + 1 := by omega
    change n < 2 ^ (r.pred + 2)
    rw [hpred']
    exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem reverseDyadicEpochIndex_add_one {n : ℕ} (hn : 2 ≤ n) :
    reverseDyadicEpochIndex n + 1 = Nat.log 2 n := by
  unfold reverseDyadicEpochIndex
  exact Nat.succ_pred_eq_of_pos (Nat.log_pos (by norm_num) hn)

theorem reverseDyadicEpoch_gridDepth (q : ℕ) :
    finiteEmpiricalBernsteinGridDepth (reverseDyadicEpochFloor q) = q + 1 := by
  simp [finiteEmpiricalBernsteinGridDepth, reverseDyadicEpochFloor,
    Nat.clog_pow]

theorem reverseDyadicEpochWeight_pos (q : ℕ) :
    0 < reverseDyadicEpochWeight q := by
  unfold reverseDyadicEpochWeight
  positivity

theorem reverseDyadicEpochWeight_le_one (q : ℕ) :
    reverseDyadicEpochWeight q ≤ 1 := by
  unfold reverseDyadicEpochWeight
  rw [div_le_one (by positivity : (0 : ℝ) < ((q : ℝ) + 1) * ((q : ℝ) + 2))]
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith

theorem reverseDyadicEpochWeight_eq_sub (q : ℕ) :
    reverseDyadicEpochWeight q =
      1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) := by
  unfold reverseDyadicEpochWeight
  field_simp
  ring

theorem reverseDyadicEpochWeight_sum_range (Q : ℕ) :
    ∑ q ∈ Finset.range Q, reverseDyadicEpochWeight q =
      1 - 1 / ((Q : ℝ) + 1) := by
  induction Q with
  | zero => norm_num
  | succ Q ih =>
      rw [Finset.sum_range_succ, ih, reverseDyadicEpochWeight_eq_sub]
      push_cast
      ring

theorem reverseDyadicEpochWeight_hasSum :
    HasSum reverseDyadicEpochWeight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun q ↦ (reverseDyadicEpochWeight_pos q).le)]
  simp_rw [reverseDyadicEpochWeight_sum_range]
  have hlim : Tendsto (fun Q : ℕ ↦ 1 / ((Q : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [sub_zero] using tendsto_const_nhds.sub hlim

theorem reverseDyadicEpochWeight_summable :
    Summable reverseDyadicEpochWeight :=
  reverseDyadicEpochWeight_hasSum.summable

theorem reverseDyadicEpochWeight_tsum :
    ∑' q, reverseDyadicEpochWeight q = 1 :=
  reverseDyadicEpochWeight_hasSum.tsum_eq

theorem reverseDyadicEpochConfidence_pos {delta : ℝ} (hdelta : 0 < delta)
    (q : ℕ) : 0 < reverseDyadicEpochConfidence delta q := by
  exact mul_pos hdelta (reverseDyadicEpochWeight_pos q)

theorem reverseDyadicEpochConfidence_hasSum (delta : ℝ) :
    HasSum (reverseDyadicEpochConfidence delta) delta := by
  change HasSum (fun q ↦ delta * reverseDyadicEpochWeight q) delta
  simpa using reverseDyadicEpochWeight_hasSum.mul_left delta

theorem reverseDyadicEpochConfidence_summable (delta : ℝ) :
    Summable (reverseDyadicEpochConfidence delta) :=
  (reverseDyadicEpochConfidence_hasSum delta).summable

theorem reverseDyadicEpochConfidence_tsum (delta : ℝ) :
    ∑' q, reverseDyadicEpochConfidence delta q = delta :=
  (reverseDyadicEpochConfidence_hasSum delta).tsum_eq

theorem reverseDyadicEpochConfidence_lt_one
    {delta : ℝ} (hdelta_one : delta < 1) (q : ℕ) :
    reverseDyadicEpochConfidence delta q < 1 := by
  calc
    reverseDyadicEpochConfidence delta q <
        1 * reverseDyadicEpochWeight q := by
      unfold reverseDyadicEpochConfidence
      exact mul_lt_mul_of_pos_right hdelta_one (reverseDyadicEpochWeight_pos q)
    _ ≤ 1 := by simpa using reverseDyadicEpochWeight_le_one q

theorem reverseDyadicEpoch_ratio (q : ℕ) {delta : ℝ} (hdelta : delta ≠ 0) :
    (((finiteEmpiricalBernsteinGridDepth
        (reverseDyadicEpochFloor q) : ℕ) : ℝ) + 1) /
          reverseDyadicEpochConfidence delta q =
      (((q : ℝ) + 1) * ((q : ℝ) + 2) ^ (2 : Nat)) / delta := by
  rw [reverseDyadicEpoch_gridDepth]
  unfold reverseDyadicEpochConfidence reverseDyadicEpochWeight
  push_cast
  field_simp
  ring

/-- Exact complexity paid by the selected dyadic epoch at sample size `n`. -/
def infiniteEmpiricalBernsteinComplexity
    [Fintype ι] (n : ℕ) (delta : ℝ)
    (prior rho : ι → ℝ) : ℝ :=
  klDiv rho prior +
    Real.log
      ((((Nat.log 2 n : ℕ) : ℝ) *
          (((Nat.log 2 n : ℕ) : ℝ) + 1) ^ (2 : Nat)) / delta)

theorem infiniteEmpiricalBernsteinComplexity_pos
    [Fintype ι] {n : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    {prior rho : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hrho : IsPMF rho) :
    0 < infiniteEmpiricalBernsteinComplexity n delta prior rho := by
  let r : ℝ := (Nat.log 2 n : ℕ)
  have hr_nat : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hr : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast hr_nat
  have hsq : (4 : ℝ) ≤ (r + 1) ^ (2 : Nat) := by
    nlinarith [sq_nonneg (r - 1)]
  have hnum : (4 : ℝ) ≤ r * (r + 1) ^ (2 : Nat) := by
    calc
      (4 : ℝ) = 1 * 4 := by norm_num
      _ ≤ r * (r + 1) ^ (2 : Nat) :=
        mul_le_mul hr hsq (by norm_num) (by linarith)
  have hratio : 1 < r * (r + 1) ^ (2 : Nat) / delta := by
    rw [lt_div_iff₀ hdelta]
    linarith
  unfold infiniteEmpiricalBernsteinComplexity
  change 0 < klDiv rho prior + Real.log (r * (r + 1) ^ (2 : Nat) / delta)
  exact add_pos_of_nonneg_of_pos (klDiv_nonneg hrho hprior)
    (Real.log_pos hratio)

/-! ## One event on the infinite iid product space -/

/-- Epoch `q`'s finite failure event, with its telescoping confidence share. -/
def reverseDyadicEpochFailure
    [Fintype Z] [Fintype ι]
    (q : ℕ) (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Set (Fin (reverseDyadicEpochHorizon q) → Z) :=
  finiteEmpiricalBernsteinReverseSqrtFailure
    (reverseDyadicEpochHorizon q) (reverseDyadicEpochHorizon_two_le q)
    (reverseDyadicEpochFloor q) p prior ell
    (reverseDyadicEpochConfidence delta q)

/-- The single failure event obtained by pulling every finite reverse epoch
onto one infinite iid path and taking their countable union. -/
def infiniteEmpiricalBernsteinReverseSqrtFailure
    [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Set (ℕ → Z) :=
  ⋃ q : ℕ, natSamplePrefix (reverseDyadicEpochHorizon q) ⁻¹'
    reverseDyadicEpochFailure q p prior ell delta

theorem infiniteEmpiricalBernsteinReverseSqrtFailure_measurable
    [Fintype Z] [MeasurableSingletonClass Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) :
    MeasurableSet
      (infiniteEmpiricalBernsteinReverseSqrtFailure p prior ell delta) := by
  unfold infiniteEmpiricalBernsteinReverseSqrtFailure
  apply MeasurableSet.iUnion
  intro q
  exact (Set.toFinite (reverseDyadicEpochFailure q p prior ell delta)).measurableSet.preimage
    (measurable_natSamplePrefix (reverseDyadicEpochHorizon q))

/-- The stitched infinite-path failure event has mass at most `delta`. -/
theorem infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.infinitePi (fun _ : ℕ ↦ hp.toPMF.toMeasure)
        (infiniteEmpiricalBernsteinReverseSqrtFailure p prior ell delta) ≤
      ENNReal.ofReal delta := by
  unfold infiniteEmpiricalBernsteinReverseSqrtFailure
  apply natPrefix_iUnion_mass_le hp.toPMF.toMeasure
    reverseDyadicEpochHorizon (reverseDyadicEpochConfidence delta)
    (fun q ↦ reverseDyadicEpochFailure q p prior ell delta)
  · intro q
    exact (reverseDyadicEpochConfidence_pos hdelta q).le
  · exact reverseDyadicEpochConfidence_summable delta
  · intro q
    unfold reverseDyadicEpochFailure
    exact finiteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      (reverseDyadicEpochHorizon q) (reverseDyadicEpochFloor q)
      (reverseDyadicEpochHorizon_two_le q)
      ⟨reverseDyadicEpochFloor_two_le q,
        reverseDyadicEpochFloor_le_horizon q⟩
      p hp hprior ell hell (reverseDyadicEpochConfidence_pos hdelta q)
  · rw [reverseDyadicEpochConfidence_tsum]

omit [MeasurableSpace Z] in
theorem samplePrefix_natSamplePrefix {s N : ℕ} (hsN : s ≤ N)
    (x : ℕ → Z) :
    samplePrefix hsN (natSamplePrefix N x) = natSamplePrefix s x := by
  rfl

omit [MeasurableSpace Z] in
/-- Outside the one stitched event, every finite prefix of size at least two
and every finite posterior obey the dyadic-floor empirical-Bernstein bound. -/
theorem infiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
    [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : ℕ → Z)
    (hx : x ∉ infiniteEmpiricalBernsteinReverseSqrtFailure
      p prior ell delta)
    (n : ℕ) (hn : 2 ≤ n)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * posteriorAverage rho
              (fun i ↦ finiteEmpiricalVariance ell i (natSamplePrefix n x)) *
            infiniteEmpiricalBernsteinComplexity n delta prior rho /
            (reverseDyadicEpochFloor (reverseDyadicEpochIndex n) : ℝ)) +
        (5 / 2 : ℝ) *
          infiniteEmpiricalBernsteinComplexity n delta prior rho /
            (reverseDyadicEpochFloor (reverseDyadicEpochIndex n) : ℝ) := by
  let q := reverseDyadicEpochIndex n
  have hspec := reverseDyadicEpochIndex_spec hn
  have hmn : reverseDyadicEpochFloor q ≤ n := by simpa [q] using hspec.1
  have hnN : n ≤ reverseDyadicEpochHorizon q := by
    exact Nat.le_of_lt (by simpa [q] using hspec.2)
  have hconf_pos := reverseDyadicEpochConfidence_pos hdelta q
  have hconf_one := reverseDyadicEpochConfidence_lt_one hdelta_one q
  have hxq : natSamplePrefix (reverseDyadicEpochHorizon q) x ∉
      reverseDyadicEpochFailure q p prior ell delta := by
    intro hxq
    apply hx
    unfold infiniteEmpiricalBernsteinReverseSqrtFailure
    exact Set.mem_iUnion.mpr ⟨q, hxq⟩
  have hfinite :=
    finiteEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
      (reverseDyadicEpochHorizon q) (reverseDyadicEpochFloor q) n
      (reverseDyadicEpochHorizon_two_le q)
      (reverseDyadicEpochFloor_two_le q) hmn hnN p hp hprior ell hell
      hconf_pos hconf_one (natSamplePrefix (reverseDyadicEpochHorizon q) x)
      (by simpa [reverseDyadicEpochFailure] using hxq) hrho
  rw [reverseDyadicEpoch_ratio q hdelta.ne'] at hfinite
  have hq1 : q + 1 = Nat.log 2 n := by
    simpa [q] using reverseDyadicEpochIndex_add_one hn
  have hq2 : q + 2 = Nat.log 2 n + 1 := by omega
  have hq1R : (q : ℝ) + 1 = (Nat.log 2 n : ℝ) := by exact_mod_cast hq1
  have hq2R : (q : ℝ) + 2 = (Nat.log 2 n : ℝ) + 1 := by exact_mod_cast hq2
  have hcomplexity :
      klDiv rho prior +
          Real.log ((((q : ℝ) + 1) * ((q : ℝ) + 2) ^ (2 : Nat)) / delta) =
        infiniteEmpiricalBernsteinComplexity n delta prior rho := by
    unfold infiniteEmpiricalBernsteinComplexity
    rw [hq1R, hq2R]
  rw [hcomplexity] at hfinite
  simpa [q, samplePrefix_natSamplePrefix] using hfinite

omit [MeasurableSpace Z] in
/-- Cleaner sample-size form of the stitched bound.  Replacing the lower
dyadic epoch endpoint by the current sample size costs at most a factor two. -/
theorem infiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
    [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : ℕ → Z)
    (hx : x ∉ infiniteEmpiricalBernsteinReverseSqrtFailure
      p prior ell delta)
    (n : ℕ) (hn : 2 ≤ n)
    (rho : ι → ℝ) (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
        (5 / 2 : ℝ) * Real.sqrt
          (posteriorAverage rho
              (fun i ↦ finiteEmpiricalVariance ell i (natSamplePrefix n x)) *
            infiniteEmpiricalBernsteinComplexity n delta prior rho /
            (n : ℝ)) +
        5 * infiniteEmpiricalBernsteinComplexity n delta prior rho /
          (n : ℝ) := by
  let q := reverseDyadicEpochIndex n
  let m := reverseDyadicEpochFloor q
  let V := posteriorAverage rho
    (fun i ↦ finiteEmpiricalVariance ell i (natSamplePrefix n x))
  let L := infiniteEmpiricalBernsteinComplexity n delta prior rho
  have hbase := infiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
    p hp hprior ell hell hdelta hdelta_one x hx n hn rho hrho
  have hm_nat : 2 ≤ m := by
    dsimp [m]
    exact reverseDyadicEpochFloor_two_le q
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < L := by
    dsimp [L]
    exact infiniteEmpiricalBernsteinComplexity_pos hn hdelta hdelta_one
      hprior hrho
  have hV : 0 ≤ V := by
    dsimp [V]
    exact (posteriorAverage_finiteEmpiricalVariance_mem_Icc
      hn ell (natSamplePrefix n x) hell hrho).1
  have hn2m_nat : n ≤ 2 * m := by
    have hspec := (reverseDyadicEpochIndex_spec hn).2
    rw [reverseDyadicEpochHorizon_eq_two_mul_floor] at hspec
    exact Nat.le_of_lt (by simpa [q, m] using hspec)
  have hn2m : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hn2m_nat
  have hrecip : 1 / (m : ℝ) ≤ 2 / (n : ℝ) := by
    rw [div_le_div_iff₀ hmR hnR]
    simpa using hn2m
  have hsarg : 2 * V * L / (m : ℝ) ≤ 4 * (V * L / (n : ℝ)) := by
    calc
      2 * V * L / (m : ℝ) = (2 * V * L) * (1 / (m : ℝ)) := by ring
      _ ≤ (2 * V * L) * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 4 * (V * L / (n : ℝ)) := by ring
  have hsqrt := Real.sqrt_le_sqrt hsarg
  have hsqrt_four : Real.sqrt (4 * (V * L / (n : ℝ))) =
      2 * Real.sqrt (V * L / (n : ℝ)) := by
    calc
      Real.sqrt (4 * (V * L / (n : ℝ))) =
          Real.sqrt 4 * Real.sqrt (V * L / (n : ℝ)) :=
        Real.sqrt_mul (by norm_num) (V * L / (n : ℝ))
      _ = 2 * Real.sqrt (V * L / (n : ℝ)) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
        rw [hsqrt4]
  rw [hsqrt_four] at hsqrt
  have hsqrt_term :
      (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) ≤
        (5 / 2 : ℝ) * Real.sqrt (V * L / (n : ℝ)) := by
    nlinarith
  have hLdiv : L / (m : ℝ) ≤ 2 * L / (n : ℝ) := by
    calc
      L / (m : ℝ) = L * (1 / (m : ℝ)) := by ring
      _ ≤ L * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip hL.le
      _ = 2 * L / (n : ℝ) := by ring
  have hlinear_term :
      (5 / 2 : ℝ) * L / (m : ℝ) ≤ 5 * L / (n : ℝ) := by
    calc
      (5 / 2 : ℝ) * L / (m : ℝ) = (5 / 2 : ℝ) * (L / (m : ℝ)) := by ring
      _ ≤ (5 / 2 : ℝ) * (2 * L / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hLdiv (by norm_num)
      _ = 5 * L / (n : ℝ) := by ring
  change posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
        (5 / 2 : ℝ) * Real.sqrt (V * L / (n : ℝ)) +
        5 * L / (n : ℝ)
  change posteriorAverage rho (finitePopulationRisk p ell) <
      posteriorAverage rho
          (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) +
        (5 / 2 : ℝ) * L / (m : ℝ) at hbase
  linarith

/-- **All-sample-size empirical-Bernstein PAC-Bayes event.**

There is one measurable exceptional set of infinite iid paths with mass at
most `delta`.  Off it, every finite prefix of size at least two and every
finite posterior obey the closed-form bound pointwise, so a path-dependent
posterior may be substituted without an additional event.  The exact
complexity uses `Nat.log 2 n` (the floor of the base-two logarithm), and the
denominator is the lower dyadic endpoint of the epoch containing `n`.

This is a stitched offline reverse-epoch theorem, not a forward e-process or
an optional-stopping theorem. -/
theorem exists_infiniteEmpiricalBernsteinReverseSqrt_event
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1) :
    ∃ E : Set (ℕ → Z),
      MeasurableSet E ∧
      Measure.infinitePi (fun _ : ℕ ↦ hp.toPMF.toMeasure) E ≤
        ENNReal.ofReal delta ∧
      ∀ x, x ∉ E → ∀ n : ℕ, 2 ≤ n →
        ∀ rho : ι → ℝ, IsPMF rho →
          posteriorAverage rho (finitePopulationRisk p ell) <
            posteriorAverage rho
                (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
              (5 / 4 : ℝ) * Real.sqrt
                (2 * posteriorAverage rho
                    (fun i ↦ finiteEmpiricalVariance ell i
                      (natSamplePrefix n x)) *
                  infiniteEmpiricalBernsteinComplexity n delta prior rho /
                  (reverseDyadicEpochFloor
                    (reverseDyadicEpochIndex n) : ℝ)) +
              (5 / 2 : ℝ) *
                infiniteEmpiricalBernsteinComplexity n delta prior rho /
                  (reverseDyadicEpochFloor
                    (reverseDyadicEpochIndex n) : ℝ) := by
  let E := infiniteEmpiricalBernsteinReverseSqrtFailure p prior ell delta
  refine ⟨E, infiniteEmpiricalBernsteinReverseSqrtFailure_measurable
    p prior ell delta, ?_, ?_⟩
  · exact infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      p hp hprior ell hell hdelta
  · intro x hx n hn rho hrho
    exact infiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
      p hp hprior ell hell hdelta hdelta_one x hx n hn rho hrho

/-- **Researcher-facing all-sample-size empirical-Bernstein PAC-Bayes bound.**

Outside one measurable exceptional event of infinite-iid mass at most
`delta`, every `n ≥ 2` and every finite posterior satisfy

`Rρ < Rhatρ,n + (5/2) sqrt(Vhatρ,n * Lρ,n / n) + 5 Lρ,n / n`,

where `Lρ,n = KL(ρ‖prior) + log(r*(r+1)^2/delta)` and
`r = Nat.log 2 n`.  The variance is the posterior average of each
hypothesis's Bessel empirical variance, not the variance of the
posterior-averaged loss. -/
theorem exists_infiniteEmpiricalBernstein_event
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1) :
    ∃ E : Set (ℕ → Z),
      MeasurableSet E ∧
      Measure.infinitePi (fun _ : ℕ ↦ hp.toPMF.toMeasure) E ≤
        ENNReal.ofReal delta ∧
      ∀ x, x ∉ E → ∀ n : ℕ, 2 ≤ n →
        ∀ rho : ι → ℝ, IsPMF rho →
          posteriorAverage rho (finitePopulationRisk p ell) <
            posteriorAverage rho
                (fun i ↦ finiteEmpiricalRisk ell i (natSamplePrefix n x)) +
              (5 / 2 : ℝ) * Real.sqrt
                (posteriorAverage rho
                    (fun i ↦ finiteEmpiricalVariance ell i
                      (natSamplePrefix n x)) *
                  infiniteEmpiricalBernsteinComplexity n delta prior rho /
                  (n : ℝ)) +
              5 * infiniteEmpiricalBernsteinComplexity n delta prior rho /
                (n : ℝ) := by
  let E := infiniteEmpiricalBernsteinReverseSqrtFailure p prior ell delta
  refine ⟨E, infiniteEmpiricalBernsteinReverseSqrtFailure_measurable
    p prior ell delta, ?_, ?_⟩
  · exact infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      p hp hprior ell hell hdelta
  · intro x hx n hn rho hrho
    exact infiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
      p hp hprior ell hell hdelta hdelta_one x hx n hn rho hrho

end

end FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch
