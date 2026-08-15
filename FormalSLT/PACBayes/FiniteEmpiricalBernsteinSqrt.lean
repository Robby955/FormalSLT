/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
import Mathlib.Data.Nat.Log

/-!
# Explicit-scale empirical-Bernstein PAC-Bayes bounds

This module removes the abstract zero-residual balance hypothesis from the
fixed-sample joint mean/Bessel-variance PAC-Bayes theorem.  A positive scale
`s <= 2` is mapped to the predeclared pair

`t = s / (1 + 2s)`, `eta = s^2 / (2(1 + 2s))`.

For every `n >= 2`, this pair satisfies the checked joint-MGF balance
condition.  Consequently one shared finite-catalog event gives the explicit
posterior bound

`R(rho) <= Rhat(rho) + L/(s n) + 2L/n + (s/2) Vhat(rho)`,

where `L = KL(rho || prior) + log (1 / (delta * w))` and `Vhat` is the
posterior average of the per-hypothesis Bessel empirical variances.

The final endpoint assumes finite data and hypothesis types, `[0,1]` loss, and
a full-support prior fixed before the sample. The scale catalog is finite and
predeclared. This module does not optimize over all real scales, and it does
not make a time-uniform claim.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.Probability.BernsteinMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

noncomputable section

variable {κ ι Z : Type*}

/-- Mean tilt associated with an empirical-Bernstein scale. -/
def finiteEmpiricalBernsteinTiltOfScale (s : ℝ) : ℝ :=
  s / (1 + 2 * s)

/-- Empirical-variance tilt associated with an empirical-Bernstein scale. -/
def finiteEmpiricalBernsteinEtaOfScale (s : ℝ) : ℝ :=
  s ^ (2 : Nat) / (2 * (1 + 2 * s))

/-- Variance tilt written as a function of the mean tilt. -/
def finiteEmpiricalBernsteinEtaOfTilt (t : ℝ) : ℝ :=
  t ^ (2 : Nat) / (2 * (1 - 2 * t))

lemma finiteEmpiricalBernsteinTiltOfScale_pos {s : ℝ} (hs : 0 < s) :
    0 < finiteEmpiricalBernsteinTiltOfScale s := by
  unfold finiteEmpiricalBernsteinTiltOfScale
  positivity

lemma finiteEmpiricalBernsteinTiltOfScale_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ finiteEmpiricalBernsteinTiltOfScale s := by
  unfold finiteEmpiricalBernsteinTiltOfScale
  positivity

lemma finiteEmpiricalBernsteinEtaOfScale_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ finiteEmpiricalBernsteinEtaOfScale s := by
  unfold finiteEmpiricalBernsteinEtaOfScale
  positivity

lemma finiteEmpiricalBernsteinEtaOfTilt_nonneg
    {t : ℝ} (_ht : 0 ≤ t) (ht2 : t < 1 / 2) :
    0 ≤ finiteEmpiricalBernsteinEtaOfTilt t := by
  unfold finiteEmpiricalBernsteinEtaOfTilt
  have hden : 0 ≤ 2 * (1 - 2 * t) := by linarith
  exact div_nonneg (sq_nonneg t) hden

lemma finiteEmpiricalBernsteinTiltOfScale_lt_one {s : ℝ} (hs : 0 ≤ s) :
    finiteEmpiricalBernsteinTiltOfScale s < 1 := by
  unfold finiteEmpiricalBernsteinTiltOfScale
  rw [div_lt_one (by positivity)]
  linarith

lemma finiteEmpiricalBernsteinTiltOfScale_le_two_fifths
    {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    finiteEmpiricalBernsteinTiltOfScale s ≤ (2 : ℝ) / 5 := by
  unfold finiteEmpiricalBernsteinTiltOfScale
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma finiteEmpiricalBernsteinEta_div_tilt {s : ℝ} (hs : 0 < s) :
    finiteEmpiricalBernsteinEtaOfScale s /
        finiteEmpiricalBernsteinTiltOfScale s = s / 2 := by
  unfold finiteEmpiricalBernsteinEtaOfScale finiteEmpiricalBernsteinTiltOfScale
  have hsne : s ≠ 0 := ne_of_gt hs
  have hden : 1 + 2 * s ≠ 0 := ne_of_gt (by positivity)
  field_simp

lemma one_div_finiteEmpiricalBernsteinTiltOfScale {s : ℝ} (hs : 0 < s) :
    1 / finiteEmpiricalBernsteinTiltOfScale s = 1 / s + 2 := by
  unfold finiteEmpiricalBernsteinTiltOfScale
  have hsne : s ≠ 0 := ne_of_gt hs
  have hden : 1 + 2 * s ≠ 0 := ne_of_gt (by positivity)
  field_simp

lemma finiteEmpiricalBernsteinEtaOfTilt_tiltOfScale
    {s : ℝ} (hs : 0 ≤ s) :
    finiteEmpiricalBernsteinEtaOfTilt
        (finiteEmpiricalBernsteinTiltOfScale s) =
      finiteEmpiricalBernsteinEtaOfScale s := by
  unfold finiteEmpiricalBernsteinEtaOfTilt finiteEmpiricalBernsteinTiltOfScale
    finiteEmpiricalBernsteinEtaOfScale
  have hden : 1 + 2 * s ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The Bessel coefficient dominates the simpler quadratic coefficient used
by the explicit-scale balance proof. -/
lemma card_mul_eta_sub_sq_le_finiteJointMeanVarianceKappa
    {n : ℕ} (hn : 2 ≤ n) (eta : ℝ) :
    (n : ℝ) * (eta - eta ^ (2 : Nat)) ≤
      finiteJointMeanVarianceKappa n eta := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hdecomp :
      finiteJointMeanVarianceKappa n eta =
        (n : ℝ) * (eta - eta ^ (2 : Nat)) +
          eta ^ (2 : Nat) * (n : ℝ) * ((n : ℝ) - 2) /
            (2 * ((n : ℝ) - 1)) := by
    unfold finiteJointMeanVarianceKappa
    field_simp [ne_of_gt hpred]
    ring
  rw [hdecomp]
  exact le_add_of_nonneg_right
    (div_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg eta) (Nat.cast_nonneg n)) (by linarith))
      (by positivity))

/-- The rational variance tilt absorbs the Bennett term for every
`0 <= t <= 2/5`. -/
theorem finiteJointMeanVariance_balance_of_tilt
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht_upper : t ≤ (2 : ℝ) / 5) :
    (n : ℝ) * (Real.exp t - 1 - t) ≤
      Real.exp (-t) *
        finiteJointMeanVarianceKappa n
          (finiteEmpiricalBernsteinEtaOfTilt t) := by
  have ht_half : t < (1 : ℝ) / 2 := by linarith
  have ht_one : t < 1 := by linarith
  have hden_subgamma : 0 < 2 * (1 - t / 3) := by linarith
  have hden_eta : 0 < 2 * (1 - 2 * t) := by linarith
  let eta := finiteEmpiricalBernsteinEtaOfTilt t
  have heta_nonneg : 0 ≤ eta :=
    finiteEmpiricalBernsteinEtaOfTilt_nonneg ht ht_half
  have heta_le_one : eta ≤ 1 := by
    dsimp [eta, finiteEmpiricalBernsteinEtaOfTilt]
    rw [div_le_one hden_eta]
    nlinarith [sq_nonneg t]
  have heta_gap_nonneg : 0 ≤ eta - eta ^ (2 : Nat) := by
    nlinarith [mul_nonneg heta_nonneg (sub_nonneg.mpr heta_le_one)]
  have hcube : t ^ (3 : Nat) ≤ t := by
    have hprod : 0 ≤ t * (1 - t) * (1 + t) := by positivity
    nlinarith
  have hpoly : 0 ≤ 4 - 9 * t - t ^ (3 : Nat) := by
    nlinarith
  have hrational :
      t ^ (2 : Nat) / (2 * (1 - t / 3)) ≤
        (1 - t) * (eta - eta ^ (2 : Nat)) := by
    have heta_gap :
        finiteEmpiricalBernsteinEtaOfTilt t -
            finiteEmpiricalBernsteinEtaOfTilt t ^ (2 : Nat) =
          (t ^ (2 : Nat) * (2 * (1 - 2 * t)) - t ^ (4 : Nat)) /
            (2 * (1 - 2 * t)) ^ (2 : Nat) := by
      unfold finiteEmpiricalBernsteinEtaOfTilt
      field_simp [ne_of_gt hden_eta]
    dsimp [eta]
    rw [heta_gap, div_le_iff₀ hden_subgamma]
    have hreassoc :
        (1 - t) *
              ((t ^ (2 : Nat) * (2 * (1 - 2 * t)) - t ^ (4 : Nat)) /
                (2 * (1 - 2 * t)) ^ (2 : Nat)) *
            (2 * (1 - t / 3)) =
          ((1 - t) *
              (t ^ (2 : Nat) * (2 * (1 - 2 * t)) - t ^ (4 : Nat)) *
            (2 * (1 - t / 3))) /
              (2 * (1 - 2 * t)) ^ (2 : Nat) := by ring
    rw [hreassoc, le_div_iff₀ (sq_pos_of_pos hden_eta)]
    ring_nf
    nlinarith [mul_nonneg (pow_nonneg ht 3) hpoly]
  have hpsi :
      Real.exp t - 1 - t ≤ t ^ (2 : Nat) / (2 * (1 - t / 3)) :=
    exp_sub_one_sub_le_sq_div ht (by linarith)
  have hpsi_eta :
      Real.exp t - 1 - t ≤ (1 - t) * (eta - eta ^ (2 : Nat)) :=
    hpsi.trans hrational
  have hexp_neg : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  have hkappa_base :=
    card_mul_eta_sub_sq_le_finiteJointMeanVarianceKappa hn eta
  have hkappa_nonneg : 0 ≤ finiteJointMeanVarianceKappa n eta :=
    le_trans (mul_nonneg (Nat.cast_nonneg n) heta_gap_nonneg) hkappa_base
  calc
    (n : ℝ) * (Real.exp t - 1 - t) ≤
        (n : ℝ) * ((1 - t) * (eta - eta ^ (2 : Nat))) :=
      mul_le_mul_of_nonneg_left hpsi_eta (Nat.cast_nonneg n)
    _ = (1 - t) * ((n : ℝ) * (eta - eta ^ (2 : Nat))) := by ring
    _ ≤ (1 - t) * finiteJointMeanVarianceKappa n eta :=
      mul_le_mul_of_nonneg_left hkappa_base (by linarith)
    _ ≤ Real.exp (-t) * finiteJointMeanVarianceKappa n eta :=
      mul_le_mul_of_nonneg_right hexp_neg hkappa_nonneg

/-- Every positive scale at most two gives an admissible zero-residual pair. -/
theorem finiteJointMeanVariance_balance_of_scale
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : 0 < s) (hs_upper : s ≤ 2) :
    (n : ℝ) *
        (Real.exp (finiteEmpiricalBernsteinTiltOfScale s) - 1 -
          finiteEmpiricalBernsteinTiltOfScale s) ≤
      Real.exp (-finiteEmpiricalBernsteinTiltOfScale s) *
        finiteJointMeanVarianceKappa n
          (finiteEmpiricalBernsteinEtaOfScale s) := by
  rw [← finiteEmpiricalBernsteinEtaOfTilt_tiltOfScale hs.le]
  exact finiteJointMeanVariance_balance_of_tilt hn
    (finiteEmpiricalBernsteinTiltOfScale_nonneg hs.le)
    (finiteEmpiricalBernsteinTiltOfScale_le_two_fifths hs.le hs_upper)

/-- The explicit scale pair also satisfies the nonnegative-`kappa`
admissibility condition needed by the joint-MGF mass theorem. -/
theorem finiteJointMeanVarianceKappa_scale_nonneg
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : 0 < s) (hs_upper : s ≤ 2) :
    0 ≤ finiteJointMeanVarianceKappa n
      (finiteEmpiricalBernsteinEtaOfScale s) := by
  let eta := finiteEmpiricalBernsteinEtaOfScale s
  have heta_nonneg : 0 ≤ eta :=
    finiteEmpiricalBernsteinEtaOfScale_nonneg hs.le
  have hden : 0 < 2 * (1 + 2 * s) := by positivity
  have heta_le_one : eta ≤ 1 := by
    dsimp [eta, finiteEmpiricalBernsteinEtaOfScale]
    rw [div_le_one hden]
    nlinarith [sq_nonneg s]
  have hgap : 0 ≤ eta - eta ^ (2 : Nat) := by
    nlinarith [mul_nonneg heta_nonneg (sub_nonneg.mpr heta_le_one)]
  exact le_trans (mul_nonneg (Nat.cast_nonneg n) hgap)
    (card_mul_eta_sub_sq_le_finiteJointMeanVarianceKappa hn eta)

/-- The one bad-sample set for a finite catalog of empirical-Bernstein
scales. -/
def finiteEmpiricalBernsteinScaleBadSamples
    [Fintype κ] [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (scale w : κ → ℝ) (delta : ℝ) : Finset (Fin n → Z) :=
  finiteJointMeanVarianceCatalogBadSamples n p prior ell
    (fun c => finiteEmpiricalBernsteinTiltOfScale (scale c))
    (fun c => finiteEmpiricalBernsteinEtaOfScale (scale c)) w delta

/-- One common event controls every entry of a finite predeclared scale
catalog. -/
theorem finiteEmpiricalBernsteinScale_badSamples_mass_le_delta
    [Fintype κ] [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {scale w : κ → ℝ}
    (hscale_pos : ∀ c, 0 < scale c)
    (hscale_upper : ∀ c, scale c ≤ 2)
    (hw : ∀ c, 0 ≤ w c) (hw_sum : ∑ c, w c ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑ S ∈ finiteEmpiricalBernsteinScaleBadSamples
        n p prior ell scale w delta,
      finiteProductSampleWeight p S) ≤ delta := by
  exact finiteJointMeanVariance_catalogBadSamples_mass_le_delta
    hn p hp hprior ell hell
    (fun c => finiteEmpiricalBernsteinTiltOfScale_nonneg (hscale_pos c).le)
    (fun c => finiteEmpiricalBernsteinEtaOfScale_nonneg (hscale_pos c).le)
    (fun c => finiteJointMeanVarianceKappa_scale_nonneg hn
      (hscale_pos c) (hscale_upper c))
    hw hw_sum hdelta

/-- Explicit-scale one-event empirical-Bernstein PAC-Bayes endpoint.

The selected scale may depend on the observed sample and posterior because the
catalog event is already simultaneous in every predeclared entry and every
finite posterior. -/
theorem finiteEmpiricalBernstein_posteriorRisk_le_scale_selected_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ) {scale w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (hscale_pos : ∀ c, 0 < scale c)
    (hscale_upper : ∀ c, scale c ≤ 2)
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinScaleBadSamples
      n p prior ell scale w delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior +
            Real.log (1 / (delta * w (select S rho)))) /
          (scale (select S rho) * (n : ℝ)) +
        2 * (klDiv rho prior +
            Real.log (1 / (delta * w (select S rho)))) / (n : ℝ) +
        (scale (select S rho) / 2) *
          posteriorAverage rho
            (fun i => finiteEmpiricalVariance ell i S) := by
  let c := select S rho
  let L := klDiv rho prior + Real.log (1 / (delta * w c))
  let V := posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S)
  have hbase :=
    finiteJointMeanVariance_posteriorRisk_le_empiricalRisk_add_empiricalVariance_zeroResidual_selected_of_not_mem
      hn p hp hprior ell hw
      (fun c => finiteEmpiricalBernsteinTiltOfScale_pos (hscale_pos c))
      (fun c => finiteJointMeanVariance_balance_of_scale hn
        (hscale_pos c) (hscale_upper c))
      select S hS hrho
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hs : 0 < scale c := hscale_pos c
  have hcomplexity :
      L /
          (finiteEmpiricalBernsteinTiltOfScale (scale c) * (n : ℝ)) =
        L / (scale c * (n : ℝ)) + 2 * L / (n : ℝ) := by
    unfold finiteEmpiricalBernsteinTiltOfScale
    field_simp [ne_of_gt hs, ne_of_gt hnR]
  have hvariance :
      (finiteEmpiricalBernsteinEtaOfScale (scale c) /
          finiteEmpiricalBernsteinTiltOfScale (scale c)) * V =
        (scale c / 2) * V := by
    rw [finiteEmpiricalBernsteinEta_div_tilt hs]
  change
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        L / (scale c * (n : ℝ)) + 2 * L / (n : ℝ) +
        (scale c / 2) * V
  change
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        L /
          (finiteEmpiricalBernsteinTiltOfScale (scale c) * (n : ℝ)) +
        (finiteEmpiricalBernsteinEtaOfScale (scale c) /
          finiteEmpiricalBernsteinTiltOfScale (scale c)) * V at hbase
  rw [hcomplexity, hvariance] at hbase
  linarith

/-! ## Concrete dyadic scale catalog -/

/-- Dyadic scale `2 / 2^j`. -/
def finiteEmpiricalBernsteinDyadicScale (j : ℕ) : ℝ :=
  2 / (2 : ℝ) ^ j

lemma finiteEmpiricalBernsteinDyadicScale_zero :
    finiteEmpiricalBernsteinDyadicScale 0 = 2 := by
  norm_num [finiteEmpiricalBernsteinDyadicScale]

lemma finiteEmpiricalBernsteinDyadicScale_succ (j : ℕ) :
    finiteEmpiricalBernsteinDyadicScale (j + 1) =
      finiteEmpiricalBernsteinDyadicScale j / 2 := by
  unfold finiteEmpiricalBernsteinDyadicScale
  rw [pow_succ]
  ring

lemma finiteEmpiricalBernsteinDyadicScale_pos (j : ℕ) :
    0 < finiteEmpiricalBernsteinDyadicScale j := by
  unfold finiteEmpiricalBernsteinDyadicScale
  positivity

lemma finiteEmpiricalBernsteinDyadicScale_le_two (j : ℕ) :
    finiteEmpiricalBernsteinDyadicScale j ≤ 2 := by
  induction j with
  | zero => rw [finiteEmpiricalBernsteinDyadicScale_zero]
  | succ j ih =>
      rw [show j + 1 = Nat.succ j by omega,
        show Nat.succ j = j + 1 by omega,
        finiteEmpiricalBernsteinDyadicScale_succ]
      have hj := finiteEmpiricalBernsteinDyadicScale_pos j
      linarith

/-- A finite dyadic catalog covers every scale between its final atom and two
within a factor of two. -/
theorem exists_dyadicScale_le_and_le_two_mul
    (J : ℕ) {u : ℝ}
    (hbottom : finiteEmpiricalBernsteinDyadicScale J ≤ u)
    (hu : u ≤ 2) :
    ∃ j : Fin (J + 1),
      finiteEmpiricalBernsteinDyadicScale j.1 ≤ u ∧
        u ≤ 2 * finiteEmpiricalBernsteinDyadicScale j.1 := by
  induction J generalizing u with
  | zero =>
      refine ⟨⟨0, by omega⟩, ?_, ?_⟩
      · simpa using hbottom
      · rw [finiteEmpiricalBernsteinDyadicScale_zero]
        linarith
  | succ J ih =>
      by_cases hprev : finiteEmpiricalBernsteinDyadicScale J ≤ u
      · obtain ⟨j, hjlow, hjhigh⟩ := ih hprev hu
        exact ⟨j.castSucc, hjlow, hjhigh⟩
      · refine ⟨Fin.last (J + 1), ?_, ?_⟩
        · simpa only [Fin.val_last] using hbottom
        · have hlt : u < finiteEmpiricalBernsteinDyadicScale J := lt_of_not_ge hprev
          rw [Fin.val_last, finiteEmpiricalBernsteinDyadicScale_succ]
          linarith

/-- Uniform weight on the `J+1` dyadic atoms. -/
def finiteEmpiricalBernsteinDyadicWeight (J : ℕ) (_j : Fin (J + 1)) : ℝ :=
  1 / ((J : ℝ) + 1)

lemma finiteEmpiricalBernsteinDyadicWeight_pos (J : ℕ) (j : Fin (J + 1)) :
    0 < finiteEmpiricalBernsteinDyadicWeight J j := by
  unfold finiteEmpiricalBernsteinDyadicWeight
  positivity

lemma finiteEmpiricalBernsteinDyadicWeight_sum_eq_one (J : ℕ) :
    (∑ j : Fin (J + 1), finiteEmpiricalBernsteinDyadicWeight J j) = 1 := by
  simp [finiteEmpiricalBernsteinDyadicWeight, div_eq_mul_inv]
  field_simp

/-- One bad-sample set for the explicit `J+1` atom dyadic catalog. -/
def finiteEmpiricalBernsteinDyadicBadSamples
    [Fintype Z] [Fintype ι] (J n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Finset (Fin n → Z) :=
  finiteEmpiricalBernsteinScaleBadSamples n p prior ell
    (fun j : Fin (J + 1) => finiteEmpiricalBernsteinDyadicScale j.1)
    (finiteEmpiricalBernsteinDyadicWeight J) delta

/-- The explicit dyadic catalog has one bad event of mass at most `delta`. -/
theorem finiteEmpiricalBernsteinDyadic_badSamples_mass_le_delta
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (J : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑ S ∈ finiteEmpiricalBernsteinDyadicBadSamples
        J n p prior ell delta,
      finiteProductSampleWeight p S) ≤ delta := by
  simpa [finiteEmpiricalBernsteinDyadicBadSamples] using
    (finiteEmpiricalBernsteinScale_badSamples_mass_le_delta
      (κ := Fin (J + 1)) hn p hp hprior ell hell
      (fun j => finiteEmpiricalBernsteinDyadicScale_pos j.1)
      (fun j => finiteEmpiricalBernsteinDyadicScale_le_two j.1)
      (fun j => (finiteEmpiricalBernsteinDyadicWeight_pos J j).le)
      (by rw [finiteEmpiricalBernsteinDyadicWeight_sum_eq_one]) hdelta)

/-- Deterministic dyadic approximation of the continuous
`A / s + s * V / 2` optimizer.  The only coverage input is that the final
dyadic atom reaches the optimizer's lower end. -/
theorem exists_dyadicScale_optimizer_bound
    (J : ℕ) {A V : ℝ}
    (hA : 0 < A) (hV : 0 ≤ V)
    (hcover : finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤ 2 * A) :
    ∃ j : Fin (J + 1),
      A / finiteEmpiricalBernsteinDyadicScale j.1 +
          finiteEmpiricalBernsteinDyadicScale j.1 * V / 2 ≤
        (5 / 4 : ℝ) * Real.sqrt (2 * A * V) + A / 2 := by
  rcases eq_or_lt_of_le hV with rfl | hVpos
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simp [finiteEmpiricalBernsteinDyadicScale_zero]
  · let u := Real.sqrt (2 * A / V)
    let R := Real.sqrt (2 * A * V)
    have hu_pos : 0 < u := Real.sqrt_pos.mpr (div_pos (by positivity) hVpos)
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hu_sq : u ^ (2 : Nat) = 2 * A / V :=
      Real.sq_sqrt (div_nonneg (by positivity) hVpos.le)
    have hu_sq_mul : u ^ (2 : Nat) * V = 2 * A := by
      rw [hu_sq, div_mul_cancel₀ _ (ne_of_gt hVpos)]
    have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
    have hR_sq : R ^ (2 : Nat) = 2 * A * V :=
      Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hA.le) hVpos.le)
    have huV_sq : (u * V) ^ (2 : Nat) = 2 * A * V := by
      rw [mul_pow]
      nlinarith
    have hR_eq : R = u * V := by
      have huv_nonneg : 0 ≤ u * V := mul_nonneg hu_nonneg hVpos.le
      nlinarith
    have hbottom_sq :
        finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) ≤ u ^ (2 : Nat) := by
      apply le_of_mul_le_mul_right _ hVpos
      simpa [hu_sq_mul] using hcover
    have hbottom : finiteEmpiricalBernsteinDyadicScale J ≤ u :=
      (sq_le_sq₀ (finiteEmpiricalBernsteinDyadicScale_pos J).le hu_nonneg).mp
        hbottom_sq
    by_cases hu_two : u ≤ 2
    · obtain ⟨j, hjlow, hjhigh⟩ :=
        exists_dyadicScale_le_and_le_two_mul J hbottom hu_two
      refine ⟨j, ?_⟩
      let s := finiteEmpiricalBernsteinDyadicScale j.1
      have hs_pos : 0 < s := finiteEmpiricalBernsteinDyadicScale_pos j.1
      have hs_nonneg : 0 ≤ s := hs_pos.le
      have hlow : s ≤ u := hjlow
      have hhigh : u ≤ 2 * s := hjhigh
      have hfactor : 0 ≤ (u - s / 2) * (2 * s - u) :=
        mul_nonneg (by nlinarith) (by linarith)
      have hratio : u ^ (2 : Nat) + s ^ (2 : Nat) ≤ (5 / 2 : ℝ) * u * s := by
        nlinarith
      have hratio_div : u ^ (2 : Nat) / s + s ≤ (5 / 2 : ℝ) * u := by
        have hdiv := div_le_div_of_nonneg_right hratio hs_nonneg
        field_simp [ne_of_gt hs_pos] at hdiv ⊢
        nlinarith
      have hA_eq : A = u ^ (2 : Nat) * V / 2 := by
        nlinarith
      calc
        A / s + s * V / 2 =
            (V / 2) * (u ^ (2 : Nat) / s + s) := by
              rw [hA_eq]
              field_simp [ne_of_gt hs_pos]
        _ ≤ (V / 2) * ((5 / 2 : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hratio_div (by positivity)
        _ = (5 / 4 : ℝ) * R := by rw [hR_eq]; ring
        _ ≤ (5 / 4 : ℝ) * R + A / 2 := by linarith
    · have hu_gt : 2 < u := lt_of_not_ge hu_two
      refine ⟨⟨0, by omega⟩, ?_⟩
      have hA_twoV : 2 * V < A := by
        nlinarith [mul_pos (sub_pos.mpr hu_gt) (add_pos_of_pos_of_nonneg hu_pos hu_nonneg)]
      have hR_gt : 2 * V < R := by
        have htwoV_nonneg : 0 ≤ 2 * V := by positivity
        nlinarith
      rw [finiteEmpiricalBernsteinDyadicScale_zero]
      dsimp [R] at hR_gt ⊢
      nlinarith

/-- The posterior average of per-hypothesis Bessel empirical variances stays
in `[0, 1/2]`.  This is not the empirical variance of a posterior-averaged
loss. -/
theorem posteriorAverage_finiteEmpiricalVariance_mem_Icc
    [Fintype ι] {n : ℕ} (hn : 2 ≤ n)
    (ell : ι → Z → ℝ) (S : Fin n → Z)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) ∈
      Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
  constructor
  · unfold posteriorAverage
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hrho.nonneg i) (finiteEmpiricalVariance_nonneg hn ell i S))
  · unfold posteriorAverage
    calc
      (∑ i, rho i * finiteEmpiricalVariance ell i S) ≤
          ∑ i, rho i * ((1 : ℝ) / 2) := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left
            (finiteEmpiricalVariance_le_half hn ell i S (fun k => hell i (S k)))
            (hrho.nonneg i))
      _ = (1 : ℝ) / 2 := by
        rw [← Finset.sum_mul, hrho.sum_one]
        norm_num

/-- Direct square-root-plus-linear posterior bound for a finite dyadic grid,
assuming its final atom reaches the relevant empirical-variance scale. -/
theorem finiteEmpiricalBernsteinDyadic_posteriorRisk_le_sqrt_of_not_mem
    [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n) (J : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinDyadicBadSamples
      J n p prior ell delta)
    {rho : ι → ℝ} (hrho : IsPMF rho)
    (hcover :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) ≤
        2 *
          ((klDiv rho prior +
              Real.log (((J : ℝ) + 1) / delta)) / (n : ℝ))) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (5 / 4 : ℝ) *
          Real.sqrt
            (2 *
              posteriorAverage rho
                (fun i => finiteEmpiricalVariance ell i S) *
              (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
              (n : ℝ)) +
        (5 / 2 : ℝ) *
          (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
          (n : ℝ) := by
  let L := klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)
  let A := L / (n : ℝ)
  let V := posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hratio : 1 < ((J : ℝ) + 1) / delta := by
    rw [lt_div_iff₀ hdelta]
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hJ : (1 : ℝ) ≤ (J : ℝ) + 1 := by linarith
    linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    have hKL := klDiv_nonneg hrho hprior
    have hlog := Real.log_pos hratio
    linarith
  have hA_pos : 0 < A := div_pos hL_pos hnR
  have hV_mem :=
    posteriorAverage_finiteEmpiricalVariance_mem_Icc hn ell S hell hrho
  have hV_nonneg : 0 ≤ V := hV_mem.1
  have hcover' : finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
      2 * A := by simpa [A, V, L] using hcover
  obtain ⟨j, hj⟩ :=
    exists_dyadicScale_optimizer_bound J hA_pos hV_nonneg hcover'
  have hlogweight :
      Real.log
          (1 /
            (delta * finiteEmpiricalBernsteinDyadicWeight J j)) =
        Real.log (((J : ℝ) + 1) / delta) := by
    congr 1
    unfold finiteEmpiricalBernsteinDyadicWeight
    field_simp [ne_of_gt hdelta]
  have hbase :=
    finiteEmpiricalBernstein_posteriorRisk_le_scale_selected_of_not_mem
      (κ := Fin (J + 1)) hn p hp hprior ell
      (fun c => finiteEmpiricalBernsteinDyadicWeight_pos J c)
      (fun c => finiteEmpiricalBernsteinDyadicScale_pos c.1)
      (fun c => finiteEmpiricalBernsteinDyadicScale_le_two c.1)
      (fun _S _rho => j) S
      (by simpa [finiteEmpiricalBernsteinDyadicBadSamples] using hS) hrho
  rw [hlogweight] at hbase
  have hterm1 :
      (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
          (finiteEmpiricalBernsteinDyadicScale j.1 * (n : ℝ)) =
        A / finiteEmpiricalBernsteinDyadicScale j.1 := by
    dsimp [A, L]
    field_simp [ne_of_gt hnR,
      ne_of_gt (finiteEmpiricalBernsteinDyadicScale_pos j.1)]
  have hterm2 :
      2 * (klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)) /
          (n : ℝ) =
        2 * A := by
    dsimp [A, L]
    ring
  rw [hterm1, hterm2] at hbase
  change
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        A / finiteEmpiricalBernsteinDyadicScale j.1 + 2 * A +
        (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V at hbase
  change
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (n : ℝ)) +
        (5 / 2 : ℝ) * L / (n : ℝ)
  have hsimplify :
      A / finiteEmpiricalBernsteinDyadicScale j.1 + 2 * A +
          (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V ≤
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (n : ℝ)) +
          (5 / 2 : ℝ) * L / (n : ℝ) := by
    have hsqrt : Real.sqrt (2 * A * V) =
        Real.sqrt (2 * V * L / (n : ℝ)) := by
      congr 1
      dsimp [A]
      ring
    calc
      A / finiteEmpiricalBernsteinDyadicScale j.1 + 2 * A +
            (finiteEmpiricalBernsteinDyadicScale j.1 / 2) * V ≤
          (5 / 4 : ℝ) * Real.sqrt (2 * A * V) + A / 2 + 2 * A := by
        nlinarith [hj]
      _ = (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (n : ℝ)) +
            (5 / 2 : ℝ) * L / (n : ℝ) := by
        rw [hsqrt]
        dsimp [A]
        ring
  linarith

/-! ## A canonical logarithmic grid -/

/-- The predeclared dyadic grid depth used by the closed-form endpoint. -/
def finiteEmpiricalBernsteinGridDepth (n : ℕ) : ℕ :=
  Nat.clog 2 n

lemma finiteEmpiricalBernsteinGridDepth_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < finiteEmpiricalBernsteinGridDepth n := by
  unfold finiteEmpiricalBernsteinGridDepth
  exact Nat.clog_pos (by omega) (lt_of_lt_of_le (by omega) hn)

/-- At depth `clog 2 n`, the last dyadic scale is at most `2/n`. -/
lemma finiteEmpiricalBernsteinDyadicScale_gridDepth_le
    {n : ℕ} (hn : 2 ≤ n) :
    finiteEmpiricalBernsteinDyadicScale
        (finiteEmpiricalBernsteinGridDepth n) ≤
      2 / (n : ℝ) := by
  let J := finiteEmpiricalBernsteinGridDepth n
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hpowNat : n ≤ 2 ^ J := by
    dsimp [J, finiteEmpiricalBernsteinGridDepth]
    exact Nat.le_pow_clog (by omega) n
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ J := by
    exact_mod_cast hpowNat
  unfold finiteEmpiricalBernsteinDyadicScale
  exact div_le_div_of_nonneg_left (by norm_num) hnR hpow

/-- The canonical logarithmic grid automatically reaches the continuous
optimizer for every posterior. No sample- or posterior-dependent grid depth
is assumed. -/
theorem finiteEmpiricalBernsteinGridDepth_coverage
    [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (S : Fin n → Z)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    finiteEmpiricalBernsteinDyadicScale
          (finiteEmpiricalBernsteinGridDepth n) ^ (2 : Nat) *
        posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) ≤
      2 *
        ((klDiv rho prior +
            Real.log
              ((((finiteEmpiricalBernsteinGridDepth n : ℕ) : ℝ) + 1) /
                delta)) /
          (n : ℝ)) := by
  let J := finiteEmpiricalBernsteinGridDepth n
  let V := posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S)
  let L := klDiv rho prior + Real.log (((J : ℝ) + 1) / delta)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hnR_two : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hJpos : 0 < J := finiteEmpiricalBernsteinGridDepth_pos hn
  have hJoneR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJpos
  have hratio : (2 : ℝ) ≤ ((J : ℝ) + 1) / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log (((J : ℝ) + 1) / delta) := by
    calc
      (1 : ℝ) / 2 = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
      _ ≤ Real.log (((J : ℝ) + 1) / delta) :=
        Real.log_le_log (by norm_num) hratio
  have hLhalf : (1 : ℝ) / 2 ≤ L := by
    dsimp [L]
    nlinarith [klDiv_nonneg hrho hprior]
  have hVmem :=
    posteriorAverage_finiteEmpiricalVariance_mem_Icc hn ell S hell hrho
  have hVnonneg : 0 ≤ V := hVmem.1
  have hVhalf : V ≤ (1 : ℝ) / 2 := hVmem.2
  have hsle : finiteEmpiricalBernsteinDyadicScale J ≤ 2 / (n : ℝ) :=
    finiteEmpiricalBernsteinDyadicScale_gridDepth_le hn
  let x : ℝ := 2 / (n : ℝ)
  have hxnonneg : 0 ≤ x := by dsimp [x]; positivity
  have hxone : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one hnR]
    exact hnR_two
  have hscale_sq :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) ≤ x ^ (2 : Nat) :=
    (sq_le_sq₀ (finiteEmpiricalBernsteinDyadicScale_pos J).le hxnonneg).mpr hsle
  have hleft :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
        x ^ (2 : Nat) * ((1 : ℝ) / 2) := by
    calc
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
          x ^ (2 : Nat) * V :=
        mul_le_mul_of_nonneg_right hscale_sq hVnonneg
      _ ≤ x ^ (2 : Nat) * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hVhalf (sq_nonneg x)
  have hxsq : x ^ (2 : Nat) ≤ x := by
    nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hxone)]
  have hsmall : x ^ (2 : Nat) * ((1 : ℝ) / 2) ≤ 1 / (n : ℝ) := by
    calc
      x ^ (2 : Nat) * ((1 : ℝ) / 2) ≤ x * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hxsq (by norm_num)
      _ = 1 / (n : ℝ) := by dsimp [x]; ring
  have hunit : 1 / (n : ℝ) ≤ 2 * (L / (n : ℝ)) := by
    calc
      1 / (n : ℝ) ≤ (2 * L) / (n : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith) hnR.le
      _ = 2 * (L / (n : ℝ)) := by ring
  have hfinal :
      finiteEmpiricalBernsteinDyadicScale J ^ (2 : Nat) * V ≤
        2 * (L / (n : ℝ)) :=
    hleft.trans (hsmall.trans hunit)
  simpa [J, V, L] using hfinal

/-- The single bad-sample set used by the canonical logarithmic-grid
empirical-Bernstein theorem. -/
def finiteEmpiricalBernsteinSqrtBadSamples
    [Fintype Z] [Fintype ι] (n : ℕ)
    (p : Z → ℝ) (prior : ι → ℝ) (ell : ι → Z → ℝ)
    (delta : ℝ) : Finset (Fin n → Z) :=
  finiteEmpiricalBernsteinDyadicBadSamples
    (finiteEmpiricalBernsteinGridDepth n) n p prior ell delta

/-- The canonical logarithmic-grid bad event has mass at most `delta`. -/
theorem finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta
    [Fintype Z] [DecidableEq Z] [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑ S ∈ finiteEmpiricalBernsteinSqrtBadSamples
        n p prior ell delta,
      finiteProductSampleWeight p S) ≤ delta := by
  simpa [finiteEmpiricalBernsteinSqrtBadSamples] using
    finiteEmpiricalBernsteinDyadic_badSamples_mass_le_delta
      hn (finiteEmpiricalBernsteinGridDepth n) p hp hprior ell hell hdelta

/-- Closed-form empirical-Bernstein PAC-Bayes bound on the canonical
predeclared logarithmic grid, paired with
`finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta` above.

On one event of mass at least `1-delta`, this holds for every finite posterior,
including a posterior selected after observing the sample. The variance is
the posterior average of per-hypothesis Bessel empirical variances. -/
theorem finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem
    [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (S : Fin n → Z)
    (hS : S ∉ finiteEmpiricalBernsteinSqrtBadSamples
      n p prior ell delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (5 / 4 : ℝ) *
          Real.sqrt
            (2 *
              posteriorAverage rho
                (fun i => finiteEmpiricalVariance ell i S) *
              (klDiv rho prior +
                Real.log
                  ((((finiteEmpiricalBernsteinGridDepth n : ℕ) : ℝ) + 1) /
                    delta)) /
              (n : ℝ)) +
        (5 / 2 : ℝ) *
          (klDiv rho prior +
            Real.log
              ((((finiteEmpiricalBernsteinGridDepth n : ℕ) : ℝ) + 1) /
                delta)) /
          (n : ℝ) := by
  simpa using
    (finiteEmpiricalBernsteinDyadic_posteriorRisk_le_sqrt_of_not_mem
      hn (finiteEmpiricalBernsteinGridDepth n) p hp hprior ell hell
      hdelta hdelta_one S
      (by simpa [finiteEmpiricalBernsteinSqrtBadSamples] using hS)
      hrho
      (finiteEmpiricalBernsteinGridDepth_coverage
        hn hprior ell hell hdelta hdelta_one S hrho))

end

end FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
