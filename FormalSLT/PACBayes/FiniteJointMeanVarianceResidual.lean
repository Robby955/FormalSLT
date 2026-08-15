/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

/-!
# Exact residual envelope for the finite joint mean/variance catalog

This module completes the scalar optimization left open by the zero-residual
branch of `FiniteJointMeanVariancePACBayes`.  For

`b = exp t - 1 - t`

and

`r = exp (-t) * kappa_n(eta) / n`,

the retained population-variance term per observation is

`v ↦ log (1 + b * v) - r * v`,

where a `[0,1]`-valued loss gives `0 ≤ v ≤ 1 / 4`.  The definition
`finiteJointMeanVarianceXi` is the exact three-branch maximum of this function
on that interval.  The resulting posterior-risk theorem retains the one-event,
one-KL, fixed-sample, finite-catalog scope of the parent module and adds the
explicit residual penalty `xi / t`.

No continuous tilt optimization or time-uniform claim is made here.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVarianceResidual

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

noncomputable section

variable {κ ι Z : Type*}

/-- The Bennett coefficient `exp t - 1 - t`. -/
def finiteJointMeanVariancePsi (t : ℝ) : ℝ :=
  Real.exp t - 1 - t

/-- The transported population-variance coefficient per observation. -/
def finiteJointMeanVarianceResidualRate (n : ℕ) (t eta : ℝ) : ℝ :=
  Real.exp (-t) * finiteJointMeanVarianceKappa n eta / (n : ℝ)

/-- The retained population-variance residual per observation. -/
def finiteJointMeanVarianceResidual (n : ℕ) (t eta v : ℝ) : ℝ :=
  Real.log (1 + finiteJointMeanVariancePsi t * v) -
    finiteJointMeanVarianceResidualRate n t eta * v

/-- Exact maximum of the retained residual over `0 ≤ v ≤ 1 / 4`.

The branches correspond respectively to a maximum at zero, at `1 / 4`, and
at the interior stationary point `1 / r - 1 / b`. -/
def finiteJointMeanVarianceXi (n : ℕ) (t eta : ℝ) : ℝ :=
  let b := finiteJointMeanVariancePsi t
  let r := finiteJointMeanVarianceResidualRate n t eta
  if b ≤ r then
    0
  else if r ≤ b / (1 + b / 4) then
    Real.log (1 + b / 4) - r / 4
  else
    Real.log (b / r) - 1 + r / b

/-- The Bennett coefficient is nonnegative for every real tilt. -/
theorem finiteJointMeanVariancePsi_nonneg (t : ℝ) :
    0 ≤ finiteJointMeanVariancePsi t := by
  unfold finiteJointMeanVariancePsi
  linarith [Real.add_one_le_exp t]

/-- A nonnegative joint MGF coefficient gives a nonnegative transported rate. -/
theorem finiteJointMeanVarianceResidualRate_nonneg
    {n : ℕ} {t eta : ℝ}
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    0 ≤ finiteJointMeanVarianceResidualRate n t eta := by
  unfold finiteJointMeanVarianceResidualRate
  exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hkappa)
    (Nat.cast_nonneg n)

/-- First branch of the exact residual formula. -/
theorem finiteJointMeanVarianceXi_eq_zero_of_ge
    {n : ℕ} {t eta : ℝ}
    (hge : finiteJointMeanVariancePsi t ≤
      finiteJointMeanVarianceResidualRate n t eta) :
    finiteJointMeanVarianceXi n t eta = 0 := by
  simp [finiteJointMeanVarianceXi, hge]

/-- Second branch of the exact residual formula. -/
theorem finiteJointMeanVarianceXi_eq_quarter_of_lt_of_le
    {n : ℕ} {t eta : ℝ}
    (hlt : finiteJointMeanVarianceResidualRate n t eta <
      finiteJointMeanVariancePsi t)
    (hle : finiteJointMeanVarianceResidualRate n t eta ≤
      finiteJointMeanVariancePsi t /
        (1 + finiteJointMeanVariancePsi t / 4)) :
    finiteJointMeanVarianceXi n t eta =
      Real.log (1 + finiteJointMeanVariancePsi t / 4) -
        finiteJointMeanVarianceResidualRate n t eta / 4 := by
  simp [finiteJointMeanVarianceXi, not_le.mpr hlt, hle]

/-- Third branch of the exact residual formula. -/
theorem finiteJointMeanVarianceXi_eq_interior_of_lt
    {n : ℕ} {t eta : ℝ}
    (hlt : finiteJointMeanVarianceResidualRate n t eta <
      finiteJointMeanVariancePsi t)
    (hthreshold : finiteJointMeanVariancePsi t /
        (1 + finiteJointMeanVariancePsi t / 4) <
      finiteJointMeanVarianceResidualRate n t eta) :
    finiteJointMeanVarianceXi n t eta =
      Real.log
          (finiteJointMeanVariancePsi t /
            finiteJointMeanVarianceResidualRate n t eta) -
        1 + finiteJointMeanVarianceResidualRate n t eta /
          finiteJointMeanVariancePsi t := by
  simp [finiteJointMeanVarianceXi, not_le.mpr hlt,
    not_le.mpr hthreshold]

/-- The exact three-branch formula bounds the retained residual at every
variance value in `[0, 1 / 4]`. -/
theorem finiteJointMeanVarianceResidual_le_xi
    {n : ℕ} {t eta v : ℝ}
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta)
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 4 : ℝ)) :
    finiteJointMeanVarianceResidual n t eta v ≤
      finiteJointMeanVarianceXi n t eta := by
  let b := finiteJointMeanVariancePsi t
  let r := finiteJointMeanVarianceResidualRate n t eta
  have hb : 0 ≤ b := by
    simpa [b] using finiteJointMeanVariancePsi_nonneg t
  have hr : 0 ≤ r := by
    simpa [r] using finiteJointMeanVarianceResidualRate_nonneg
      (t := t) hkappa
  have hv0 : 0 ≤ v := hv.1
  have hvq : v ≤ (1 : ℝ) / 4 := hv.2
  have hx : 0 < 1 + b * v := by
    nlinarith [mul_nonneg hb hv0]
  by_cases hbr : b ≤ r
  · have hlog : Real.log (1 + b * v) ≤ b * v := by
      linarith [Real.log_le_sub_one_of_pos hx]
    have hmul : b * v ≤ r * v :=
      mul_le_mul_of_nonneg_right hbr hv0
    simpa [finiteJointMeanVarianceResidual, finiteJointMeanVarianceXi,
      b, r, hbr] using (show Real.log (1 + b * v) - r * v ≤ 0 by
        linarith)
  · have hrb : r < b := lt_of_not_ge hbr
    have hbpos : 0 < b := lt_of_le_of_lt hr hrb
    have hy : 0 < 1 + b / 4 := by nlinarith
    by_cases hrq : r ≤ b / (1 + b / 4)
    · have hratio : 0 < (1 + b * v) / (1 + b / 4) :=
        div_pos hx hy
      have hlogratio := Real.log_le_sub_one_of_pos hratio
      have hlogdiff :
          Real.log (1 + b * v) - Real.log (1 + b / 4) ≤
            (1 + b * v) / (1 + b / 4) - 1 := by
        rw [← Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
        exact hlogratio
      have hratio_eq :
          (1 + b * v) / (1 + b / 4) - 1 =
            (b / (1 + b / 4)) * (v - 1 / 4) := by
        field_simp [ne_of_gt hy]
        ring
      have hslope :
          (b / (1 + b / 4)) * (v - 1 / 4) ≤
            r * (v - 1 / 4) :=
        mul_le_mul_of_nonpos_right hrq (sub_nonpos.mpr hvq)
      have hbound :
          Real.log (1 + b * v) - r * v ≤
            Real.log (1 + b / 4) - r / 4 := by
        rw [hratio_eq] at hlogdiff
        linarith
      simpa [finiteJointMeanVarianceResidual, finiteJointMeanVarianceXi,
        b, r, hbr, hrq] using hbound
    · have hthreshold : b / (1 + b / 4) < r := lt_of_not_ge hrq
      have hrpos : 0 < r := lt_of_le_of_lt
        (by positivity : 0 ≤ b / (1 + b / 4)) hthreshold
      have hbratio : 0 < b / r := div_pos hbpos hrpos
      have hu : 0 < (1 + b * v) / (b / r) := div_pos hx hbratio
      have hlogratio := Real.log_le_sub_one_of_pos hu
      have hlogdiff :
          Real.log (1 + b * v) - Real.log (b / r) ≤
            (1 + b * v) / (b / r) - 1 := by
        rw [← Real.log_div (ne_of_gt hx) (ne_of_gt hbratio)]
        exact hlogratio
      have hratio_eq :
          (1 + b * v) / (b / r) - 1 = r / b + r * v - 1 := by
        field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
      have hbound :
          Real.log (1 + b * v) - r * v ≤
            Real.log (b / r) - 1 + r / b := by
        rw [hratio_eq] at hlogdiff
        linarith
      simpa [finiteJointMeanVarianceResidual, finiteJointMeanVarianceXi,
        b, r, hbr, hrq] using hbound

/-- The three-branch residual envelope is attained at zero, at `1 / 4`, or at
the interior stationary point.  Together with
`finiteJointMeanVarianceResidual_le_xi`, this identifies `xi` as the exact
maximum on `[0, 1 / 4]`. -/
theorem finiteJointMeanVarianceXi_attained
    {n : ℕ} {t eta : ℝ}
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    ∃ v : ℝ, v ∈ Set.Icc (0 : ℝ) (1 / 4 : ℝ) ∧
      finiteJointMeanVarianceResidual n t eta v =
        finiteJointMeanVarianceXi n t eta := by
  let b := finiteJointMeanVariancePsi t
  let r := finiteJointMeanVarianceResidualRate n t eta
  have hb : 0 ≤ b := by
    simpa [b] using finiteJointMeanVariancePsi_nonneg t
  have hr : 0 ≤ r := by
    simpa [r] using finiteJointMeanVarianceResidualRate_nonneg
      (t := t) hkappa
  by_cases hbr : b ≤ r
  · refine ⟨0, by norm_num, ?_⟩
    simp [finiteJointMeanVarianceResidual, finiteJointMeanVarianceXi,
      b, r, hbr]
  · have hrb : r < b := lt_of_not_ge hbr
    have hbpos : 0 < b := lt_of_le_of_lt hr hrb
    have hy : 0 < 1 + b / 4 := by nlinarith
    by_cases hrq : r ≤ b / (1 + b / 4)
    · refine ⟨(1 : ℝ) / 4, by norm_num, ?_⟩
      simp [finiteJointMeanVarianceResidual, finiteJointMeanVarianceXi,
        b, r, hbr, hrq]
      ring_nf
    · have hthreshold : b / (1 + b / 4) < r := lt_of_not_ge hrq
      have hrpos : 0 < r := lt_of_le_of_lt
        (by positivity : 0 ≤ b / (1 + b / 4)) hthreshold
      let vstar := 1 / r - 1 / b
      have hvstar0 : 0 ≤ vstar := by
        dsimp [vstar]
        field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
        nlinarith
      have hthreshold_mul : b < r * (1 + b / 4) :=
        (div_lt_iff₀ hy).mp hthreshold
      have hvstarq : vstar ≤ (1 : ℝ) / 4 := by
        dsimp [vstar]
        field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
        nlinarith
      have harg : 1 + b * vstar = b / r := by
        dsimp [vstar]
        field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
        ring
      have hpenalty : r * vstar = 1 - r / b := by
        dsimp [vstar]
        field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
      refine ⟨vstar, ⟨hvstar0, hvstarq⟩, ?_⟩
      unfold finiteJointMeanVarianceResidual
      change Real.log (1 + b * vstar) - r * vstar = _
      rw [harg, hpenalty]
      simp [finiteJointMeanVarianceXi, b, r, hbr, hrq]
      ring_nf

/-- `xi` is the greatest value of the retained residual on the bounded-loss
variance interval. -/
theorem finiteJointMeanVarianceXi_isGreatest
    {n : ℕ} {t eta : ℝ}
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    IsGreatest
      (finiteJointMeanVarianceResidual n t eta ''
        Set.Icc (0 : ℝ) (1 / 4 : ℝ))
      (finiteJointMeanVarianceXi n t eta) := by
  constructor
  · rcases finiteJointMeanVarianceXi_attained (t := t) hkappa with
      ⟨v, hv, hvalue⟩
    exact ⟨v, hv, hvalue⟩
  · intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact finiteJointMeanVarianceResidual_le_xi hkappa hv

/-- The exact residual maximum is nonnegative because the residual vanishes at
population variance zero. -/
theorem finiteJointMeanVarianceXi_nonneg
    {n : ℕ} {t eta : ℝ}
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    0 ≤ finiteJointMeanVarianceXi n t eta := by
  have h := finiteJointMeanVarianceResidual_le_xi
    (t := t) (eta := eta) (v := 0) hkappa (by norm_num)
  simpa [finiteJointMeanVarianceResidual] using h

/-- Posterior-averaged population variance stays in `[0, 1 / 4]` for a
posterior PMF over `[0,1]`-valued losses. -/
theorem posteriorAverage_finitePopulationVariance_mem_Icc
    [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationVariance p ell) ∈
      Set.Icc (0 : ℝ) (1 / 4 : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hrho.nonneg i)
      (finitePopulationVariance_nonneg p hp ell i)
  · calc
      posteriorAverage rho (finitePopulationVariance p ell) ≤
          ∑ i : ι, rho i * ((1 : ℝ) / 4) := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left
            (finitePopulationVariance_le_quarter p hp ell i (hell i))
            (hrho.nonneg i))
      _ = 1 / 4 := by rw [← Finset.sum_mul, hrho.sum_one]; norm_num

/-- Fully explicit one-event posterior-risk bound for every branch of the
retained population-variance residual. -/
theorem finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    (c : κ) (htc : 0 < t c)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / (delta * w c))) /
          (t c * (n : ℝ)) +
        (eta c / t c) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        finiteJointMeanVarianceXi n (t c) (eta c) / t c := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  let V := posteriorAverage rho (finitePopulationVariance p ell)
  have hV : V ∈ Set.Icc (0 : ℝ) (1 / 4 : ℝ) := by
    simpa [V] using
      posteriorAverage_finitePopulationVariance_mem_Icc p hp ell hell hrho
  have hresidual := finiteJointMeanVarianceResidual_le_xi
    (t := t c) (eta := eta c) hkappa hV
  have hraw := finiteJointMeanVariance_posteriorGap_le_of_not_mem
    n p hp hprior ell hw S hS c hrho
  have hrate :
      (n : ℝ) * finiteJointMeanVarianceResidualRate n (t c) (eta c) =
        Real.exp (-t c) * finiteJointMeanVarianceKappa n (eta c) := by
    unfold finiteJointMeanVarianceResidualRate
    field_simp [ne_of_gt hnR]
  have hcollapsed :
      t c * (n : ℝ) *
          (posteriorAverage rho (finitePopulationRisk p ell) -
            posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) ≤
        klDiv rho prior + Real.log (1 / (delta * w c)) +
          eta c * (n : ℝ) *
            posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          (n : ℝ) * finiteJointMeanVarianceXi n (t c) (eta c) := by
    have hresidual_scaled :=
      mul_le_mul_of_nonneg_left hresidual (le_of_lt hnR)
    unfold finiteJointMeanVarianceResidual finiteJointMeanVariancePsi at hresidual_scaled
    rw [mul_sub,
      ← mul_assoc (n : ℝ)
        (finiteJointMeanVarianceResidualRate n (t c) (eta c)) V,
      hrate] at hresidual_scaled
    dsimp [V] at hresidual_scaled
    linarith
  have hdenom : 0 < t c * (n : ℝ) := mul_pos htc hnR
  have hdiv :
      posteriorAverage rho (finitePopulationRisk p ell) -
          posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) ≤
        (klDiv rho prior + Real.log (1 / (delta * w c)) +
            eta c * (n : ℝ) *
              posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
            (n : ℝ) * finiteJointMeanVarianceXi n (t c) (eta c)) /
          (t c * (n : ℝ)) := by
    rw [le_div_iff₀ hdenom]
    nlinarith
  have hsplit :
      (klDiv rho prior + Real.log (1 / (delta * w c)) +
            eta c * (n : ℝ) *
              posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
            (n : ℝ) * finiteJointMeanVarianceXi n (t c) (eta c)) /
          (t c * (n : ℝ)) =
        (klDiv rho prior + Real.log (1 / (delta * w c))) /
            (t c * (n : ℝ)) +
          (eta c / t c) *
            posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
          finiteJointMeanVarianceXi n (t c) (eta c) / t c := by
    field_simp [ne_of_gt htc, ne_of_gt hnR]
  calc
    posteriorAverage rho (finitePopulationRisk p ell) =
        posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
          (posteriorAverage rho (finitePopulationRisk p ell) -
            posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S)) := by
      ring
    _ ≤ posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior + Real.log (1 / (delta * w c)) +
            eta c * (n : ℝ) *
              posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
            (n : ℝ) * finiteJointMeanVarianceXi n (t c) (eta c)) /
          (t c * (n : ℝ)) := by
      simpa [add_comm] using
        add_le_add_left hdiv
          (posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S))
    _ = _ := by rw [hsplit]; ring

/-- Selector form of the exact-residual posterior-risk bound. -/
theorem finiteJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem
    [Fintype κ] [Fintype Z] [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (ell : ι → Z → ℝ)
    (hell : ∀ i z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta w : κ → ℝ}
    (hw : ∀ c, 0 < w c) {delta : ℝ}
    (ht_pos : ∀ c, 0 < t c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa n (eta c))
    (select : (Fin n → Z) → (ι → ℝ) → κ)
    (S : Fin n → Z)
    (hS : S ∉ finiteJointMeanVarianceCatalogBadSamples n p prior ell t eta w delta)
    {rho : ι → ℝ} (hrho : IsPMF rho) :
    posteriorAverage rho (finitePopulationRisk p ell) ≤
      posteriorAverage rho (fun i => finiteEmpiricalRisk ell i S) +
        (klDiv rho prior +
            Real.log (1 / (delta * w (select S rho)))) /
          (t (select S rho) * (n : ℝ)) +
        (eta (select S rho) / t (select S rho)) *
          posteriorAverage rho (fun i => finiteEmpiricalVariance ell i S) +
        finiteJointMeanVarianceXi n
            (t (select S rho)) (eta (select S rho)) /
          t (select S rho) :=
  finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem
    hn p hp hprior ell hell hw S hS (select S rho)
      (ht_pos (select S rho)) (hkappa (select S rho)) hrho

end

end FormalSLT.PACBayes.FiniteJointMeanVarianceResidual
