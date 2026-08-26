/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.ForwardPredictableMeanBesselProcess

/-!
# Predictable-tilt forward empirical-Bernstein processes

This module allows the empirical-Bernstein tilt to vary predictably with time
and the observed past.  For a predictable conditional-mean process `mean` and
a predictable tilt process `lambda`, the one-step factor is

`exp (lambda_k * (X_k - mean_k) - psi(lambda_k) * (X_k - P_k)^2)`.

Under bounded observations, exact conditional centering, and a uniform tilt
cap strictly below one, the finite product of these factors is an e-process.
The result is process-level: varying tilts produce weighted linear and
quadratic sums, so no unweighted hybrid-Bessel boundary is claimed here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- One empirical-Bernstein factor with predictable conditional mean and
predictable tilt. -/
def forwardPredictableTiltMeanEmpiricalBernsteinFactor {Omega : Type*}
    (X mean lambda : ℕ → Omega → ℝ) (k : ℕ) (omega : Omega) : ℝ :=
  Real.exp
    (lambda k omega * (X k omega - mean k omega) -
      forwardEmpiricalBernsteinPsi (lambda k omega) *
        (X k omega - forwardPredictorProcess X k omega) ^ 2)

/-- Exponential process obtained by summing predictable-tilt
empirical-Bernstein scores. -/
def forwardPredictableTiltMeanEmpiricalBernsteinProcess {Omega : Type*}
    (X mean lambda : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  Real.exp
    (∑ k ∈ Finset.range n,
      (lambda k omega * (X k omega - mean k omega) -
        forwardEmpiricalBernsteinPsi (lambda k omega) *
          (X k omega - forwardPredictorProcess X k omega) ^ 2))

/-- Exact multiplicative update of the predictable-tilt process. -/
lemma forwardPredictableTiltMeanEmpiricalBernsteinProcess_succ
    {Omega : Type*} (X mean lambda : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda (n + 1) omega =
      forwardPredictableTiltMeanEmpiricalBernsteinProcess
          X mean lambda n omega *
        forwardPredictableTiltMeanEmpiricalBernsteinFactor
          X mean lambda n omega := by
  unfold forwardPredictableTiltMeanEmpiricalBernsteinProcess
    forwardPredictableTiltMeanEmpiricalBernsteinFactor
  rw [Finset.sum_range_succ, ← Real.exp_add]

/-- The empirical-Bernstein cumulant preserves strong measurability under
composition with a real-valued function. -/
lemma stronglyMeasurable_forwardEmpiricalBernsteinPsi_comp
    {Omega : Type*} {m : MeasurableSpace Omega}
    {lambda : Omega → ℝ} (hlambda : StronglyMeasurable[m] lambda) :
    StronglyMeasurable[m]
      (fun omega => forwardEmpiricalBernsteinPsi (lambda omega)) := by
  unfold forwardEmpiricalBernsteinPsi
  have harg : StronglyMeasurable[m] (fun omega => 1 - lambda omega) :=
    stronglyMeasurable_const.sub hlambda
  have hlog : StronglyMeasurable[m]
      (fun omega => Real.log (1 - lambda omega)) :=
    (Real.measurable_log.comp harg.measurable).stronglyMeasurable
  exact hlog.neg.sub hlambda

/-- The predictable-tilt one-step factor has conditional expectation at most
one. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinFactor_condExp_le_one
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ} {k : ℕ}
    (hL1 : L < 1)
    (hX_meas : Measurable (X k)) (hX_int : Integrable (X k) mu)
    (hP_meas : StronglyMeasurable[F k] (forwardPredictorProcess X k))
    (hmean_meas : StronglyMeasurable[F k] (mean k))
    (hlambda_meas : StronglyMeasurable[F k] (lambda k))
    (hX_unit : ∀ᵐ omega ∂mu, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hP_unit : ∀ᵐ omega ∂mu,
      0 ≤ forwardPredictorProcess X k omega ∧
        forwardPredictorProcess X k omega ≤ 1)
    (hlambda_range : ∀ᵐ omega ∂mu,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : mu[X k | F k] =ᵐ[mu] mean k) :
    mu[forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k | F k] ≤ᵐ[mu] fun _ => (1 : ℝ) := by
  let P : Omega → ℝ := forwardPredictorProcess X k
  let M : Omega → ℝ := mean k
  let T : Omega → ℝ := lambda k
  let A : Omega → ℝ := fun omega => T omega * (P omega - M omega)
  let Z : Omega → ℝ := fun omega => Real.exp (A omega)
  let Y : Omega → ℝ := fun omega => 1 + T omega * (X k omega - P omega)
  let C : ℝ := Real.exp L
  have hM_unit : ∀ᵐ omega ∂mu, 0 ≤ M omega ∧ M omega ≤ 1 := by
    simpa [M] using predictableMeanProcess_mem_Icc_ae hX_int hX_unit hmean
  have hP_global : StronglyMeasurable P := hP_meas.mono (F.le k)
  have hM_global : StronglyMeasurable M := hmean_meas.mono (F.le k)
  have hT_global : StronglyMeasurable T := hlambda_meas.mono (F.le k)
  have hT_bdd : ∀ᵐ omega ∂mu, |T omega| ≤ L := by
    filter_upwards [hlambda_range] with omega h
    simpa [T, abs_of_nonneg h.1] using h.2
  have hP_bdd : ∀ᵐ omega ∂mu, |P omega| ≤ (1 : ℝ) := by
    filter_upwards [hP_unit] with omega h
    simpa [P, abs_of_nonneg h.1] using h.2
  have hP_int : Integrable P mu :=
    Integrable.of_bound hP_global.aestronglyMeasurable 1 hP_bdd
  have hR_int : Integrable (fun omega => X k omega - P omega) mu :=
    hX_int.sub hP_int
  have hTR_int : Integrable
      (fun omega => T omega * (X k omega - P omega)) mu :=
    hR_int.bdd_mul hT_global.aestronglyMeasurable hT_bdd
  have hY_int : Integrable Y mu := (integrable_const 1).add hTR_int
  have hZ_meas : StronglyMeasurable[F k] Z := by
    have hA : StronglyMeasurable[F k] A :=
      hlambda_meas.mul (hP_meas.sub hmean_meas)
    exact Real.continuous_exp.comp_stronglyMeasurable hA
  have hZ_bdd : ∀ᵐ omega ∂mu, |Z omega| ≤ C := by
    filter_upwards [hP_unit, hM_unit, hlambda_range] with
      omega hP_omega hM_omega hT_omega
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    dsimp [A, C, P, M, T]
    have hdiff :
        forwardPredictorProcess X k omega - mean k omega ≤ 1 := by
      linarith
    have hmul_le :
        lambda k omega *
            (forwardPredictorProcess X k omega - mean k omega) ≤
          lambda k omega := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hdiff hT_omega.1
    exact hmul_le.trans hT_omega.2
  have hcomparison_int : Integrable (fun omega => Z omega * Y omega) mu :=
    hY_int.bdd_mul (hZ_meas.mono (F.le k)).aestronglyMeasurable hZ_bdd
  have hX_global : StronglyMeasurable (X k) := hX_meas.stronglyMeasurable
  have hpsi_global : StronglyMeasurable
      (fun omega => forwardEmpiricalBernsteinPsi (T omega)) :=
    stronglyMeasurable_forwardEmpiricalBernsteinPsi_comp hT_global
  have hfactor_meas : Measurable
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k) := by
    apply StronglyMeasurable.measurable
    unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hT_global.mul (hX_global.sub hM_global)).sub
        (hpsi_global.mul ((hX_global.sub hP_global).pow 2)))
  have hpoint : ∀ᵐ omega ∂mu,
      forwardPredictableTiltMeanEmpiricalBernsteinFactor
          X mean lambda k omega ≤ Z omega * Y omega := by
    filter_upwards [hX_unit, hP_unit, hlambda_range] with
      omega hX_omega hP_omega hT_omega
    have hz : -(1 : ℝ) ≤ X k omega - P omega := by
      dsimp [P] at hP_omega ⊢
      linarith
    have hT1 : T omega < 1 := lt_of_le_of_lt hT_omega.2 hL1
    have hs := exp_forwardEmpiricalBernstein_le_one_add
      hT_omega.1 hT1 hz
    calc
      forwardPredictableTiltMeanEmpiricalBernsteinFactor
          X mean lambda k omega =
          Real.exp (A omega) *
            Real.exp (T omega * (X k omega - P omega) -
              forwardEmpiricalBernsteinPsi (T omega) *
                (X k omega - P omega) ^ 2) := by
            rw [← Real.exp_add]
            unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
            dsimp [A, P, M, T]
            congr 1
            ring
      _ ≤ Real.exp (A omega) *
          (1 + T omega * (X k omega - P omega)) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Z omega * Y omega := rfl
  have hfactor_int : Integrable
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k) mu := by
    refine Integrable.mono' hcomparison_int
      hfactor_meas.aestronglyMeasurable ?_
    filter_upwards [hpoint] with omega h
    rw [Real.norm_eq_abs, abs_of_pos (by
      unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
      exact Real.exp_pos _)]
    exact h
  have hmono :
      mu[forwardPredictableTiltMeanEmpiricalBernsteinFactor
          X mean lambda k | F k] ≤ᵐ[mu]
        mu[fun omega => Z omega * Y omega | F k] :=
    condExp_mono hfactor_int hcomparison_int hpoint
  have hpull :
      mu[fun omega => Z omega * Y omega | F k] =ᵐ[mu]
        fun omega => Z omega * (mu[Y | F k]) omega :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (F.le k) hZ_meas hZ_bdd hY_int
  have hP_cond : mu[P | F k] = P :=
    condExp_of_stronglyMeasurable (F.le k) hP_meas hP_int
  have hR_cond :
      mu[fun omega => X k omega - P omega | F k] =ᵐ[mu]
        fun omega => M omega - P omega := by
    have hsub := condExp_sub hX_int hP_int (F k)
    filter_upwards [hsub, hmean] with omega hsub_omega hmean_omega
    change mu[X k - P | F k] omega = M omega - P omega
    rw [hsub_omega]
    simp only [Pi.sub_apply]
    rw [hmean_omega, hP_cond]
  have hTR_cond :
      mu[fun omega => T omega * (X k omega - P omega) | F k] =ᵐ[mu]
        fun omega => T omega *
          (mu[fun omega => X k omega - P omega | F k]) omega :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (F.le k) hlambda_meas hT_bdd hR_int
  have hY_cond : mu[Y | F k] =ᵐ[mu]
      fun omega => 1 + T omega * (M omega - P omega) := by
    have hadd := condExp_add (integrable_const (1 : ℝ)) hTR_int (F k)
    have hone : mu[(fun _ : Omega => (1 : ℝ)) | F k] =
        fun _ => (1 : ℝ) := condExp_const (F.le k) 1
    filter_upwards [hadd, hTR_cond, hR_cond] with
      omega hadd_omega hTR_omega hR_omega
    change mu[(fun _ : Omega => (1 : ℝ)) +
      (fun omega => T omega * (X k omega - P omega)) | F k] omega =
        1 + T omega * (M omega - P omega)
    rw [hadd_omega]
    simp only [Pi.add_apply]
    rw [hone, hTR_omega, hR_omega]
  filter_upwards [hmono, hpull, hY_cond] with
    omega hmono_omega hpull_omega hY_omega
  refine hmono_omega.trans ?_
  rw [hpull_omega, hY_omega]
  have ha : 1 - A omega ≤ Real.exp (-A omega) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-A omega)
  calc
    Z omega * (1 + T omega * (M omega - P omega)) =
        Real.exp (A omega) * (1 - A omega) := by
      dsimp [Z, A]
      congr 1
      ring
    _ ≤ Real.exp (A omega) * Real.exp (-A omega) :=
      mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- A predictable-tilt factor is strongly measurable when its observation,
predictor, conditional mean, and tilt are strongly measurable. -/
theorem stronglyMeasurable_forwardPredictableTiltMeanEmpiricalBernsteinFactor
    {Omega : Type*} {m : MeasurableSpace Omega}
    {X mean lambda : ℕ → Omega → ℝ} {k : ℕ}
    (hX_meas : StronglyMeasurable[m] (X k))
    (hP_meas : StronglyMeasurable[m] (forwardPredictorProcess X k))
    (hmean_meas : StronglyMeasurable[m] (mean k))
    (hlambda_meas : StronglyMeasurable[m] (lambda k)) :
    StronglyMeasurable[m]
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k) := by
  have hpsi :=
    stronglyMeasurable_forwardEmpiricalBernsteinPsi_comp hlambda_meas
  unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hlambda_meas.mul (hX_meas.sub hmean_meas)).sub
      (hpsi.mul ((hX_meas.sub hP_meas).pow 2)))

/-- The predictable-tilt process is adapted when observations are revealed
one step after the past and both the means and tilts are predictable. -/
theorem stronglyAdapted_forwardPredictableTiltMeanEmpiricalBernsteinProcess
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ}
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda) :
    StronglyAdapted F
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda) := by
  have hP_adapted : StronglyAdapted F (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  intro n
  have hscore : StronglyMeasurable[F n]
      (fun omega => ∑ k ∈ Finset.range n,
        (lambda k omega * (X k omega - mean k omega) -
          forwardEmpiricalBernsteinPsi (lambda k omega) *
            (X k omega - forwardPredictorProcess X k omega) ^ 2)) := by
    have hrw :
        (fun omega => ∑ k ∈ Finset.range n,
          (lambda k omega * (X k omega - mean k omega) -
            forwardEmpiricalBernsteinPsi (lambda k omega) *
              (X k omega - forwardPredictorProcess X k omega) ^ 2)) =
          ∑ k ∈ Finset.range n,
            (fun omega =>
              lambda k omega * (X k omega - mean k omega) -
                forwardEmpiricalBernsteinPsi (lambda k omega) *
                  (X k omega - forwardPredictorProcess X k omega) ^ 2) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hXk : StronglyMeasurable[F n] (X k) :=
      (hX_adapted k).mono (F.mono (Nat.succ_le_of_lt hk))
    have hPk : StronglyMeasurable[F n] (forwardPredictorProcess X k) :=
      (hP_adapted k).mono (F.mono (le_of_lt hk))
    have hMk : StronglyMeasurable[F n] (mean k) :=
      (hmean_adapted k).mono (F.mono (le_of_lt hk))
    have hTk : StronglyMeasurable[F n] (lambda k) :=
      (hlambda_adapted k).mono (F.mono (le_of_lt hk))
    have hpsi := stronglyMeasurable_forwardEmpiricalBernsteinPsi_comp hTk
    exact (hTk.mul (hXk.sub hMk)).sub
      (hpsi.mul ((hXk.sub hPk).pow 2))
  change StronglyMeasurable[F n]
    (fun omega => Real.exp
      (∑ k ∈ Finset.range n,
        (lambda k omega * (X k omega - mean k omega) -
          forwardEmpiricalBernsteinPsi (lambda k omega) *
            (X k omega - forwardPredictorProcess X k omega) ^ 2)))
  exact Real.continuous_exp.comp_stronglyMeasurable hscore

/-- Pointwise exponential envelope for one predictable-tilt factor. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_exp
    {Omega : Type*}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ} {k : ℕ} {omega : Omega}
    (hL1 : L < 1)
    (hX_unit : 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_nonneg : 0 ≤ mean k omega)
    (hlambda_range :
      0 ≤ lambda k omega ∧ lambda k omega ≤ L) :
    forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k omega ≤ Real.exp L := by
  unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
  apply Real.exp_le_exp.mpr
  have hdiff : X k omega - mean k omega ≤ 1 := by
    linarith [hX_unit.2]
  have hlinear :
      lambda k omega * (X k omega - mean k omega) ≤ L := by
    have hmul :
        lambda k omega * (X k omega - mean k omega) ≤
          lambda k omega := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hdiff hlambda_range.1
    exact hmul.trans hlambda_range.2
  have hpenalty :
      0 ≤ forwardEmpiricalBernsteinPsi (lambda k omega) *
        (X k omega - forwardPredictorProcess X k omega) ^ 2 :=
    mul_nonneg
      (forwardEmpiricalBernsteinPsi_nonneg hlambda_range.1
        (hlambda_range.2.trans_lt hL1))
      (sq_nonneg _)
  linarith

/-- A finite-time almost-sure bound for one predictable-tilt factor. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_ae
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ} {k : ℕ}
    (hL1 : L < 1)
    (hX_unit : ∀ omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_nonneg : ∀ᵐ omega ∂mu, 0 ≤ mean k omega)
    (hlambda_range : ∀ᵐ omega ∂mu,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L) :
    ∀ᵐ omega ∂mu,
      forwardPredictableTiltMeanEmpiricalBernsteinFactor
          X mean lambda k omega ≤ Real.exp L := by
  filter_upwards [hmean_nonneg, hlambda_range] with omega hM hT
  exact forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_exp
    hL1 (hX_unit omega) hM hT

/-- Pointwise exponential envelope for a predictable-tilt process. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_exp
    {Omega : Type*}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_nonneg : ∀ k omega, 0 ≤ mean k omega)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (n : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda n omega ≤ Real.exp ((n : ℝ) * L) := by
  induction n with
  | zero =>
      simp [forwardPredictableTiltMeanEmpiricalBernsteinProcess]
  | succ n ih =>
      rw [forwardPredictableTiltMeanEmpiricalBernsteinProcess_succ]
      have hfactor :=
        forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_exp
          hL1 (hX_unit n omega) (hmean_nonneg n omega)
            (hlambda_range n omega)
      calc
        forwardPredictableTiltMeanEmpiricalBernsteinProcess
              X mean lambda n omega *
            forwardPredictableTiltMeanEmpiricalBernsteinFactor
              X mean lambda n omega ≤
            Real.exp ((n : ℝ) * L) * Real.exp L :=
          mul_le_mul ih hfactor (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp ((((n + 1 : ℕ) : ℝ) * L)) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- A finite-time almost-sure bound for the predictable-tilt process. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_ae
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_nonneg : ∀ k, ∀ᵐ omega ∂mu, 0 ≤ mean k omega)
    (hlambda_range : ∀ k, ∀ᵐ omega ∂mu,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (n : ℕ) :
    ∀ᵐ omega ∂mu,
      forwardPredictableTiltMeanEmpiricalBernsteinProcess
          X mean lambda n omega ≤ Real.exp ((n : ℝ) * L) := by
  have hmean_all : ∀ᵐ omega ∂mu,
      ∀ k ∈ Finset.range n, 0 ≤ mean k omega :=
    (Finset.eventually_all (Finset.range n)).2 fun k _ => hmean_nonneg k
  have hlambda_all : ∀ᵐ omega ∂mu,
      ∀ k ∈ Finset.range n,
        0 ≤ lambda k omega ∧ lambda k omega ≤ L :=
    (Finset.eventually_all (Finset.range n)).2 fun k _ => hlambda_range k
  filter_upwards [hmean_all, hlambda_all] with omega hmean_omega hlambda_omega
  unfold forwardPredictableTiltMeanEmpiricalBernsteinProcess
  apply Real.exp_le_exp.mpr
  calc
    (∑ k ∈ Finset.range n,
        (lambda k omega * (X k omega - mean k omega) -
          forwardEmpiricalBernsteinPsi (lambda k omega) *
            (X k omega - forwardPredictorProcess X k omega) ^ 2)) ≤
        ∑ _k ∈ Finset.range n, L :=
      Finset.sum_le_sum fun k hk => by
        have hT := hlambda_omega k hk
        have hdiff : X k omega - mean k omega ≤ 1 := by
          linarith [(hX_unit k omega).2, hmean_omega k hk]
        have hlinear :
            lambda k omega * (X k omega - mean k omega) ≤ L := by
          have hmul :
              lambda k omega * (X k omega - mean k omega) ≤
                lambda k omega := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hdiff hT.1
          exact hmul.trans hT.2
        have hpenalty :
            0 ≤ forwardEmpiricalBernsteinPsi (lambda k omega) *
              (X k omega - forwardPredictorProcess X k omega) ^ 2 :=
          mul_nonneg
            (forwardEmpiricalBernsteinPsi_nonneg hT.1 (hT.2.trans_lt hL1))
            (sq_nonneg _)
        linarith
    _ = (n : ℝ) * L := by simp

/-- Each predictable-tilt factor is integrable under the bounded conditional
mean model. -/
theorem integrable_forwardPredictableTiltMeanEmpiricalBernsteinFactor_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (k : ℕ) :
    Integrable
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k) mu := by
  have hX_meas : Measurable (X k) :=
    ((hX_adapted k).mono (F.le (k + 1))).measurable
  have hX_int : Integrable (X k) mu := by
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hP_adapted : StronglyAdapted F (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  have hfactor_meas : StronglyMeasurable
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda k) :=
    stronglyMeasurable_forwardPredictableTiltMeanEmpiricalBernsteinFactor
      ((hX_adapted k).mono (F.le (k + 1)))
      ((hP_adapted k).mono (F.le k))
      ((hmean_adapted k).mono (F.le k))
      ((hlambda_adapted k).mono (F.le k))
  have hmean_nonneg : ∀ᵐ omega ∂mu, 0 ≤ mean k omega :=
    (predictableMeanProcess_mem_Icc_ae hX_int
      (Filter.Eventually.of_forall (hX_unit k)) (hmean k)).mono fun _ h => h.1
  refine Integrable.of_bound hfactor_meas.aestronglyMeasurable
    (Real.exp L) ?_
  filter_upwards [forwardPredictableTiltMeanEmpiricalBernsteinFactor_le_ae
      hL1 (hX_unit k) hmean_nonneg
      (Filter.Eventually.of_forall (hlambda_range k))] with omega h
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold forwardPredictableTiltMeanEmpiricalBernsteinFactor
    exact Real.exp_pos _)]
  exact h

/-- The predictable-tilt process is integrable at every finite time under the
bounded conditional-mean model. -/
theorem integrable_forwardPredictableTiltMeanEmpiricalBernsteinProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (n : ℕ) :
    Integrable
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda n) mu := by
  have hX_int : ∀ k, Integrable (X k) mu := by
    intro k
    have hX_meas : Measurable (X k) :=
      ((hX_adapted k).mono (F.le (k + 1))).measurable
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hmean_nonneg : ∀ k, ∀ᵐ omega ∂mu, 0 ≤ mean k omega :=
    fun k => (predictableMeanProcess_mem_Icc_ae (hX_int k)
      (Filter.Eventually.of_forall (hX_unit k)) (hmean k)).mono fun _ h => h.1
  have hadapted :=
    stronglyAdapted_forwardPredictableTiltMeanEmpiricalBernsteinProcess
      hX_adapted hmean_adapted hlambda_adapted
  refine Integrable.of_bound
    ((hadapted n).mono (F.le n)).aestronglyMeasurable
      (Real.exp ((n : ℝ) * L)) ?_
  filter_upwards [forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_ae
      hL1 hX_unit hmean_nonneg
      (fun k => Filter.Eventually.of_forall (hlambda_range k)) n] with omega h
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold forwardPredictableTiltMeanEmpiricalBernsteinProcess
    exact Real.exp_pos _)]
  exact h

/-- The forward empirical-Bernstein product with a predictable tilt schedule
is an e-process under the bounded conditional-mean model. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda) := by
  have hX_meas : ∀ k, Measurable (X k) := fun k =>
    ((hX_adapted k).mono (F.le (k + 1))).measurable
  have hX_int : ∀ k, Integrable (X k) mu := by
    intro k
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hP_adapted : StronglyAdapted F (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  have hprocess_adapted :=
    stronglyAdapted_forwardPredictableTiltMeanEmpiricalBernsteinProcess
      hX_adapted hmean_adapted hlambda_adapted
  have hprocess_int : ∀ n, Integrable
      (forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda n) mu :=
    fun n =>
      integrable_forwardPredictableTiltMeanEmpiricalBernsteinProcess_of_bounded
        hL1 hX_adapted hmean_adapted hlambda_adapted hX_unit
        hlambda_range hmean n
  have hfactor_int : ∀ n, Integrable
      (forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean lambda n) mu :=
    fun n =>
      integrable_forwardPredictableTiltMeanEmpiricalBernsteinFactor_of_bounded
        hL1 hX_adapted hmean_adapted hlambda_adapted hX_unit
        hlambda_range hmean n
  have hmean_nonneg : ∀ k, ∀ᵐ omega ∂mu, 0 ≤ mean k omega :=
    fun k => (predictableMeanProcess_mem_Icc_ae (hX_int k)
      (Filter.Eventually.of_forall (hX_unit k)) (hmean k)).mono fun _ h => h.1
  have hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ omega ∂mu,
      |forwardPredictableTiltMeanEmpiricalBernsteinProcess
          X mean lambda n omega| ≤ C := by
    intro n
    refine ⟨Real.exp ((n : ℝ) * L), ?_⟩
    filter_upwards [forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_ae
        hL1 hX_unit hmean_nonneg
        (fun k => Filter.Eventually.of_forall (hlambda_range k)) n] with omega h
    rw [abs_of_pos (by
      unfold forwardPredictableTiltMeanEmpiricalBernsteinProcess
      exact Real.exp_pos _)]
    exact h
  refine
    { nonneg := fun _ _ => (Real.exp_pos _).le
      start_one := fun omega => by
        simp [forwardPredictableTiltMeanEmpiricalBernsteinProcess]
      supermartingale := ?_ }
  refine supermartingale_nat hprocess_adapted hprocess_int ?_
  intro n
  let Z : Omega → ℝ :=
    forwardPredictableTiltMeanEmpiricalBernsteinProcess X mean lambda n
  let Y : Omega → ℝ :=
    forwardPredictableTiltMeanEmpiricalBernsteinFactor X mean lambda n
  have hfact :
      forwardPredictableTiltMeanEmpiricalBernsteinProcess
          X mean lambda (n + 1) =
        fun omega => Z omega * Y omega := by
    funext omega
    exact forwardPredictableTiltMeanEmpiricalBernsteinProcess_succ
      X mean lambda n omega
  have hZ_meas : StronglyMeasurable[F n] Z := hprocess_adapted n
  obtain ⟨C, hZ_bdd⟩ := hprocess_bdd n
  have hpull :
      mu[fun omega => Z omega * Y omega | F n] =ᵐ[mu]
        fun omega => Z omega * (mu[Y | F n]) omega :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (F.le n) hZ_meas hZ_bdd (by simpa [Y] using hfactor_int n)
  have hP_unit : ∀ᵐ omega ∂mu,
      0 ≤ forwardPredictorProcess X n omega ∧
        forwardPredictorProcess X n omega ≤ 1 :=
    Filter.Eventually.of_forall
      (forwardPredictorProcess_mem_Icc_of_mem_Icc hX_unit n)
  have hstep :=
    forwardPredictableTiltMeanEmpiricalBernsteinFactor_condExp_le_one
      (F := F) (X := X) (mean := mean) (lambda := lambda)
      (L := L) (k := n) hL1 (hX_meas n) (hX_int n)
      (hP_adapted n) (hmean_adapted n) (hlambda_adapted n)
      (Filter.Eventually.of_forall (hX_unit n)) hP_unit
      (Filter.Eventually.of_forall (hlambda_range n)) (hmean n)
  rw [hfact]
  filter_upwards [hpull, hstep] with omega hpull_omega hstep_omega
  rw [hpull_omega]
  have hZ_nonneg : 0 ≤ Z omega := by
    dsimp [Z, forwardPredictableTiltMeanEmpiricalBernsteinProcess]
    exact (Real.exp_pos _).le
  calc
    Z omega * (mu[Y | F n]) omega ≤ Z omega * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [Y] using hstep_omega) hZ_nonneg
    _ = forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean lambda n omega := by simp [Z]

/-! ## Lower-tail orientation -/

/-- Predictable-tilt lower-tail factor, implemented by complementing bounded
observations and their predictable conditional means. -/
def forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor {Omega : Type*}
    (X mean lambda : ℕ → Omega → ℝ) (k : ℕ) (omega : Omega) : ℝ :=
  forwardPredictableTiltMeanEmpiricalBernsteinFactor
    (fun j omega => 1 - X j omega) (fun j omega => 1 - mean j omega)
      lambda k omega

/-- Predictable-tilt lower-tail process.  Its linear term is the weighted
conditional-mean minus observation gap, while the predictable quadratic term
is unchanged by complementation. -/
def forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess {Omega : Type*}
    (X mean lambda : ℕ → Omega → ℝ) : ℕ → Omega → ℝ :=
  forwardPredictableTiltMeanEmpiricalBernsteinProcess
    (fun j omega => 1 - X j omega) (fun j omega => 1 - mean j omega) lambda

/-- Explicit lower-tail score for one predictable-tilt factor. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor_eq
    {Omega : Type*} (X mean lambda : ℕ → Omega → ℝ)
    (k : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor
        X mean lambda k omega =
      Real.exp
        (lambda k omega * (mean k omega - X k omega) -
          forwardEmpiricalBernsteinPsi (lambda k omega) *
            (X k omega - forwardPredictorProcess X k omega) ^ 2) := by
  unfold forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor
    forwardPredictableTiltMeanEmpiricalBernsteinFactor
  rw [forwardPredictorProcess_one_sub]
  congr 1
  ring

/-- Explicit cumulative lower-tail score for the predictable-tilt process. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eq
    {Omega : Type*} (X mean lambda : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean lambda n omega =
      Real.exp
        (∑ k ∈ Finset.range n,
          (lambda k omega * (mean k omega - X k omega) -
            forwardEmpiricalBernsteinPsi (lambda k omega) *
              (X k omega - forwardPredictorProcess X k omega) ^ 2)) := by
  unfold forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
    forwardPredictableTiltMeanEmpiricalBernsteinProcess
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [forwardPredictorProcess_one_sub]
  ring

/-- Pointwise exponential envelope for the lower-tail predictable-tilt
process.  Only the upper bound on the conditional mean enters this envelope;
the lower bound required by the e-process theorem is not needed here. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_le_exp
    {Omega : Type*}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_le_one : ∀ k omega, mean k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (n : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean lambda n omega ≤ Real.exp ((n : ℝ) * L) := by
  change forwardPredictableTiltMeanEmpiricalBernsteinProcess
      (fun k omega => 1 - X k omega)
      (fun k omega => 1 - mean k omega) lambda n omega ≤
    Real.exp ((n : ℝ) * L)
  exact forwardPredictableTiltMeanEmpiricalBernsteinProcess_le_exp hL1
    (fun k omega => by
      constructor <;> linarith [(hX_unit k omega).1, (hX_unit k omega).2])
    (fun k omega => by linarith [hmean_le_one k omega])
    hlambda_range n omega

/-- Complementing `[0,1]` observations turns the upper predictable-tilt
e-process into a lower-tail e-process with the same predictable tilt schedule. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L : ℝ}
    (hL1 : L < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
        X mean lambda) := by
  let Y : ℕ → Omega → ℝ := fun k omega => 1 - X k omega
  let M : ℕ → Omega → ℝ := fun k omega => 1 - mean k omega
  have hY_adapted : IncrementAdapted F Y := incrementAdapted_one_sub hX_adapted
  have hM_adapted : StronglyAdapted F M := by
    intro k
    exact stronglyMeasurable_const.sub (hmean_adapted k)
  have hY_unit : ∀ k omega, 0 ≤ Y k omega ∧ Y k omega ≤ 1 := by
    intro k omega
    dsimp [Y]
    constructor <;> linarith [(hX_unit k omega).1, (hX_unit k omega).2]
  have hX_int : ∀ k, Integrable (X k) mu := by
    intro k
    have hX_meas : Measurable (X k) :=
      ((hX_adapted k).mono (F.le (k + 1))).measurable
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hY_mean : ∀ k, mu[Y k | F k] =ᵐ[mu] M k := by
    intro k
    have hsub := condExp_sub (integrable_const (1 : ℝ)) (hX_int k) (F k)
    have hone : mu[(fun _ : Omega => (1 : ℝ)) | F k] = fun _ => (1 : ℝ) :=
      condExp_const (F.le k) 1
    filter_upwards [hsub, hmean k] with omega hsub_omega hmean_omega
    change mu[(fun _ : Omega => (1 : ℝ)) - X k | F k] omega =
      1 - mean k omega
    rw [hsub_omega, hone]
    simp only [Pi.sub_apply]
    rw [hmean_omega]
  change EProcess mu F
    (forwardPredictableTiltMeanEmpiricalBernsteinProcess Y M lambda)
  exact forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    hL1 hY_adapted hM_adapted hlambda_adapted hY_unit
      hlambda_range hY_mean

/-- Finite-horizon Type-I control for the lower-tail predictable-tilt process. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinLower_typeI_control
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L alpha : ℝ}
    (hL1 : L < 1) (halpha : 0 < alpha)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (n : ℕ) :
    mu.real
        {omega |
          (1 : ℝ) / alpha ≤
            finiteRunningMax
              (forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
                X mean lambda) n omega} ≤
      alpha := by
  exact eProcess_typeI_control
    (forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
      hL1 hX_adapted hmean_adapted hlambda_adapted hX_unit
      hlambda_range hmean)
    halpha n

/-- Safe-testing control for the predictable-tilt empirical-Bernstein process
up to any declared finite horizon. -/
theorem forwardPredictableTiltMeanEmpiricalBernstein_typeI_control
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean lambda : ℕ → Omega → ℝ} {L alpha : ℝ}
    (hL1 : L < 1) (halpha : 0 < alpha)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hlambda_adapted : StronglyAdapted F lambda)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hlambda_range : ∀ k omega,
      0 ≤ lambda k omega ∧ lambda k omega ≤ L)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (n : ℕ) :
    mu.real
        {omega |
          (1 : ℝ) / alpha ≤
            finiteRunningMax
              (forwardPredictableTiltMeanEmpiricalBernsteinProcess
                X mean lambda) n omega} ≤
      alpha := by
  exact eProcess_typeI_control
    (forwardPredictableTiltMeanEmpiricalBernsteinProcess_eProcess_of_bounded
      hL1 hX_adapted hmean_adapted hlambda_adapted hX_unit
      hlambda_range hmean)
    halpha n

/-- Constant tilt schedules recover the existing fixed-tilt factor. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinFactor_const_tilt_eq
    {Omega : Type*} (X mean : ℕ → Omega → ℝ) (lam : ℝ)
    (k : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinFactor
        X mean (fun _ _ => lam) k omega =
      forwardPredictableMeanEmpiricalBernsteinFactor
        X mean lam k omega := by
  rfl

/-- Constant tilt schedules recover the existing fixed-tilt process. -/
theorem forwardPredictableTiltMeanEmpiricalBernsteinProcess_const_tilt_eq
    {Omega : Type*} (X mean : ℕ → Omega → ℝ) (lam : ℝ)
    (n : ℕ) (omega : Omega) :
    forwardPredictableTiltMeanEmpiricalBernsteinProcess
        X mean (fun _ _ => lam) n omega =
      forwardPredictableMeanEmpiricalBernsteinProcess
        X mean lam n omega := by
  induction n with
  | zero =>
      simp [forwardPredictableTiltMeanEmpiricalBernsteinProcess,
        forwardPredictableMeanEmpiricalBernsteinProcess,
        forwardPredictableQuadratic]
  | succ n ih =>
      rw [forwardPredictableTiltMeanEmpiricalBernsteinProcess_succ,
        forwardPredictableMeanEmpiricalBernsteinProcess_succ, ih,
        forwardPredictableTiltMeanEmpiricalBernsteinFactor_const_tilt_eq]

end

end FormalSLT.AnytimeValid
