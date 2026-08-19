/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.ForwardBesselProcess

/-!
# Forward Bessel processes with predictable conditional means

This module lifts the forward predictable-residual empirical-Bernstein process
from a fixed conditional mean to a predictable conditional-mean process.  The
statistical ingredient is known: Howard--Ramdas--McAuliffe--Sekhon formulate
their empirical-Bernstein confidence sequence for the running average of
conditional means, while Waudby-Smith--Ramdas specialize their closed-form
predictable plug-in construction to a shared conditional mean.  No novelty
claim is made for the predictable-mean e-process.

The checked contribution here is the interface with FormalSLT's deterministic
forward-Bessel algebra.  If `mean k` is measurable with respect to the past
filtration and is a version of `E[X k | F k]`, then the product of the standard
one-step factors is an e-process.  Its lower-tail score is

`lam * sum (mean k - X k) - psi(lam) * predictableQuadratic X`.

The existing Welford/Bessel bound on `predictableQuadratic X` is pathwise and
does not use stationarity or a constant mean.  It therefore supplies the same
hybrid-Bessel lower envelope and an anytime-valid boundary for the running
average of the predictable conditional means.

References:

* Howard, Ramdas, McAuliffe, and Sekhon (2021), *Time-uniform,
  nonparametric, nonasymptotic confidence sequences*, Theorem 4.
* Waudby-Smith and Ramdas (2024), *Estimating means of bounded random
  variables by betting*, Section 3.
* Chugg and Ramdas (2025), *Closed-form empirical Bernstein confidence
  sequences for scalars and matrices*.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- One upper-tail empirical-Bernstein factor centered by a predictable
conditional-mean process. -/
def forwardPredictableMeanEmpiricalBernsteinFactor {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (k : ℕ) (omega : Omega) : ℝ :=
  Real.exp
    (lam * (X k omega - mean k omega) - forwardEmpiricalBernsteinPsi lam *
      (X k omega - forwardPredictorProcess X k omega) ^ 2)

/-- The exponential product process associated with predictable conditional
means. -/
def forwardPredictableMeanEmpiricalBernsteinProcess {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k omega - mean k omega)) -
      forwardEmpiricalBernsteinPsi lam *
        forwardPredictableQuadratic (fun k => X k omega) n)

/-- Exact multiplicative update of the predictable-mean process. -/
lemma forwardPredictableMeanEmpiricalBernsteinProcess_succ {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (n : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinProcess X mean lam (n + 1) omega =
      forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n omega *
        forwardPredictableMeanEmpiricalBernsteinFactor X mean lam n omega := by
  unfold forwardPredictableMeanEmpiricalBernsteinProcess
    forwardPredictableMeanEmpiricalBernsteinFactor forwardPredictorProcess
  rw [Finset.sum_range_succ, forwardPredictableQuadratic_succ, ← Real.exp_add]
  congr 1
  ring

/-- A predictable version of the conditional mean of a `[0,1]` observation is
itself `[0,1]` almost surely. -/
lemma predictableMeanProcess_mem_Icc_ae
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {k : ℕ}
    (hX_int : Integrable (X k) mu)
    (hX_unit : ∀ᵐ omega ∂mu, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : mu[X k | F k] =ᵐ[mu] mean k) :
    ∀ᵐ omega ∂mu, 0 ≤ mean k omega ∧ mean k omega ≤ 1 := by
  have hlo : ∀ᵐ omega ∂mu, 0 ≤ mu[X k | F k] omega :=
    condExp_nonneg (hX_unit.mono fun omega h => h.1)
  have hhi : mu[X k | F k] ≤ᵐ[mu]
      mu[(fun _ : Omega => (1 : ℝ)) | F k] :=
    condExp_mono hX_int (integrable_const 1)
      (hX_unit.mono fun omega h => h.2)
  have hone : mu[(fun _ : Omega => (1 : ℝ)) | F k] = fun _ => (1 : ℝ) :=
    condExp_const (F.le k) 1
  filter_upwards [hlo, hhi, hmean] with omega hlo_omega hhi_omega hmean_omega
  rw [hmean_omega] at hlo_omega
  have hhi' : mean k omega ≤ 1 := by
    rw [hmean_omega] at hhi_omega
    simpa [hone] using hhi_omega
  exact ⟨hlo_omega, hhi'⟩

/-- The predictable-mean one-step factor has conditional expectation at most
one.  This is the usual Howard empirical-Bernstein factor inequality with the
conditional mean represented by a past-measurable random variable. -/
theorem forwardPredictableMeanEmpiricalBernsteinFactor_condExp_le_one
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ} {k : ℕ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_meas : Measurable (X k)) (hX_int : Integrable (X k) mu)
    (hP_meas : StronglyMeasurable[F k] (forwardPredictorProcess X k))
    (hmean_meas : StronglyMeasurable[F k] (mean k))
    (hX_unit : ∀ᵐ omega ∂mu, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hP_unit : ∀ᵐ omega ∂mu,
      0 ≤ forwardPredictorProcess X k omega ∧
        forwardPredictorProcess X k omega ≤ 1)
    (hmean : mu[X k | F k] =ᵐ[mu] mean k) :
    mu[forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k | F k]
      ≤ᵐ[mu] fun _ => (1 : ℝ) := by
  let P : Omega → ℝ := forwardPredictorProcess X k
  let M : Omega → ℝ := mean k
  let A : Omega → ℝ := fun omega => lam * (P omega - M omega)
  let Z : Omega → ℝ := fun omega => Real.exp (A omega)
  let Y : Omega → ℝ := fun omega => 1 + lam * (X k omega - P omega)
  let C : ℝ := Real.exp lam
  have hM_unit : ∀ᵐ omega ∂mu, 0 ≤ M omega ∧ M omega ≤ 1 := by
    simpa [M] using predictableMeanProcess_mem_Icc_ae hX_int hX_unit hmean
  have hP_global : StronglyMeasurable P := hP_meas.mono (F.le k)
  have hM_global : StronglyMeasurable M := hmean_meas.mono (F.le k)
  have hP_bdd : ∀ᵐ omega ∂mu, |P omega| ≤ (1 : ℝ) := by
    filter_upwards [hP_unit] with omega h
    simpa [P, abs_of_nonneg h.1] using h.2
  have hP_int : Integrable P mu :=
    Integrable.of_bound hP_global.aestronglyMeasurable 1 hP_bdd
  have hR_int : Integrable (fun omega => X k omega - P omega) mu :=
    hX_int.sub hP_int
  have hY_int : Integrable Y mu :=
    (integrable_const 1).add (hR_int.const_mul lam)
  have hZ_meas : StronglyMeasurable[F k] Z := by
    have hA : StronglyMeasurable[F k] A :=
      (hP_meas.sub hmean_meas).const_mul lam
    exact Real.continuous_exp.comp_stronglyMeasurable hA
  have hZ_bdd : ∀ᵐ omega ∂mu, |Z omega| ≤ C := by
    filter_upwards [hP_unit, hM_unit] with omega hP_omega hM_omega
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    dsimp [A, C, P, M]
    have hdiff : forwardPredictorProcess X k omega - mean k omega ≤ 1 := by
      linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff hlam0
  have hcomparison_int : Integrable (fun omega => Z omega * Y omega) mu :=
    hY_int.bdd_mul (hZ_meas.mono (F.le k)).aestronglyMeasurable hZ_bdd
  have hfactor_meas : Measurable
      (forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k) := by
    change Measurable (fun omega => Real.exp
      (lam * (X k omega - M omega) - forwardEmpiricalBernsteinPsi lam *
        (X k omega - P omega) ^ 2))
    fun_prop
  have hpoint : ∀ᵐ omega ∂mu,
      forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k omega ≤
        Z omega * Y omega := by
    filter_upwards [hX_unit, hP_unit] with omega hX_omega hP_omega
    have hz : -(1 : ℝ) ≤ X k omega - P omega := by
      dsimp [P] at hP_omega ⊢
      linarith
    have hs := exp_forwardEmpiricalBernstein_le_one_add hlam0 hlam1 hz
    calc
      forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k omega =
          Real.exp (A omega) *
            Real.exp (lam * (X k omega - P omega) -
              forwardEmpiricalBernsteinPsi lam * (X k omega - P omega) ^ 2) := by
            rw [<- Real.exp_add]
            unfold forwardPredictableMeanEmpiricalBernsteinFactor
            dsimp [A, P, M]
            congr 1
            ring
      _ ≤ Real.exp (A omega) * (1 + lam * (X k omega - P omega)) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Z omega * Y omega := rfl
  have hfactor_int : Integrable
      (forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k) mu := by
    refine Integrable.mono' hcomparison_int hfactor_meas.aestronglyMeasurable ?_
    filter_upwards [hpoint] with omega h
    rw [Real.norm_eq_abs, abs_of_pos (by
      unfold forwardPredictableMeanEmpiricalBernsteinFactor
      exact Real.exp_pos _)]
    exact h
  have hmono :
      mu[forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k | F k]
        ≤ᵐ[mu] mu[fun omega => Z omega * Y omega | F k] :=
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
  have hY_cond : mu[Y | F k] =ᵐ[mu]
      fun omega => 1 + lam * (M omega - P omega) := by
    have hadd :=
      condExp_add (integrable_const (1 : ℝ)) (hR_int.const_mul lam) (F k)
    have hscale := condExp_smul (𝕜 := ℝ) (μ := mu) (m := F k) lam
      (fun omega => X k omega - P omega)
    have hscale' :
        mu[fun omega => lam * (X k omega - P omega) | F k] =ᵐ[mu]
          fun omega => lam *
            (mu[fun omega => X k omega - P omega | F k]) omega := by
      filter_upwards [hscale] with omega hscale_omega
      change mu[lam • (fun omega => X k omega - P omega) | F k] omega =
        lam * (mu[fun omega => X k omega - P omega | F k]) omega
      simpa only [Pi.smul_apply, smul_eq_mul] using hscale_omega
    have hone : mu[(fun _ : Omega => (1 : ℝ)) | F k] = fun _ => (1 : ℝ) :=
      condExp_const (F.le k) 1
    filter_upwards [hadd, hscale', hR_cond] with omega hadd_omega hscale_omega hR_omega
    change mu[(fun _ : Omega => (1 : ℝ)) +
      (fun omega => lam * (X k omega - P omega)) | F k] omega =
        1 + lam * (M omega - P omega)
    rw [hadd_omega]
    simp only [Pi.add_apply]
    rw [hone, hscale_omega, hR_omega]
  filter_upwards [hmono, hpull, hY_cond] with omega hmono_omega hpull_omega hY_omega
  refine hmono_omega.trans ?_
  rw [hpull_omega, hY_omega]
  have ha : 1 - A omega ≤ Real.exp (-A omega) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-A omega)
  calc
    Z omega * (1 + lam * (M omega - P omega)) =
        Real.exp (A omega) * (1 - A omega) := by
      dsimp [Z, A]
      congr 1
      ring
    _ ≤ Real.exp (A omega) * Real.exp (-A omega) :=
      mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le
    _ = 1 := by rw [<- Real.exp_add]; simp

/-- The predictable-mean process is adapted when observations are revealed one
step after the past and the conditional means are past-measurable. -/
theorem stronglyAdapted_forwardPredictableMeanEmpiricalBernsteinProcess
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {F : Filtration ℕ mOmega} {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean) :
    StronglyAdapted F
      (forwardPredictableMeanEmpiricalBernsteinProcess X mean lam) := by
  have hP_adapted : StronglyAdapted F (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  intro n
  have hcentered : StronglyMeasurable[F n]
      (fun omega => ∑ k ∈ Finset.range n, (X k omega - mean k omega)) := by
    have hrw : (fun omega => ∑ k ∈ Finset.range n,
        (X k omega - mean k omega)) =
        ∑ k ∈ Finset.range n, (fun omega => X k omega - mean k omega) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    exact ((hX_adapted k).mono (F.mono (Nat.succ_le_of_lt hk))).sub
      ((hmean_adapted k).mono (F.mono (le_of_lt hk)))
  have hquadratic : StronglyMeasurable[F n]
      (fun omega => forwardPredictableQuadratic (fun k => X k omega) n) := by
    have hrw :
        (fun omega => forwardPredictableQuadratic (fun k => X k omega) n) =
          ∑ k ∈ Finset.range n,
            (fun omega => (X k omega - forwardPredictorProcess X k omega) ^ 2) := by
      funext omega
      simp only [forwardPredictableQuadratic, forwardPredictorProcess,
        Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hXk : StronglyMeasurable[F n] (X k) :=
      (hX_adapted k).mono (F.mono (Nat.succ_le_of_lt hk))
    have hPk : StronglyMeasurable[F n] (forwardPredictorProcess X k) :=
      (hP_adapted k).mono (F.mono (le_of_lt hk))
    exact (hXk.sub hPk).pow 2
  change StronglyMeasurable[F n] (fun omega => Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k omega - mean k omega)) -
      forwardEmpiricalBernsteinPsi lam *
        forwardPredictableQuadratic (fun k => X k omega) n))
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hcentered.const_mul lam).sub
      (hquadratic.const_mul (forwardEmpiricalBernsteinPsi lam)))

/-- A finite-time almost-sure bound used for integrability. -/
theorem forwardPredictableMeanEmpiricalBernsteinProcess_le_ae
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean_nonneg : ∀ k, ∀ᵐ omega ∂mu, 0 ≤ mean k omega)
    (n : ℕ) :
    ∀ᵐ omega ∂mu,
      forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n omega ≤
        Real.exp (lam * (n : ℝ)) := by
  have hall : ∀ᵐ omega ∂mu,
      ∀ k ∈ Finset.range n, 0 ≤ mean k omega :=
    (Finset.eventually_all (Finset.range n)).2 fun k _ => hmean_nonneg k
  filter_upwards [hall] with omega hmean_omega
  unfold forwardPredictableMeanEmpiricalBernsteinProcess
  apply Real.exp_le_exp.mpr
  have hsum_le :
      (∑ k ∈ Finset.range n, (X k omega - mean k omega)) ≤ (n : ℝ) := by
    calc
      (∑ k ∈ Finset.range n, (X k omega - mean k omega)) ≤
          ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k hk => by
          linarith [(hX_unit k omega).2, hmean_omega k hk]
      _ = (n : ℝ) := by simp
  have hlinear :
      lam * (∑ k ∈ Finset.range n, (X k omega - mean k omega)) ≤
        lam * (n : ℝ) := mul_le_mul_of_nonneg_left hsum_le hlam0
  have hpenalty : 0 ≤ forwardEmpiricalBernsteinPsi lam *
      forwardPredictableQuadratic (fun k => X k omega) n :=
    mul_nonneg (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith

/-- Bounded adapted observations and their predictable conditional means make
each process value integrable. -/
theorem integrable_forwardPredictableMeanEmpiricalBernsteinProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (n : ℕ) :
    Integrable (forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n) mu := by
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
    stronglyAdapted_forwardPredictableMeanEmpiricalBernsteinProcess
      (lam := lam) hX_adapted hmean_adapted
  refine Integrable.of_bound
    ((hadapted n).mono (F.le n)).aestronglyMeasurable
      (Real.exp (lam * (n : ℝ))) ?_
  filter_upwards [forwardPredictableMeanEmpiricalBernsteinProcess_le_ae
      hlam0 hlam1 hX_unit hmean_nonneg n] with omega h
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold forwardPredictableMeanEmpiricalBernsteinProcess
    exact Real.exp_pos _)]
  exact h

/-- Bounded adapted observations and predictable means make each one-step
factor integrable. -/
theorem integrable_forwardPredictableMeanEmpiricalBernsteinFactor_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k)
    (k : ℕ) :
    Integrable (forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k) mu := by
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
      (forwardPredictableMeanEmpiricalBernsteinFactor X mean lam k) := by
    unfold forwardPredictableMeanEmpiricalBernsteinFactor
    have hX_global : StronglyMeasurable (X k) :=
      (hX_adapted k).mono (F.le (k + 1))
    have hP_global : StronglyMeasurable (forwardPredictorProcess X k) :=
      (hP_adapted k).mono (F.le k)
    have hM_global : StronglyMeasurable (mean k) :=
      (hmean_adapted k).mono (F.le k)
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((hX_global.sub hM_global).const_mul lam).sub
        (((hX_global.sub hP_global).pow 2).const_mul
          (forwardEmpiricalBernsteinPsi lam)))
  have hmean_unit := predictableMeanProcess_mem_Icc_ae hX_int
    (Filter.Eventually.of_forall (hX_unit k)) (hmean k)
  refine Integrable.of_bound hfactor_meas.aestronglyMeasurable (Real.exp lam) ?_
  filter_upwards [hmean_unit] with omega hM
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold forwardPredictableMeanEmpiricalBernsteinFactor
    exact Real.exp_pos _)]
  unfold forwardPredictableMeanEmpiricalBernsteinFactor
  apply Real.exp_le_exp.mpr
  have hlinear : X k omega - mean k omega ≤ 1 := by
    linarith [(hX_unit k omega).2, hM.1]
  have htilt : lam * (X k omega - mean k omega) ≤ lam := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlinear hlam0
  have hpenalty : 0 ≤ forwardEmpiricalBernsteinPsi lam *
      (X k omega - forwardPredictorProcess X k omega) ^ 2 :=
    mul_nonneg (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1) (sq_nonneg _)
  linarith

/-- The predictable-mean product is an e-process under the bounded conditional
mean model. -/
theorem forwardPredictableMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (forwardPredictableMeanEmpiricalBernsteinProcess X mean lam) := by
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
    stronglyAdapted_forwardPredictableMeanEmpiricalBernsteinProcess
      (lam := lam) hX_adapted hmean_adapted
  have hprocess_int : ∀ n, Integrable
      (forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n) mu :=
    fun n => integrable_forwardPredictableMeanEmpiricalBernsteinProcess_of_bounded
      hlam0 hlam1 hX_adapted hmean_adapted hX_unit hmean n
  have hfactor_int : ∀ n, Integrable
      (forwardPredictableMeanEmpiricalBernsteinFactor X mean lam n) mu :=
    fun n => integrable_forwardPredictableMeanEmpiricalBernsteinFactor_of_bounded
      hlam0 hlam1 hX_adapted hmean_adapted hX_unit hmean n
  have hmean_nonneg : ∀ k, ∀ᵐ omega ∂mu, 0 ≤ mean k omega :=
    fun k => (predictableMeanProcess_mem_Icc_ae (hX_int k)
      (Filter.Eventually.of_forall (hX_unit k)) (hmean k)).mono fun _ h => h.1
  have hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ omega ∂mu,
      |forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n omega| ≤ C := by
    intro n
    refine ⟨Real.exp (lam * (n : ℝ)), ?_⟩
    filter_upwards [forwardPredictableMeanEmpiricalBernsteinProcess_le_ae
        hlam0 hlam1 hX_unit hmean_nonneg n] with omega h
    rw [abs_of_pos (by
      unfold forwardPredictableMeanEmpiricalBernsteinProcess
      exact Real.exp_pos _)]
    exact h
  refine
    { nonneg := fun _ _ => (Real.exp_pos _).le
      start_one := fun omega => by
        simp [forwardPredictableMeanEmpiricalBernsteinProcess,
          forwardPredictableQuadratic]
      supermartingale := ?_ }
  refine supermartingale_nat hprocess_adapted hprocess_int ?_
  intro n
  let Z : Omega → ℝ :=
    forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n
  let Y : Omega → ℝ :=
    forwardPredictableMeanEmpiricalBernsteinFactor X mean lam n
  have hfact :
      forwardPredictableMeanEmpiricalBernsteinProcess X mean lam (n + 1) =
        fun omega => Z omega * Y omega := by
    funext omega
    exact forwardPredictableMeanEmpiricalBernsteinProcess_succ X mean lam n omega
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
    forwardPredictableMeanEmpiricalBernsteinFactor_condExp_le_one
      (F := F) (X := X) (mean := mean) (lam := lam) (k := n)
      hlam0 hlam1 (hX_meas n) (hX_int n) (hP_adapted n)
      (hmean_adapted n) (Filter.Eventually.of_forall (hX_unit n))
      hP_unit (hmean n)
  rw [hfact]
  filter_upwards [hpull, hstep] with omega hpull_omega hstep_omega
  rw [hpull_omega]
  have hZ_nonneg : 0 ≤ Z omega := by
    dsimp [Z, forwardPredictableMeanEmpiricalBernsteinProcess]
    exact (Real.exp_pos _).le
  calc
    Z omega * (mu[Y | F n]) omega ≤ Z omega * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [Y] using hstep_omega) hZ_nonneg
    _ = forwardPredictableMeanEmpiricalBernsteinProcess X mean lam n omega := by
      simp [Z]

/-- Direct lower-tail one-step factor. -/
def forwardPredictableMeanEmpiricalBernsteinLowerFactor {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (k : ℕ) (omega : Omega) : ℝ :=
  forwardPredictableMeanEmpiricalBernsteinFactor
    (fun j omega => 1 - X j omega) (fun j omega => 1 - mean j omega) lam k omega

/-- Direct lower-tail product process. -/
def forwardPredictableMeanEmpiricalBernsteinLowerProcess {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) : ℕ → Omega → ℝ :=
  forwardPredictableMeanEmpiricalBernsteinProcess
    (fun j omega => 1 - X j omega) (fun j omega => 1 - mean j omega) lam

/-- The complemented one-step factor has the desired lower-tail score. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerFactor_eq {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (k : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinLowerFactor X mean lam k omega =
      Real.exp
        (lam * (mean k omega - X k omega) - forwardEmpiricalBernsteinPsi lam *
          (X k omega - forwardPredictorProcess X k omega) ^ 2) := by
  unfold forwardPredictableMeanEmpiricalBernsteinLowerFactor
    forwardPredictableMeanEmpiricalBernsteinFactor
  rw [forwardPredictorProcess_one_sub]
  congr 1
  ring

/-- The complemented product has the cumulative lower-tail score. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (n : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam n omega =
      Real.exp
        (lam * (∑ k ∈ Finset.range n, (mean k omega - X k omega)) -
          forwardEmpiricalBernsteinPsi lam *
            forwardPredictableQuadratic (fun k => X k omega) n) := by
  unfold forwardPredictableMeanEmpiricalBernsteinLowerProcess
    forwardPredictableMeanEmpiricalBernsteinProcess
  rw [forwardPredictableQuadratic_one_sub]
  congr 1
  apply congrArg (fun s : ℝ => lam * s -
    forwardEmpiricalBernsteinPsi lam *
      forwardPredictableQuadratic (fun k => X k omega) n)
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact lower-tail factor update. -/
lemma forwardPredictableMeanEmpiricalBernsteinLowerProcess_succ {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (n : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam (n + 1) omega =
      forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam n omega *
        forwardPredictableMeanEmpiricalBernsteinLowerFactor X mean lam n omega := by
  exact forwardPredictableMeanEmpiricalBernsteinProcess_succ
    (fun j omega => 1 - X j omega) (fun j omega => 1 - mean j omega) lam n omega

/-- Conditional expectation control for the direct lower-tail factor. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerFactor_condExp_le_one
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ} {k : ℕ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ j omega, 0 ≤ X j omega ∧ X j omega ≤ 1)
    (hmean : ∀ j, mu[X j | F j] =ᵐ[mu] mean j) :
    mu[forwardPredictableMeanEmpiricalBernsteinLowerFactor X mean lam k | F k]
      ≤ᵐ[mu] fun _ => (1 : ℝ) := by
  let Y : ℕ → Omega → ℝ := fun j omega => 1 - X j omega
  let M : ℕ → Omega → ℝ := fun j omega => 1 - mean j omega
  have hX_meas : Measurable (X k) :=
    ((hX_adapted k).mono (F.le (k + 1))).measurable
  have hX_int : Integrable (X k) mu := by
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hY_adapted : IncrementAdapted F Y := incrementAdapted_one_sub hX_adapted
  have hP_adapted : StronglyAdapted F (forwardPredictorProcess Y) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hY_adapted
  have hY_unit : ∀ j omega, 0 ≤ Y j omega ∧ Y j omega ≤ 1 := by
    intro j omega
    dsimp [Y]
    constructor <;> linarith [(hX_unit j omega).1, (hX_unit j omega).2]
  have hY_int : Integrable (Y k) mu := (integrable_const 1).sub hX_int
  have hM_adapted : StronglyAdapted F M := by
    intro j
    exact stronglyMeasurable_const.sub (hmean_adapted j)
  have hY_mean : mu[Y k | F k] =ᵐ[mu] M k := by
    have hsub := condExp_sub (integrable_const (1 : ℝ)) hX_int (F k)
    have hone : mu[(fun _ : Omega => (1 : ℝ)) | F k] = fun _ => (1 : ℝ) :=
      condExp_const (F.le k) 1
    filter_upwards [hsub, hmean k] with omega hsub_omega hmean_omega
    change mu[(fun _ : Omega => (1 : ℝ)) - X k | F k] omega =
      1 - mean k omega
    rw [hsub_omega, hone]
    simp only [Pi.sub_apply]
    rw [hmean_omega]
  change mu[forwardPredictableMeanEmpiricalBernsteinFactor Y M lam k | F k]
    ≤ᵐ[mu] fun _ => (1 : ℝ)
  exact forwardPredictableMeanEmpiricalBernsteinFactor_condExp_le_one
      (F := F) (X := Y) (mean := M) (lam := lam) (k := k)
      hlam0 hlam1
      ((hY_adapted k).mono (F.le (k + 1))).measurable hY_int
      (hP_adapted k) (hM_adapted k)
      (Filter.Eventually.of_forall (hY_unit k))
      (Filter.Eventually.of_forall
        (forwardPredictorProcess_mem_Icc_of_mem_Icc hY_unit k)) hY_mean

/-- The lower-tail predictable-mean product is an e-process. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    EProcess mu F
      (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam) := by
  let Y : ℕ → Omega → ℝ := fun k omega => 1 - X k omega
  let M : ℕ → Omega → ℝ := fun k omega => 1 - mean k omega
  have hY_adapted : IncrementAdapted F Y := incrementAdapted_one_sub hX_adapted
  have hY_unit : ∀ k omega, 0 ≤ Y k omega ∧ Y k omega ≤ 1 := by
    intro k omega
    dsimp [Y]
    constructor <;> linarith [(hX_unit k omega).1, (hX_unit k omega).2]
  have hM_adapted : StronglyAdapted F M := by
    intro k
    exact stronglyMeasurable_const.sub (hmean_adapted k)
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
  exact forwardPredictableMeanEmpiricalBernsteinProcess_eProcess_of_bounded
    (X := Y) (mean := M) hlam0 hlam1 hY_adapted hM_adapted hY_unit hY_mean

/-- Lower-tail hybrid-Bessel expression for a predictable mean process.  It is
a pointwise lower envelope of the actual product e-process, not itself an
e-process. -/
def forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam : ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (mean k omega - X k omega)) -
      forwardEmpiricalBernsteinPsi lam *
        forwardHybridBesselPenalty (fun k => X k omega) n)

/-- The deterministic hybrid-Bessel envelope survives unchanged when the
conditional mean varies predictably. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
    {Omega : Type*} {X mean : ℕ → Omega → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {n : ℕ} (hn : 2 ≤ n) (omega : Omega)
    (hX : ∀ i < n, 0 ≤ X i omega ∧ X i omega ≤ 1) :
    forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope
        X mean lam n omega ≤
      forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam n omega := by
  rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
  unfold forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope
  apply Real.exp_le_exp.mpr
  have hq := forwardPredictableQuadratic_le_hybrid_bessel
    (fun k => X k omega) hn hX
  have hpen := mul_le_mul_of_nonneg_left hq
    (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1)
  linarith

/-- Sum of predictable-mean residuals as a difference of prefix means. -/
lemma sum_predictableMean_sub_eq_mul_sub_forwardPrefixMean
    (mean x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, (mean k - x k)) =
      (n : ℝ) * (forwardPrefixMean mean n - forwardPrefixMean x n) := by
  unfold forwardPrefixMean
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib]
  field_simp [hn0]

/-- Failure of the explicit hybrid-Bessel boundary for the running average of
predictable conditional means. -/
def forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure {Omega : Type*}
    (X mean : ℕ → Omega → ℝ) (lam delta : ℝ) : Set Omega :=
  {omega | ∃ n : ℕ, 2 ≤ n ∧
    forwardEmpiricalBernsteinBesselBoundary X lam delta n omega ≤
      forwardPrefixMean (fun k => mean k omega) n -
        forwardPrefixMean (fun k => X k omega) n}

/-- A boundary failure forces the actual predictable-mean product e-process to
cross `1 / delta` at the same time. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_subset_crossing
    {Omega : Type*} {X mean : ℕ → Omega → ℝ} {lam delta : ℝ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1) :
    forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure
        X mean lam delta ≤
      atTopCrossingEvent
        (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam)
        (1 / delta) := by
  intro omega h_omega
  rcases h_omega with ⟨n, hn, hboundary⟩
  refine ⟨n, ?_⟩
  have hnpos : 0 < n := by omega
  have hdenpos : 0 < (n : ℝ) * lam :=
    mul_pos (Nat.cast_pos.mpr hnpos) hlam
  have hmul := (div_le_iff₀ hdenpos).mp hboundary
  have hsum := sum_predictableMean_sub_eq_mul_sub_forwardPrefixMean
    (fun k => mean k omega) (fun k => X k omega) hnpos
  have hlog_le :
      Real.log (1 / delta) ≤
        lam * (∑ k ∈ Finset.range n, (mean k omega - X k omega)) -
          forwardEmpiricalBernsteinPsi lam *
            forwardHybridBesselPenalty (fun k => X k omega) n := by
    rw [hsum]
    nlinarith
  have hthreshold :
      (1 / delta) ≤
        forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope
          X mean lam n omega := by
    rw [<- Real.exp_log (one_div_pos.mpr hdelta)]
    exact Real.exp_le_exp.mpr hlog_le
  exact hthreshold.trans
    (forwardPredictableMeanEmpiricalBernsteinLowerBesselEnvelope_le_process
      hlam.le hlam1 hn omega (fun i hi => hX_unit i omega))

/-- Fixed-tilt, all-time hybrid-Bessel bound for the running average of a
predictable conditional-mean process. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_mass_le_delta
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam delta : ℝ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    mu.real
        (forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure
          X mean lam delta) ≤ delta := by
  have hE :=
    forwardPredictableMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
      hlam.le hlam1 hX_adapted hmean_adapted hX_unit hmean
  have hville := ville_atTop_maximal_ineq
    (μ := mu) (𝒢 := F)
    (M := forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam)
    hE.supermartingale hE.nonneg (one_div_pos.mpr hdelta)
  rw [hE.integral_start_eq_one] at hville
  have hcross : mu.real
      (atTopCrossingEvent
        (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam)
        (1 / delta)) ≤ delta := by
    calc
      mu.real
          (atTopCrossingEvent
            (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam)
            (1 / delta)) =
          delta * ((1 / delta) *
            mu.real
              (atTopCrossingEvent
                (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam)
                (1 / delta))) := by
        field_simp [hdelta.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hdelta.le
      _ = delta := by ring
  exact (measureReal_mono
    (forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_subset_crossing
      hdelta hlam hlam1 hX_unit)).trans hcross

/-- Outside the canonical failure event, the explicit boundary holds at every
time `n >= 2` for the running average of predictable conditional means. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerBessel_all_of_not_mem
    {Omega : Type*} {X mean : ℕ → Omega → ℝ} {lam delta : ℝ} {omega : Omega}
    (h_omega : omega ∉
      forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure
        X mean lam delta) :
    ∀ n : ℕ, 2 ≤ n →
      forwardPrefixMean (fun k => mean k omega) n <
        forwardPrefixMean (fun k => X k omega) n +
          forwardEmpiricalBernsteinBesselBoundary X lam delta n omega := by
  intro n hn
  apply lt_of_not_ge
  intro hfail
  apply h_omega
  exact ⟨n, hn, by linarith⟩

/-- One event of outer failure mass at most `delta` carries the explicit
predictable-mean hybrid-Bessel boundary simultaneously for all `n >= 2`. -/
theorem exists_forwardPredictableMeanEmpiricalBernsteinLowerBessel_event
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration ℕ mOmega}
    {X mean : ℕ → Omega → ℝ} {lam delta : ℝ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted F X)
    (hmean_adapted : StronglyAdapted F mean)
    (hX_unit : ∀ k omega, 0 ≤ X k omega ∧ X k omega ≤ 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ ≤ delta ∧
        ∀ omega ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          forwardPrefixMean (fun k => mean k omega) n <
            forwardPrefixMean (fun k => X k omega) n +
              forwardEmpiricalBernsteinBesselBoundary X lam delta n omega := by
  let badEvent :=
    forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure
      X mean lam delta
  refine ⟨badEventᶜ, ?_, ?_⟩
  · simpa [badEvent] using
      (forwardPredictableMeanEmpiricalBernsteinLowerBesselFailure_mass_le_delta
        hdelta hlam hlam1 hX_adapted hmean_adapted hX_unit hmean)
  · intro omega h_omega
    exact forwardPredictableMeanEmpiricalBernsteinLowerBessel_all_of_not_mem h_omega

/-- Constant predictable means recover the merged fixed-mean upper process. -/
theorem forwardPredictableMeanEmpiricalBernsteinProcess_const_mean_eq
    {Omega : Type*} (X : ℕ → Omega → ℝ) (mean lam : ℝ)
    (n : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinProcess
        X (fun _ _ => mean) lam n omega =
      forwardEmpiricalBernsteinProcess X mean lam n omega := by
  rfl

/-- Constant predictable means recover the merged fixed-mean lower process. -/
theorem forwardPredictableMeanEmpiricalBernsteinLowerProcess_const_mean_eq
    {Omega : Type*} (X : ℕ → Omega → ℝ) (mean lam : ℝ)
    (n : ℕ) (omega : Omega) :
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
        X (fun _ _ => mean) lam n omega =
      forwardEmpiricalBernsteinLowerProcess X mean lam n omega := by
  rfl

end

end FormalSLT.AnytimeValid
