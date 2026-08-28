/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionGeometry
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# A continuous mixture over singular fractions for forward-Bessel bounds

This module mixes the actual lower-tail forward empirical-Bernstein
e-processes over the singular fraction map `u ↦ exp (-1 / u)` under the
uniform prior on `[0,1]`.  One Ville event then controls every time `n ≥ 2`
and every target fraction `0 < λ ≤ exp (-1)`.

The observable hybrid-Bessel expression remains a pointwise lower envelope;
it is not asserted to be an e-process.  The continuous prior mixture is the
stochastic object to which Ville's inequality is applied.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes.TimeUniformContinuous
open scoped BigOperators ENNReal

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- Uniform-prior mixture of the actual lower-tail empirical-Bernstein
processes reached by the singular fraction map. -/
def singularFractionLowerMixtureProcess
    (X : Nat → Omega → Real) (mean : Real) : Nat → Omega → Real :=
  continuousPriorMixtureProcess (uniformTiltPrior 0 1) fun u =>
    forwardEmpiricalBernsteinLowerProcess X mean (singularFraction u)

/-- The one common Ville event for the singular-fraction lower mixture. -/
def singularFractionLowerMixtureExceptionalEvent
    (X : Nat → Omega → Real) (mean delta : Real) : Set Omega :=
  {omega | ∃ n : Nat, 0 < n ∧
    1 / delta ≤ singularFractionLowerMixtureProcess X mean n omega}

/-- The observable all-fraction boundary at target fraction `lam`. -/
def singularFractionForwardBesselBoundary
    (X : Nat → Omega → Real) (lam delta : Real)
    (n : Nat) (omega : Omega) : Real :=
  lam * forwardHybridBesselPenalty (fun k => X k omega) n +
    Real.exp 1 / lam *
      Real.log
        (singularFractionLogScale lam *
          (singularFractionLogScale lam + 1) / delta)

private theorem stronglyMeasurable_forwardLowerSum
    {m : MeasurableSpace Omega} {X : Nat → Omega → Real}
    (mean : Real) (n : Nat)
    (hX : ∀ k < n, StronglyMeasurable[m] (X k)) :
    StronglyMeasurable[m]
      (fun omega => ∑ k ∈ Finset.range n, (mean - X k omega)) := by
  have heq :
      (fun omega => ∑ k ∈ Finset.range n, (mean - X k omega)) =
        ∑ k ∈ Finset.range n, (fun omega => mean - X k omega) := by
    funext omega
    simp only [Finset.sum_apply]
  rw [heq]
  exact Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
    stronglyMeasurable_const.sub (hX k (Finset.mem_range.mp hk))

private theorem stronglyMeasurable_forwardPredictorProcess_prefix
    {m : MeasurableSpace Omega} {X : Nat → Omega → Real}
    {n k : Nat} (hk : k < n)
    (hX : ∀ j < n, StronglyMeasurable[m] (X j)) :
    StronglyMeasurable[m] (forwardPredictorProcess X k) := by
  by_cases hk0 : k = 0
  · subst k
    change StronglyMeasurable[m] (fun _ : Omega => (1 : Real) / 2)
    exact stronglyMeasurable_const
  · have hsum : StronglyMeasurable[m]
        (fun omega => ∑ j ∈ Finset.range k, X j omega) := by
      have heq :
          (fun omega => ∑ j ∈ Finset.range k, X j omega) =
            ∑ j ∈ Finset.range k, X j := by
        funext omega
        simp only [Finset.sum_apply]
      rw [heq]
      exact Finset.stronglyMeasurable_sum (Finset.range k) fun j hj =>
        hX j ((Finset.mem_range.mp hj).trans hk)
    have heq : forwardPredictorProcess X k =
        fun omega =>
          (∑ j ∈ Finset.range k, X j omega) * ((k : Real)⁻¹) := by
      funext omega
      simp [forwardPredictorProcess, forwardPredictor, hk0,
        forwardPrefixMean, div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const ((k : Real)⁻¹)

private theorem stronglyMeasurable_forwardPredictableQuadratic_prefix
    {m : MeasurableSpace Omega} {X : Nat → Omega → Real}
    (n : Nat) (hX : ∀ k < n, StronglyMeasurable[m] (X k)) :
    StronglyMeasurable[m]
      (fun omega => forwardPredictableQuadratic (fun k => X k omega) n) := by
  have heq :
      (fun omega => forwardPredictableQuadratic (fun k => X k omega) n) =
        ∑ k ∈ Finset.range n,
          (fun omega => (X k omega - forwardPredictorProcess X k omega) ^ 2) := by
    funext omega
    simp only [forwardPredictableQuadratic, forwardPredictorProcess,
      Finset.sum_apply]
  rw [heq]
  exact Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
    ((hX k (Finset.mem_range.mp hk)).sub
      (stronglyMeasurable_forwardPredictorProcess_prefix
        (Finset.mem_range.mp hk) hX)).pow 2

private theorem stronglyMeasurable_singularFractionLowerProcess_prod
    {m : MeasurableSpace Omega} {X : Nat → Omega → Real}
    (mean : Real) (n : Nat)
    (hX : ∀ k < n, StronglyMeasurable[m] (X k)) :
    StronglyMeasurable[MeasurableSpace.prod m inferInstance]
      (fun q : Omega × Real =>
        forwardEmpiricalBernsteinLowerProcess X mean
          (singularFraction q.2) n q.1) := by
  have hsum : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
      (fun q : Omega × Real =>
        ∑ k ∈ Finset.range n, (mean - X k q.1)) :=
    (stronglyMeasurable_forwardLowerSum mean n hX).comp_measurable
      (measurable_fst : Measurable (Prod.fst : Omega × Real → Omega))
  have hquad : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
      (fun q : Omega × Real =>
        forwardPredictableQuadratic (fun k => X k q.1) n) :=
    (stronglyMeasurable_forwardPredictableQuadratic_prefix n hX).comp_measurable
      (measurable_fst : Measurable (Prod.fst : Omega × Real → Omega))
  have htheta : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
      (fun q : Omega × Real => singularFraction q.2) :=
    (measurable_singularFraction.comp measurable_snd).stronglyMeasurable
  have hpsi : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
      (fun q : Omega × Real =>
        forwardEmpiricalBernsteinPsi (singularFraction q.2)) := by
    unfold forwardEmpiricalBernsteinPsi
    have harg : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
        (fun q : Omega × Real => 1 - singularFraction q.2) :=
      stronglyMeasurable_const.sub htheta
    have hlog : StronglyMeasurable[MeasurableSpace.prod m inferInstance]
        (fun q : Omega × Real => Real.log (1 - singularFraction q.2)) :=
      (Real.measurable_log.comp harg.measurable).stronglyMeasurable
    exact hlog.neg.sub htheta
  rw [show (fun q : Omega × Real =>
      forwardEmpiricalBernsteinLowerProcess X mean
        (singularFraction q.2) n q.1) =
      fun q => Real.exp
        (singularFraction q.2 *
            (∑ k ∈ Finset.range n, (mean - X k q.1)) -
          forwardEmpiricalBernsteinPsi (singularFraction q.2) *
            forwardPredictableQuadratic (fun k => X k q.1) n) by
    funext q
    rw [forwardEmpiricalBernsteinLowerProcess_eq]]
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((htheta.mul hsum).sub (hpsi.mul hquad))

private theorem stronglyMeasurable_singularFractionLowerProcess_parameter
    (X : Nat → Omega → Real) (mean : Real) (n : Nat) (omega : Omega) :
    StronglyMeasurable
      (fun u => forwardEmpiricalBernsteinLowerProcess X mean
        (singularFraction u) n omega) := by
  have htheta : StronglyMeasurable singularFraction :=
    measurable_singularFraction.stronglyMeasurable
  have hpsi : StronglyMeasurable
      (fun u => forwardEmpiricalBernsteinPsi (singularFraction u)) := by
    unfold forwardEmpiricalBernsteinPsi
    have harg : StronglyMeasurable
        (fun u => 1 - singularFraction u) :=
      stronglyMeasurable_const.sub htheta
    have hlog : StronglyMeasurable
        (fun u => Real.log (1 - singularFraction u)) :=
      (Real.measurable_log.comp harg.measurable).stronglyMeasurable
    exact hlog.neg.sub htheta
  rw [show (fun u => forwardEmpiricalBernsteinLowerProcess X mean
      (singularFraction u) n omega) =
      fun u => Real.exp
        (singularFraction u *
            (∑ k ∈ Finset.range n, (mean - X k omega)) -
          forwardEmpiricalBernsteinPsi (singularFraction u) *
            forwardPredictableQuadratic (fun k => X k omega) n) by
    funext u
    rw [forwardEmpiricalBernsteinLowerProcess_eq]]
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((htheta.mul_const _).sub (hpsi.mul_const _))

/-- The hybrid Bessel penalty is nonnegative from time two onward. -/
theorem forwardHybridBesselPenalty_nonneg_of_two
    (x : Nat → Real) {n : Nat} (hn : 2 ≤ n) :
    0 ≤ forwardHybridBesselPenalty x n := by
  have hq : 0 ≤ forwardBesselQ x n := forwardBesselQ_nonneg x n
  unfold forwardHybridBesselPenalty
  apply le_min
  · nlinarith
  · have hden : 0 < (n : Real) - 1 := by
      have : (1 : Real) < (n : Real) := by
        exact_mod_cast (show 1 < n by omega)
      linarith
    have hratio : 0 ≤ (n : Real) / ((n : Real) - 1) :=
      div_nonneg (Nat.cast_nonneg n) hden.le
    have hharm : 0 ≤ ((harmonic (n - 2) : Rat) : Real) := by
      unfold harmonic
      positivity
    positivity

private theorem singularFractionLowerProcess_le_exp_card
    {X : Nat → Omega → Real} {mean u : Real}
    (hmean : mean ∈ Set.Icc (0 : Real) 1)
    (hX : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hu : u ∈ Set.Icc (0 : Real) 1) (n : Nat) (omega : Omega) :
    forwardEmpiricalBernsteinLowerProcess X mean (singularFraction u) n omega ≤
      Real.exp (n : Real) := by
  rw [forwardEmpiricalBernsteinLowerProcess_eq]
  apply Real.exp_le_exp.mpr
  have htheta0 : 0 ≤ singularFraction u := singularFraction_nonneg u
  have htheta1 : singularFraction u ≤ 1 :=
    (singularFraction_lt_one_of_mem_unit hu).le
  have hsum :
      (∑ k ∈ Finset.range n, (mean - X k omega)) ≤ (n : Real) := by
    calc
      (∑ k ∈ Finset.range n, (mean - X k omega)) ≤
          ∑ _k ∈ Finset.range n, (1 : Real) := by
            apply Finset.sum_le_sum
            intro k _hk
            linarith [(hmean.2), ((hX k omega).1)]
      _ = (n : Real) := by simp
  have hlinear : singularFraction u *
      (∑ k ∈ Finset.range n, (mean - X k omega)) ≤ (n : Real) := by
    calc
      singularFraction u *
          (∑ k ∈ Finset.range n, (mean - X k omega)) ≤
          singularFraction u * (n : Real) :=
        mul_le_mul_of_nonneg_left hsum htheta0
      _ ≤ 1 * (n : Real) :=
        mul_le_mul_of_nonneg_right htheta1 (Nat.cast_nonneg n)
      _ = (n : Real) := one_mul _
  have hpenalty : 0 ≤
      forwardEmpiricalBernsteinPsi (singularFraction u) *
        forwardPredictableQuadratic (fun k => X k omega) n := by
    apply mul_nonneg
    · exact forwardEmpiricalBernsteinPsi_nonneg htheta0
        (singularFraction_lt_one_of_mem_unit hu)
    · unfold forwardPredictableQuadratic
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- Bounded adapted observations make the continuous singular-fraction mixture
an actual e-process.  Product and restricted-product integrability are
derived from an explicit uniform finite-time bound. -/
theorem singularFractionLowerMixtureProcess_eProcess
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real} {mean : Real}
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    EProcess mu F (singularFractionLowerMixtureProcess X mean) := by
  let prior : Measure Real := uniformTiltPrior 0 1
  let M : Real → Nat → Omega → Real := fun u =>
    forwardEmpiricalBernsteinLowerProcess X mean (singularFraction u)
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    exact uniformTiltPrior_isProbabilityMeasure (by norm_num)
  have hjoint_ambient (n : Nat) : StronglyMeasurable
      (fun q : Omega × Real => M q.2 n q.1) := by
    dsimp [M]
    exact stronglyMeasurable_singularFractionLowerProcess_prod mean n
      (fun k _hk => (hX_adapted k).mono (F.le (k + 1)))
  have hjoint (n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × Real => M q.2 n q.1) := by
    dsimp [M]
    exact stronglyMeasurable_singularFractionLowerProcess_prod mean n
      (fun k hk => (hX_adapted k).mono
        (F.mono (Nat.succ_le_of_lt hk)))
  have hprod_current (n : Nat) : Integrable
      (fun q : Omega × Real => M q.2 n q.1) (mu.prod prior) := by
    refine Integrable.of_bound (hjoint_ambient n).aestronglyMeasurable
      (Real.exp (n : Real)) ?_
    have hsupp : ∀ᵐ q : Omega × Real ∂(mu.prod prior),
        q.2 ∈ Set.Icc (0 : Real) 1 := by
      exact (Measure.quasiMeasurePreserving_snd).ae
        (by simpa [prior] using
          (uniformTiltPrior_ae_mem_Icc (lam0 := (0 : Real)) (lam1 := 1)))
    filter_upwards [hsupp] with q hq
    rw [Real.norm_eq_abs, abs_of_pos (by
      dsimp [M]
      rw [forwardEmpiricalBernsteinLowerProcess_eq]
      positivity)]
    exact singularFractionLowerProcess_le_exp_card hmean_unit hX_unit hq n q.1
  have hprod_prior (n : Nat) : Integrable
      (fun q : Real × Omega => M q.1 n q.2) (prior.prod mu) := by
    simpa [Function.comp_def] using (hprod_current n).swap
  have hmix_adapted : StronglyAdapted F
      (singularFractionLowerMixtureProcess X mean) := by
    intro n
    change StronglyMeasurable[F n]
      (fun omega => ∫ u, M u n omega ∂prior)
    letI : MeasurableSpace Omega := F n
    exact StronglyMeasurable.integral_prod_right' (ν := prior) (hjoint n)
  have hmix_integrable (n : Nat) :
      Integrable (singularFractionLowerMixtureProcess X mean n) mu := by
    exact (hprod_current n).integral_prod_left
  have hrestrict (n : Nat) {s : Set Omega} : Integrable
      (fun q : Omega × Real => M q.2 n q.1)
      ((mu.restrict s).prod prior) :=
    (hprod_current n).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hfixed : ∀ᵐ u ∂prior, Supermartingale (M u) F mu := by
    have hsupp : ∀ᵐ u ∂prior, u ∈ Set.Icc (0 : Real) 1 := by
      simpa [prior] using
        (uniformTiltPrior_ae_mem_Icc (lam0 := (0 : Real)) (lam1 := 1))
    filter_upwards [hsupp] with u hu
    exact (forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
      (singularFraction_nonneg u) (singularFraction_lt_one_of_mem_unit hu)
      hX_adapted hX_unit hmean).supermartingale
  have hsup : Supermartingale
      (singularFractionLowerMixtureProcess X mean) F mu := by
    change Supermartingale (continuousPriorMixtureProcess prior M) F mu
    exact (continuousPriorMixture_supermartingale
      hmix_adapted hmix_integrable
      (fun n => hprod_prior (n + 1))
      (fun n _s _hs _hfinite => hrestrict (n + 1))
      hprod_current
      (fun n _s _hs _hfinite => hrestrict n)
      hfixed (fun u n omega => by
        rw [forwardEmpiricalBernsteinLowerProcess_eq]
        exact (Real.exp_pos _).le)).1
  refine
    { nonneg := ?_
      start_one := ?_
      supermartingale := hsup }
  · intro n omega
    change 0 ≤ ∫ u, M u n omega ∂prior
    exact integral_nonneg fun u => by
      dsimp [M]
      rw [forwardEmpiricalBernsteinLowerProcess_eq]
      exact (Real.exp_pos _).le
  · intro omega
    simp [singularFractionLowerMixtureProcess,
      continuousPriorMixtureProcess,
      forwardEmpiricalBernsteinLowerProcess_eq,
      forwardPredictableQuadratic]

/-- The one singular-mixture exceptional event has mass at most `delta`. -/
theorem singularFractionLowerMixtureExceptionalEvent_mass_le_delta
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real} {mean delta : Real}
    (hdelta : 0 < delta)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) ≤
      delta := by
  let prior : Measure Real := uniformTiltPrior 0 1
  let M : Real → Nat → Omega → Real := fun u =>
    forwardEmpiricalBernsteinLowerProcess X mean (singularFraction u)
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    exact uniformTiltPrior_isProbabilityMeasure (by norm_num)
  have hE := singularFractionLowerMixtureProcess_eProcess
    hX_adapted hX_unit hmean_unit hmean
  change mu.real {omega | ∃ n : Nat, 0 < n ∧
    1 / delta ≤ continuousPriorMixtureProcess prior M n omega} ≤ delta
  exact continuousPriorMixture_crossing_bound hdelta hE.supermartingale
    hE.nonneg (fun u omega => by
      dsimp [M]
      simp [forwardEmpiricalBernsteinLowerProcess_eq,
        forwardPredictableQuadratic])

private theorem integrable_singularFractionLowerProcess_prior
    {X : Nat → Omega → Real} {mean : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (n : Nat) (omega : Omega) :
    Integrable
      (fun u => forwardEmpiricalBernsteinLowerProcess X mean
        (singularFraction u) n omega)
      (uniformTiltPrior 0 1) := by
  have hparameter : StronglyMeasurable
      (fun u => forwardEmpiricalBernsteinLowerProcess X mean
        (singularFraction u) n omega) :=
    stronglyMeasurable_singularFractionLowerProcess_parameter
      X mean n omega
  letI : IsProbabilityMeasure (uniformTiltPrior 0 1) :=
    uniformTiltPrior_isProbabilityMeasure (by norm_num)
  refine Integrable.of_bound hparameter.aestronglyMeasurable
    (Real.exp (n : Real)) ?_
  filter_upwards [uniformTiltPrior_ae_mem_Icc
      (lam0 := (0 : Real)) (lam1 := 1)] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (by
    rw [forwardEmpiricalBernsteinLowerProcess_eq]
    positivity)]
  exact singularFractionLowerProcess_le_exp_card hmean_unit hX_unit hu n omega

/-- Outside the single Ville event, the observable Bessel boundary holds for
every time `n ≥ 2` and every fraction `0 < lam ≤ exp (-1)`. -/
theorem singularFractionLowerMixture_all_fraction_boundary
    {X : Nat → Omega → Real} {mean delta : Real}
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {omega : Omega}
    (homega : omega ∉
      singularFractionLowerMixtureExceptionalEvent X mean delta) :
    ∀ n : Nat, 2 ≤ n → ∀ lam : Real,
      0 < lam → lam ≤ Real.exp (-1) →
      (∑ k ∈ Finset.range n, (mean - X k omega)) <
        singularFractionForwardBesselBoundary X lam delta n omega := by
  letI : IsProbabilityMeasure (uniformTiltPrior 0 1) :=
    uniformTiltPrior_isProbabilityMeasure (by norm_num)
  intro n hn lam hlam_pos hlam
  let S : Real := ∑ k ∈ Finset.range n, (mean - X k omega)
  let Q : Real := forwardHybridBesselPenalty (fun k => X k omega) n
  let L : Real := singularFractionLogScale lam
  let A : Real := L * (L + 1)
  have hL : 1 ≤ L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos (zero_lt_one.trans_le hL) (by linarith)
  have hratio_one : 1 < A / delta := by
    apply (lt_div_iff₀ hdelta).2
    have hA_two : 2 ≤ A := by
      dsimp [A]
      nlinarith
    linarith
  have hlog_pos : 0 < Real.log (A / delta) := Real.log_pos hratio_one
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact forwardHybridBesselPenalty_nonneg_of_two _ hn
  have hboundary_pos : 0 <
      lam * Q + Real.exp 1 / lam * Real.log (A / delta) := by
    have hleft : 0 ≤ lam * Q := by positivity
    have hright : 0 < Real.exp 1 / lam * Real.log (A / delta) := by positivity
    linarith
  by_cases hS : S < 0
  · change S < singularFractionForwardBesselBoundary X lam delta n omega
    simpa [singularFractionForwardBesselBoundary, S, Q, L, A] using
      hS.trans hboundary_pos
  · apply lt_of_not_ge
    intro hfail
    have hfail' :
        lam * Q +
            Real.exp 1 / lam * Real.log (A / delta) ≤ S := by
      simpa [singularFractionForwardBesselBoundary, S, Q, L, A] using hfail
    have hgap : Real.exp 1 / lam * Real.log (A / delta) ≤
        S - lam * Q := by
      linarith
    have hgap_nonneg : 0 ≤ S - lam * Q := by
      have : 0 < Real.exp 1 / lam * Real.log (A / delta) := by positivity
      linarith
    have hscaled : Real.log (A / delta) ≤
        lam / Real.exp 1 * (S - lam * Q) := by
      calc
        Real.log (A / delta) = lam / Real.exp 1 *
            (Real.exp 1 / lam * Real.log (A / delta)) := by
              field_simp [hlam_pos.ne', Real.exp_ne_zero]
        _ ≤ lam / Real.exp 1 * (S - lam * Q) :=
          mul_le_mul_of_nonneg_left hgap (by positivity)
    have hfiber : Integrable
        (fun u => forwardEmpiricalBernsteinLowerProcess X mean
          (singularFraction u) n omega)
        (uniformTiltPrior 0 1) := by
      exact integrable_singularFractionLowerProcess_prior
        hX_unit hmean_unit n omega
    have hlower (u : Real) (hu : u ∈ singularFractionWindow lam) :
        A / delta ≤
          forwardEmpiricalBernsteinLowerProcess X mean
            (singularFraction u) n omega := by
      have hmap := singularFractionWindow_maps hlam_pos hlam hu
      have htheta0 : 0 ≤ singularFraction u := singularFraction_nonneg u
      have htheta_lam : singularFraction u ≤ lam := hmap.2
      have htheta_exp : singularFraction u ≤ Real.exp (-1) :=
        htheta_lam.trans hlam
      have hpsi := forwardEmpiricalBernsteinPsi_le_sq_of_le_exp_neg_one
        htheta0 htheta_exp
      have htheta_sq : singularFraction u ^ 2 ≤
          lam * singularFraction u := by
        nlinarith
      have hlinear : lam / Real.exp 1 * (S - lam * Q) ≤
          singularFraction u * (S - lam * Q) :=
        mul_le_mul_of_nonneg_right hmap.1 hgap_nonneg
      have hpenalty :
          forwardEmpiricalBernsteinPsi (singularFraction u) * Q ≤
            (lam * singularFraction u) * Q := by
        exact (mul_le_mul_of_nonneg_right hpsi hQ).trans
          (mul_le_mul_of_nonneg_right htheta_sq hQ)
      have hexponent : Real.log (A / delta) ≤
          singularFraction u * S -
            forwardEmpiricalBernsteinPsi (singularFraction u) * Q := by
        calc
          Real.log (A / delta) ≤
              lam / Real.exp 1 * (S - lam * Q) := hscaled
          _ ≤ singularFraction u * (S - lam * Q) := hlinear
          _ ≤ singularFraction u * S -
              forwardEmpiricalBernsteinPsi (singularFraction u) * Q := by
            nlinarith
      calc
        A / delta = Real.exp (Real.log (A / delta)) := by
          rw [Real.exp_log (div_pos hA_pos hdelta)]
        _ ≤ forwardEmpiricalBernsteinLowerBesselEnvelope X mean
              (singularFraction u) n omega := by
          unfold forwardEmpiricalBernsteinLowerBesselEnvelope
          apply Real.exp_le_exp.mpr
          simpa [S, Q] using hexponent
        _ ≤ forwardEmpiricalBernsteinLowerProcess X mean
              (singularFraction u) n omega :=
          forwardEmpiricalBernsteinLowerBesselEnvelope_le_lowerProcess
            htheta0 (lt_of_le_of_lt htheta_exp
              (Real.exp_lt_one_iff.mpr (by norm_num))) hn omega
            (fun i hi => hX_unit i omega)
    have hmix := continuousPriorMixtureProcess_competes_of_priorMass
      (uniformTiltPrior 0 1) (measurableSet_singularFractionWindow lam)
      (M := fun u =>
        forwardEmpiricalBernsteinLowerProcess X mean (singularFraction u))
      (c := A / delta) (n := n) (ω := omega)
      (fun u => by
        rw [forwardEmpiricalBernsteinLowerProcess_eq]
        exact (Real.exp_pos _).le)
      hfiber hlower
    have hmass := singularFractionWindow_uniformTiltPrior_real hlam_pos hlam
    have hcross : 1 / delta ≤
        singularFractionLowerMixtureProcess X mean n omega := by
      change 1 / delta ≤ continuousPriorMixtureProcess
        (uniformTiltPrior 0 1)
        (fun u => forwardEmpiricalBernsteinLowerProcess X mean
          (singularFraction u)) n omega
      rw [hmass] at hmix
      have hA_def : singularFractionLogScale lam *
          (singularFractionLogScale lam + 1) = A := rfl
      rw [hA_def] at hmix
      have hid : (1 / A) * (A / delta) = 1 / delta := by
        field_simp [hA_pos.ne', hdelta.ne']
      rwa [hid] at hmix
    exact homega ⟨n, by omega, hcross⟩

/-- End-to-end common-event theorem for the singular-fraction mixture.

The exceptional event is chosen before the reporting time and target
fraction.  Outside it, the observable hybrid-Bessel inequality therefore
holds simultaneously for every `n ≥ 2` and every
`0 < lam ≤ exp (-1)`. -/
theorem singularFractionLowerMixture_timeUniform_all_fraction
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat → Omega → Real}
    {mean delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : mean ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] fun _ => mean) :
    mu.real (singularFractionLowerMixtureExceptionalEvent X mean delta) ≤
        delta ∧
      ∀ omega ∉ singularFractionLowerMixtureExceptionalEvent X mean delta,
        ∀ n : Nat, 2 ≤ n → ∀ lam : Real,
          0 < lam → lam ≤ Real.exp (-1) →
          (∑ k ∈ Finset.range n, (mean - X k omega)) <
            singularFractionForwardBesselBoundary X lam delta n omega := by
  constructor
  · exact singularFractionLowerMixtureExceptionalEvent_mass_le_delta
      hdelta hX_adapted hX_unit hmean_unit hmean
  · intro omega homega
    exact singularFractionLowerMixture_all_fraction_boundary
      hX_unit hmean_unit hdelta hdelta_one homega

end

end FormalSLT.AnytimeValid
