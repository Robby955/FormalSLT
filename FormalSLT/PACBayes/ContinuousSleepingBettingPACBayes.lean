/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingMixture
import FormalSLT.AnytimeValid.ForwardBesselProcess
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous PAC-Bayes bridge for executable sleeping betting masters

This module connects the exact finite-prefix implementation of a countable
sleeping-expert betting master to the continuous-hypothesis PAC-Bayes layer.
For every hypothesis, the master bet is computed from the active finite prefix
and the closed-form dyadic sleeping tail. A probability prior then mixes those
strictly positive master wealth processes over an arbitrary measurable
hypothesis space.

One common event controls every positive reporting time and every eligible posterior.
Outside that event, the posterior-average log wealth is bounded by the
posterior KL divergence plus `log (1 / delta)`. The posterior may be selected
after observing the path; no measurability of that pointwise selector is
needed.

The module also supplies the exact empirical-Bernstein lower bound on log
wealth, exposes the dyadic price of post-path atom selection, and derives an
ordinary upper bound for posterior-average constant conditional risk by
running the master on complemented losses. A second endpoint removes the
unknown residual penalty using a bounded-loss envelope. The per-hypothesis
master is finite-time executable; arbitrary continuous posterior integrals and
KL terms are mathematical objects and require separate numerical witnesses for
an executable certificate.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.TimeUniformContinuous

namespace FormalSLT.PACBayes.ContinuousSleepingBettingPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-! ## Exact empirical-Bernstein log-wealth lower bounds -/

/-- Exact empirical-Bernstein score accumulated by one betting strategy on one
residual path. Unlike a generic quadratic relaxation, this retains the sharp
log-cumulant `forwardEmpiricalBernsteinPsi` already used by FormalSLT's
predictable plug-in process. -/
def forwardEmpiricalBernsteinBettingScore
    (residual bet : Nat -> Omega -> Real) (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    (bet k omega * residual k omega -
      forwardEmpiricalBernsteinPsi (bet k omega) * residual k omega ^ 2)

/-- One legal empirical-Bernstein score is bounded by the logarithm of its
algebraic betting factor. -/
theorem forwardEmpiricalBernsteinScore_le_log_one_add
    {lam z : Real} (hlam0 : 0 <= lam) (hlam1 : lam < 1)
    (hz : -1 <= z) :
    lam * z - forwardEmpiricalBernsteinPsi lam * z ^ 2 <=
      Real.log (1 + lam * z) := by
  have hpos : 0 < 1 + lam * z := by
    have hprod : -lam <= lam * z :=
      by simpa using mul_le_mul_of_nonneg_left hz hlam0
    linarith
  exact (Real.le_log_iff_exp_le hpos).2
    (exp_forwardEmpiricalBernstein_le_one_add hlam0 hlam1 hz)

/-- The exact pathwise empirical-Bernstein score lower-bounds log wealth for
every predictable strategy taking values in `[0, 1)`, provided residuals are
bounded below by `-1`. -/
theorem forwardEmpiricalBernsteinBettingScore_le_log_algebraicBettingWealth
    (residual bet : Nat -> Omega -> Real) (n : Nat) (omega : Omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n -> 0 <= bet k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n -> bet k omega < 1)
    (hresidual : forall k, k ∈ Finset.range n -> -1 <= residual k omega) :
    forwardEmpiricalBernsteinBettingScore residual bet n omega <=
      Real.log (algebraicBettingWealth residual bet n omega) := by
  unfold forwardEmpiricalBernsteinBettingScore algebraicBettingWealth
  rw [Real.log_prod]
  · exact Finset.sum_le_sum fun k hk =>
      forwardEmpiricalBernsteinScore_le_log_one_add
        (hbet_nonneg k hk) (hbet_lt_one k hk) (hresidual k hk)
  · intro k hk
    have hprod : -bet k omega <= bet k omega * residual k omega :=
      by simpa using
        mul_le_mul_of_nonneg_left (hresidual k hk) (hbet_nonneg k hk)
    have hpos : 0 < 1 + bet k omega * residual k omega := by
      linarith [hbet_lt_one k hk]
    exact hpos.ne'

/-- The executable countable master pays exactly the negative log of the
selected expert's dyadic prior weight on top of its exact empirical-Bernstein
score. -/
theorem forwardEmpiricalBernsteinBettingScore_le_log_countableSleepingMaster_sub_logWeight
    {residual : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hwealth_nonneg : forall i k xi,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy i) k xi)
    {j n : Nat} (hjn : j < n) (omega : Omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hresidual : forall k, k ∈ Finset.range n ->
      -1 <= residual k omega) :
    forwardEmpiricalBernsteinBettingScore residual
        (sleepingStrategy strategy j) n omega <=
      Real.log
          (algebraicBettingWealth residual
            (countableSleepingMasterBet residual strategy) n omega) -
        Real.log (dyadicExpertWeight j) := by
  have hscore :=
    forwardEmpiricalBernsteinBettingScore_le_log_algebraicBettingWealth
      residual (sleepingStrategy strategy j) n omega hbet_nonneg
        hbet_lt_one hresidual
  have hexpert_pos :
      0 < algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega := by
    unfold algebraicBettingWealth
    exact Finset.prod_pos fun k hk => by
      have hprod :
          -sleepingStrategy strategy j k omega <=
            sleepingStrategy strategy j k omega * residual k omega :=
        by simpa using
          mul_le_mul_of_nonneg_left (hresidual k hk) (hbet_nonneg k hk)
      linarith [hbet_lt_one k hk]
  have hregret := countableSleepingMaster_logWealth_regret_le
    hwealth_nonneg hjn hexpert_pos
  linarith

/-- The executable countable sleeping-expert master wealth associated with one
hypothesis. Its master bet is a finite computation at every time. -/
def continuousSleepingBettingMasterProcess
    (X : Theta -> Nat -> Omega -> Real) (center : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) :
    Theta -> Nat -> Omega -> Real :=
  fun theta =>
    bettingWealthProcess (X theta)
      (countableSleepingMasterBet
        (fun k omega => X theta k omega - center theta) strategy)
      (center theta)

/-- Positive-time crossing event for the continuous prior mixture of
executable sleeping-master wealth processes. -/
def continuousSleepingBettingPACBayesExceptionalEvent
    (prior : Measure Theta)
    (X : Theta -> Nat -> Omega -> Real) (center : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) (delta : Real) : Set Omega :=
  {omega | exists n : Nat, 0 < n ∧
    (1 / delta) <=
      continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess X center strategy) n omega}

omit [MeasurableSpace Theta] in
/-- Each hypothesis-indexed executable sleeping master is an e-process when
all of its declared sleeping experts are e-processes. -/
theorem continuousSleepingBettingMasterProcess_eProcess
    [IsFiniteMeasure mu]
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall theta j,
      EProcess mu F
        (bettingWealthProcess (X theta)
          (sleepingStrategy strategy j) (center theta)))
    (theta : Theta) :
    EProcess mu F
      (continuousSleepingBettingMasterProcess X center strategy theta) := by
  unfold continuousSleepingBettingMasterProcess
  exact countableSleepingMasterBet_eProcess
    (X theta) (center theta) strategy (hX_adapted theta)
      hstrategy_adapted (hcomponent theta)

omit [MeasurableSpace Theta] in
/-- The closed-form sleeping tail makes the executable master wealth strictly
positive, even though component e-processes are only assumed nonnegative. -/
theorem continuousSleepingBettingMasterProcess_pos
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hcomponent_nonneg : forall theta j n omega,
      0 <= bettingWealthProcess (X theta)
        (sleepingStrategy strategy j) (center theta) n omega)
    (theta : Theta) (n : Nat) (omega : Omega) :
    0 < continuousSleepingBettingMasterProcess
      X center strategy theta n omega := by
  let residual : Nat -> Omega -> Real :=
    fun k xi => X theta k xi - center theta
  have hwealth_nonneg : forall j k xi,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) k xi := by
    intro j k xi
    simpa [residual, algebraicBettingWealth_eq_bettingWealthProcess] using
      hcomponent_nonneg theta j k xi
  unfold continuousSleepingBettingMasterProcess
  rw [← algebraicBettingWealth_eq_bettingWealthProcess]
  rw [countableSleepingMasterWealth_eq_mixture residual strategy
    (fun k xi =>
      (countableSleepingMixtureWealth_pos hwealth_nonneg k xi).ne') n omega]
  exact countableSleepingMixtureWealth_pos hwealth_nonneg n omega

omit [MeasurableSpace Theta] in
/-- One selected sleeping strategy lower-bounds the logarithm of the
hypothesis-indexed executable master, with its exact dyadic atom cost exposed.
This statement is pathwise; the PAC-Bayes event is applied below. -/
theorem
    forwardEmpiricalBernsteinBettingScore_le_log_continuousSleepingBettingMaster_sub_logWeight
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hcomponent_nonneg : forall theta i k xi,
      0 <= bettingWealthProcess (X theta)
        (sleepingStrategy strategy i) (center theta) k xi)
    {j n : Nat} (hjn : j < n) (omega : Omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hresidual : forall theta k, k ∈ Finset.range n ->
      -1 <= X theta k omega - center theta) :
    forall theta,
      forwardEmpiricalBernsteinBettingScore
          (fun k xi => X theta k xi - center theta)
          (sleepingStrategy strategy j) n omega <=
        Real.log
            (continuousSleepingBettingMasterProcess
              X center strategy theta n omega) -
          Real.log (dyadicExpertWeight j) := by
  intro theta
  have hwealth_nonneg : forall i k xi,
      0 <= algebraicBettingWealth
        (fun t eta => X theta t eta - center theta)
        (sleepingStrategy strategy i) k xi := by
    intro i k xi
    simpa only [algebraicBettingWealth_eq_bettingWealthProcess] using
      hcomponent_nonneg theta i k xi
  have hscore :=
    forwardEmpiricalBernsteinBettingScore_le_log_countableSleepingMaster_sub_logWeight
      hwealth_nonneg hjn omega hbet_nonneg hbet_lt_one
        (hresidual theta)
  simpa only [continuousSleepingBettingMasterProcess,
    algebraicBettingWealth_eq_bettingWealthProcess] using hscore

/-- Ville control for the continuous prior mixture of executable masters.
The product-integrability assumptions are the explicit Fubini obligations for
mixing over an arbitrary measurable hypothesis space. -/
theorem continuousSleepingBettingPACBayesExceptionalEvent_mass_le_delta
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall theta j,
      EProcess mu F
        (bettingWealthProcess (X theta)
          (sleepingStrategy strategy j) (center theta)))
    (h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess X center strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess X center strategy) n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        continuousSleepingBettingMasterProcess X center strategy
          p.1 (n + 1) p.2) (prior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess X center strategy
            p.2 (n + 1) p.1) ((mu.restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        continuousSleepingBettingMasterProcess X center strategy
          p.2 n p.1) (mu.prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess X center strategy
            p.2 n p.1) ((mu.restrict s).prod prior)) :
    mu.real (continuousSleepingBettingPACBayesExceptionalEvent
      prior X center strategy delta) <= delta := by
  let M := continuousSleepingBettingMasterProcess X center strategy
  have hfixed : ∀ᵐ theta ∂prior, Supermartingale (M theta) F mu :=
    Filter.Eventually.of_forall fun theta =>
      (continuousSleepingBettingMasterProcess_eProcess
        hX_adapted hstrategy_adapted hcomponent theta).supermartingale
  have hnonneg : forall theta n omega, 0 <= M theta n omega := by
    intro theta n omega
    exact (continuousSleepingBettingMasterProcess_eProcess
      hX_adapted hstrategy_adapted hcomponent theta).nonneg n omega
  have hmix := continuousPriorMixture_supermartingale
    (prior := prior) (M := M) h_adapted_mix h_integrable_mix
      hM_int_next hM_int_next_restrict hM_int_current
      hM_int_current_restrict hfixed hnonneg
  have hcross := continuousPriorMixture_crossing_bound
    (prior := prior) (M := M) hdelta hmix.1 hmix.2 (fun theta omega => by
      simp [M, continuousSleepingBettingMasterProcess,
        bettingWealthProcess])
  simpa [continuousSleepingBettingPACBayesExceptionalEvent, M] using hcross

/-- Outside the single prior-mixture crossing event, every eligible posterior
and every positive reporting time satisfy a PAC-Bayes log-wealth inequality. -/
theorem continuousSleepingBettingPACBayes_allPosteriors_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hcomponent_nonneg : forall theta j n omega,
      0 <= bettingWealthProcess (X theta)
        (sleepingStrategy strategy j) (center theta) n omega)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        X center strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingBettingPACBayesExceptionalEvent
      prior X center strategy delta) :
    forall posterior : Measure Theta,
      IsProbabilityMeasure posterior -> posterior ≪ prior ->
      Integrable (llr posterior prior) posterior ->
      forall n : Nat, 0 < n ->
        Integrable
          (fun theta => Real.log
            (continuousSleepingBettingMasterProcess
              X center strategy theta n omega)) posterior ->
        (∫ theta, Real.log
            (continuousSleepingBettingMasterProcess
              X center strategy theta n omega) ∂posterior) <
          (InformationTheory.klDiv posterior prior).toReal +
            Real.log (1 / delta) := by
  intro posterior hposterior hposterior_prior hllr n hn hscore_int
  letI : IsProbabilityMeasure posterior := hposterior
  let M := continuousSleepingBettingMasterProcess X center strategy
  have hM_pos : forall theta, 0 < M theta n omega := fun theta =>
    continuousSleepingBettingMasterProcess_pos
      hcomponent_nonneg theta n omega
  have hmix_lt :
      continuousPriorMixtureProcess prior M n omega < 1 / delta := by
    apply lt_of_not_ge
    intro hcross
    apply homega
    exact ⟨n, hn, by simpa [M] using hcross⟩
  have hexp_eq :
      (fun theta => Real.exp (Real.log (M theta n omega))) =
        fun theta => M theta n omega := by
    funext theta
    exact Real.exp_log (hM_pos theta)
  have hexp_int : Integrable
      (fun theta => Real.exp (Real.log (M theta n omega))) prior := by
    rw [hexp_eq]
    simpa [M] using hprior_integrable n omega
  have hmix_pos : 0 < continuousPriorMixtureProcess prior M n omega := by
    have hpos := integral_exp_pos hexp_int
    rw [hexp_eq] at hpos
    simpa [continuousPriorMixtureProcess] using hpos
  have hdv := continuous_donsker_varadhan posterior prior
    hposterior_prior (fun theta => Real.log (M theta n omega))
      hexp_int (by simpa [M] using hscore_int) hllr
  rw [hexp_eq] at hdv
  have hdv' :
      (∫ theta, Real.log (M theta n omega) ∂posterior) <=
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (continuousPriorMixtureProcess prior M n omega) := by
    simpa [continuousPriorMixtureProcess] using hdv
  have hthreshold_pos : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hlog_lt :
      Real.log (continuousPriorMixtureProcess prior M n omega) <
        Real.log (1 / delta) :=
    Real.strictMonoOn_log hmix_pos hthreshold_pos hmix_lt
  have hfinal :
      (∫ theta, Real.log (M theta n omega) ∂posterior) <
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) :=
    lt_of_le_of_lt hdv'
      (add_lt_add_right hlog_lt
        (InformationTheory.klDiv posterior prior).toReal)
  change
    (∫ theta, Real.log (M theta n omega) ∂posterior) <
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta)
  exact hfinal

/-- Outside the common prior-mixture event, every active sleeping strategy
atom and every eligible posterior satisfy the exact empirical-Bernstein score
bound. The atom can be chosen after observing the path; its selection cost is
the explicit term `-log (dyadicExpertWeight j)`. -/
theorem continuousSleepingBettingPACBayes_selectedAtomScore_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hcomponent_nonneg : forall theta i k xi,
      0 <= bettingWealthProcess (X theta)
        (sleepingStrategy strategy i) (center theta) k xi)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        X center strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingBettingPACBayesExceptionalEvent
      prior X center strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n) (hn : 0 < n)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hresidual : forall theta k, k ∈ Finset.range n ->
      -1 <= X theta k omega - center theta)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingBettingMasterProcess
          X center strategy theta n omega)) posterior)
    (hscore_integrable : Integrable
      (fun theta => forwardEmpiricalBernsteinBettingScore
        (fun k xi => X theta k xi - center theta)
        (sleepingStrategy strategy j) n omega) posterior) :
    (∫ theta, forwardEmpiricalBernsteinBettingScore
        (fun k xi => X theta k xi - center theta)
        (sleepingStrategy strategy j) n omega ∂posterior) <
      (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) - Real.log (dyadicExpertWeight j) := by
  letI : IsProbabilityMeasure posterior := hposterior
  have hpac := continuousSleepingBettingPACBayes_allPosteriors_of_not_mem
    prior hdelta hcomponent_nonneg hprior_integrable homega posterior
      hposterior hposterior_prior hllr n hn hlog_integrable
  have hpoint :=
    forwardEmpiricalBernsteinBettingScore_le_log_continuousSleepingBettingMaster_sub_logWeight
      hcomponent_nonneg hjn omega hbet_nonneg hbet_lt_one hresidual
  have hrhs_integrable : Integrable
      (fun theta => Real.log
          (continuousSleepingBettingMasterProcess
            X center strategy theta n omega) -
        Real.log (dyadicExpertWeight j)) posterior :=
    hlog_integrable.sub (integrable_const _)
  have hintegral_le :=
    integral_mono hscore_integrable hrhs_integrable hpoint
  rw [integral_sub hlog_integrable (integrable_const _)] at hintegral_le
  simp only [integral_const, probReal_univ, one_smul] at hintegral_le
  linarith

/-! ## Constant conditional-risk inversion -/

/-- Accumulated predictable exposure of one sleeping strategy atom. -/
def sleepingStrategyExposure
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n, sleepingStrategy strategy j k omega

/-- Tilt-weighted observed loss for one hypothesis and selected atom. -/
def sleepingStrategyWeightedLossAt
    (loss : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    sleepingStrategy strategy j k omega * loss theta k omega

/-- Exact empirical-Bernstein residual penalty for one hypothesis and selected
atom. -/
def sleepingStrategyEmpiricalBernsteinPenaltyAt
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    forwardEmpiricalBernsteinPsi
        (sleepingStrategy strategy j k omega) *
      (risk theta - loss theta k omega) ^ 2

omit [MeasurableSpace Theta] in
/-- Running the lower-tail betting master on complemented losses turns its
residual into `risk - loss`. Its exact score is exposure times risk, minus the
observed weighted loss and empirical-Bernstein residual penalty. -/
theorem forwardEmpiricalBernsteinBettingScore_oneSub_eq
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega) :
    forwardEmpiricalBernsteinBettingScore
        (fun k xi => (1 - loss theta k xi) - (1 - risk theta))
        (sleepingStrategy strategy j) n omega =
      sleepingStrategyExposure strategy j n omega * risk theta -
        sleepingStrategyWeightedLossAt
          loss strategy theta j n omega -
        sleepingStrategyEmpiricalBernsteinPenaltyAt
          loss risk strategy theta j n omega := by
  unfold forwardEmpiricalBernsteinBettingScore sleepingStrategyExposure
    sleepingStrategyWeightedLossAt
    sleepingStrategyEmpiricalBernsteinPenaltyAt
  calc
    (∑ k ∈ Finset.range n,
        (sleepingStrategy strategy j k omega *
            ((1 - loss theta k omega) - (1 - risk theta)) -
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy strategy j k omega) *
            ((1 - loss theta k omega) - (1 - risk theta)) ^ 2)) =
      ∑ k ∈ Finset.range n,
        ((sleepingStrategy strategy j k omega * risk theta -
            sleepingStrategy strategy j k omega * loss theta k omega) -
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy strategy j k omega) *
            (risk theta - loss theta k omega) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = (∑ k ∈ Finset.range n,
          sleepingStrategy strategy j k omega) * risk theta -
        (∑ k ∈ Finset.range n,
          sleepingStrategy strategy j k omega * loss theta k omega) -
        ∑ k ∈ Finset.range n,
          forwardEmpiricalBernsteinPsi
              (sleepingStrategy strategy j k omega) *
            (risk theta - loss theta k omega) ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_mul]

/-- Posterior-average tilt-weighted observed loss for one selected sleeping
strategy atom. -/
def continuousSleepingPosteriorWeightedLoss
    (posterior : Measure Theta)
    (loss : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∫ theta, sleepingStrategyWeightedLossAt
    loss strategy theta j n omega ∂posterior

/-- Posterior-average exact residual penalty for one selected sleeping
strategy atom. This penalty contains the unknown risk parameter; the fully
observable envelope below replaces it by a deterministic pathwise cap. -/
def continuousSleepingPosteriorEmpiricalBernsteinPenalty
    (posterior : Measure Theta)
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega) : Real :=
  ∫ theta, sleepingStrategyEmpiricalBernsteinPenaltyAt
    loss risk strategy theta j n omega ∂posterior

/-- Exact selected-atom upper boundary for a posterior-average constant risk
parameter. It is normalized by the selected strategy's realized positive
exposure and charges both model-posterior KL and the selected atom's dyadic
code length. -/
def continuousSleepingBettingPACBayesOrdinaryRiskBoundary
    (prior posterior : Measure Theta)
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (delta : Real) (j n : Nat) (omega : Omega) : Real :=
  continuousSleepingPosteriorWeightedLoss
      posterior loss strategy j n omega /
      sleepingStrategyExposure strategy j n omega +
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) - Real.log (dyadicExpertWeight j) +
        continuousSleepingPosteriorEmpiricalBernsteinPenalty
          posterior loss risk strategy j n omega) /
      sleepingStrategyExposure strategy j n omega

/-- Exact posterior integral identity behind the ordinary-risk inversion. The
selected strategy is shared across hypotheses, so its exposure factors out of
the posterior integral. -/
theorem integral_forwardEmpiricalBernsteinBettingScore_oneSub
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega)
    (hrisk_integrable : Integrable risk posterior)
    (hloss_integrable : Integrable
      (fun theta => sleepingStrategyWeightedLossAt
        loss strategy theta j n omega) posterior)
    (hpenalty_integrable : Integrable
      (fun theta => sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega) posterior) :
    (∫ theta, forwardEmpiricalBernsteinBettingScore
        (fun k xi => (1 - loss theta k xi) - (1 - risk theta))
        (sleepingStrategy strategy j) n omega ∂posterior) =
      sleepingStrategyExposure strategy j n omega *
          (∫ theta, risk theta ∂posterior) -
        continuousSleepingPosteriorWeightedLoss
          posterior loss strategy j n omega -
        continuousSleepingPosteriorEmpiricalBernsteinPenalty
          posterior loss risk strategy j n omega := by
  let exposure := sleepingStrategyExposure strategy j n omega
  let observed : Theta -> Real := fun theta =>
    sleepingStrategyWeightedLossAt loss strategy theta j n omega
  let penalty : Theta -> Real := fun theta =>
    sleepingStrategyEmpiricalBernsteinPenaltyAt
      loss risk strategy theta j n omega
  have hexposureRisk : Integrable
      (fun theta => exposure * risk theta) posterior :=
    hrisk_integrable.const_mul exposure
  have hobserved : Integrable observed posterior := by
    simpa [observed] using hloss_integrable
  have hpenalty : Integrable penalty posterior := by
    simpa [penalty] using hpenalty_integrable
  have hinner :
      (∫ theta, exposure * risk theta - observed theta ∂posterior) =
        exposure * (∫ theta, risk theta ∂posterior) -
          ∫ theta, observed theta ∂posterior := by
    have h := integral_sub hexposureRisk hobserved
    simpa only [Pi.sub_apply, integral_const_mul] using h
  have houter :
      (∫ theta, (exposure * risk theta - observed theta) -
          penalty theta ∂posterior) =
        (∫ theta, exposure * risk theta - observed theta ∂posterior) -
          ∫ theta, penalty theta ∂posterior := by
    have h := integral_sub (hexposureRisk.sub hobserved) hpenalty
    simpa only [Pi.sub_apply] using h
  calc
    (∫ theta, forwardEmpiricalBernsteinBettingScore
        (fun k xi => (1 - loss theta k xi) - (1 - risk theta))
        (sleepingStrategy strategy j) n omega ∂posterior) =
      ∫ theta, (exposure * risk theta - observed theta) -
        penalty theta ∂posterior := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun theta => by
            simpa [exposure, observed, penalty] using
              forwardEmpiricalBernsteinBettingScore_oneSub_eq
                loss risk strategy theta j n omega
    _ = exposure * (∫ theta, risk theta ∂posterior) -
        (∫ theta, observed theta ∂posterior) -
        ∫ theta, penalty theta ∂posterior := by
      rw [houter, hinner]
    _ = sleepingStrategyExposure strategy j n omega *
          (∫ theta, risk theta ∂posterior) -
        continuousSleepingPosteriorWeightedLoss
          posterior loss strategy j n omega -
        continuousSleepingPosteriorEmpiricalBernsteinPenalty
          posterior loss risk strategy j n omega := by
      rfl

/-- On the common complemented-loss event, every eligible posterior and every
active catalog atom with positive exposure yield an upper bound on the
posterior average of the declared constant risk parameter.

To interpret `risk theta` as conditional risk, the component e-process premise
must be discharged from the corresponding conditional-mean model. Population,
future, stationary, or deployment-risk interpretations require additional
bridges and are not claimed here. -/
theorem
    continuousSleepingBettingPACBayes_ordinaryRisk_allPosteriors_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {loss : Theta -> Nat -> Omega -> Real} {risk : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hcomponent_nonneg : forall theta i k xi,
      0 <= bettingWealthProcess (fun t eta => 1 - loss theta t eta)
        (sleepingStrategy strategy i) (1 - risk theta) k xi)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        (fun theta k xi => 1 - loss theta k xi)
        (fun theta => 1 - risk theta) strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingBettingPACBayesExceptionalEvent
      prior (fun theta k xi => 1 - loss theta k xi)
        (fun theta => 1 - risk theta) strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n)
    (hexposure : 0 < sleepingStrategyExposure strategy j n omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hloss_unit : forall theta k, k ∈ Finset.range n ->
      loss theta k omega ∈ Set.Icc (0 : Real) 1)
    (hrisk_unit : forall theta, risk theta ∈ Set.Icc (0 : Real) 1)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingBettingMasterProcess
          (fun theta k xi => 1 - loss theta k xi)
          (fun theta => 1 - risk theta) strategy theta n omega)) posterior)
    (hrisk_integrable : Integrable risk posterior)
    (hloss_integrable : Integrable
      (fun theta => sleepingStrategyWeightedLossAt
        loss strategy theta j n omega) posterior)
    (hpenalty_integrable : Integrable
      (fun theta => sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega) posterior) :
    (∫ theta, risk theta ∂posterior) <
      continuousSleepingBettingPACBayesOrdinaryRiskBoundary
        prior posterior loss risk strategy delta j n omega := by
  letI : IsProbabilityMeasure posterior := hposterior
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hjn
  have hresidual : forall theta k, k ∈ Finset.range n ->
      -1 <= (1 - loss theta k omega) - (1 - risk theta) := by
    intro theta k hk
    have hloss := (hloss_unit theta k hk).2
    have hrisk := (hrisk_unit theta).1
    linarith
  have hscore_integrable : Integrable
      (fun theta => forwardEmpiricalBernsteinBettingScore
        (fun k xi => (1 - loss theta k xi) - (1 - risk theta))
        (sleepingStrategy strategy j) n omega) posterior := by
    have hrhs : Integrable
        (fun theta =>
          (sleepingStrategyExposure strategy j n omega * risk theta -
            sleepingStrategyWeightedLossAt
              loss strategy theta j n omega) -
          sleepingStrategyEmpiricalBernsteinPenaltyAt
            loss risk strategy theta j n omega) posterior :=
      ((hrisk_integrable.const_mul
          (sleepingStrategyExposure strategy j n omega)).sub
        hloss_integrable).sub hpenalty_integrable
    refine hrhs.congr (Filter.Eventually.of_forall fun theta => ?_)
    symm
    exact forwardEmpiricalBernsteinBettingScore_oneSub_eq
      loss risk strategy theta j n omega
  have hscore :=
    continuousSleepingBettingPACBayes_selectedAtomScore_of_not_mem
      prior hdelta hcomponent_nonneg hprior_integrable homega posterior
        hposterior hposterior_prior hllr hjn hn hbet_nonneg hbet_lt_one
        hresidual hlog_integrable hscore_integrable
  rw [integral_forwardEmpiricalBernsteinBettingScore_oneSub
    posterior loss risk strategy j n omega hrisk_integrable
      hloss_integrable hpenalty_integrable] at hscore
  unfold continuousSleepingBettingPACBayesOrdinaryRiskBoundary
  rw [← add_div]
  apply (lt_div_iff₀ hexposure).2
  linarith

/-- Fully observable selected-atom ordinary-risk envelope. The exact residual
penalty is conservatively bounded by `sum psi(lambda_k)` using only that losses
and the declared constant risk parameter lie in `[0,1]`. -/
def continuousSleepingBettingPACBayesObservableOrdinaryRiskBoundary
    (prior posterior : Measure Theta)
    (loss : Theta -> Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (delta : Real) (j n : Nat) (omega : Omega) : Real :=
  continuousSleepingPosteriorWeightedLoss
      posterior loss strategy j n omega /
      sleepingStrategyExposure strategy j n omega +
    ((InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) - Real.log (dyadicExpertWeight j) +
        ∑ k ∈ Finset.range n,
          forwardEmpiricalBernsteinPsi
            (sleepingStrategy strategy j k omega)) /
      sleepingStrategyExposure strategy j n omega

omit [MeasurableSpace Theta] in
/-- The exact risk-dependent residual penalty of one hypothesis is bounded by
the observable sum of cumulants for bounded losses and risks. -/
theorem sleepingStrategyEmpiricalBernsteinPenaltyAt_le_sumPsi
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (theta : Theta) (j n : Nat) (omega : Omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hloss_unit : forall k, k ∈ Finset.range n ->
      loss theta k omega ∈ Set.Icc (0 : Real) 1)
    (hrisk_unit : risk theta ∈ Set.Icc (0 : Real) 1) :
    sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega <=
      ∑ k ∈ Finset.range n,
        forwardEmpiricalBernsteinPsi
          (sleepingStrategy strategy j k omega) := by
  unfold sleepingStrategyEmpiricalBernsteinPenaltyAt
  apply Finset.sum_le_sum
  intro k hk
  have hpsi : 0 <= forwardEmpiricalBernsteinPsi
      (sleepingStrategy strategy j k omega) :=
    forwardEmpiricalBernsteinPsi_nonneg
      (hbet_nonneg k hk) (hbet_lt_one k hk)
  have hresidual_lower :
      -1 <= risk theta - loss theta k omega := by
    linarith [(hrisk_unit).1, (hloss_unit k hk).2]
  have hresidual_upper :
      risk theta - loss theta k omega <= 1 := by
    linarith [(hrisk_unit).2, (hloss_unit k hk).1]
  have hsquare : (risk theta - loss theta k omega) ^ 2 <= 1 := by
    have hproduct :
        0 <= (1 - (risk theta - loss theta k omega)) *
          (1 + (risk theta - loss theta k omega)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  simpa using mul_le_mul_of_nonneg_left hsquare hpsi

/-- The posterior-average exact residual penalty is bounded by the same
observable cumulant sum because the posterior has total mass one. -/
theorem continuousSleepingPosteriorEmpiricalBernsteinPenalty_le_sumPsi
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (loss : Theta -> Nat -> Omega -> Real) (risk : Theta -> Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (j n : Nat) (omega : Omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hloss_unit : forall theta k, k ∈ Finset.range n ->
      loss theta k omega ∈ Set.Icc (0 : Real) 1)
    (hrisk_unit : forall theta, risk theta ∈ Set.Icc (0 : Real) 1)
    (hpenalty_integrable : Integrable
      (fun theta => sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega) posterior) :
    continuousSleepingPosteriorEmpiricalBernsteinPenalty
        posterior loss risk strategy j n omega <=
      ∑ k ∈ Finset.range n,
        forwardEmpiricalBernsteinPsi
          (sleepingStrategy strategy j k omega) := by
  unfold continuousSleepingPosteriorEmpiricalBernsteinPenalty
  calc
    (∫ theta, sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega ∂posterior) <=
      ∫ _theta, (∑ k ∈ Finset.range n,
        forwardEmpiricalBernsteinPsi
          (sleepingStrategy strategy j k omega)) ∂posterior :=
      integral_mono hpenalty_integrable (integrable_const _)
        (fun theta =>
          sleepingStrategyEmpiricalBernsteinPenaltyAt_le_sumPsi
            loss risk strategy theta j n omega hbet_nonneg hbet_lt_one
              (hloss_unit theta) (hrisk_unit theta))
    _ = ∑ k ∈ Finset.range n,
        forwardEmpiricalBernsteinPsi
          (sleepingStrategy strategy j k omega) := by
      simp only [integral_const, probReal_univ, one_smul]

/-- Observable ordinary-risk endpoint: outside the common complemented-loss
event, posterior and sleeping atom may be selected from the observed path, and
the resulting upper boundary contains only observed losses, declared bets,
KL, confidence, and dyadic atom cost. -/
theorem
    continuousSleepingBettingPACBayes_observableOrdinaryRisk_allPosteriors_of_not_mem
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {loss : Theta -> Nat -> Omega -> Real} {risk : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hcomponent_nonneg : forall theta i k xi,
      0 <= bettingWealthProcess (fun t eta => 1 - loss theta t eta)
        (sleepingStrategy strategy i) (1 - risk theta) k xi)
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        (fun theta k xi => 1 - loss theta k xi)
        (fun theta => 1 - risk theta) strategy theta n omega) prior)
    {omega : Omega}
    (homega : omega ∉ continuousSleepingBettingPACBayesExceptionalEvent
      prior (fun theta k xi => 1 - loss theta k xi)
        (fun theta => 1 - risk theta) strategy delta)
    (posterior : Measure Theta)
    (hposterior : IsProbabilityMeasure posterior)
    (hposterior_prior : posterior ≪ prior)
    (hllr : Integrable (llr posterior prior) posterior)
    {j n : Nat} (hjn : j < n)
    (hexposure : 0 < sleepingStrategyExposure strategy j n omega)
    (hbet_nonneg : forall k, k ∈ Finset.range n ->
      0 <= sleepingStrategy strategy j k omega)
    (hbet_lt_one : forall k, k ∈ Finset.range n ->
      sleepingStrategy strategy j k omega < 1)
    (hloss_unit : forall theta k, k ∈ Finset.range n ->
      loss theta k omega ∈ Set.Icc (0 : Real) 1)
    (hrisk_unit : forall theta, risk theta ∈ Set.Icc (0 : Real) 1)
    (hlog_integrable : Integrable
      (fun theta => Real.log
        (continuousSleepingBettingMasterProcess
          (fun theta k xi => 1 - loss theta k xi)
          (fun theta => 1 - risk theta) strategy theta n omega)) posterior)
    (hrisk_integrable : Integrable risk posterior)
    (hloss_integrable : Integrable
      (fun theta => sleepingStrategyWeightedLossAt
        loss strategy theta j n omega) posterior)
    (hpenalty_integrable : Integrable
      (fun theta => sleepingStrategyEmpiricalBernsteinPenaltyAt
        loss risk strategy theta j n omega) posterior) :
    (∫ theta, risk theta ∂posterior) <
      continuousSleepingBettingPACBayesObservableOrdinaryRiskBoundary
        prior posterior loss strategy delta j n omega := by
  letI : IsProbabilityMeasure posterior := hposterior
  have hexact :=
    continuousSleepingBettingPACBayes_ordinaryRisk_allPosteriors_of_not_mem
      prior hdelta hcomponent_nonneg hprior_integrable homega posterior
        hposterior hposterior_prior hllr hjn hexposure hbet_nonneg
        hbet_lt_one hloss_unit hrisk_unit hlog_integrable hrisk_integrable
        hloss_integrable hpenalty_integrable
  have hpenalty :=
    continuousSleepingPosteriorEmpiricalBernsteinPenalty_le_sumPsi
      posterior loss risk strategy j n omega hbet_nonneg hbet_lt_one
        hloss_unit hrisk_unit hpenalty_integrable
  unfold continuousSleepingBettingPACBayesOrdinaryRiskBoundary at hexact
  unfold continuousSleepingBettingPACBayesObservableOrdinaryRiskBoundary
  have hwidth :
      ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) - Real.log (dyadicExpertWeight j) +
          continuousSleepingPosteriorEmpiricalBernsteinPenalty
            posterior loss risk strategy j n omega) /
          sleepingStrategyExposure strategy j n omega <=
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) - Real.log (dyadicExpertWeight j) +
          ∑ k ∈ Finset.range n,
            forwardEmpiricalBernsteinPsi
              (sleepingStrategy strategy j k omega)) /
          sleepingStrategyExposure strategy j n omega :=
    (div_le_div_iff_of_pos_right hexposure).2 (by linarith)
  exact lt_of_lt_of_le hexact (by linarith)

/-- One event of outer mass at least `1 - delta` carries the executable
sleeping-master log-wealth bound simultaneously over positive reporting times
and all eligible posteriors. The posterior may be selected from the realized
path. -/
theorem exists_continuousSleepingBettingPACBayes_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X : Theta -> Nat -> Omega -> Real} {center : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F (X theta))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall theta j,
      EProcess mu F
        (bettingWealthProcess (X theta)
          (sleepingStrategy strategy j) (center theta)))
    (h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess X center strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess X center strategy) n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        continuousSleepingBettingMasterProcess X center strategy
          p.1 (n + 1) p.2) (prior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess X center strategy
            p.2 (n + 1) p.1) ((mu.restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        continuousSleepingBettingMasterProcess X center strategy
          p.2 n p.1) (mu.prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess X center strategy
            p.2 n p.1) ((mu.restrict s).prod prior))
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        X center strategy theta n omega) prior) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        forall omega, omega ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 0 < n ->
              Integrable
                (fun theta => Real.log
                  (continuousSleepingBettingMasterProcess
                    X center strategy theta n omega)) posterior ->
              (∫ theta, Real.log
                  (continuousSleepingBettingMasterProcess
                    X center strategy theta n omega) ∂posterior) <
                (InformationTheory.klDiv posterior prior).toReal +
                  Real.log (1 / delta) := by
  let badEvent := continuousSleepingBettingPACBayesExceptionalEvent
    prior X center strategy delta
  have hmass : mu.real badEvent <= delta := by
    simpa [badEvent] using
      continuousSleepingBettingPACBayesExceptionalEvent_mass_le_delta
        prior hdelta hX_adapted hstrategy_adapted hcomponent
        h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
        hM_int_current hM_int_current_restrict
  refine ⟨badEventᶜ, by simpa, ?_⟩
  intro omega homega posterior hposterior hposterior_prior hllr n hn
    hscore_int
  have hcomponent_nonneg : forall theta j k xi,
      0 <= bettingWealthProcess (X theta)
        (sleepingStrategy strategy j) (center theta) k xi := by
    intro theta j k xi
    exact (hcomponent theta j).nonneg k xi
  apply continuousSleepingBettingPACBayes_allPosteriors_of_not_mem
    prior hdelta hcomponent_nonneg hprior_integrable
      (omega := omega) (by simpa [badEvent] using homega)
      posterior hposterior hposterior_prior hllr n hn hscore_int

/-- One event of outer mass at least `1 - delta` carries the fully observable
ordinary-risk envelope simultaneously over positive reporting times, all
eligible continuous posteriors, and every active positive-exposure atom in the
predeclared countable predictable-strategy catalog.

The process is run on complemented losses, so its residual is `risk - loss`.
The statistical premise remains explicit: every declared component wealth
must be an e-process for the supplied constant center. This theorem therefore
certifies posterior-average constant conditional risk only when that premise is
discharged from the user's conditional-mean model. -/
theorem
    exists_continuousSleepingBettingPACBayes_observableOrdinaryRisk_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {loss : Theta -> Nat -> Omega -> Real} {risk : Theta -> Real}
    {strategy : Nat -> Nat -> Omega -> Real} {delta : Real}
    (hdelta : 0 < delta)
    (hX_adapted : forall theta, IncrementAdapted F
      (fun k omega => 1 - loss theta k omega))
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall theta j,
      EProcess mu F
        (bettingWealthProcess (fun k omega => 1 - loss theta k omega)
          (sleepingStrategy strategy j) (1 - risk theta)))
    (h_adapted_mix : StronglyAdapted F
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess
          (fun theta k omega => 1 - loss theta k omega)
          (fun theta => 1 - risk theta) strategy)))
    (h_integrable_mix : forall n, Integrable
      (continuousPriorMixtureProcess prior
        (continuousSleepingBettingMasterProcess
          (fun theta k omega => 1 - loss theta k omega)
          (fun theta => 1 - risk theta) strategy) n) mu)
    (hM_int_next : forall n, Integrable
      (fun p : Theta × Omega =>
        continuousSleepingBettingMasterProcess
          (fun theta k omega => 1 - loss theta k omega)
          (fun theta => 1 - risk theta) strategy
          p.1 (n + 1) p.2) (prior.prod mu))
    (hM_int_next_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess
            (fun theta k omega => 1 - loss theta k omega)
            (fun theta => 1 - risk theta) strategy
            p.2 (n + 1) p.1) ((mu.restrict s).prod prior))
    (hM_int_current : forall n, Integrable
      (fun p : Omega × Theta =>
        continuousSleepingBettingMasterProcess
          (fun theta k omega => 1 - loss theta k omega)
          (fun theta => 1 - risk theta) strategy
          p.2 n p.1) (mu.prod prior))
    (hM_int_current_restrict : forall n, forall {s : Set Omega},
      MeasurableSet s -> mu s < ⊤ -> Integrable
        (fun p : Omega × Theta =>
          continuousSleepingBettingMasterProcess
            (fun theta k omega => 1 - loss theta k omega)
            (fun theta => 1 - risk theta) strategy
            p.2 n p.1) ((mu.restrict s).prod prior))
    (hprior_integrable : forall n omega, Integrable
      (fun theta => continuousSleepingBettingMasterProcess
        (fun theta k xi => 1 - loss theta k xi)
        (fun theta => 1 - risk theta) strategy theta n omega) prior) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ <= delta ∧
        forall omega, omega ∈ goodEvent ->
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall j n : Nat, j < n ->
              0 < sleepingStrategyExposure strategy j n omega ->
              (forall k, k ∈ Finset.range n ->
                0 <= sleepingStrategy strategy j k omega) ->
              (forall k, k ∈ Finset.range n ->
                sleepingStrategy strategy j k omega < 1) ->
              (forall theta k, k ∈ Finset.range n ->
                loss theta k omega ∈ Set.Icc (0 : Real) 1) ->
              (forall theta, risk theta ∈ Set.Icc (0 : Real) 1) ->
              Integrable
                (fun theta => Real.log
                  (continuousSleepingBettingMasterProcess
                    (fun theta k xi => 1 - loss theta k xi)
                    (fun theta => 1 - risk theta) strategy
                    theta n omega)) posterior ->
              Integrable risk posterior ->
              Integrable
                (fun theta => sleepingStrategyWeightedLossAt
                  loss strategy theta j n omega) posterior ->
              Integrable
                (fun theta => sleepingStrategyEmpiricalBernsteinPenaltyAt
                  loss risk strategy theta j n omega) posterior ->
              (∫ theta, risk theta ∂posterior) <
                continuousSleepingBettingPACBayesObservableOrdinaryRiskBoundary
                  prior posterior loss strategy delta j n omega := by
  let badEvent := continuousSleepingBettingPACBayesExceptionalEvent
    prior (fun theta k omega => 1 - loss theta k omega)
      (fun theta => 1 - risk theta) strategy delta
  have hmass : mu.real badEvent <= delta := by
    simpa [badEvent] using
      continuousSleepingBettingPACBayesExceptionalEvent_mass_le_delta
        prior hdelta hX_adapted hstrategy_adapted hcomponent
        h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
        hM_int_current hM_int_current_restrict
  refine ⟨badEventᶜ, by simpa, ?_⟩
  intro omega homega posterior hposterior hposterior_prior hllr j n hjn
    hexposure hbet_nonneg hbet_lt_one hloss_unit hrisk_unit
    hlog_integrable hrisk_integrable hloss_integrable hpenalty_integrable
  have hcomponent_nonneg : forall theta i k xi,
      0 <= bettingWealthProcess (fun t eta => 1 - loss theta t eta)
        (sleepingStrategy strategy i) (1 - risk theta) k xi := by
    intro theta i k xi
    exact (hcomponent theta i).nonneg k xi
  apply
    continuousSleepingBettingPACBayes_observableOrdinaryRisk_allPosteriors_of_not_mem
      prior hdelta hcomponent_nonneg hprior_integrable
        (omega := omega) (by simpa [badEvent] using homega)
        posterior hposterior hposterior_prior hllr hjn hexposure
        hbet_nonneg hbet_lt_one hloss_unit hrisk_unit hlog_integrable
        hrisk_integrable hloss_integrable hpenalty_integrable

end

end FormalSLT.PACBayes.ContinuousSleepingBettingPACBayes
