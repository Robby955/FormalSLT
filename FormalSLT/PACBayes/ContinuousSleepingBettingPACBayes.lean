/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingMixture
import FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Continuous PAC-Bayes bridge for executable sleeping betting masters

This module connects the exact finite-prefix implementation of a countable
sleeping-expert betting master to the continuous-hypothesis PAC-Bayes layer.
For every hypothesis, the master bet is computed from the active finite prefix
and the closed-form dyadic sleeping tail. A probability prior then mixes those
strictly positive master wealth processes over an arbitrary measurable
hypothesis space.

One common event controls every reporting time and every eligible posterior.
Outside that event, the posterior-average log wealth is bounded by the
posterior KL divergence plus `log (1 / delta)`. The posterior may be selected
after observing the path; no measurability of that pointwise selector is
needed.

This is the process-level PAC-Bayes bridge for the executable master. It does
not yet turn log wealth into an ordinary-risk inequality; that requires a
separate lower bound on log wealth for the chosen betting catalog.
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
and every reporting time satisfy a PAC-Bayes log-wealth inequality. -/
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

/-- One event of outer mass at least `1 - delta` carries the executable
sleeping-master log-wealth bound simultaneously over time and all eligible
posteriors. The posterior may be selected from the realized path. -/
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

end

end FormalSLT.PACBayes.ContinuousSleepingBettingPACBayes
