/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.MixtureCS
import FormalSLT.PACBayes.ContinuousChangeOfMeasure
import Mathlib.Tactic

/-!
# Time-uniform continuous PAC-Bayes bridge

This module proves the process-level bridge from a measurable hypothesis space
to a time-uniform PAC-Bayes inequality.  For an arbitrary probability prior on
the hypothesis space, it integrates a family of nonnegative supermartingales,
proves that the prior mixture is again a supermartingale using explicit product
and restricted-product integrability hypotheses, applies countable-time Ville,
and then performs the continuous Donsker--Varadhan inversion for an absolutely
continuous posterior with integrable log-likelihood ratio.

The main theorem, `timeUniformContinuousPACBayes_bound`, is deliberately a
process theorem.  Its score process is abstract, and the hypothesis that each
per-hypothesis exponential score process is a supermartingale remains visible.
No loss model, i.i.d. sampling theorem, or Gaussian measure/KL identification is
claimed here.  There are no `sorry`, `admit`, custom axioms, or custom constants.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open scoped ENNReal

namespace FormalSLT.PACBayes.TimeUniformContinuous

noncomputable section

variable {Θ Ω : Type*} [MeasurableSpace Θ] {mΩ : MeasurableSpace Ω}

/-- Prior integral of a parameterized real-valued process. -/
def continuousPriorMixtureProcess
    (prior : Measure Θ) (M : Θ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ θ, M θ n ω ∂prior

/--
One conditional-expectation step for an arbitrary continuous prior mixture.

The product-integrability hypotheses are the exact Fubini obligations needed
to test the inequality on filtration-measurable sets.  In particular, the
conclusion is not obtained by assuming that conditional expectation commutes
with the prior integral.
-/
theorem continuousPriorMixture_condExp_step_of_fixed_hypothesis_steps
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : Measure Θ} [IsProbabilityMeasure prior]
    {M : Θ → ℕ → Ω → ℝ}
    (h_adapted_mix : StronglyAdapted ℱ (continuousPriorMixtureProcess prior M))
    (h_integrable_mix :
      ∀ n, Integrable (continuousPriorMixtureProcess prior M n) μ)
    (hM_int_next :
      ∀ n, Integrable (fun p : Θ × Ω => M p.1 (n + 1) p.2) (prior.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 (n + 1) p.1)
          ((μ.restrict s).prod prior))
    (hM_int_current :
      ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod prior))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 n p.1)
          ((μ.restrict s).prod prior))
    (hfixed_step :
      ∀ n, ∀ᵐ θ ∂prior,
        μ[fun ω => M θ (n + 1) ω | ℱ n] ≤ᵐ[μ] fun ω => M θ n ω) :
    ∀ n,
      μ[continuousPriorMixtureProcess prior M (n + 1) | ℱ n]
        ≤ᵐ[μ] continuousPriorMixtureProcess prior M n := by
  intro n
  refine ae_le_of_forall_subalgebra_setIntegral_le (ℱ.le n)
    integrable_condExp (h_integrable_mix n) stronglyMeasurable_condExp
    (h_adapted_mix n) ?_
  intro s hs hμs
  have hs₀ : MeasurableSet s := ℱ.le n s hs
  have hnext_restrict := hM_int_next_restrict n hs₀ hμs
  have hcurrent_restrict := hM_int_current_restrict n hs₀ hμs
  have hnext_fiber : ∀ᵐ θ ∂prior, Integrable (fun ω => M θ (n + 1) ω) μ := by
    simpa using (hM_int_next n).prod_right_ae
  have hcurrent_fiber : ∀ᵐ θ ∂prior, Integrable (fun ω => M θ n ω) μ := by
    simpa using (hM_int_current n).prod_left_ae
  calc
    ∫ ω in s,
        (μ[continuousPriorMixtureProcess prior M (n + 1) | ℱ n]) ω ∂μ
        = ∫ ω in s, continuousPriorMixtureProcess prior M (n + 1) ω ∂μ := by
            exact setIntegral_condExp (ℱ.le n) (h_integrable_mix (n + 1)) hs
    _ = ∫ θ, ∫ ω in s, M θ (n + 1) ω ∂μ ∂prior := by
          simpa [continuousPriorMixtureProcess, Function.uncurry] using
            (integral_integral_swap (μ := μ.restrict s) (ν := prior)
              (f := fun ω θ => M θ (n + 1) ω) hnext_restrict)
    _ ≤ ∫ θ, ∫ ω in s, M θ n ω ∂μ ∂prior := by
          refine integral_mono_ae hnext_restrict.integral_prod_right
            hcurrent_restrict.integral_prod_right ?_
          filter_upwards [hfixed_step n, hnext_fiber, hcurrent_fiber] with
            θ hstep hnext_int hcurrent_int
          calc
            ∫ ω in s, M θ (n + 1) ω ∂μ
                = ∫ ω in s, (μ[fun ω => M θ (n + 1) ω | ℱ n]) ω ∂μ := by
                    exact (setIntegral_condExp (ℱ.le n) hnext_int hs).symm
            _ ≤ ∫ ω in s, M θ n ω ∂μ := by
                    exact setIntegral_mono_ae integrable_condExp.integrableOn
                      hcurrent_int.integrableOn hstep
    _ = ∫ ω in s, continuousPriorMixtureProcess prior M n ω ∂μ := by
          simpa [continuousPriorMixtureProcess, Function.uncurry] using
            (integral_integral_swap (μ := μ.restrict s) (ν := prior)
              (f := fun ω θ => M θ n ω) hcurrent_restrict).symm

/--
A probability-prior integral of a prior-almost-everywhere supermartingale
family with everywhere-nonnegative values is a nonnegative supermartingale.

All joint and restricted-product integrability assumptions needed by Fubini are
explicit.  The theorem therefore supplies the missing continuous-hypothesis
analogue of the finite prior sum in `TimeUniformPACBayes`.
-/
theorem continuousPriorMixture_supermartingale
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : Measure Θ} [IsProbabilityMeasure prior]
    {M : Θ → ℕ → Ω → ℝ}
    (h_adapted_mix : StronglyAdapted ℱ (continuousPriorMixtureProcess prior M))
    (h_integrable_mix :
      ∀ n, Integrable (continuousPriorMixtureProcess prior M n) μ)
    (hM_int_next :
      ∀ n, Integrable (fun p : Θ × Ω => M p.1 (n + 1) p.2) (prior.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 (n + 1) p.1)
          ((μ.restrict s).prod prior))
    (hM_int_current :
      ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod prior))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 n p.1)
          ((μ.restrict s).prod prior))
    (hfixed : ∀ᵐ θ ∂prior, Supermartingale (M θ) ℱ μ)
    (hnonneg : ∀ θ n ω, 0 ≤ M θ n ω) :
    Supermartingale (continuousPriorMixtureProcess prior M) ℱ μ
      ∧ ∀ n ω, 0 ≤ continuousPriorMixtureProcess prior M n ω := by
  have hfixed_step :
      ∀ n, ∀ᵐ θ ∂prior,
        μ[fun ω => M θ (n + 1) ω | ℱ n] ≤ᵐ[μ] fun ω => M θ n ω := by
    intro n
    filter_upwards [hfixed] with θ hθ
    exact hθ.condExp_ae_le (Nat.le_succ n)
  have h_cond_step :
      ∀ n,
        μ[continuousPriorMixtureProcess prior M (n + 1) | ℱ n]
          ≤ᵐ[μ] continuousPriorMixtureProcess prior M n :=
    continuousPriorMixture_condExp_step_of_fixed_hypothesis_steps
      h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
      hM_int_current hM_int_current_restrict hfixed_step
  refine ⟨supermartingale_nat h_adapted_mix h_integrable_mix h_cond_step, ?_⟩
  intro n ω
  exact integral_nonneg fun θ => hnonneg θ n ω

/--
One reverse conditional-expectation step for an arbitrary continuous prior
mixture.

This is the submartingale analogue of
`continuousPriorMixture_condExp_step_of_fixed_hypothesis_steps`.  The product
integrability hypotheses expose the Fubini obligations rather than assuming
that conditional expectation commutes with the prior integral.
-/
theorem continuousPriorMixture_condExp_step_ge_of_fixed_hypothesis_steps
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : Measure Θ} [IsProbabilityMeasure prior]
    {M : Θ → ℕ → Ω → ℝ}
    (h_adapted_mix : StronglyAdapted ℱ (continuousPriorMixtureProcess prior M))
    (h_integrable_mix :
      ∀ n, Integrable (continuousPriorMixtureProcess prior M n) μ)
    (hM_int_next :
      ∀ n, Integrable (fun p : Θ × Ω => M p.1 (n + 1) p.2) (prior.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 (n + 1) p.1)
          ((μ.restrict s).prod prior))
    (hM_int_current :
      ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod prior))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 n p.1)
          ((μ.restrict s).prod prior))
    (hfixed_step :
      ∀ n, ∀ᵐ θ ∂prior,
        (fun ω => M θ n ω) ≤ᵐ[μ] μ[fun ω => M θ (n + 1) ω | ℱ n]) :
    ∀ n,
      continuousPriorMixtureProcess prior M n
        ≤ᵐ[μ] μ[continuousPriorMixtureProcess prior M (n + 1) | ℱ n] := by
  intro n
  refine ae_le_of_forall_subalgebra_setIntegral_le (ℱ.le n)
    (h_integrable_mix n) integrable_condExp
    (h_adapted_mix n) stronglyMeasurable_condExp ?_
  intro s hs hμs
  have hs₀ : MeasurableSet s := ℱ.le n s hs
  have hnext_restrict := hM_int_next_restrict n hs₀ hμs
  have hcurrent_restrict := hM_int_current_restrict n hs₀ hμs
  have hnext_fiber : ∀ᵐ θ ∂prior, Integrable (fun ω => M θ (n + 1) ω) μ := by
    simpa using (hM_int_next n).prod_right_ae
  have hcurrent_fiber : ∀ᵐ θ ∂prior, Integrable (fun ω => M θ n ω) μ := by
    simpa using (hM_int_current n).prod_left_ae
  calc
    ∫ ω in s, continuousPriorMixtureProcess prior M n ω ∂μ
        = ∫ θ, ∫ ω in s, M θ n ω ∂μ ∂prior := by
          simpa [continuousPriorMixtureProcess, Function.uncurry] using
            (integral_integral_swap (μ := μ.restrict s) (ν := prior)
              (f := fun ω θ => M θ n ω) hcurrent_restrict)
    _ ≤ ∫ θ, ∫ ω in s, M θ (n + 1) ω ∂μ ∂prior := by
          refine integral_mono_ae hcurrent_restrict.integral_prod_right
            hnext_restrict.integral_prod_right ?_
          filter_upwards [hfixed_step n, hcurrent_fiber, hnext_fiber] with
            θ hstep hcurrent_int hnext_int
          calc
            ∫ ω in s, M θ n ω ∂μ
                ≤ ∫ ω in s, (μ[fun ω => M θ (n + 1) ω | ℱ n]) ω ∂μ := by
                    exact setIntegral_mono_ae hcurrent_int.integrableOn
                      integrable_condExp.integrableOn hstep
            _ = ∫ ω in s, M θ (n + 1) ω ∂μ := by
                    exact setIntegral_condExp (ℱ.le n) hnext_int hs
    _ = ∫ ω in s, continuousPriorMixtureProcess prior M (n + 1) ω ∂μ := by
          simpa [continuousPriorMixtureProcess, Function.uncurry] using
            (integral_integral_swap (μ := μ.restrict s) (ν := prior)
              (f := fun ω θ => M θ (n + 1) ω) hnext_restrict).symm
    _ = ∫ ω in s,
          (μ[continuousPriorMixtureProcess prior M (n + 1) | ℱ n]) ω ∂μ := by
            exact (setIntegral_condExp (ℱ.le n) (h_integrable_mix (n + 1)) hs).symm

/--
A probability-prior integral of a prior-almost-everywhere submartingale
family is a submartingale, under the explicit product-integrability
obligations needed by Fubini.
-/
theorem continuousPriorMixture_submartingale
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : Measure Θ} [IsProbabilityMeasure prior]
    {M : Θ → ℕ → Ω → ℝ}
    (h_adapted_mix : StronglyAdapted ℱ (continuousPriorMixtureProcess prior M))
    (h_integrable_mix :
      ∀ n, Integrable (continuousPriorMixtureProcess prior M n) μ)
    (hM_int_next :
      ∀ n, Integrable (fun p : Θ × Ω => M p.1 (n + 1) p.2) (prior.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 (n + 1) p.1)
          ((μ.restrict s).prod prior))
    (hM_int_current :
      ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod prior))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => M p.2 n p.1)
          ((μ.restrict s).prod prior))
    (hfixed : ∀ᵐ θ ∂prior, Submartingale (M θ) ℱ μ) :
    Submartingale (continuousPriorMixtureProcess prior M) ℱ μ := by
  have hfixed_step :
      ∀ n, ∀ᵐ θ ∂prior,
        (fun ω => M θ n ω) ≤ᵐ[μ] μ[fun ω => M θ (n + 1) ω | ℱ n] := by
    intro n
    filter_upwards [hfixed] with θ hθ
    exact hθ.2.1 n (n + 1) (Nat.le_succ n)
  exact submartingale_nat h_adapted_mix h_integrable_mix
    (continuousPriorMixture_condExp_step_ge_of_fixed_hypothesis_steps
      h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
      hM_int_current hM_int_current_restrict hfixed_step)

/--
Countable-time Ville control for a continuous prior mixture that starts at one.
-/
theorem continuousPriorMixture_crossing_bound
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : Measure Θ} [IsProbabilityMeasure prior]
    {M : Θ → ℕ → Ω → ℝ} {delta : ℝ}
    (hδ : 0 < delta)
    (hsup : Supermartingale (continuousPriorMixtureProcess prior M) ℱ μ)
    (hnonneg : ∀ n ω, 0 ≤ continuousPriorMixtureProcess prior M n ω)
    (hzero : ∀ θ ω, M θ 0 ω = 1) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ continuousPriorMixtureProcess prior M n ω} ≤ delta := by
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ) (M := continuousPriorMixtureProcess prior M)
      hsup hnonneg ha
  have hM0 : ∫ ω, continuousPriorMixtureProcess prior M 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => continuousPriorMixtureProcess prior M 0 ω) =ᵐ[μ]
          fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by
        simp [continuousPriorMixtureProcess, hzero]
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent
        (continuousPriorMixtureProcess prior M) (1 / delta)) ≤ delta := by
    calc
      μ.real (atTopCrossingEvent
          (continuousPriorMixtureProcess prior M) (1 / delta))
          = delta * ((1 / delta) *
              μ.real (atTopCrossingEvent
                (continuousPriorMixtureProcess prior M) (1 / delta))) := by
              field_simp [hδ.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ continuousPriorMixtureProcess prior M n ω}
        ⊆ atTopCrossingEvent (continuousPriorMixtureProcess prior M) (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn, hcross⟩
    exact ⟨n, hcross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/-- Prior mixture of exponentiated score processes. -/
def continuousExponentialMixtureProcess
    (prior : Measure Θ) (score : Θ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  continuousPriorMixtureProcess prior
    (fun θ k ξ => Real.exp (score θ k ξ)) n ω

/-- Posterior boundary-failure event for the continuous process-level theorem. -/
def timeUniformContinuousPACBayesUpperFailure
    (prior posterior : Measure Θ) (score : Θ → ℕ → Ω → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    (InformationTheory.klDiv posterior prior).toReal + Real.log (1 / delta)
      ≤ ∫ θ, score θ n ω ∂posterior}

/--
Continuous Donsker--Varadhan inversion: a posterior boundary failure forces the
prior exponential mixture to cross `1 / delta` at the same time.
-/
theorem timeUniformContinuousPACBayesUpperFailure_subset_crossing
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hρπ : posterior ≪ prior)
    (score : Θ → ℕ → Ω → ℝ) {delta : ℝ}
    (hδ : 0 < delta)
    (hexp_int :
      ∀ n ω, Integrable (fun θ => Real.exp (score θ n ω)) prior)
    (hscore_int :
      ∀ n ω, Integrable (fun θ => score θ n ω) posterior)
    (hllr : Integrable (llr posterior prior) posterior) :
    timeUniformContinuousPACBayesUpperFailure prior posterior score delta
      ⊆ {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ continuousExponentialMixtureProcess prior score n ω} := by
  intro ω hω
  rcases hω with ⟨n, hn_pos, hfail⟩
  refine ⟨n, hn_pos, ?_⟩
  have hmix_pos : 0 < continuousExponentialMixtureProcess prior score n ω := by
    simpa [continuousExponentialMixtureProcess, continuousPriorMixtureProcess] using
      (integral_exp_pos (hexp_int n ω))
  have hdv :=
    ContinuousChangeOfMeasure.continuous_donsker_varadhan
      posterior prior hρπ (fun θ => score θ n ω)
      (hexp_int n ω) (hscore_int n ω) hllr
  have hdv' :
      ∫ θ, score θ n ω ∂posterior ≤
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (continuousExponentialMixtureProcess prior score n ω) := by
    simpa [continuousExponentialMixtureProcess, continuousPriorMixtureProcess] using hdv
  have hlog_le :
      Real.log (1 / delta) ≤
        Real.log (continuousExponentialMixtureProcess prior score n ω) := by
    linarith
  have hdelta_inv_pos : 0 < 1 / delta := one_div_pos.mpr hδ
  exact (Real.log_le_log_iff hdelta_inv_pos hmix_pos).mp hlog_le

/--
End-to-end process-level time-uniform continuous PAC-Bayes bound.

The per-hypothesis exponential score processes are assumed to be
supermartingales almost everywhere under the prior.  Unlike a certificate
wrapper, this theorem derives the prior-mixture supermartingale through Fubini,
derives Ville's crossing probability, and derives the posterior inversion via
the continuous change-of-measure theorem.
-/
theorem timeUniformContinuousPACBayes_bound
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hρπ : posterior ≪ prior)
    (score : Θ → ℕ → Ω → ℝ) {delta : ℝ}
    (hδ : 0 < delta)
    (h_adapted_mix :
      StronglyAdapted ℱ (continuousExponentialMixtureProcess prior score))
    (h_integrable_mix :
      ∀ n, Integrable (continuousExponentialMixtureProcess prior score n) μ)
    (hM_int_next :
      ∀ n, Integrable
        (fun p : Θ × Ω => Real.exp (score p.1 (n + 1) p.2)) (prior.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => Real.exp (score p.2 (n + 1) p.1))
          ((μ.restrict s).prod prior))
    (hM_int_current :
      ∀ n, Integrable (fun p : Ω × Θ => Real.exp (score p.2 n p.1))
        (μ.prod prior))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable (fun p : Ω × Θ => Real.exp (score p.2 n p.1))
          ((μ.restrict s).prod prior))
    (hfixed :
      ∀ᵐ θ ∂prior,
        Supermartingale (fun n ω => Real.exp (score θ n ω)) ℱ μ)
    (hscore_zero : ∀ θ ω, score θ 0 ω = 0)
    (hexp_int :
      ∀ n ω, Integrable (fun θ => Real.exp (score θ n ω)) prior)
    (hscore_int :
      ∀ n ω, Integrable (fun θ => score θ n ω) posterior)
    (hllr : Integrable (llr posterior prior) posterior) :
    μ.real (timeUniformContinuousPACBayesUpperFailure
      prior posterior score delta) ≤ delta := by
  have hmix :
      Supermartingale
          (continuousPriorMixtureProcess prior
            (fun θ n ω => Real.exp (score θ n ω))) ℱ μ
        ∧ ∀ n ω,
          0 ≤ continuousPriorMixtureProcess prior
            (fun θ k ξ => Real.exp (score θ k ξ)) n ω := by
    refine continuousPriorMixture_supermartingale
      (μ := μ) (ℱ := ℱ) (prior := prior)
      (M := fun θ n ω => Real.exp (score θ n ω))
      ?_ ?_ hM_int_next hM_int_next_restrict hM_int_current
        hM_int_current_restrict hfixed ?_
    · change StronglyAdapted ℱ
        (continuousExponentialMixtureProcess prior score)
      exact h_adapted_mix
    · intro n
      change Integrable (continuousExponentialMixtureProcess prior score n) μ
      exact h_integrable_mix n
    · intro θ n ω
      exact (Real.exp_pos _).le
  have hcross :
      μ.real {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ continuousExponentialMixtureProcess prior score n ω}
        ≤ delta := by
    have hcross' :=
      continuousPriorMixture_crossing_bound
        (μ := μ) (ℱ := ℱ) (prior := prior)
        (M := fun θ n ω => Real.exp (score θ n ω))
        hδ hmix.1 hmix.2
        (fun θ ω => by simp [hscore_zero θ ω])
    simpa [continuousExponentialMixtureProcess] using hcross'
  exact (measureReal_mono
    (timeUniformContinuousPACBayesUpperFailure_subset_crossing
      prior posterior hρπ score hδ hexp_int hscore_int hllr)).trans hcross

end

end FormalSLT.PACBayes.TimeUniformContinuous
