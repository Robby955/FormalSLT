/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

/-!
# Supermartingale Ville maximal inequality

Mathlib exposes only the submartingale maximal inequality `MeasureTheory.maximal_ineq`. This
file provides the nonnegative-supermartingale form (Ville's inequality): for a nonnegative
supermartingale `M` and any threshold `a`,

`a * μ.real {ω | a ≤ max_{k ≤ n} M_k ω} ≤ ∫ ω, M 0 ω ∂μ`.

The intended use is `a > 0`, where dividing by `a` gives `μ.real {max ≥ a} ≤ E[M 0] / a`; the
inequality itself needs no sign hypothesis. It is derived from the same hitting-time route that
underlies `maximal_ineq`, with the final step using the supermartingale optional-stopping bound
`E[M_τ] ≤ E[M_0]` (obtained by applying `Submartingale.expected_stoppedValue_mono` to `-M`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace FormalSLT.AnytimeValid

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- **Ville's inequality** (nonnegative-supermartingale maximal inequality). -/
theorem ville_maximal_ineq [IsFiniteMeasure μ]
    (hsup : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {a : ℝ} (n : ℕ) :
    a * μ.real {ω | a ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => M k ω}
      ≤ ∫ ω, M 0 ω ∂μ := by
  classical
  set τ : Ω → ℕ∞ := fun ω => ((hittingBtwn M (Set.Ici a) 0 n ω : ℕ) : ℕ∞) with hτ_def
  set evt : Set Ω :=
    {ω | a ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => M k ω} with hevt
  have hadapted : Adapted 𝒢 M := hsup.stronglyAdapted.adapted
  have hτ_stop : IsStoppingTime 𝒢 τ := by
    rw [hτ_def]; exact hadapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ_le : ∀ ω, τ ω ≤ (n : ℕ∞) := by
    intro ω
    have hle : hittingBtwn M (Set.Ici a) 0 n ω ≤ n := hittingBtwn_le ω
    simp only [hτ_def]
    exact_mod_cast hle
  have hint : ∀ i, Integrable (M i) μ := hsup.integrable
  have hsv_int : Integrable (stoppedValue M τ) μ :=
    integrable_stoppedValue ℕ hτ_stop hint hτ_le
  have hsv_nonneg : 0 ≤ stoppedValue M τ := fun ω => hnonneg _ ω
  -- measurability of the running-max event
  have hmeas_evt : MeasurableSet evt :=
    measurableSet_le measurable_const
      (measurable_range_sup'' fun k _ => (hsup.stronglyMeasurable k).measurable.le (𝒢.le k))
  -- on evt the stopped value reaches a
  have hstep : ∀ ω ∈ evt, a ≤ stoppedValue M τ ω := by
    intro ω hω
    rw [hevt, Set.mem_setOf_eq, le_sup'_iff] at hω
    have hmem : stoppedValue M τ ω ∈ Set.Ici a := by
      rw [hτ_def]
      refine stoppedValue_hittingBtwn_mem ?_
      obtain ⟨k, hk_mem, hk_le⟩ := hω
      rw [mem_range, Nat.lt_succ_iff] at hk_mem
      exact ⟨k, ⟨Nat.zero_le _, hk_mem⟩, hk_le⟩
    exact hmem
  -- Step B: a · μ(evt) ≤ ∫_evt stoppedValue M τ
  have hB : a * μ.real evt ≤ ∫ ω in evt, stoppedValue M τ ω ∂μ :=
    setIntegral_ge_of_const_le_real hmeas_evt (measure_ne_top _ _) hstep hsv_int.integrableOn
  -- Step C: ∫_evt stoppedValue ≤ ∫ stoppedValue
  have hC : ∫ ω in evt, stoppedValue M τ ω ∂μ ≤ ∫ ω, stoppedValue M τ ω ∂μ :=
    setIntegral_le_integral hsv_int (Filter.Eventually.of_forall hsv_nonneg)
  -- Step D: optional stopping for the supermartingale, ∫ stoppedValue M τ ≤ ∫ M 0
  have hD : ∫ ω, stoppedValue M τ ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
    have hsub : Submartingale (-M) 𝒢 μ := hsup.neg
    have hmono := hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ_stop
        (fun _ => bot_le) hτ_le
    -- E[stoppedValue (-M) σ] = -E[stoppedValue M σ] for any stopping time σ
    have key : ∀ σ : Ω → ℕ∞,
        ∫ ω, stoppedValue (-M) σ ω ∂μ = -∫ ω, stoppedValue M σ ω ∂μ := by
      intro σ
      have hfun : (fun ω => stoppedValue (-M) σ ω) = fun ω => -(stoppedValue M σ ω) := by
        funext ω; simp only [stoppedValue, Pi.neg_apply]
      rw [hfun, integral_neg]
    simp only [key] at hmono
    rw [stoppedValue_const] at hmono
    linarith
  calc a * μ.real evt ≤ ∫ ω in evt, stoppedValue M τ ω ∂μ := hB
    _ ≤ ∫ ω, stoppedValue M τ ω ∂μ := hC
    _ ≤ ∫ ω, M 0 ω ∂μ := hD

end FormalSLT.AnytimeValid
