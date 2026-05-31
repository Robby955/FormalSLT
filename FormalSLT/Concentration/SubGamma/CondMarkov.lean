/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional Markov inequality for nonnegative integrable RVs

A conditional analogue of Markov's inequality: for nonnegative integrable
`Y` and `c > 0`, the conditional probability `μ[1_{Y ≥ c} | m]` is
bounded above by `μ[Y | m] / c` almost surely. Stated additively as

    c · μ[1_{Y ≥ c} | m] ≤ᵐ[μ] μ[Y | m]

to avoid premature division by `c`.

This is the building block used to convert a conditional MGF bound into a
conditional tail bound (Cramér–Chernoff step), so it sits in the chain
between the extractor and the Freedman corollary.

**Mathlib status:** mathlib has unconditional Markov
(`MeasureTheory.mul_meas_ge_le_lintegral₀` and friends) but no direct
conditional analogue at `condExp` level. The proof here is a one-step
lift via `condExp_mono` of the pointwise inequality
`c · 1_{Y ≥ c}(ω) ≤ Y(ω)` (using `Y ≥ 0` a.s.), followed by
`condExp_smul` to factor `c` outside.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.Concentration.SubGamma

/--
**Conditional Markov inequality (a.e. form).**

For nonnegative integrable `Y` and `c > 0`, the conditional probability
that `Y ≥ c`, multiplied by `c`, is bounded a.e. by `μ[Y | m]`.

The conditional probability is encoded as
`μ[1_{Y ≥ c} | m]` — the conditional expectation of the indicator. (This
is *not* the pointwise indicator: the inequality is at the conditional
level, not the realisation level.)
-/
theorem cond_markov_of_nonneg
    {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ m₀)
    {Y : Ω → ℝ} {c : ℝ}
    (_hc_pos : 0 < c)
    (hY_meas : Measurable[m₀] Y)
    (hY_int : Integrable Y μ)
    (hY_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω) :
    (fun ω => c * (μ[Set.indicator {ω' | c ≤ Y ω'} (fun _ => (1 : ℝ)) | m]) ω)
      ≤ᵐ[μ] μ[Y | m] := by
  -- Step 1: name the indicator and record measurability (all w.r.t. `m₀`).
  -- Use the preimage form `S = Y ⁻¹' Set.Ici c` so the σ-algebra is inferred from `hY_meas`.
  set S : Set Ω := {ω' | c ≤ Y ω'} with hS_def
  have hS_eq : S = Y ⁻¹' Set.Ici c := by ext ω; simp [hS_def, Set.mem_Ici]
  have hS_meas : MeasurableSet[m₀] S := hS_eq ▸ hY_meas measurableSet_Ici
  set Z : Ω → ℝ := S.indicator (fun _ => (1 : ℝ)) with hZ_def
  have hZ_meas : Measurable[m₀] Z :=
    Measurable.indicator (m := m₀) measurable_const hS_meas
  -- Step 2: pointwise bound `c · Z(ω) ≤ Y(ω)` on the a.s. set `Y ≥ 0`.
  have hcZ_le_Y : (fun ω => c * Z ω) ≤ᵐ[μ] Y := by
    filter_upwards [hY_nonneg] with ω hY_nn
    by_cases hω : ω ∈ S
    · rw [hZ_def, Set.indicator_of_mem hω, mul_one]
      exact hω
    · rw [hZ_def, Set.indicator_of_notMem hω, mul_zero]
      exact hY_nn
  -- Step 3: integrability of `Z` and `c · Z` (Z is a bounded indicator).
  have hZ_bdd : ∀ ω, |Z ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ S
    · simp [hZ_def, Set.indicator_of_mem hω]
    · simp [hZ_def, Set.indicator_of_notMem hω]
  have hZ_int : Integrable Z μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hZ_meas.aestronglyMeasurable
      (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using hZ_bdd ω))
  have hcZ_int : Integrable (fun ω => c * Z ω) μ := hZ_int.const_mul c
  -- Step 4: condExp_mono gives `μ[c · Z | m] ≤ᵐ μ[Y | m]`.
  have h_mono : μ[fun ω => c * Z ω | m] ≤ᵐ[μ] μ[Y | m] :=
    condExp_mono hcZ_int hY_int hcZ_le_Y
  -- Step 5: condExp_smul factors the scalar `c` out of the conditional expectation.
  have h_smul := condExp_smul (𝕜 := ℝ) (μ := μ) (m := m) c Z
  -- `c • Z = fun ω => c * Z ω` and `(c • μ[Z | m]) ω = c * (μ[Z | m]) ω`.
  have h_factor : μ[fun ω => c * Z ω | m] =ᵐ[μ] fun ω => c * (μ[Z | m]) ω := by
    filter_upwards [h_smul] with ω hω
    simpa [Pi.smul_apply, smul_eq_mul] using hω
  -- Step 6: combine.
  filter_upwards [h_mono, h_factor] with ω h_mono' h_factor'
  exact h_factor' ▸ h_mono'

end FormalSLT.Concentration.SubGamma
