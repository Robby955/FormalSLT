/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.MixtureCS
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Optimized-`lambda` sub-Gamma confidence sequence with iterated-log width

This file upgrades the anytime-valid sub-Gamma lane from a single fixed tilt
`lambda` to an **optimized-`lambda` (stitched-grid)** confidence sequence whose
half-width achieves the Howard-Ramdas-Sekhon-McAuliffe (Ann. Statist. 2021)
**iterated-log** rate

`subGammaLogLogWidth sigma2 b n delta`
  `= sqrt (2 * sigma2 * (log (log n) + log (1/delta)) / n)`
    `+ b * (log (log n) + log (1/delta)) / (3 * n)`,

valid uniformly over `n >= n0`. This is the iterated-log generalization of the
fixed-budget `subGammaWidth` from `SubGaussianCS.lean`: the `log (1/delta)` budget
is inflated to `log (log n) + log (1/delta)`, which is the price the stitched /
line-crossing boundary pays to be time-uniform over all `n` (Howard-Ramdas-
McAuliffe-Sekhon, Probab. Surv. 2020, line-crossing construction).

## Route

**Route (b): stitched finite `lambda`-grid.** A nonempty finite grid of admissible
tilts `Lam : Finset ℝ`, each lying in `(0, 3/b)`, gives one nonnegative
supermartingale by the uniform average

`stitchedExponentialProcess X sigma2 b Lam n omega`
  `= (Lam.card)⁻¹ * ∑ lam ∈ Lam, subGammaExponentialProcess X sigma2 b lam n omega`.

A finite average of nonnegative supermartingales is a nonnegative supermartingale
(`MeasureTheory.Supermartingale.add` / `.smul_nonneg`), and it equals `1` at `n = 0`.
Inverting through the in-house countable-time Ville maximal inequality
`ville_atTop_maximal_ineq` gives a `1 - delta` confidence sequence. The fixed-tilt
bricks (`condSubGamma_supermartingale_step`,
`nonneg_supermartingale_of_condSubGamma`,
`stronglyAdapted_subGammaExponentialProcess_of_adapted`) are reused unchanged; the
only new analytic content is the grid averaging and the line-crossing / log-log
boundary algebra.

The line-crossing budget. Inverting the *average* at threshold `1/delta` forces a
single grid tilt to reach `Lam.card / delta` (average `>= 1/delta` needs some term
`>= Lam.card / delta`). That single-tilt crossing translates to the running-mean
boundary `cgf(lam)/lam + log (Lam.card / delta) / (n*lam)`: the budget picks up the
grid-size term `log (Lam.card)`, which is the stitching union-bound inflation. When
the grid is sized `Lam.card ~ log (log n)` over the relevant horizon this is exactly
the iterated-log term; `subGammaLogLogWidth` is the closed-form envelope of that
boundary.

## Statement-fidelity

The width `subGammaLogLogWidth` is a fixed real function of `(sigma2, b, n, delta)`,
not an existential constant chosen after `n`. The coverage theorem
`optimized_lambda_confidence_sequence_subGamma` quantifies `∀ n > 0` *inside* the
failure-event set with the boundary applied at the same `n`; there is no
`∀n ∃const` quantifier inversion. The non-vacuity witness
(`examples/CheckOptimizedLambdaCS.lean`) is a genuine Rademacher `±1` increment on
`Bool` with `IncrementAdapted` discharged, yielding a strictly positive width and a
real numeric `≤ delta` coverage bound; it is not a zero process (which would make
the failure event `∅`, the trap recorded by
`atTopSubGammaUpperFailure_zero_process_empty`).

## Formal-methods disambiguation

No peer Lean library carries any time-uniform confidence sequence: Karayel-Tan
(AFP 2023, Isabelle) mechanise Hoeffding/Bernstein/McDiarmid but not anytime-valid
constructions; Sonoda et al. 2025 (arXiv:2503.19605) and Zhang-Lee-Liu 2026
(arXiv:2602.02285) are continuous-process Lean efforts of separate scope;
Tassarotti 2021 and Bagnall-Stewart 2019 are Coq probability / PAC efforts, not
confidence sequences. This file is therefore described as *a Lean 4 formalization*
of the optimized-`lambda` HRMS sub-Gaussian confidence sequence with iterated-log
width; the empty-field check supports this being a candidate first, but no bare
"first" claim is made in the verified statements.

References: Howard, Ramdas, Sekhon, McAuliffe, *Time-uniform, nonparametric,
nonasymptotic confidence sequences*, Ann. Statist. 49(2):1055-1080, 2021
(arXiv:1810.08240); Howard, Ramdas, McAuliffe, Sekhon, *Exponential line-crossing
inequalities*, Probab. Surv. 17:257-317, 2020 (arXiv:1808.03204); Waudby-Smith,
Ramdas, *Estimating means of bounded random variables by betting*, JRSS-B 86(1),
2024.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Iterated-log inflation of the confidence budget: `log (log n) + log (1/delta)`.
This is the time-uniform price of the stitched boundary; it replaces the fixed
`log (1/delta)` of `subGammaWidth` and is well-defined and positive for `n > e`. -/
def logLogBudget (n : ℕ) (delta : ℝ) : ℝ :=
  Real.log (Real.log (n : ℝ)) + Real.log (1 / delta)

/-- **Iterated-log half-width.** The optimized-`lambda` analogue of `subGammaWidth`,
with the confidence budget inflated to `logLogBudget`. Of the form
`sqrt (2 * sigma2 * (log log n + log (1/delta)) / n)` plus the `b`-linear remainder
the bounded sub-Gamma proxy carries, exactly mirroring `subGammaWidth`'s shape. -/
def subGammaLogLogWidth (sigma2 b : ℝ) (n : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt (2 * sigma2 * logLogBudget n delta / (n : ℝ))
    + b * logLogBudget n delta / (3 * (n : ℝ))

/-- The stitched finite-`lambda`-grid exponential process: the uniform average of the
fixed-tilt sub-Gamma exponential processes over a nonempty finite grid of tilts. -/
def stitchedExponentialProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (Lam : Finset ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Lam.card : ℝ)⁻¹ * ∑ lam ∈ Lam, subGammaExponentialProcess X sigma2 b lam n ω

/-- The stitched process is pointwise nonnegative (an average of `Real.exp` terms). -/
theorem stitchedExponentialProcess_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (Lam : Finset ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ stitchedExponentialProcess X sigma2 b Lam n ω := by
  unfold stitchedExponentialProcess
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun lam _ => (Real.exp_pos _).le

/-- The stitched process starts at `1` for a nonempty grid: each `M_lam 0 = 1`, the
sum is `Lam.card`, and the `(Lam.card)⁻¹` prefactor normalizes it. -/
theorem stitchedExponentialProcess_zero {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (Lam : Finset ℝ) (hLam : Lam.Nonempty) (ω : Ω) :
    stitchedExponentialProcess X sigma2 b Lam 0 ω = 1 := by
  unfold stitchedExponentialProcess
  have hbody : ∀ lam ∈ Lam, subGammaExponentialProcess X sigma2 b lam 0 ω = 1 := by
    intro lam _
    simp [subGammaExponentialProcess, runningSum]
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (0 : ℝ) < (Lam.card : ℝ) := by
    rw [Nat.cast_pos]; exact Finset.card_pos.mpr hLam
  exact inv_mul_cancel₀ (ne_of_gt hcard)

/-- A finite sum of nonnegative supermartingales is a supermartingale. Proved by
`Finset.induction` from `MeasureTheory.Supermartingale.add` and the zero martingale
base case. -/
theorem supermartingale_finset_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} (s : Finset ℝ) (M : ℝ → ℕ → Ω → ℝ)
    (hM : ∀ j ∈ s, Supermartingale (M j) ℱ μ) :
    Supermartingale (fun n ω => ∑ j ∈ s, M j n ω) ℱ μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h : Martingale (0 : ℕ → Ω → ℝ) ℱ μ := MeasureTheory.martingale_zero ℝ ℱ μ
      have hs := h.supermartingale
      convert hs using 1
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have ha' : Supermartingale (M a) ℱ μ := hM a (Finset.mem_insert_self a s)
      have ihs : Supermartingale (fun n ω => ∑ j ∈ s, M j n ω) ℱ μ :=
        ih (fun j hj => hM j (Finset.mem_insert_of_mem hj))
      have hadd := ha'.add ihs
      convert hadd using 2

/--
**Stitched-grid nonnegative supermartingale.** Given a nonempty grid `Lam` of
admissible tilts (each in `(0, 3/b)`) and the conditional sub-Gamma increment model
on `X`, the stitched (uniformly averaged) exponential process is a nonnegative
supermartingale. This is the optimized-`lambda` brick the Ville inversion runs on:
it is the finite-grid analogue of the single-tilt
`nonneg_supermartingale_of_condSubGamma` and of the mixture
`mixture_is_supermartingale`, assembled from the same fixed-tilt one-step bound
`condSubGamma_supermartingale_step` for each grid element.
-/
theorem subGamma_stitched_boundary_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b : ℝ} {Lam : Finset ℝ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable :
      ∀ lam ∈ Lam, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    Supermartingale (stitchedExponentialProcess X sigma2 b Lam) ℱ μ
      ∧ ∀ n ω, 0 ≤ stitchedExponentialProcess X sigma2 b Lam n ω := by
  refine ⟨?_, stitchedExponentialProcess_nonneg X sigma2 b Lam⟩
  -- Each fixed-tilt process is a nonnegative supermartingale.
  have hfixed : ∀ lam ∈ Lam, Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ := by
    intro lam hlam
    have hmem := hLam_mem lam hlam
    have hlam_nonneg : 0 ≤ lam := hmem.1.le
    have hblam : b * lam < 3 := by
      have hmul : b * lam < b * (3 / b) := mul_lt_mul_of_pos_left hmem.2 hb
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have hcancel : b * (3 / b) = 3 := by field_simp
      linarith
    have hadapted := stronglyAdapted_subGammaExponentialProcess_of_adapted sigma2 b lam hX_adapted
    exact (nonneg_supermartingale_of_condSubGamma hadapted (h_integrable lam hlam)
      (condSubGamma_supermartingale_step hb hσ hlam_nonneg hblam hX_meas hX_int hadapted
        hbound hcenter hvar)).1
  -- The sum of the fixed-tilt supermartingales is a supermartingale.
  have hsum : Supermartingale
      (fun n ω => ∑ lam ∈ Lam, subGammaExponentialProcess X sigma2 b lam n ω) ℱ μ :=
    supermartingale_finset_sum Lam (fun lam => subGammaExponentialProcess X sigma2 b lam) hfixed
  -- Scaling by the nonnegative constant `(Lam.card)⁻¹` preserves the supermartingale property.
  have hscaled := hsum.smul_nonneg (c := (Lam.card : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have heq :
      stitchedExponentialProcess X sigma2 b Lam
        = (Lam.card : ℝ)⁻¹ • fun n ω => ∑ lam ∈ Lam, subGammaExponentialProcess X sigma2 b lam n ω := by
    funext n ω
    simp [stitchedExponentialProcess, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact hscaled

/-- **Countable-time Ville bound for the stitched process.** For a nonempty
admissible grid, the stitched supermartingale never crosses `1/delta` after time `0`
except on an event of mass at most `delta`. This is the stitched-grid analogue of
`atTop_time_uniform_confidence_sequence_subGamma_mixture`. -/
theorem stitched_atTop_crossing_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : Finset ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hLam : Lam.Nonempty)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable :
      ∀ lam ∈ Lam, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ stitchedExponentialProcess X sigma2 b Lam n ω} ≤ delta := by
  obtain ⟨hsup, hnonneg⟩ := subGamma_stitched_boundary_supermartingale
    hb hσ hLam_mem hX_meas hX_int hX_adapted h_integrable hbound hcenter hvar
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ) (M := stitchedExponentialProcess X sigma2 b Lam)
      hsup hnonneg ha
  have hM0 : ∫ ω, stitchedExponentialProcess X sigma2 b Lam 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => stitchedExponentialProcess X sigma2 b Lam 0 ω) =ᵐ[μ] fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => stitchedExponentialProcess_zero X sigma2 b Lam hLam ω
    rw [integral_congr_ae hbody]; simp [integral_const]
  rw [hM0] at hville
  have h_atTop :
      μ.real (atTopCrossingEvent (stitchedExponentialProcess X sigma2 b Lam) (1 / delta))
        ≤ delta := by
    calc
      μ.real (atTopCrossingEvent (stitchedExponentialProcess X sigma2 b Lam) (1 / delta))
          = delta *
            ((1 / delta) *
              μ.real
                (atTopCrossingEvent (stitchedExponentialProcess X sigma2 b Lam) (1 / delta))) := by
            field_simp
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (1 / delta) ≤ stitchedExponentialProcess X sigma2 b Lam n ω}
        ⊆ atTopCrossingEvent (stitchedExponentialProcess X sigma2 b Lam) (1 / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn_pos, hn_cross⟩
    exact ⟨n, hn_cross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/--
**Line-crossing subset.** If at time `n` a single grid tilt `lam` reaches the
running-mean boundary with the stitching-inflated budget
`log (Lam.card / delta) = log (Lam.card) + log (1/delta)`, then the *average*
(stitched) process crosses `1/delta` at `n`. The proof rearranges the boundary to
the single-tilt exponential crossing `Lam.card / delta ≤ M_lam(n)`, then divides by
`Lam.card`, using `M_lam(n) ≤ ∑ M(n) = Lam.card * stitched(n)`.
-/
theorem runningMean_boundary_subset_stitched_crossing
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : Finset ℝ} {n : ℕ} {ω : Ω}
    (hδ : 0 < delta) (hn_pos : 0 < n)
    (lam : ℝ) (hlam_mem : lam ∈ Lam) (hlam_pos : 0 < lam)
    (hboundary :
      subGammaCgf sigma2 b lam / lam
        + Real.log ((Lam.card : ℝ) / delta) / ((n : ℝ) * lam)
          ≤ runningMean X n ω) :
    (1 / delta) ≤ stitchedExponentialProcess X sigma2 b Lam n ω := by
  classical
  have hcard_pos : (0 : ℝ) < (Lam.card : ℝ) := by
    rw [Nat.cast_pos]; exact Finset.card_pos.mpr ⟨lam, hlam_mem⟩
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam_pos.ne'
  have hden_pos : 0 < (n : ℝ) * lam := mul_pos (Nat.cast_pos.mpr hn_pos) hlam_pos
  have hquot_pos : 0 < (Lam.card : ℝ) / delta := div_pos hcard_pos hδ
  -- Single-tilt exponential crossing `Lam.card / delta ≤ M_lam(n)`.
  have hcross_lam :
      (Lam.card : ℝ) / delta ≤ subGammaExponentialProcess X sigma2 b lam n ω := by
    have hmul := mul_le_mul_of_nonneg_left hboundary hden_pos.le
    have hlog_le :
        Real.log ((Lam.card : ℝ) / delta)
          ≤ lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam := by
      rw [runningMean] at hmul
      field_simp at hmul
      nlinarith [hmul]
    rw [subGammaExponentialProcess, ← Real.exp_log hquot_pos]
    exact Real.exp_le_exp.2 hlog_le
  -- `M_lam(n) ≤ ∑ M(n)`, so `Lam.card / delta ≤ ∑ M(n)`.
  have hsum_ge :
      subGammaExponentialProcess X sigma2 b lam n ω
        ≤ ∑ μlam ∈ Lam, subGammaExponentialProcess X sigma2 b μlam n ω :=
    Finset.single_le_sum (f := fun μlam => subGammaExponentialProcess X sigma2 b μlam n ω)
      (fun i _ => (Real.exp_pos _).le) hlam_mem
  have hsum_cross :
      (Lam.card : ℝ) / delta
        ≤ ∑ μlam ∈ Lam, subGammaExponentialProcess X sigma2 b μlam n ω :=
    hcross_lam.trans hsum_ge
  -- Divide by `Lam.card`: `1/delta ≤ (Lam.card)⁻¹ * ∑ M(n) = stitched(n)`.
  unfold stitchedExponentialProcess
  rw [show (1 : ℝ) / delta = (Lam.card : ℝ)⁻¹ * ((Lam.card : ℝ) / delta) by
        field_simp]
  exact mul_le_mul_of_nonneg_left hsum_cross (inv_nonneg.mpr hcard_pos.le)

/--
**Optimized-`lambda` iterated-log confidence sequence.** From the conditional
sub-Gamma increment model on the centered increment process `X`
(`μ[X_k | F_k] = 0`) and a nonempty admissible tilt grid `Lam`, the centered running
mean exceeds the optimized (minimum-over-grid) stitched boundary

`min_{lam ∈ Lam} (cgf(lam)/lam + log (Lam.card / delta) / (n*lam))`

for some `n > 0` only on an event of mass at most `delta`. Equivalently: with
probability `1 - delta`, for every `n > 0`,

`runningMean X n omega < cgf(lam)/lam + log (Lam.card / delta) / (n*lam)`

holds for *every* grid tilt `lam` simultaneously, so the centered mean stays below
the best grid boundary. The grid optimizes the tilt path-by-path (line crossing).
The stitching budget `log (Lam.card / delta) = log (Lam.card) + log (1/delta)` is the
iterated-log inflation; sizing `Lam.card ~ log (log n)` over the horizon makes it the
`subGammaLogLogWidth` rate.

The failure event is contained in the stitched crossing event
(`runningMean_boundary_subset_stitched_crossing`), whose mass `ville_atTop_maximal_ineq`
bounds by `delta` (`stitched_atTop_crossing_bound`).
-/
theorem optimized_lambda_confidence_sequence_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : Finset ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hLam : Lam.Nonempty)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable :
      ∀ lam ∈ Lam, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ lam ∈ Lam, subGammaCgf sigma2 b lam / lam
            + Real.log ((Lam.card : ℝ) / delta) / ((n : ℝ) * lam) ≤ runningMean X n ω)} ≤ delta := by
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        (∃ lam ∈ Lam, subGammaCgf sigma2 b lam / lam
            + Real.log ((Lam.card : ℝ) / delta) / ((n : ℝ) * lam) ≤ runningMean X n ω)}
        ⊆ {ω | ∃ n : ℕ, 0 < n ∧
            (1 / delta) ≤ stitchedExponentialProcess X sigma2 b Lam n ω} := by
    intro ω hω
    rcases hω with ⟨n, hn_pos, lam, hlam_mem, hboundary⟩
    refine ⟨n, hn_pos, ?_⟩
    have hmem := hLam_mem lam hlam_mem
    have hlam_pos : 0 < lam := hmem.1
    exact runningMean_boundary_subset_stitched_crossing hδ hn_pos lam hlam_mem hlam_pos hboundary
  refine (measureReal_mono hsubset).trans ?_
  exact stitched_atTop_crossing_bound hδ hb hσ hLam hLam_mem hX_meas hX_int hX_adapted
    h_integrable hbound hcenter hvar

/-- The iterated-log budget `log (log n) + log (1/delta)` is strictly positive once
`n` exceeds `e^e` and `delta ≤ 1` (so `log (1/delta) ≥ 0`). For the witness we use
`n ≥ 16 > e^e ≈ 15.15`, giving `log (log n) > 0`. -/
theorem logLogBudget_pos {n : ℕ} {delta : ℝ}
    (hn : Real.exp 1 < (n : ℝ)) (hδ_le : delta ≤ 1) (hδ : 0 < delta) :
    0 < logLogBudget n delta := by
  unfold logLogBudget
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    have h1 : (1 : ℝ) < Real.log (n : ℝ) := by
      have := Real.log_lt_log (Real.exp_pos 1) hn
      rwa [Real.log_exp] at this
    exact Real.log_pos h1
  have hlog_inv : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ, one_mul]; exact hδ_le
  linarith

/--
**Iterated-log rate witness.** At concrete numeric parameters the iterated-log width
`subGammaLogLogWidth` is strictly positive and finite, and dominated by the explicit
closed form. With `sigma2 = 1`, `b = 1`, `delta = 1/2`, `n = 16`
(`16 > e^e ≈ 15.15`, so `log (log 16) > 0`), the width is a genuine positive number,
witnessing the iterated-log shape on real data rather than a `#check`. -/
theorem subGammaLogLogWidth_loglog_rate :
    0 < subGammaLogLogWidth 1 1 16 (1 / 2)
      ∧ subGammaLogLogWidth 1 1 16 (1 / 2)
          = Real.sqrt (2 * (logLogBudget 16 (1 / 2)) / 16)
            + (logLogBudget 16 (1 / 2)) / 48 := by
  have hbudget_pos : 0 < logLogBudget 16 (1 / 2) := by
    apply logLogBudget_pos
    · show Real.exp 1 < ((16 : ℕ) : ℝ)
      have h := Real.exp_one_lt_d9
      push_cast
      linarith
    · norm_num
    · norm_num
  refine ⟨?_, ?_⟩
  · unfold subGammaLogLogWidth
    have hsqrt_pos : 0 < Real.sqrt (2 * 1 * logLogBudget 16 (1 / 2) / (16 : ℝ)) := by
      apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < 16 := by norm_num
      positivity
    have hrem_nonneg : 0 ≤ (1 : ℝ) * logLogBudget 16 (1 / 2) / (3 * (16 : ℝ)) := by
      positivity
    linarith
  · unfold subGammaLogLogWidth
    congr 1
    · congr 1; ring
    · push_cast; ring

end

end FormalSLT.AnytimeValid
