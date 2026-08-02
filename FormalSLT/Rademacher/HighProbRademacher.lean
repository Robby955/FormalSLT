/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.GenGapTail
import FormalSLT.Rademacher.Symmetrization

/-!
# High-probability Rademacher generalization bound

Stage C of `docs/plans/mcdiarmid-rademacher-plan.md`.

Combines:
  (A) the expected Rademacher symmetrization theorem:
      `E[genGap] ≤ 2 · E[empiricalRademacherComplexity]`
      (`expected_genGap_le_two_expected_empiricalRademacherComplexity`)
  (B) the Azuma-style one-sided tail from Stage B:
      `P(genGap ≥ E[genGap] + ε) ≤ exp(-ε² n / (8 B²))`
      (`genGap_tail_bound_azuma_explicit`)

to obtain:

    P(genGap S ≥ 2 · E_S[empiricalRademacherComplexity] + ε)
      ≤ exp(-ε² n / (8 B²))

## Interpretation

This theorem gives the following public threshold:
with probability at least `1 - exp(-ε² n / (8 B²))` over an iid sample
`S ~ μⁿ`, the generalization gap satisfies

    genGap(S) < 2 · E_S[R̂ad_n(ℓ, S)] + ε

where `R̂ad_n(ℓ, S)` is the empirical Rademacher complexity of the loss
class on the sample, and the expectation is over the sample.

## Scope and constants

- **One-sided** bound on genGap = sup_h (risk(h) − R̂_S(h)).
- **Azuma constant** (factor-of-4 gap to sharp McDiarmid), tracked explicitly.
- **Finite hypothesis class** `ι` with `[Fintype ι] [Nonempty ι]`.
- **Bounded loss** `|ℓ_i(z)| ≤ B` for all `i`, `z`.
- **iid sample** `S ~ μⁿ`.
- The **deterministic** bound `E_S[empiricalRademacherComplexity]`
  appears in the event, not the **random** `empiricalRademacherComplexity ℓ S`.
  A future PR can state the random-variable form using a second
  application of concentration to the Rademacher complexity itself.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory Filter ProbabilityTheory Real
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap integrable_genGap)
open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity)
open FormalSLT.Azuma.ExposureMartingale
  (genGap_tail_bound_azuma_explicit)
open FormalSLT.Rademacher.Symmetrization
  (expected_genGap_le_two_expected_empiricalRademacherComplexity)

noncomputable section

namespace FormalSLT.Rademacher.HighProbRademacher

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-! ### Main theorem -/

/-- **High-probability Rademacher generalization bound.**

For a finite hypothesis class `ι` with uniformly `B`-bounded loss and
an iid sample `S ~ μⁿ`:

    P(genGap(S) ≥ 2 · E_S[R̂ad_n(ℓ, S)] + ε) ≤ exp(-ε² n / (8 B²))

Proof sketch:
1. `E[genGap] ≤ 2 · E[R̂ad]` (Rademacher symmetrization, Stage A).
2. `P(genGap ≥ E[genGap] + ε) ≤ exp(-ε² n / (8 B²))` (Azuma tail, Stage B).
3. Since `E[genGap] ≤ 2 · E[R̂ad]`, the event
   `{S | 2 · E[R̂ad] + ε ≤ genGap S}` is contained in
   `{S | E[genGap] + ε ≤ genGap S}`, so the tail probability
   decreases.

This is the monotonicity argument: if `a ≤ b` then
`{x | b + t ≤ f x} ⊆ {x | a + t ≤ f x}` and so `P(f ≥ b + t) ≤ P(f ≥ a + t)`.
We apply this with `a = E[genGap]` and `b = 2 · E[R̂ad]`.

Claim-facing wrapper for theorempath.com evidence entry `claim:rademacher-complexity::high-probability-rademacher-gengap-bound`.
-/
theorem genGap_highProb_rademacher {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n)
              + ε ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 * ↑n / (8 * B ^ 2)) := by
  -- The Azuma tail bound gives:
  -- P(genGap S ≥ E[genGap] + ε) ≤ exp(-ε²n/(8B²))
  have h_azuma := genGap_tail_bound_azuma_explicit (ν := μ) hB hℓ_meas hℓ_bdd hn hε
  -- Unfold piMeasure in the Azuma bound to match our goal.
  simp only [piMeasure] at h_azuma ⊢
  -- The Rademacher symmetrization theorem gives:
  -- E[genGap] ≤ 2 · E[empiricalRademacherComplexity]
  have h_symm := expected_genGap_le_two_expected_empiricalRademacherComplexity
    μ ℓ hB.le hℓ_meas hℓ_bdd hn
  simp only [piMeasure] at h_symm
  -- Set notation.
  set μn := Measure.pi (fun _ : Fin n => μ)
  set E_genGap := ∫ s, genGap μ ℓ s ∂μn
  set E_rad := ∫ S', empiricalRademacherComplexity ℓ S' ∂μn
  -- Key monotonicity: since E_genGap ≤ 2 * E_rad, the event
  -- {S | 2 * E_rad + ε ≤ genGap S} ⊆ {S | E_genGap + ε ≤ genGap S}.
  have h_subset : {S : Fin n → Z | 2 * E_rad + ε ≤ genGap μ ℓ S}
      ⊆ {S : Fin n → Z | E_genGap + ε ≤ genGap μ ℓ S} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    linarith [h_symm]
  -- Monotonicity of measure: P(A) ≤ P(B) when A ⊆ B.
  have h_mono : μn.real {S : Fin n → Z | 2 * E_rad + ε ≤ genGap μ ℓ S}
      ≤ μn.real {S : Fin n → Z | E_genGap + ε ≤ genGap μ ℓ S} :=
    measureReal_mono h_subset
  -- Chain: P(genGap ≥ 2·E[Rad] + ε) ≤ P(genGap ≥ E[genGap] + ε) ≤ exp(...)
  linarith [h_mono, h_azuma]

end FormalSLT.Rademacher.HighProbRademacher
