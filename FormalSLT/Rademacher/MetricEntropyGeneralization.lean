import FormalSLT.Rademacher.Symmetrization
import FormalSLT.Rademacher.RademacherBoundedDifferences
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Metric-entropy generalization bound (symmetrization ∘ Dudley entropy integral)

The two existing halves of the finite-class data-dependent story are

* symmetrization — `expected_genGap_le_two_expected_empiricalRademacherComplexity`
  (Stage 3), bounding the expected worst-case generalization gap by twice the
  expected empirical Rademacher complexity, and
* chaining — `dudley_rademacher_complexity_bound`, bounding the empirical
  Rademacher complexity of a *fixed* sample by the finite Dudley entropy integral.

This module composes them. The composition needs the per-sample chaining bound to
hold with a sample-independent covering-number profile, i.e. a *uniform* ceiling
on the empirical Rademacher complexity. That uniform ceiling is exactly what
`integral_mono` carries through the expectation.

What this module provides:

* `expected_genGap_le_of_uniform_empiricalRademacher_bound`
  — the abstract composition: any uniform ceiling `D` on the empirical Rademacher
  complexity lifts to `E_S genGap ≤ 2·D`.
* `expected_genGap_le_dudley_entropy_integral`
  — the metric-entropy corollary: instantiating the uniform ceiling with the
  Dudley entropy integral makes the entropy integrand explicit.

Out of scope:

* Re-deriving the chaining bound. The per-sample Dudley bound
  (`dudley_rademacher_complexity_bound`) is consumed through its conclusion; this
  module does not reopen the sub-Gaussian increment control or the net data.
* High-probability (McDiarmid) versions of the composed bound.
* Continuous / uncountable hypothesis classes.
-/

namespace FormalSLT.Rademacher.MetricEntropyGeneralization

open MeasureTheory
open scoped BigOperators
open FormalSLT.GhostSample (piMeasure genGap)
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)
open FormalSLT.Rademacher (empiricalRademacher_integrable)
open FormalSLT.Rademacher.Symmetrization
  (expected_genGap_le_two_expected_empiricalRademacherComplexity)

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Z : Type*} [MeasurableSpace Z]
variable {n : ℕ}

/-! ### Abstract composition -/

/-- **Expected generalization gap from a uniform Rademacher ceiling.**

For a finite, nonempty hypothesis class with bounded measurable real-valued losses
`|ℓ i z| ≤ B` (with `0 ≤ B`) against an iid sample of size `n ≥ 1` from a
probability measure `μ`, if the empirical Rademacher complexity is bounded by a
single sample-independent constant `D` for every sample, then the expected
worst-case generalization gap is bounded by `2·D`:

```
(∀ S, R̂ad_n(ℓ ∘ H, S) ≤ D)  ⟹  E_S sup_h (risk(h) − R̂_S(h)) ≤ 2·D
```

Proof: symmetrization bounds the expected gap by twice the *expected* empirical
Rademacher complexity; the uniform ceiling `D` dominates the integrand pointwise,
so `integral_mono` bounds the expectation by `D` (the constant integrates to `D`
against a probability measure). -/
theorem expected_genGap_le_of_uniform_empiricalRademacher_bound
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) {D : ℝ}
    (hUniform : ∀ S : Fin n → Z, empiricalRademacherComplexity ℓ S ≤ D) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n) ≤ 2 * D := by
  -- Symmetrization: the expected gap is at most twice the expected Rademacher term.
  have h_sym :
      ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
        ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) :=
    expected_genGap_le_two_expected_empiricalRademacherComplexity
      μ ℓ hB hℓ_meas hℓ_bdd hn
  -- The empirical Rademacher term is integrable on the iid product.
  have h_int :
      Integrable (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
        (piMeasure μ n) :=
    empiricalRademacher_integrable μ ℓ hB hℓ_meas hℓ_bdd hn
  -- The uniform ceiling dominates the integrand, so the expectation is at most `D`.
  have h_mean_le :
      ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) ≤ D := by
    have h_mono := integral_mono h_int (integrable_const D) hUniform
    have h_const : ∫ _S : Fin n → Z, D ∂(piMeasure μ n) = D := by simp
    rwa [h_const] at h_mono
  linarith

/-! ### Metric-entropy corollary -/

/-- **Metric-entropy generalization bound.**

Composes symmetrization with the finite Dudley entropy integral. The hypothesis
`hDudley` is the *uniform* metric-entropy certificate: the per-sample chaining
bound `dudley_rademacher_complexity_bound` holding for every sample with a single
sample-independent covering-number profile `coveringNumberAtRadius`. Under that
certificate the expected worst-case generalization gap is bounded by twice the
Dudley entropy integral:

```
E_S sup_h (risk(h) − R̂_S(h)) ≤ 8 · √(2/n) · ∫_a^b √(log N(ε)) dε
```

This theorem *composes* the two halves; it does not re-derive the chaining bound.
The constant `8 = 2·4` is the symmetrization factor `2` times the chaining
constant `4`. -/
theorem expected_genGap_le_dudley_entropy_integral
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n)
    (a b : ℝ) (coveringNumberAtRadius : ℝ → ℕ)
    (hDudley : ∀ S : Fin n → Z,
      empiricalRademacherComplexity ℓ S ≤
        4 * Real.sqrt (2 / (n : ℝ)) *
          ∫ ε in a..b, Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n) ≤
      8 * Real.sqrt (2 / (n : ℝ)) *
        ∫ ε in a..b, Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)) := by
  have h := expected_genGap_le_of_uniform_empiricalRademacher_bound
    μ ℓ hB hℓ_meas hℓ_bdd hn hDudley
  have hEq :
      2 * (4 * Real.sqrt (2 / (n : ℝ)) *
          ∫ ε in a..b, Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
        = 8 * Real.sqrt (2 / (n : ℝ)) *
            ∫ ε in a..b, Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)) := by
    ring
  rwa [hEq] at h

/-! ### Non-vacuity

The composition premise is satisfiable and the theorem is not vacuously true: for
any bounded measurable loss class the uniform ceiling `D = B` is discharged from
`abs_empiricalRademacherComplexity_le`, so the composition specializes to the real
conclusion `E_S genGap ≤ 2·B`. -/

example (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n) ≤ 2 * B :=
  expected_genGap_le_of_uniform_empiricalRademacher_bound μ ℓ hB hℓ_meas hℓ_bdd hn
    (fun S => (abs_le.mp
      (FormalSLT.Rademacher.Decoupling.abs_empiricalRademacherComplexity_le
        hB hℓ_bdd hn S)).2)

-- A fully concrete instantiation, eliminating every type-class and data
-- hypothesis, confirms the bundle is inhabited: `Z = ℝ` with the Dirac law,
-- `ι = Unit`, the identically-zero loss (bounded by `B = 0`), sample size `n = 1`,
-- and uniform ceiling `D = 0`. The conclusion `∫ genGap ≤ 0` is a real inequality.
example :
    ∫ S, genGap (Measure.dirac (0 : ℝ)) (fun _ : Unit => fun _ : ℝ => (0 : ℝ)) S
        ∂(piMeasure (Measure.dirac (0 : ℝ)) 1)
      ≤ 2 * (0 : ℝ) :=
  expected_genGap_le_of_uniform_empiricalRademacher_bound
    (μ := Measure.dirac (0 : ℝ))
    (ℓ := fun _ : Unit => fun _ : ℝ => (0 : ℝ)) (B := 0) le_rfl
    (fun _ => measurable_const) (fun _ _ => abs_zero.le) Nat.one_pos
    (D := 0)
    (fun S => (abs_le.mp
      (FormalSLT.Rademacher.Decoupling.abs_empiricalRademacherComplexity_le
        (ℓ := fun _ : Unit => fun _ : ℝ => (0 : ℝ)) (B := 0) le_rfl
        (fun _ _ => abs_zero.le) Nat.one_pos S)).2)

end FormalSLT.Rademacher.MetricEntropyGeneralization
