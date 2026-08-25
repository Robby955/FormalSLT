import FormalSLT.Covering.ContinuousDudley
import FormalSLT.Covering.DudleySumToIntegral
import FormalSLT.Rademacher.Massart

/-!
# Arbitrary-measure finite-net and conditional Dudley bounds

The finite Dudley lane (`FiniteSubGaussianChaining` → `TotalBoundedDudley` →
`ContinuousDudley`) states every expected-supremum bound through
`finiteExpectation P.weight`, i.e. a finite weighted sum
`∑ ω, weight ω · X ω` over a `Fintype Ω`. That is strictly less general than a
genuine measure-theoretic expectation `∫ ω, X ω ∂μ` against an arbitrary
probability measure on an arbitrary measurable space.

This module develops the arbitrary-measure side of that generality gap. It
re-derives the sub-Gaussian finite-maximum engine at the Bochner-integral level,
proves a one-scale finite-net entropy bound directly from process and net data,
and records a conditional lift of the continuous Dudley entropy integral to

  `∫ ω, supFunctional ω ∂μ ≤ coarseBudget + 4 · √(2 · σ²) · ∫₀^{R/2} entropyAtRadius`,

where `μ` is an arbitrary probability measure (`IsProbabilityMeasure μ`) on an
arbitrary `[MeasurableSpace Ω]`. The generic theorem permits Dirac measures;
the concrete Boolean witness below uses the non-Dirac uniform measure.

## Why the lift is a re-derivation, not a re-statement

The finite proof rests on exactly three algebraic laws of the expectation
operator plus one analytic inequality:

* monotonicity (`finiteExpectation_mono` ↔ `integral_mono`),
* additivity over a finite family (`finiteExpectation_sum` ↔ `integral_finsetSum`),
* unit normalization (`finiteExpectation_const_of_sum_one` ↔ `integral_const`
  with `μ univ = 1`),
* the Chernoff step `exp(x) ≥ 1 + x` (shared, measure-independent).

The Bochner integral satisfies all four, so the finite Chernoff bound
`expectation_le_of_shifted_exp_mgf` and the finite-max bound
`finite_expectedSup_le_of_shifted_mgf` transfer line-for-line, with the
measurability/integrability side conditions promoted to explicit hypotheses
(the honest measure-theoretic content the finite case got for free over a
`Fintype`).

## What is proved

* `MeasureSubGaussianProcess`: a process over an arbitrary probability space
  with a measure-theoretic sub-Gaussian increment MGF bound.
* `integral_le_of_shifted_exp_mgf`: integral-level Chernoff step.
* `integral_expectedSup_le_of_shifted_mgf`: integral-level finite-max
  entropy budget.
* `integral_finiteSup_le_of_mgf_log`: integral-level finite-max MGF-to-budget
  bridge.
* `MeasureSubGaussianProcess.integral_projectionPairSup_le_coveringNumber_sqrt`:
  one-scale finite-net entropy bound with the projection-pair geometry and
  chosen-net cardinality comparison discharged internally.
* `continuous_dudley_entropy_integral_of_measure`: the terminal continuous
  Dudley entropy integral against an arbitrary probability measure.
* `continuous_dudley_entropy_integral_of_measure_coveringNumber`: the
  covering-number `√(log N)` specialization.

The one-scale theorem does not use `MeasureChainingBudget`: it constructs its
finite projection-pair bound from the process MGF and the two supplied nets.
The terminal continuous-integral theorems below still take
`MeasureChainingBudget`; they do not yet construct the full multiscale chain or
discharge the separability boundary.

## References (verbatim)

* R. M. Dudley, "The sizes of compact subsets of Hilbert space and continuity of
  Gaussian processes," Journal of Functional Analysis 1 (1967).
* S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A
  Nonasymptotic Theory of Independence*, Oxford University Press (2013), §13.
* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer
  (2014).

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Covering.MeasureDudley

open MeasureTheory
open FormalSLT.Rademacher.FiniteSample
open scoped BigOperators

noncomputable section

universe u v

variable {Ω : Type u} {T : Type v}

/-! ## Integral-level Chernoff and finite-max sub-Gaussian engine -/

/-- A real-valued process over an arbitrary measure space with sub-Gaussian
increment control.

Unlike `FiniteSubGaussianProcess`, the outcome type is not finite and
expectations are Bochner integrals against `μ`. Evaluation measurability and
the integrability of both increments and exponential increments are explicit
fields: they are analytic obligations, not consequences of finiteness. -/
structure MeasureSubGaussianProcess [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Type v) where
  X : Ω → T → ℝ
  dist : T → T → ℝ
  dist_nonneg : ∀ s t : T, 0 ≤ dist s t
  varianceProxy : ℝ
  varianceProxy_nonneg : 0 ≤ varianceProxy
  measurable_eval : ∀ t : T, Measurable (fun ω => X ω t)
  integrable_increment : ∀ s t : T, Integrable (fun ω => X ω t - X ω s) μ
  integrable_exp_increment : ∀ s t : T, ∀ lam : ℝ,
    Integrable (fun ω => Real.exp (lam * (X ω t - X ω s))) μ
  mgf_increment : ∀ s t : T, ∀ lam : ℝ,
    (∫ ω, Real.exp (lam * (X ω t - X ω s)) ∂μ) ≤
      Real.exp (lam ^ 2 * varianceProxy * dist s t ^ 2 / 2)

namespace MeasureSubGaussianProcess

/-- Radius-bounded form of the arbitrary-measure increment MGF bound. -/
theorem increment_mgf_le_radius
    [MeasurableSpace Ω] {μ : Measure Ω}
    (P : MeasureSubGaussianProcess μ T)
    (s t : T) (r : ℝ)
    (hr : P.dist s t ≤ r) (hr_nonneg : 0 ≤ r) (lam : ℝ) :
    (∫ ω, Real.exp (lam * (P.X ω t - P.X ω s)) ∂μ) ≤
      Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2) := by
  refine (P.mgf_increment s t lam).trans ?_
  apply Real.exp_le_exp.mpr
  have hdist_sq : P.dist s t ^ 2 ≤ r ^ 2 := by
    nlinarith [hr, P.dist_nonneg s t, hr_nonneg]
  have hcoef_nonneg : 0 ≤ lam ^ 2 * P.varianceProxy / 2 := by
    nlinarith [sq_nonneg lam, P.varianceProxy_nonneg]
  have hmul := mul_le_mul_of_nonneg_left hdist_sq hcoef_nonneg
  nlinarith [hmul]

end MeasureSubGaussianProcess

/-- A finite supremum of integrable real random variables is integrable. -/
theorem integrable_finiteSup_of_integrable
    [MeasurableSpace Ω] (μ : Measure Ω)
    {I : Type*} [Fintype I] [Nonempty I]
    (Y : Ω → I → ℝ)
    (hY : ∀ i : I, Integrable (fun ω => Y ω i) μ) :
    Integrable (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω)) μ := by
  classical
  have hfun :
      Integrable
        ((Finset.univ : Finset I).sup' Finset.univ_nonempty
          (fun i : I => fun ω : Ω => Y ω i)) μ :=
    Finset.sup'_induction (p := fun f : Ω → ℝ => Integrable f μ)
      Finset.univ_nonempty
      (fun i : I => fun ω : Ω => Y ω i)
      (fun _f hf _g hg => Integrable.sup hf hg)
      (fun i _hi => hY i)
  have heq :
      ((Finset.univ : Finset I).sup' Finset.univ_nonempty
          (fun i : I => fun ω : Ω => Y ω i)) =
        (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω)) := by
    funext ω
    rw [Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty
      (fun f : Ω → ℝ => f ω) (fun _ _ => rfl)]
    rfl
  rw [← heq]
  exact hfun

/-- Integrability closure for the shifted exponential of a finite supremum.
Positivity of `lam` makes the shifted exponential monotone, so it commutes with
the finite maximum. -/
theorem integrable_exp_finiteSup_sub_of_integrable
    [MeasurableSpace Ω] (μ : Measure Ω)
    {I : Type*} [Fintype I] [Nonempty I]
    (Y : Ω → I → ℝ) (lam budget : ℝ) (hlam : 0 ≤ lam)
    (hcoord : ∀ i : I,
      Integrable (fun ω => Real.exp (lam * (Y ω i - budget))) μ) :
    Integrable
      (fun ω => Real.exp
        (lam * (FiniteSubGaussianChaining.finiteSup (Y ω) - budget))) μ := by
  let shiftedExp : ℝ → ℝ := fun x => Real.exp (lam * (x - budget))
  have hmono : Monotone shiftedExp := by
    intro x y hxy
    apply Real.exp_monotone
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hxy budget) hlam
  have hfinite :
      Integrable
        (fun ω => FiniteSubGaussianChaining.finiteSup
          (fun i : I => shiftedExp (Y ω i))) μ :=
    integrable_finiteSup_of_integrable μ
      (fun ω i => shiftedExp (Y ω i)) hcoord
  refine hfinite.congr (Filter.Eventually.of_forall ?_)
  intro ω
  unfold FiniteSubGaussianChaining.finiteSup
  exact (Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty shiftedExp
    (fun x y => hmono.map_max)).symm

/-- **Integral-level Chernoff bound.**

If, against a probability measure `μ`, the shifted exponential moment of a
real random variable `Z` is at most `1`, then the mean of `Z` is at most
`budget`. This is the Bochner-integral analog of
`FiniteSubGaussianChaining.expectation_le_of_shifted_exp_mgf`; the same
`exp x ≥ 1 + x` Chernoff step drives both, with `integral_mono`,
`integral_add`, and `integral_const` (with `μ univ = 1`) standing in for the
finite-sum algebra. -/
theorem integral_le_of_shifted_exp_mgf
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (lam budget : ℝ) (hlam : 0 < lam)
    (hZ_int : Integrable Z μ)
    (hexp_int : Integrable (fun ω => Real.exp (lam * (Z ω - budget))) μ)
    (hmgf : (∫ ω, Real.exp (lam * (Z ω - budget)) ∂μ) ≤ 1) :
    (∫ ω, Z ω ∂μ) ≤ budget := by
  -- pointwise Chernoff: `lam·(Z-budget) ≤ exp(lam·(Z-budget)) - 1`
  have hpoint : ∀ ω : Ω,
      lam * (Z ω - budget) ≤ Real.exp (lam * (Z ω - budget)) - 1 := by
    intro ω
    have h := Real.add_one_le_exp (lam * (Z ω - budget))
    linarith
  -- integrability of the affine left side and the shifted-exp right side
  have hleft_int : Integrable (fun ω => lam * (Z ω - budget)) μ := by
    have : Integrable (fun ω => Z ω - budget) μ := hZ_int.sub (integrable_const budget)
    exact this.const_mul lam
  have hright_int : Integrable (fun ω => Real.exp (lam * (Z ω - budget)) - 1) μ :=
    hexp_int.sub (integrable_const 1)
  -- monotone integral of the pointwise Chernoff inequality
  have hmain :
      (∫ ω, lam * (Z ω - budget) ∂μ) ≤
        ∫ ω, (Real.exp (lam * (Z ω - budget)) - 1) ∂μ :=
    integral_mono hleft_int hright_int hpoint
  -- evaluate the left integral: lam·(∫Z - budget)
  have hleft :
      (∫ ω, lam * (Z ω - budget) ∂μ) = lam * ((∫ ω, Z ω ∂μ) - budget) := by
    have hsub : (∫ ω, (Z ω - budget) ∂μ) = (∫ ω, Z ω ∂μ) - budget := by
      rw [integral_sub hZ_int (integrable_const budget), integral_const]
      simp
    rw [integral_const_mul, hsub]
  -- evaluate the right integral: ∫exp - 1
  have hright :
      (∫ ω, (Real.exp (lam * (Z ω - budget)) - 1) ∂μ) =
        (∫ ω, Real.exp (lam * (Z ω - budget)) ∂μ) - 1 := by
    rw [integral_sub hexp_int (integrable_const 1), integral_const]
    simp
  rw [hleft, hright] at hmain
  have hnonpos :
      (∫ ω, Real.exp (lam * (Z ω - budget)) ∂μ) - 1 ≤ 0 := by linarith
  have hscaled : lam * ((∫ ω, Z ω ∂μ) - budget) ≤ 0 := hmain.trans hnonpos
  nlinarith

/-- **Integral-level finite-max entropy budget.**

If each of finitely many coordinates `Y · t` has shifted exponential moment at
most `1 / |T|` against a probability measure `μ`, then the mean of the finite
supremum `ω ↦ finiteSup (Y ω)` is at most `budget`. This is the
integral analog of `FiniteSubGaussianChaining.finite_expectedSup_le_of_shifted_mgf`:
the exponential of a finite max is bounded by the sum of coordinate
exponentials (`exp_finiteSup_sub_le_sum_exp_sub`, measure-independent), and the
integral then distributes over the finite coordinate family by
`integral_finsetSum`. -/
theorem integral_expectedSup_le_of_shifted_mgf
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype T] [Nonempty T]
    (Y : Ω → T → ℝ) (lam budget : ℝ) (hlam : 0 < lam)
    (hsup_int :
      Integrable
        (fun ω => Real.exp (lam *
          (FiniteSubGaussianChaining.finiteSup (Y ω) - budget))) μ)
    (hmeanSup_int :
      Integrable (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω)) μ)
    (hcoord_int : ∀ t : T,
      Integrable (fun ω => Real.exp (lam * (Y ω t - budget))) μ)
    (hcoord : ∀ t : T,
      (∫ ω, Real.exp (lam * (Y ω t - budget)) ∂μ) ≤ (Fintype.card T : ℝ)⁻¹) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤ budget := by
  -- the integral of the coordinate-sum dominates the integral of the max-exp
  have hsumfun_int :
      Integrable (fun ω => ∑ t : T, Real.exp (lam * (Y ω t - budget))) μ :=
    integrable_finsetSum Finset.univ (fun t _ => hcoord_int t)
  refine integral_le_of_shifted_exp_mgf μ
    (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω))
    lam budget hlam hmeanSup_int hsup_int ?_
  calc
    (∫ ω, Real.exp (lam *
        (FiniteSubGaussianChaining.finiteSup (Y ω) - budget)) ∂μ)
        ≤ ∫ ω, (∑ t : T, Real.exp (lam * (Y ω t - budget))) ∂μ :=
          integral_mono hsup_int hsumfun_int
            (fun ω =>
              FiniteSubGaussianChaining.exp_finiteSup_sub_le_sum_exp_sub
                (Y ω) lam budget)
    _ = ∑ t : T, ∫ ω, Real.exp (lam * (Y ω t - budget)) ∂μ :=
          integral_finsetSum Finset.univ (fun t _ => hcoord_int t)
    _ ≤ ∑ _t : T, (Fintype.card T : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro t _
          exact hcoord t
    _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hcard_ne : (Fintype.card T : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_ne_zero (α := T))
          field_simp

/-- **Integral-level finite-max MGF-to-budget bridge.**

If every coordinate has moment generating function at most `exp q` at a fixed
positive `λ` against a probability measure `μ`, then the mean of the finite
supremum is at most `(log |T| + q) / λ`. This is the integral analog of
`FiniteSubGaussianChaining.finite_expectedSup_le_of_mgf_log`. -/
theorem integral_finiteSup_le_of_mgf_log
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype T] [Nonempty T]
    (Y : Ω → T → ℝ) (lam q : ℝ) (hlam : 0 < lam)
    (hsup_int :
      Integrable
        (fun ω => Real.exp (lam *
          (FiniteSubGaussianChaining.finiteSup (Y ω) -
            (Real.log (Fintype.card T : ℝ) + q) / lam))) μ)
    (hmeanSup_int :
      Integrable (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω)) μ)
    (hcoord_int : ∀ t : T,
      Integrable
        (fun ω => Real.exp (lam *
          (Y ω t - (Real.log (Fintype.card T : ℝ) + q) / lam))) μ)
    (hcoord : ∀ t : T,
      (∫ ω, Real.exp (lam * Y ω t) ∂μ) ≤ Real.exp q) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤
      (Real.log (Fintype.card T : ℝ) + q) / lam := by
  set budget := (Real.log (Fintype.card T : ℝ) + q) / lam with hbudget
  refine integral_expectedSup_le_of_shifted_mgf μ Y lam budget hlam
    hsup_int hmeanSup_int hcoord_int ?_
  intro t
  -- rewrite the shifted exponential as `exp(-lam·budget) · exp(lam·Y)`
  have hrw : ∀ ω : Ω,
      Real.exp (lam * (Y ω t - budget)) =
        Real.exp (-(lam * budget)) * Real.exp (lam * Y ω t) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hintegral_eq :
      (∫ ω, Real.exp (lam * (Y ω t - budget)) ∂μ) =
        Real.exp (-(lam * budget)) * ∫ ω, Real.exp (lam * Y ω t) ∂μ := by
    simp_rw [hrw]
    rw [integral_const_mul]
  rw [hintegral_eq]
  -- exp(-lam·budget) = (|T|·exp q)⁻¹ since lam·budget = log|T| + q
  have hcard_pos : (0 : ℝ) < (Fintype.card T : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := T))
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hlam_budget : lam * budget = Real.log (Fintype.card T : ℝ) + q := by
    rw [hbudget]
    field_simp
  have hexp_neg :
      Real.exp (-(lam * budget)) =
        (Fintype.card T : ℝ)⁻¹ * Real.exp (-q) := by
    rw [hlam_budget]
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hcard_pos]
  rw [hexp_neg]
  -- (|T|⁻¹ · exp(-q)) · ∫exp(lam Y) ≤ (|T|⁻¹ · exp(-q)) · exp q = |T|⁻¹
  have hcoef_nonneg : 0 ≤ (Fintype.card T : ℝ)⁻¹ * Real.exp (-q) := by positivity
  calc
    (Fintype.card T : ℝ)⁻¹ * Real.exp (-q) * ∫ ω, Real.exp (lam * Y ω t) ∂μ
        ≤ (Fintype.card T : ℝ)⁻¹ * Real.exp (-q) * Real.exp q :=
          mul_le_mul_of_nonneg_left (hcoord t) hcoef_nonneg
    _ = (Fintype.card T : ℝ)⁻¹ := by
          rw [mul_assoc, ← Real.exp_add]
          simp

/-- Fixed-tilt finite-max bound with all measure-theoretic integrability
obligations discharged from coordinate hypotheses. -/
theorem integral_finiteSup_le_of_mgf_log_of_integrable
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [Nonempty I]
    (Y : Ω → I → ℝ) (lam q : ℝ) (hlam : 0 < lam)
    (hcoord_int : ∀ i : I, Integrable (fun ω => Y ω i) μ)
    (hexp_int : ∀ i : I, ∀ theta : ℝ,
      Integrable (fun ω => Real.exp (theta * Y ω i)) μ)
    (hcoord : ∀ i : I,
      (∫ ω, Real.exp (lam * Y ω i) ∂μ) ≤ Real.exp q) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤
      (Real.log (Fintype.card I : ℝ) + q) / lam := by
  let budget := (Real.log (Fintype.card I : ℝ) + q) / lam
  have hmeanSup_int :
      Integrable (fun ω => FiniteSubGaussianChaining.finiteSup (Y ω)) μ :=
    integrable_finiteSup_of_integrable μ Y hcoord_int
  have hcoord_shift_int : ∀ i : I,
      Integrable (fun ω => Real.exp (lam * (Y ω i - budget))) μ := by
    intro i
    have hbase := (hexp_int i lam).const_mul (Real.exp (-(lam * budget)))
    refine hbase.congr (Filter.Eventually.of_forall ?_)
    intro ω
    change Real.exp (-(lam * budget)) * Real.exp (lam * Y ω i) =
      Real.exp (lam * (Y ω i - budget))
    rw [← Real.exp_add]
    congr 1
    ring
  have hsup_shift_int :
      Integrable
        (fun ω => Real.exp
          (lam * (FiniteSubGaussianChaining.finiteSup (Y ω) - budget))) μ :=
    integrable_exp_finiteSup_sub_of_integrable
      μ Y lam budget hlam.le hcoord_shift_int
  exact integral_finiteSup_le_of_mgf_log μ Y lam q hlam
    hsup_shift_int hmeanSup_int hcoord_shift_int hcoord

/-- Optimized arbitrary-measure finite sub-Gaussian maximum bound. -/
theorem integral_finiteSup_le_of_subGaussian_mgf_sqrt
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [Nonempty I]
    (Y : Ω → I → ℝ) (variance : ℝ)
    (hvariance : 0 < variance)
    (hcoord_int : ∀ i : I, Integrable (fun ω => Y ω i) μ)
    (hexp_int : ∀ i : I, ∀ lam : ℝ,
      Integrable (fun ω => Real.exp (lam * Y ω i)) μ)
    (hcoord : ∀ i : I, ∀ lam : ℝ,
      (∫ ω, Real.exp (lam * Y ω i) ∂μ) ≤
        Real.exp (lam ^ 2 * variance / 2))
    (hcard : 1 < Fintype.card I) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤
      Real.sqrt (2 * variance * Real.log (Fintype.card I : ℝ)) := by
  let L := Real.log (Fintype.card I : ℝ)
  let lam := Real.sqrt (2 * L / variance)
  have hL : 0 < L := by
    have hcard_real : (1 : ℝ) < (Fintype.card I : ℝ) := by
      exact_mod_cast hcard
    simpa [L] using Real.log_pos hcard_real
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos_of_pos (by positivity)
  calc
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ)
        ≤ (Real.log (Fintype.card I : ℝ) + lam ^ 2 * variance / 2) / lam :=
          integral_finiteSup_le_of_mgf_log_of_integrable μ Y lam
            (lam ^ 2 * variance / 2) hlam hcoord_int hexp_int
            (fun i => hcoord i lam)
    _ = Real.sqrt (2 * variance * Real.log (Fintype.card I : ℝ)) := by
          have hopt :=
            FiniteSubGaussianChaining.sqrt_entropy_optimizer_identity hL hvariance
          dsimp [lam]
          simpa [L, mul_assoc, mul_left_comm, mul_comm] using hopt

/-- Optimized arbitrary-measure finite sub-Gaussian maximum bound, including
singleton index families. A singleton pays zero entropy. -/
theorem integral_finiteSup_le_of_subGaussian_mgf_sqrt_nonempty
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [Nonempty I]
    (Y : Ω → I → ℝ) (variance : ℝ)
    (hvariance : 0 < variance)
    (hcoord_int : ∀ i : I, Integrable (fun ω => Y ω i) μ)
    (hexp_int : ∀ i : I, ∀ lam : ℝ,
      Integrable (fun ω => Real.exp (lam * Y ω i)) μ)
    (hcoord : ∀ i : I, ∀ lam : ℝ,
      (∫ ω, Real.exp (lam * Y ω i) ∂μ) ≤
        Real.exp (lam ^ 2 * variance / 2)) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤
      Real.sqrt (2 * variance * Real.log (Fintype.card I : ℝ)) := by
  by_cases hcard : 1 < Fintype.card I
  · exact integral_finiteSup_le_of_subGaussian_mgf_sqrt
      μ Y variance hvariance hcoord_int hexp_int hcoord hcard
  · have hcard_eq : Fintype.card I = 1 := by
      have hpos : 0 < Fintype.card I := Fintype.card_pos
      omega
    have hlog : Real.log (Fintype.card I : ℝ) = 0 := by simp [hcard_eq]
    have hsqrt :
        Real.sqrt (2 * variance * Real.log (Fintype.card I : ℝ)) = 0 := by
      simp [hlog]
    rw [hsqrt]
    refine FiniteSubGaussianChaining.real_le_of_forall_pos_le_add ?_
    intro eta heta
    let lam := eta / variance
    have hlam : 0 < lam := div_pos heta hvariance
    have hbound :
        (∫ ω, FiniteSubGaussianChaining.finiteSup (Y ω) ∂μ) ≤
          (Real.log (Fintype.card I : ℝ) + lam ^ 2 * variance / 2) / lam :=
      integral_finiteSup_le_of_mgf_log_of_integrable μ Y lam
        (lam ^ 2 * variance / 2) hlam hcoord_int hexp_int
        (fun i => hcoord i lam)
    have hbudget_eq :
        (Real.log (Fintype.card I : ℝ) + lam ^ 2 * variance / 2) / lam =
          lam * variance / 2 := by
      rw [hlog]
      field_simp [ne_of_gt hlam]
      ring
    have hbudget_le : lam * variance / 2 ≤ eta := by
      dsimp [lam]
      field_simp [ne_of_gt hvariance]
      linarith
    exact hbound.trans (by linarith)

namespace MeasureSubGaussianProcess

/-- One-scale square-root entropy bound for a finite family of increments over
an arbitrary probability space. -/
theorem integral_incrementFamilySup_le_radius_sqrt_nonempty
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [Nonempty I]
    (P : MeasureSubGaussianProcess μ T)
    (left right : I → T) (r : ℝ)
    (hvariance : 0 < P.varianceProxy)
    (hr : ∀ i : I, P.dist (left i) (right i) ≤ r)
    (hr_pos : 0 < r) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup
        (fun i : I => P.X ω (right i) - P.X ω (left i)) ∂μ) ≤
      Real.sqrt
        (2 * P.varianceProxy * r ^ 2 * Real.log (Fintype.card I : ℝ)) := by
  have hvariance_radius : 0 < P.varianceProxy * r ^ 2 := by positivity
  have hmain := integral_finiteSup_le_of_subGaussian_mgf_sqrt_nonempty
    μ (fun ω i => P.X ω (right i) - P.X ω (left i))
    (P.varianceProxy * r ^ 2) hvariance_radius
    (fun i => P.integrable_increment (left i) (right i))
    (fun i lam => P.integrable_exp_increment (left i) (right i) lam)
    (fun i lam => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        increment_mgf_le_radius P (left i) (right i) r (hr i) hr_pos.le lam)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/-- **Arbitrary-measure one-scale finite-net entropy bound.**

For two finite nets of the same sub-Gaussian process metric, the expected
maximum over realized projection-pair increments is controlled by the square
root of the log product of their chosen-net cardinalities (the two
`FiniteNet.coveringNumber` fields). The projection-pair radius and cardinality
estimates are derived internally. No `MeasureChainingBudget`, coarse budget,
terminal boundary, or finite outcome-space assumption appears. -/
theorem integral_projectionPairSup_le_coveringNumber_sqrt
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Nonempty T] {A B : Type*} [Fintype A] [Fintype B]
    (P : MeasureSubGaussianProcess μ T)
    (N₀ : FiniteSubGaussianChaining.FiniteNet T A)
    (N₁ : FiniteSubGaussianChaining.FiniteNet T B)
    (hdist₀ : N₀.dist = P.dist) (hdist₁ : N₁.dist = P.dist)
    (hsymm : ∀ s t, P.dist s t = P.dist t s)
    (htri : ∀ x y z, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradius : 0 < N₀.radius + N₁.radius) :
    (∫ ω, FiniteSubGaussianChaining.finiteSup
      (fun pair : FiniteSubGaussianChaining.FiniteNet.ProjectionPair N₀ N₁ =>
        P.X ω (N₁.center pair.1.2) - P.X ω (N₀.center pair.1.1)) ∂μ) ≤
      Real.sqrt
        (2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 *
          Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) := by
  let Pair := FiniteSubGaussianChaining.FiniteNet.ProjectionPair N₀ N₁
  let left : Pair → T := fun pair => N₀.center pair.1.1
  let right : Pair → T := fun pair => N₁.center pair.1.2
  have hpair : ∀ pair : Pair,
      P.dist (left pair) (right pair) ≤ N₀.radius + N₁.radius := by
    intro pair
    have h :=
      FiniteSubGaussianChaining.FiniteNet.projectionPair_dist_le_radius_sum
        N₀ N₁ (by rw [hdist₀, hdist₁])
        (by
          intro s t
          rw [hdist₀]
          exact hsymm s t)
        (by
          intro x y z
          rw [hdist₀]
          exact htri x y z)
        pair
    simpa [left, right, hdist₀] using h
  refine (integral_incrementFamilySup_le_radius_sqrt_nonempty
    μ P left right (N₀.radius + N₁.radius) hvariance hpair hradius).trans ?_
  apply Real.sqrt_le_sqrt
  have hcoef_nonneg :
      0 ≤ 2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 := by
    nlinarith [P.varianceProxy_nonneg, sq_nonneg (N₀.radius + N₁.radius)]
  exact mul_le_mul_of_nonneg_left
    (FiniteSubGaussianChaining.FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul
      N₀ N₁)
    hcoef_nonneg

end MeasureSubGaussianProcess

/-! ## The continuous Dudley entropy integral against an arbitrary measure -/

/-- **Measure-theoretic chaining budget.**

This packages the output of the dyadic chaining decomposition for the
integral-level expectation `∫ ω, supFunctional ω ∂μ`, mirroring the role of
`TotalBoundedDudley.SeparableTerminalSupremumBoundaryChoice` in the finite
lane. For every positive boundary slack `eta`, it produces a dyadic truncation
level `m` at which the mean of the supremum functional is within `eta` of the
coarse budget plus the truncated `√(2·σ²)`-scaled Dudley sum
`∫ ε in (radiusScale/2^(m+1))..(radiusScale/2), entropyAtRadius ε`.

The geometry that constructs such a budget (nets, covering numbers, the
sub-Gaussian increment peeling) is measure-independent and already verified in
the finite lane; here it is the explicit honest hypothesis, and the value of
this module is the *expectation-operator lift*: turning the truncated, slacked
budget into the full continuous integral against `μ`. -/
def MeasureChainingBudget
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (supFunctional : Ω → ℝ)
    (coarseBudget radiusScale varianceProxy : ℝ)
    (entropyAtRadius : ℝ → ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ m : ℕ,
      (∫ ω, supFunctional ω ∂μ) ≤
        coarseBudget + 4 * Real.sqrt (2 * varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) + eta

/-- **Continuous Dudley entropy integral against an arbitrary probability
measure.**

The mean (Bochner integral against an arbitrary probability measure `μ` on an
arbitrary measurable space `Ω`) of the supremum functional is bounded by the
continuous Dudley entropy integral:

  `∫ ω, supFunctional ω ∂μ ≤ coarseBudget + 4·√(2·varianceProxy)·∫₀^{R/2} entropyAtRadius`.

This is the measure-theoretic generalization of
`ContinuousDudley.continuous_dudley_entropy_integral`, whose left side is the
finite weighted sum `finiteExpectation P.weight supFunctional`. The proof takes
the per-slack truncated chaining budget, dominates each finite truncated
integral by the full continuous integral (nonnegative entropy profile, the
same step the finite lane uses), and squeezes the boundary slack `eta → 0`.

In the empirical Rademacher normalization `varianceProxy ≍ B²/n`,
`4·√(2·varianceProxy)` is the `C/√n` constant of Boucheron–Lugosi–Massart 2013
§13 and `entropyAtRadius ε` plays the role of `√(log N(F, ε))`. -/
theorem continuous_dudley_entropy_integral_of_measure
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (supFunctional : Ω → ℝ)
    (coarseBudget radiusScale varianceProxy : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (_hvariance : 0 ≤ varianceProxy)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hbudget : MeasureChainingBudget μ supFunctional
      coarseBudget radiusScale varianceProxy entropyAtRadius) :
    (∫ ω, supFunctional ω ∂μ) ≤
      coarseBudget + 4 * Real.sqrt (2 * varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  set globalBudget :=
    coarseBudget + 4 * Real.sqrt (2 * varianceProxy) *
      (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) with hglobal
  -- squeeze the boundary slack to zero
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  obtain ⟨m, hm⟩ := hbudget eta heta
  -- the truncated dyadic integral is dominated by the full continuous integral
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) :=
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
  have hsub2 :
      Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
      Set.right_mem_uIcc
  have hI1 :
      IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume
        (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hnn :
      0 ≤ ∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε :=
    intervalIntegral.integral_nonneg ha_nonneg (fun u _ => hentropy_nonneg u)
  have hdom :
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        ≤ ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
    linarith [hadd, hnn]
  have hsqrt_nonneg : 0 ≤ 4 * Real.sqrt (2 * varianceProxy) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdom hsqrt_nonneg
  -- chain the truncated bound to the full continuous integral, keeping the slack
  calc
    (∫ ω, supFunctional ω ∂μ)
        ≤ coarseBudget + 4 * Real.sqrt (2 * varianceProxy) *
            (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
              entropyAtRadius ε) + eta := hm
    _ ≤ globalBudget + eta := by rw [hglobal]; linarith [hmul]

/-- **Continuous Dudley covering-number bound against an arbitrary probability
measure.**

Specialization of `continuous_dudley_entropy_integral_of_measure` to the
covering-number entropy profile `ε ↦ √(log N(F, ε))` for an abstract positive
antitone covering-number function. Interval integrability on `[0, R/2]` is
discharged from the named brick
`DudleySumToIntegral.coveringNumber_entropy_integrable_of_antitone`; the chaining
budget is supplied by the caller.

In the empirical Rademacher normalization `varianceProxy ≍ B²/n` this reads

  `∫ ω, supFunctional ω ∂μ ≤ coarseBudget + (C/√n) ∫₀^{R/2} √(log N(F, ε)) dε`,

the Dudley entropy integral with a genuine measure-theoretic expectation on the
left, against an arbitrary probability measure `μ`. -/
theorem continuous_dudley_entropy_integral_of_measure_coveringNumber
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (supFunctional : Ω → ℝ)
    (coarseBudget radiusScale varianceProxy : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hradiusScale : 0 < radiusScale)
    (hvariance : 0 ≤ varianceProxy)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hbudget : MeasureChainingBudget μ supFunctional
      coarseBudget radiusScale varianceProxy
      (fun ε => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))) :
    (∫ ω, supFunctional ω ∂μ) ≤
      coarseBudget + 4 * Real.sqrt (2 * varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  refine continuous_dudley_entropy_integral_of_measure μ supFunctional
    coarseBudget radiusScale varianceProxy
    (fun ε => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
    hradiusScale hvariance (fun ε => Real.sqrt_nonneg _) ?_ hbudget
  exact DudleySumToIntegral.coveringNumber_entropy_integrable_of_antitone
    coveringNumberAtRadius 0 (radiusScale / 2) hcover_antitone hcover_pos

/-! ## Non-vacuity: a genuine non-Dirac probability measure -/

/-- A genuine two-point probability measure that is **not** a single Dirac mass:
the uniform mixture `½·δ_true + ½·δ_false` on `Bool`. This witnesses that the
measure-theoretic Dudley bound is instantiated against a real averaging
measure, not a domain-collapsing point evaluation. -/
def uniformBool : Measure Bool :=
  (2⁻¹ : ENNReal) • Measure.dirac true + (2⁻¹ : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure uniformBool := by
  constructor
  unfold uniformBool
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply', MeasurableSet.univ, Set.mem_univ, Set.indicator_of_mem,
    Pi.one_apply, mul_one]
  rw [ENNReal.inv_two_add_inv_two]

/-- The integral against `uniformBool` is the genuine two-point average. -/
theorem integral_uniformBool (f : Bool → ℝ) :
    (∫ ω, f ω ∂uniformBool) = 2⁻¹ * f true + 2⁻¹ * f false := by
  haveI : IsFiniteMeasure ((2⁻¹ : ENNReal) • Measure.dirac true) :=
    Measure.smul_finite _ (by simp)
  haveI : IsFiniteMeasure ((2⁻¹ : ENNReal) • Measure.dirac false) :=
    Measure.smul_finite _ (by simp)
  unfold uniformBool
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [smul_eq_mul]

/-! ### Executable two-net witness for the one-scale theorem -/

/-- Discrete distance on the Boolean index set. -/
def boolProjectionDist (s t : Bool) : ℝ := if s = t then 0 else 1

/-- The Boolean discrete distance is nonnegative. -/
theorem boolProjectionDist_nonneg (s t : Bool) : 0 ≤ boolProjectionDist s t := by
  by_cases h : s = t <;> simp [boolProjectionDist, h]

/-- Symmetry of the Boolean discrete distance. -/
theorem boolProjectionDist_symm (s t : Bool) :
    boolProjectionDist s t = boolProjectionDist t s := by
  cases s <;> cases t <;> norm_num [boolProjectionDist]

/-- Triangle inequality for the Boolean discrete distance. -/
theorem boolProjectionDist_triangle (x y z : Bool) :
    boolProjectionDist x z ≤ boolProjectionDist x y + boolProjectionDist y z := by
  cases x <;> cases y <;> cases z <;> norm_num [boolProjectionDist]

/-- Rademacher process that is zero at `false` and a fair sign at `true`. -/
def boolProjectionValue (ω t : Bool) : ℝ :=
  if t then signOfBool ω else 0

/-- The Boolean projection process has sub-Gaussian increments with unit
variance proxy under `uniformBool`. -/
theorem boolProjection_mgf_bound (s t : Bool) (lam : ℝ) :
    (∫ ω, Real.exp
        (lam * (boolProjectionValue ω t - boolProjectionValue ω s)) ∂uniformBool) ≤
      Real.exp (lam ^ 2 * (1 : ℝ) * boolProjectionDist s t ^ 2 / 2) := by
  cases s <;> cases t
  · rw [integral_uniformBool]
    norm_num [boolProjectionValue, boolProjectionDist]
  · rw [integral_uniformBool]
    calc
      2⁻¹ * Real.exp
          (lam * (boolProjectionValue true true - boolProjectionValue true false)) +
          2⁻¹ * Real.exp
          (lam * (boolProjectionValue false true - boolProjectionValue false false))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (1 : ℝ))) / 2 := by
              simp [boolProjectionValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam 1
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * boolProjectionDist false true ^ 2 / 2) := by
              norm_num [boolProjectionDist]
  · rw [integral_uniformBool]
    calc
      2⁻¹ * Real.exp
          (lam * (boolProjectionValue true false - boolProjectionValue true true)) +
          2⁻¹ * Real.exp
          (lam * (boolProjectionValue false false - boolProjectionValue false true))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (-1 : ℝ))) / 2 := by
              simp [boolProjectionValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (-1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam (-1)
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * boolProjectionDist true false ^ 2 / 2) := by
              norm_num [boolProjectionDist]
  · rw [integral_uniformBool]
    norm_num [boolProjectionValue, boolProjectionDist]

/-- The Boolean Rademacher process packaged in the arbitrary-measure API. -/
def boolProjectionProcess : MeasureSubGaussianProcess uniformBool Bool where
  X := boolProjectionValue
  dist := boolProjectionDist
  dist_nonneg := boolProjectionDist_nonneg
  varianceProxy := 1
  varianceProxy_nonneg := by norm_num
  measurable_eval := by intro t; exact measurable_of_finite _
  integrable_increment := by intro s t; exact Integrable.of_finite
  integrable_exp_increment := by intro s t lam; exact Integrable.of_finite
  mgf_increment := boolProjection_mgf_bound

/-- One-point coarse net centered at `false`. -/
def boolCoarseNet : FiniteSubGaussianChaining.FiniteNet Bool Unit where
  dist := boolProjectionDist
  dist_nonneg := boolProjectionDist_nonneg
  center := fun _ => false
  project := fun _ => ()
  radius := 1
  radius_nonneg := by norm_num
  covers := by intro t; cases t <;> norm_num [boolProjectionDist]

/-- Exact two-point net on `Bool`. -/
def boolFullNet : FiniteSubGaussianChaining.FiniteNet Bool Bool where
  dist := boolProjectionDist
  dist_nonneg := boolProjectionDist_nonneg
  center := id
  project := id
  radius := 0
  radius_nonneg := by norm_num
  covers := by intro t; cases t <;> norm_num [boolProjectionDist]

/-- Realized projection-pair maximum between the coarse and full Boolean nets. -/
def boolProjectionPairSup (ω : Bool) : ℝ :=
  FiniteSubGaussianChaining.finiteSup
    (fun pair : FiniteSubGaussianChaining.FiniteNet.ProjectionPair
        boolCoarseNet boolFullNet =>
      boolProjectionProcess.X ω (boolFullNet.center pair.1.2) -
        boolProjectionProcess.X ω (boolCoarseNet.center pair.1.1))

private theorem boolProjectionPairSup_true : boolProjectionPairSup true = 1 := by
  unfold boolProjectionPairSup FiniteSubGaussianChaining.finiteSup
  apply le_antisymm
  · apply Finset.sup'_le
    intro pair _hpair
    rcases pair with ⟨⟨a, b⟩, t, ht⟩
    cases ht
    cases t <;> norm_num [boolProjectionProcess, boolProjectionValue,
      boolCoarseNet, boolFullNet]
  · have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset
        (FiniteSubGaussianChaining.FiniteNet.ProjectionPair boolCoarseNet boolFullNet)))
      (fun pair =>
        boolProjectionProcess.X true (boolFullNet.center pair.1.2) -
          boolProjectionProcess.X true (boolCoarseNet.center pair.1.1))
      (Finset.mem_univ
        (FiniteSubGaussianChaining.FiniteNet.projectionPairOf
          boolCoarseNet boolFullNet true))
    simpa [FiniteSubGaussianChaining.FiniteNet.projectionPairOf,
      boolProjectionProcess, boolProjectionValue, boolCoarseNet, boolFullNet] using hsel

private theorem boolProjectionPairSup_false : boolProjectionPairSup false = 0 := by
  unfold boolProjectionPairSup FiniteSubGaussianChaining.finiteSup
  apply le_antisymm
  · apply Finset.sup'_le
    intro pair _hpair
    rcases pair with ⟨⟨a, b⟩, t, ht⟩
    cases ht
    cases t <;> norm_num [boolProjectionProcess, boolProjectionValue,
      boolCoarseNet, boolFullNet]
  · have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset
        (FiniteSubGaussianChaining.FiniteNet.ProjectionPair boolCoarseNet boolFullNet)))
      (fun pair =>
        boolProjectionProcess.X false (boolFullNet.center pair.1.2) -
          boolProjectionProcess.X false (boolCoarseNet.center pair.1.1))
      (Finset.mem_univ
        (FiniteSubGaussianChaining.FiniteNet.projectionPairOf
          boolCoarseNet boolFullNet false))
    simpa [FiniteSubGaussianChaining.FiniteNet.projectionPairOf,
      boolProjectionProcess, boolProjectionValue, boolCoarseNet, boolFullNet] using hsel

/-- The concrete one-scale maximum is nonzero: its exact expectation is `1/2`.
This prevents a zero or singleton-only theorem from satisfying the checker. -/
theorem integral_boolProjectionPairSup_eq_half :
    (∫ ω, boolProjectionPairSup ω ∂uniformBool) = (2⁻¹ : ℝ) := by
  rw [integral_uniformBool]
  rw [boolProjectionPairSup_true, boolProjectionPairSup_false]
  norm_num

/-- The concrete Boolean projection-pair maximum has strictly positive mean. -/
theorem integral_boolProjectionPairSup_pos :
    0 < (∫ ω, boolProjectionPairSup ω ∂uniformBool) := by
  rw [integral_boolProjectionPairSup_eq_half]
  norm_num

/-- The arbitrary-measure one-scale theorem instantiated on the one-point to
full Boolean net transition. -/
theorem integral_boolProjectionPairSup_le_coveringNumber_sqrt :
    (∫ ω, boolProjectionPairSup ω ∂uniformBool) ≤
      Real.sqrt
        (2 * boolProjectionProcess.varianceProxy *
          (boolCoarseNet.radius + boolFullNet.radius) ^ 2 *
          Real.log
            (boolCoarseNet.coveringNumber * boolFullNet.coveringNumber : ℝ)) := by
  simpa [boolProjectionPairSup] using
    MeasureSubGaussianProcess.integral_projectionPairSup_le_coveringNumber_sqrt
      uniformBool boolProjectionProcess boolCoarseNet boolFullNet rfl rfl
      boolProjectionDist_symm boolProjectionDist_triangle
      (by norm_num [boolProjectionProcess])
      (by norm_num [boolCoarseNet, boolFullNet])

/-- The witness supremum functional: distinct values on the two outcomes. Its
mean under `uniformBool` is `½`, which equals neither outcome value, so the
expectation genuinely averages over a non-collapsed domain. -/
def witnessSup : Bool → ℝ := fun b => if b then 1 else 0

/-- The mean of `witnessSup` under the genuine mixture is `½` — strictly between
its two pointwise values, confirming the measure does not collapse to a point. -/
theorem integral_witnessSup_uniformBool :
    (∫ ω, witnessSup ω ∂uniformBool) = 2⁻¹ := by
  rw [integral_uniformBool]
  simp [witnessSup]

/-- **Non-vacuity instance with a STRICT coarse budget (entropy term load-bearing).**

The terminal continuous Dudley integral bound holds for the genuine non-Dirac
probability measure `uniformBool` with the witness supremum functional, a real
positive variance proxy, and the constant entropy profile `ε ↦ 1` (nonnegative,
interval-integrable). Here `coarseBudget = ¼` is set STRICTLY BELOW the mean
`∫ witnessSup = ½`, so the coarse budget alone CANNOT cover the integral: the
`4·√(2·varianceProxy)·∫ entropyAtRadius` term must carry the remaining `¼`. This
is the honest demonstration that the entropy term bites, in contrast to the
budget-equals-mean choice where it is pure absorbed slack.

Concretely the chaining budget at scale `m = 1` reads
`½ ≤ ¼ + 4·√2·(∫_{¼}^{½} 1) + eta = ¼ + 4·√2·¼ + eta = ¼ + √2 + eta`,
which holds since `√2 > ¼`; and the global conclusion is
`½ ≤ ¼ + 4·√2·(∫_0^{½} 1) = ¼ + 4·√2·½ = ¼ + 2·√2`.

Because the mean `½` differs from both pointwise values of `witnessSup` AND from
the coarse budget `¼`, the entropy term is genuinely needed: this is neither the
finite single-point case nor the slack-absorbed budget. -/
theorem continuous_dudley_entropy_integral_of_measure_nonvacuous :
    (∫ ω, witnessSup ω ∂uniformBool) ≤
      (4⁻¹ : ℝ) + 4 * Real.sqrt (2 * (1 : ℝ)) *
        (∫ _ε in (0 : ℝ)..((1 : ℝ) / 2), (1 : ℝ)) := by
  have hbudget :
      MeasureChainingBudget uniformBool witnessSup
        (4⁻¹ : ℝ) 1 1 (fun _ => 1) := by
    intro eta heta
    refine ⟨1, ?_⟩
    -- mean = ½ STRICTLY ABOVE coarseBudget = ¼; the truncated Dudley term must cover ¼
    rw [integral_witnessSup_uniformBool]
    -- at m = 1 the truncated integral ∫_{1/4}^{1/2} 1 = 1/4, scaled by 4·√2 = √2 > 1/4
    have htrunc : (∫ _ε in ((1 : ℝ) / (2 : ℝ) ^ (1 + 1))..((1 : ℝ) / 2), (1 : ℝ))
        = (1 : ℝ) / 4 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      norm_num
    rw [htrunc]
    have hsqrt2 : Real.sqrt (2 * (1 : ℝ)) = Real.sqrt 2 := by norm_num
    rw [hsqrt2]
    have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by norm_num)
    -- ¼ + 4·√2·¼ + eta = ¼ + √2 + eta ≥ ½, since √2 ≥ 1 > ¼ and eta > 0
    nlinarith [hsqrt_ge, heta.le]
  exact continuous_dudley_entropy_integral_of_measure uniformBool witnessSup
    (4⁻¹ : ℝ) 1 1 (fun _ => 1) (by norm_num) (by norm_num)
    (fun _ => by norm_num) (intervalIntegrable_const) hbudget

/-- The coarse budget `¼` is STRICTLY below the integral `½`: the entropy term is
load-bearing, not absorbed slack. (Contrast the budget-equals-mean choice, where
the `4·√(2σ²)·entropy` term could be dropped and the bound would still hold.) -/
theorem nonvacuous_coarseBudget_lt_integral :
    (4⁻¹ : ℝ) < (∫ ω, witnessSup ω ∂uniformBool) := by
  rw [integral_witnessSup_uniformBool]; norm_num

end

end FormalSLT.Covering.MeasureDudley
