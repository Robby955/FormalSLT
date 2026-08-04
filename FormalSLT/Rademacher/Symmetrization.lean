import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import FormalSLT.Risk
import FormalSLT.Rademacher.FiniteSample
import FormalSLT.GhostSample
import FormalSLT.Rademacher.Decoupling

/-!
# Expected finite-sample Rademacher symmetrization (Stage 3)

Combines Stage 1 (`FiniteSampleGhostSampleReplacement`) and Stage 2
(`RademacherDecoupling`) into the recognizable expected symmetrization
theorem for finite hypothesis classes:

```
E_S sup_h ( risk(h) − R̂_S(h) )
  ≤ 2 · E_S R̂ad_n(ℓ ∘ H, S)
```

where `S` is an iid sample of size `n` drawn from a probability measure
`μ`, `H` is a finite nonempty hypothesis class, and the loss `ℓ i` is
measurable and bounded `|ℓ i z| ≤ B` for some `0 ≤ B`.

Proof strategy: pure transitivity through Stage 1 and Stage 2.

```
∫ genGap dπ
  ≤ ∫ ∫ decoupledGap dπ dπ        — Stage 1
  =  ∫ decoupledGap d(π × π)      — Fubini (`MeasureTheory.integral_prod`)
  ≤ 2 · ∫ R̂ad_n dπ                — Stage 2
```

What this module provides:

* `expected_genGap_le_two_expected_empiricalRademacherComplexity`
  — the Stage 3 final theorem.

Out of scope:

* High-probability Rademacher generalization (no McDiarmid, no
  bounded-differences inequality).
* Massart finite-class Rademacher bound.
* VC-to-PAC sample complexity.
* Algorithmic stability.
* PAC-Bayes.
* Uncountable hypothesis classes, separability, contraction.
* No manifest entry. Integration with the Lean manifest, the
  Rademacher complexity / symmetrization page, and the `/lean`
  dashboard is deferred to a follow-up PR.
-/

namespace FormalSLT.Rademacher.Symmetrization

open MeasureTheory
open scoped BigOperators
open FormalSLT.GhostSample
  (piMeasure genGap decoupledGap expected_genGap_le_expected_decoupledGap)
open FormalSLT.Rademacher.Decoupling
  (expected_decoupledGap_le_two_expected_empiricalRademacherComplexity)
open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity)

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Z : Type*} [MeasurableSpace Z]
variable {n : ℕ}

/-! ### Joint integrability of `decoupledGap` on the iid product -/

/-- `decoupledGap ℓ p.1 p.2` is jointly measurable on
`(Fin n → Z) × (Fin n → Z)`. Each component (the per-`i` empirical-risk
difference) is measurable as a finite arithmetic combination of
coordinate projections of `ℓ`; the finite supremum is then measurable. -/
private lemma measurable_decoupledGap_joint
    {ℓ : ι → Z → ℝ} (hℓ_meas : ∀ i, Measurable (ℓ i)) :
    Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
      decoupledGap ℓ p.1 p.2) := by
  have h_each : ∀ i : ι,
      Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i) := by
    intro i
    refine Measurable.sub ?_ ?_
    · unfold Risk.empiricalRisk
      refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_snd)
    · unfold Risk.empiricalRisk
      refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact (hℓ_meas i).comp ((measurable_pi_apply k).comp measurable_fst)
  have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
    (f := fun i (p : (Fin n → Z) × (Fin n → Z)) =>
      Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i)
    Finset.univ_nonempty (fun i _ => h_each i)
  convert h_pi using 1
  ext p
  unfold decoupledGap
  simp [Finset.sup'_apply]

omit [MeasurableSpace Z] in
/-- Boundedness of `decoupledGap` on the iid product by `2B`, mirroring
Stage 1's univariate `abs_decoupledGap_le`. -/
private lemma abs_decoupledGap_joint_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) (hn : 0 < n)
    (p : (Fin n → Z) × (Fin n → Z)) :
    |decoupledGap ℓ p.1 p.2| ≤ 2 * B := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  -- Bound each |R̂_{S'} ℓ i| ≤ B and |R̂_S ℓ i| ≤ B.
  have h_emp_bdd : ∀ (z : Fin n → Z) (i : ι),
      |Risk.empiricalRisk z ℓ i| ≤ B := by
    intro z i
    unfold Risk.empiricalRisk
    rw [abs_mul, abs_inv, Nat.abs_cast]
    have h_sum_le : |∑ k : Fin n, ℓ i (z k)| ≤ (n : ℝ) * B := by
      calc |∑ k : Fin n, ℓ i (z k)|
          ≤ ∑ k : Fin n, |ℓ i (z k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, B :=
            Finset.sum_le_sum (fun k _ => hℓ_bdd i (z k))
        _ = (n : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
    calc ((n : ℝ))⁻¹ * |∑ k : Fin n, ℓ i (z k)|
        ≤ ((n : ℝ))⁻¹ * ((n : ℝ) * B) := by
          exact mul_le_mul_of_nonneg_left h_sum_le (by positivity)
      _ = B := by field_simp
  -- Bound each i-component.
  have h_each_le : ∀ i : ι,
      Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i ≤ 2 * B := by
    intro i
    have h1 : Risk.empiricalRisk p.2 ℓ i ≤ B := (abs_le.mp (h_emp_bdd p.2 i)).2
    have h2 : -B ≤ Risk.empiricalRisk p.1 ℓ i := (abs_le.mp (h_emp_bdd p.1 i)).1
    linarith
  have h_each_ge : ∀ i : ι,
      -(2 * B) ≤ Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i := by
    intro i
    have h1 : -B ≤ Risk.empiricalRisk p.2 ℓ i := (abs_le.mp (h_emp_bdd p.2 i)).1
    have h2 : Risk.empiricalRisk p.1 ℓ i ≤ B := (abs_le.mp (h_emp_bdd p.1 i)).2
    linarith
  -- Pull through the sup'.
  unfold decoupledGap
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Lower bound: -(2B) ≤ sup.
    refine le_trans (h_each_ge i₀) ?_
    exact Finset.le_sup' (s := (Finset.univ : Finset ι))
      (f := fun i => Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i)
      (Finset.mem_univ i₀)
  · -- Upper bound: sup ≤ 2B.
    exact Finset.sup'_le (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
      (fun i => Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i)
      (fun i _ => h_each_le i)

/-- Bounded measurable functions are integrable on a finite measure. -/
private lemma integrable_of_bounded_meas {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} {B : ℝ} (hf_meas : Measurable f) (hf_bdd : ∀ a, |f a| ≤ B) :
    Integrable f ν := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := B) ?_
  refine Filter.Eventually.of_forall (fun a => ?_)
  exact (Real.norm_eq_abs (f a)) ▸ hf_bdd a

/-- Joint integrability of `decoupledGap` on the iid product. -/
private lemma integrable_decoupledGap_joint
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B) (hn : 0 < n) :
    Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
      decoupledGap ℓ p.1 p.2) ((piMeasure μ n).prod (piMeasure μ n)) :=
  integrable_of_bounded_meas (B := 2 * B) _
    (measurable_decoupledGap_joint hℓ_meas)
    (abs_decoupledGap_joint_le hB hℓ_bdd hn)

/-! ### Stage 3 final theorem -/

/-- **Expected finite-sample Rademacher symmetrization (Stage 3).**

For a finite, nonempty hypothesis class with bounded measurable real-valued
losses `|ℓ i z| ≤ B` (with `0 ≤ B`) against an iid sample of size `n ≥ 1`
from a probability measure `μ`, the expected worst-case generalization gap
is bounded by twice the expected empirical Rademacher complexity:

```
E_S sup_h (risk(h) − R̂_S(h))  ≤  2 · E_S R̂ad_n(ℓ ∘ H, S)
```

Proof: chain Stage 1 (ghost-sample replacement) and Stage 2 (Rademacher
decoupling) by transitivity, after converting Stage 1's iterated integral
to Stage 2's joint integral via Fubini. -/
theorem expected_genGap_le_two_expected_empiricalRademacherComplexity
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
      ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := by
  -- Stage 1: E_S genGap ≤ E_S E_{S'} decoupledGap.
  have h1 :
      ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
        ≤ ∫ S, ∫ S', decoupledGap ℓ S S' ∂(piMeasure μ n)
              ∂(piMeasure μ n) :=
    expected_genGap_le_expected_decoupledGap μ ℓ hB hℓ_meas hℓ_bdd hn
  -- Fubini: iterated integral = joint integral against the product measure.
  have h_int :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) =>
        decoupledGap ℓ p.1 p.2) ((piMeasure μ n).prod (piMeasure μ n)) :=
    integrable_decoupledGap_joint μ hB hℓ_meas hℓ_bdd hn
  have h_fubini :
      ∫ p, decoupledGap ℓ p.1 p.2 ∂((piMeasure μ n).prod (piMeasure μ n))
        = ∫ S, ∫ S', decoupledGap ℓ S S' ∂(piMeasure μ n)
              ∂(piMeasure μ n) :=
    MeasureTheory.integral_prod _ h_int
  -- Stage 2: E_{(S,S')} decoupledGap ≤ 2 · E_S R̂ad_n.
  have h2 :
      ∫ p, decoupledGap ℓ p.1 p.2 ∂((piMeasure μ n).prod (piMeasure μ n))
        ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) :=
    expected_decoupledGap_le_two_expected_empiricalRademacherComplexity
      μ ℓ hB hℓ_meas hℓ_bdd hn
  -- Transitivity.
  linarith [h1, h_fubini, h2]

end FormalSLT.Rademacher.Symmetrization
