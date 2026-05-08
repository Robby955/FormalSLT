import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import FormalSLT.Risk

/-!
# Ghost-sample replacement in expectation (Stage 1 of finite-sample
symmetrization)

This module formalizes the *ghost-sample replacement* step of the classical
symmetrization argument for empirical processes. Given an iid sample `S` of
size `n` from a probability measure `μ` and a finite hypothesis class with
bounded loss, the ghost-sample replacement asserts:

```
E_S sup_h ( risk μ ℓ h − empiricalRisk S ℓ h )
  ≤ E_S E_{S'} sup_h ( empiricalRisk S' ℓ h − empiricalRisk S ℓ h )
```

This is *only* the ghost-sample step. It is **not** the Rademacher
symmetrization theorem — the right-hand side is still the expected supremum
over a non-symmetrized double-sample functional, not a Rademacher
complexity. Stage 2 of the chain (sign-vector decoupling) introduces the
Rademacher signs and produces the factor-of-two bound by an expected
empirical Rademacher complexity.

What this module provides (all closed, no `sorry`, no `admit`):

* `piMeasure μ n` — the iid product measure `μ^n` on `Fin n → Z`.
* `expected_empiricalRisk_eq_risk` — Fubini-style identity:
  `∫ S, empiricalRisk S ℓ h ∂(piMeasure μ n) = risk μ ℓ h`.
* `expected_genGap_le_expected_decoupledGap` — the ghost-sample replacement
  inequality, in expected form.

Hypotheses kept minimal:

* `[Fintype ι] [Nonempty ι]` — finite, nonempty hypothesis class.
* `(μ : Measure Z) [IsProbabilityMeasure μ]` — population law.
* `(ℓ : ι → Z → ℝ)` — real-valued loss.
* `(B : ℝ)` and `hℓ_bdd : ∀ i z, |ℓ i z| ≤ B` — bounded loss.
* `(hℓ_meas : ∀ i, Measurable (ℓ i))` — measurability per hypothesis.
* `(hn : 0 < n)` — nonempty sample.

Out of scope for this module (deferred to later PRs):

- The Rademacher decoupling step (introduces sign vectors and produces
  the factor 2 · `empiricalRademacherComplexity`).
- The combined expected symmetrization theorem.
- Any high-probability bound (no McDiarmid, no sub-Gaussian tail).
- Uncountable hypothesis classes, separability hypotheses, ε-net
  arguments, or contraction lemmas.
-/

namespace FormalSLT.GhostSample

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Z : Type*} [MeasurableSpace Z]

/-! ### Product (iid) measure on samples of size `n` -/

/-- The iid product measure `μ^n` on `Fin n → Z`. Each coordinate is an
independent draw from `μ`. -/
noncomputable def piMeasure (μ : Measure Z) (n : ℕ) : Measure (Fin n → Z) :=
  Measure.pi (fun _ : Fin n => μ)

instance instIsProbabilityMeasurePi
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (piMeasure μ n) := by
  unfold piMeasure
  infer_instance

/-! ### Bounded-loss helpers -/

/-- A bounded measurable real-valued function is integrable against any
finite measure. -/
private lemma integrable_of_bounded_measurable
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} {B : ℝ} (hf_meas : Measurable f) (hf_bdd : ∀ a, |f a| ≤ B) :
    Integrable f ν := by
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := B) ?_
  refine Filter.Eventually.of_forall (fun a => ?_)
  exact (Real.norm_eq_abs (f a)) ▸ hf_bdd a

set_option linter.unusedSectionVars false in
/-- A bounded measurable family of losses is integrable against any
probability measure. -/
private lemma integrable_loss_of_bounded
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ}
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (i : ι) : Integrable (ℓ i) μ :=
  integrable_of_bounded_measurable μ (hℓ_meas i) (hℓ_bdd i)

set_option linter.unusedSectionVars false in
/-- The empirical risk of any hypothesis on any sample is bounded by `B` in
absolute value, when the loss is bounded by `B`. -/
private lemma abs_empiricalRisk_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (_hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (z : Fin n → Z) (i : ι) :
    |Risk.empiricalRisk z ℓ i| ≤ B := by
  unfold Risk.empiricalRisk
  rw [abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg n)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_sum_abs : |∑ k : Fin n, ℓ i (z k)| ≤ (n : ℝ) * B := by
    calc |∑ k : Fin n, ℓ i (z k)|
        ≤ ∑ k : Fin n, |ℓ i (z k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, B := Finset.sum_le_sum (fun k _ => hℓ_bdd i (z k))
      _ = (n : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((n : ℝ))⁻¹ * |∑ k : Fin n, ℓ i (z k)|
        = (n : ℝ)⁻¹ * |∑ k : Fin n, ℓ i (z k)| from rfl]
  calc (n : ℝ)⁻¹ * |∑ k : Fin n, ℓ i (z k)|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * B) :=
        mul_le_mul_of_nonneg_left h_sum_abs (inv_nonneg.mpr hn_pos.le)
    _ = B := by field_simp

/-! ### Fubini-style identity for empirical risk -/

set_option linter.unusedSectionVars false in
/-- The pi-measure-integrability of `(fun S : Fin n → Z => ℓ (S k))` for any
single coordinate `k`. -/
private lemma integrable_loss_eval
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    {n : ℕ} (i : ι) (k : Fin n) :
    Integrable (fun S : Fin n → Z => ℓ i (S k)) (piMeasure μ n) := by
  unfold piMeasure
  exact integrable_comp_eval (hℓ_int i)

/-- The pi-measure-integrability of `empiricalRisk · ℓ i`. -/
private lemma integrable_empiricalRisk
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    {n : ℕ} (i : ι) :
    Integrable (fun S : Fin n → Z => Risk.empiricalRisk S ℓ i) (piMeasure μ n) := by
  unfold Risk.empiricalRisk
  refine Integrable.const_mul ?_ ((n : ℝ)⁻¹)
  exact integrable_finsetSum _ (fun k _ => integrable_loss_eval μ hℓ_int i k)

/-- **Expected empirical risk equals population risk.** A direct Fubini /
coordinate-projection argument: each `(fun S => ℓ i (S k))` integrates to
`risk μ ℓ i`, the sum gives `n · risk`, and the `(1/n)` rescaling cancels. -/
theorem expected_empiricalRisk_eq_risk
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_int : ∀ i, Integrable (ℓ i) μ)
    {n : ℕ} (hn : 0 < n) (i : ι) :
    ∫ S, Risk.empiricalRisk S ℓ i ∂(piMeasure μ n) = Risk.risk μ ℓ i := by
  -- Establish the per-coordinate identity ∫ S, ℓ i (S k) = ∫ z, ℓ i z.
  have h_per_coord : ∀ k : Fin n,
      ∫ S, ℓ i (S k) ∂(piMeasure μ n) = ∫ z, ℓ i z ∂μ := by
    intro k
    unfold piMeasure
    exact integral_comp_eval (hℓ_meas i).aestronglyMeasurable
  -- Sum-of-integrals = integral-of-sum (Fubini).
  have h_int_eval : ∀ k : Fin n,
      Integrable (fun S : Fin n → Z => ℓ i (S k)) (piMeasure μ n) :=
    fun k => integrable_loss_eval μ hℓ_int i k
  have h_sum :
      ∫ S, (∑ k : Fin n, ℓ i (S k)) ∂(piMeasure μ n)
        = ∑ k : Fin n, ∫ S, ℓ i (S k) ∂(piMeasure μ n) :=
    integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun k _ => h_int_eval k)
  -- Now compute the empirical risk integral.
  unfold Risk.empiricalRisk Risk.risk
  rw [integral_const_mul, h_sum]
  simp only [h_per_coord]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  field_simp

/-! ### Ghost-sample replacement -/

/-- The *generalization gap* over the finite hypothesis class: the largest
population-minus-empirical risk gap. -/
noncomputable def genGap
    (μ : Measure Z) (ℓ : ι → Z → ℝ) {n : ℕ} (S : Fin n → Z) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i)

/-- The *decoupled gap* on a sample-ghost-sample pair: the largest
ghost-empirical-minus-empirical risk gap. -/
noncomputable def decoupledGap
    (ℓ : ι → Z → ℝ) {n : ℕ} (S S' : Fin n → Z) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i)

/-! ### Measurability and integrability of the suprema -/

/-- Measurability of the decoupled gap as a function of the ghost sample
(with the training sample held fixed). Each component is measurable as a
finite arithmetic combination of coordinate projections of `ℓ`. The finite
supremum of measurable functions is measurable. -/
private lemma measurable_decoupledGap_in_ghost
    {ℓ : ι → Z → ℝ} (hℓ_meas : ∀ i, Measurable (ℓ i))
    {n : ℕ} (S : Fin n → Z) :
    Measurable (fun S' : Fin n → Z => decoupledGap ℓ S S') := by
  have h_each : ∀ i : ι,
      Measurable (fun S' : Fin n → Z =>
        Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i) := by
    intro i
    refine Measurable.sub ?_ measurable_const
    unfold Risk.empiricalRisk
    refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact (hℓ_meas i).comp (measurable_pi_apply k)
  have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
    (f := fun i (S' : Fin n → Z) =>
      Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i)
    Finset.univ_nonempty (fun i _ => h_each i)
  convert h_pi using 1
  ext S'
  unfold decoupledGap
  simp [Finset.sup'_apply]

/-- Boundedness of the decoupled gap by `2B` when the loss is bounded by
`B`. -/
private lemma abs_decoupledGap_le
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S S' : Fin n → Z) :
    |decoupledGap ℓ S S'| ≤ 2 * B := by
  -- Bound each component by 2B, then take sup and take min on the negative side.
  have h_each_le_2B : ∀ i : ι,
      Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i ≤ 2 * B := by
    intro i
    have h1 : Risk.empiricalRisk S' ℓ i ≤ B := by
      have := abs_empiricalRisk_le hB hℓ_bdd hn S' i
      linarith [abs_le.mp this]
    have h2 : -B ≤ Risk.empiricalRisk S ℓ i := by
      have := abs_empiricalRisk_le hB hℓ_bdd hn S i
      linarith [abs_le.mp this]
    linarith
  have h_each_ge_neg_2B : ∀ i : ι,
      -(2 * B) ≤ Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i := by
    intro i
    have h1 : -B ≤ Risk.empiricalRisk S' ℓ i := by
      have := abs_empiricalRisk_le hB hℓ_bdd hn S' i
      linarith [abs_le.mp this]
    have h2 : Risk.empiricalRisk S ℓ i ≤ B := by
      have := abs_empiricalRisk_le hB hℓ_bdd hn S i
      linarith [abs_le.mp this]
    linarith
  -- Now bound the sup.
  have h_sup_le : decoupledGap ℓ S S' ≤ 2 * B := by
    unfold decoupledGap
    refine Finset.sup'_le _ _ (fun i _ => h_each_le_2B i)
  -- And bound the sup from below using one element.
  have h_sup_ge : -(2 * B) ≤ decoupledGap ℓ S S' := by
    unfold decoupledGap
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have h_le_sup :
        Risk.empiricalRisk S' ℓ i₀ - Risk.empiricalRisk S ℓ i₀
          ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i) :=
      Finset.le_sup'
        (f := fun j => Risk.empiricalRisk S' ℓ j - Risk.empiricalRisk S ℓ j)
        (s := (Finset.univ : Finset ι)) (Finset.mem_univ i₀)
    linarith [h_each_ge_neg_2B i₀]
  rw [abs_le]
  exact ⟨h_sup_ge, h_sup_le⟩

/-- Integrability of the decoupled gap in the ghost variable, for a fixed
training sample, when the loss is bounded and measurable. -/
private lemma integrable_decoupledGap_in_ghost
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) :
    Integrable (fun S' : Fin n → Z => decoupledGap ℓ S S') (piMeasure μ n) :=
  integrable_of_bounded_measurable (B := 2 * B) (piMeasure μ n)
    (measurable_decoupledGap_in_ghost hℓ_meas S)
    (fun S' => abs_decoupledGap_le hB hℓ_bdd hn S S')

/-- Measurability of the generalization gap as a function of the training
sample. Each component is `risk μ ℓ i` (a constant in `S`) minus
`empRisk S ℓ i` (measurable in `S` as above). -/
lemma measurable_genGap
    (μ : Measure Z)
    {ℓ : ι → Z → ℝ} (hℓ_meas : ∀ i, Measurable (ℓ i))
    {n : ℕ} :
    Measurable (fun S : Fin n → Z => genGap μ ℓ S) := by
  have h_each : ∀ i : ι,
      Measurable (fun S : Fin n → Z =>
        Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i) := by
    intro i
    refine Measurable.sub measurable_const ?_
    unfold Risk.empiricalRisk
    refine Measurable.const_mul ?_ ((n : ℝ)⁻¹)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact (hℓ_meas i).comp (measurable_pi_apply k)
  have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
    (f := fun i (S : Fin n → Z) =>
      Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i)
    Finset.univ_nonempty (fun i _ => h_each i)
  convert h_pi using 1
  ext S
  unfold genGap
  simp [Finset.sup'_apply]

/-- Boundedness of `genGap S` by `2B`. -/
private lemma abs_genGap_le
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) :
    |genGap μ ℓ S| ≤ 2 * B := by
  -- |risk μ ℓ i| ≤ B from bounded loss + integral_le_of_bounded.
  have h_risk_abs : ∀ i, |Risk.risk μ ℓ i| ≤ B := by
    intro i
    unfold Risk.risk
    have h_int : Integrable (ℓ i) μ :=
      integrable_loss_of_bounded μ hℓ_meas hℓ_bdd i
    have h_norm := norm_integral_le_integral_norm (μ := μ) (f := ℓ i)
    have h_norm_bound : ∫ z, ‖ℓ i z‖ ∂μ ≤ B := by
      have h_each : ∀ z, ‖ℓ i z‖ ≤ B := by
        intro z
        rw [Real.norm_eq_abs]; exact hℓ_bdd i z
      have h_le := MeasureTheory.integral_mono_of_nonneg
          (μ := μ) (f := fun z => ‖ℓ i z‖) (g := fun _ => B)
          (Filter.Eventually.of_forall (fun z => norm_nonneg _))
          (integrable_const B)
          (Filter.Eventually.of_forall h_each)
      have h_const : ∫ _z, B ∂μ = B := by
        rw [integral_const, probReal_univ, one_smul]
      linarith
    have : ‖∫ z, ℓ i z ∂μ‖ ≤ B := h_norm.trans h_norm_bound
    rwa [Real.norm_eq_abs] at this
  -- |empRisk S ℓ i| ≤ B from earlier.
  have h_each_le_2B : ∀ i : ι,
      Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i ≤ 2 * B := by
    intro i
    have h1 : Risk.risk μ ℓ i ≤ B := by linarith [abs_le.mp (h_risk_abs i)]
    have h2 : -B ≤ Risk.empiricalRisk S ℓ i := by
      linarith [abs_le.mp (abs_empiricalRisk_le hB hℓ_bdd hn S i)]
    linarith
  have h_each_ge_neg_2B : ∀ i : ι,
      -(2 * B) ≤ Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i := by
    intro i
    have h1 : -B ≤ Risk.risk μ ℓ i := by linarith [abs_le.mp (h_risk_abs i)]
    have h2 : Risk.empiricalRisk S ℓ i ≤ B := by
      linarith [abs_le.mp (abs_empiricalRisk_le hB hℓ_bdd hn S i)]
    linarith
  have h_sup_le : genGap μ ℓ S ≤ 2 * B := by
    unfold genGap
    refine Finset.sup'_le _ _ (fun i _ => h_each_le_2B i)
  have h_sup_ge : -(2 * B) ≤ genGap μ ℓ S := by
    unfold genGap
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have h_le_sup :
        Risk.risk μ ℓ i₀ - Risk.empiricalRisk S ℓ i₀
          ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty
              (fun i => Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i) :=
      Finset.le_sup'
        (f := fun j => Risk.risk μ ℓ j - Risk.empiricalRisk S ℓ j)
        (s := (Finset.univ : Finset ι)) (Finset.mem_univ i₀)
    linarith [h_each_ge_neg_2B i₀]
  rw [abs_le]
  exact ⟨h_sup_ge, h_sup_le⟩

/-- Integrability of `genGap` against the iid product measure. -/
lemma integrable_genGap
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun S : Fin n → Z => genGap μ ℓ S) (piMeasure μ n) :=
  integrable_of_bounded_measurable (B := 2 * B) (piMeasure μ n)
    (measurable_genGap μ hℓ_meas)
    (fun S => abs_genGap_le μ hB hℓ_meas hℓ_bdd hn S)

/-! ### Pointwise step: bound `genGap S` by the inner ghost integral -/

/-- For a fixed training sample `S`, the generalization gap is bounded by
the expectation of the decoupled gap over the ghost sample. This is the
"ghost-sample replacement" inequality at a single `S`. -/
private lemma genGap_le_integral_decoupledGap
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) (S : Fin n → Z) :
    genGap μ ℓ S
      ≤ ∫ S' : Fin n → Z, decoupledGap ℓ S S' ∂(piMeasure μ n) := by
  -- For each h : ι, the gap risk h - empRisk S h equals
  -- ∫_{S'} (empRisk_{S'} ℓ h - empRisk_S ℓ h) ∂(pi μ).
  have hℓ_int : ∀ i, Integrable (ℓ i) μ :=
    integrable_loss_of_bounded μ hℓ_meas hℓ_bdd
  -- Establish the per-h identity: risk h - empRisk_S h = ∫_{S'} (empRisk_{S'} h - empRisk_S h).
  have h_per_h : ∀ i : ι,
      Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i
        = ∫ S' : Fin n → Z,
            (Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i)
              ∂(piMeasure μ n) := by
    intro i
    have h_emp_int : Integrable
        (fun S' : Fin n → Z => Risk.empiricalRisk S' ℓ i) (piMeasure μ n) :=
      integrable_empiricalRisk μ hℓ_int i
    have h_const_int : Integrable
        (fun _ : Fin n → Z => Risk.empiricalRisk S ℓ i) (piMeasure μ n) :=
      integrable_const _
    rw [integral_sub h_emp_int h_const_int]
    rw [integral_const, probReal_univ, one_smul]
    rw [expected_empiricalRisk_eq_risk μ ℓ hℓ_meas hℓ_int hn i]
  -- Pointwise inequality: each component is bounded by decoupledGap S S'.
  have h_int_decoupled : Integrable
      (fun S' : Fin n → Z => decoupledGap ℓ S S') (piMeasure μ n) :=
    integrable_decoupledGap_in_ghost μ hB hℓ_meas hℓ_bdd hn S
  -- For each h, the per-h integral is ≤ ∫ decoupledGap.
  have h_per_h_le_integral : ∀ i : ι,
      Risk.risk μ ℓ i - Risk.empiricalRisk S ℓ i
        ≤ ∫ S' : Fin n → Z, decoupledGap ℓ S S' ∂(piMeasure μ n) := by
    intro i
    rw [h_per_h i]
    have h_int_diff : Integrable
        (fun S' : Fin n → Z =>
          Risk.empiricalRisk S' ℓ i - Risk.empiricalRisk S ℓ i)
        (piMeasure μ n) := by
      refine Integrable.sub ?_ (integrable_const _)
      exact integrable_empiricalRisk μ hℓ_int i
    refine integral_mono h_int_diff h_int_decoupled (fun S' => ?_)
    unfold decoupledGap
    exact Finset.le_sup'
      (f := fun j => Risk.empiricalRisk S' ℓ j - Risk.empiricalRisk S ℓ j)
      (s := (Finset.univ : Finset ι)) (Finset.mem_univ i)
  -- Take sup over h on the LHS.
  unfold genGap
  refine Finset.sup'_le _ _ (fun i _ => h_per_h_le_integral i)

/-! ### Main theorem: ghost-sample replacement in expectation -/

/-- **Ghost-sample replacement (in expectation).** For a finite, nonempty
hypothesis class with bounded measurable real-valued losses against an iid
sample of size `n ≥ 1` from a probability measure `μ`, the expected
worst-case generalization gap is bounded by the expected supremum of the
ghost-sample-minus-sample empirical-risk gap. -/
theorem expected_genGap_le_expected_decoupledGap
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
      ≤ ∫ S, ∫ S', decoupledGap ℓ S S' ∂(piMeasure μ n) ∂(piMeasure μ n) := by
  -- Step 1: per-component joint measurability.
  have h_each_joint_meas : ∀ i : ι,
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
  -- Step 2: joint measurability of decoupledGap via the convert + sup'_apply
  -- bridge between the function-form and pointwise form of `Finset.sup'`.
  have h_joint_meas :
      Measurable (fun p : (Fin n → Z) × (Fin n → Z) =>
        decoupledGap ℓ p.1 p.2) := by
    have h_pi := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
      (f := fun i (p : (Fin n → Z) × (Fin n → Z)) =>
        Risk.empiricalRisk p.2 ℓ i - Risk.empiricalRisk p.1 ℓ i)
      Finset.univ_nonempty (fun i _ => h_each_joint_meas i)
    convert h_pi using 1
    ext p
    unfold decoupledGap
    simp [Finset.sup'_apply]
  -- Step 3: joint boundedness gives joint integrability on the product measure.
  have h_joint_bdd : ∀ p : (Fin n → Z) × (Fin n → Z),
      |decoupledGap ℓ p.1 p.2| ≤ 2 * B :=
    fun p => abs_decoupledGap_le hB hℓ_bdd hn p.1 p.2
  have h_joint_int :
      Integrable (fun p : (Fin n → Z) × (Fin n → Z) => decoupledGap ℓ p.1 p.2)
        ((piMeasure μ n).prod (piMeasure μ n)) :=
    integrable_of_bounded_measurable
      (B := 2 * B) ((piMeasure μ n).prod (piMeasure μ n))
      h_joint_meas h_joint_bdd
  -- Step 4: Fubini gives integrability of `S ↦ ∫ S', decoupledGap S S' ∂μ^n`.
  have h_inner_int :
      Integrable
        (fun S : Fin n → Z =>
          ∫ S' : Fin n → Z, decoupledGap ℓ S S' ∂(piMeasure μ n))
        (piMeasure μ n) :=
    h_joint_int.integral_prod_left
  -- Step 5: monotonicity of the integral, with the per-S bound from
  -- `genGap_le_integral_decoupledGap`.
  refine integral_mono ?_ h_inner_int (fun S => ?_)
  · exact integrable_genGap μ hB hℓ_meas hℓ_bdd hn
  · exact genGap_le_integral_decoupledGap μ hB hℓ_meas hℓ_bdd hn S

end FormalSLT.GhostSample
