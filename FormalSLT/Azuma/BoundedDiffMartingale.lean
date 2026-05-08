import FormalSLT.Azuma.ExposureMartingale

/-!
# Bounded-difference exposure-martingale increments (algebraic core)

Stage B sub-PR 2 of `docs/plans/mcdiarmid-rademacher-plan.md`.

This module ships the **algebraic / a.e. core** of the bridge from
sub-PR 1's exposure martingale to mathlib's Azuma-Hoeffding theorem
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`).

Contents:

* `exposureIncrement μ f k S = M_{k+1} S - M_k S` (k : Fin n) — the
  martingale-difference increments.
* `sum_exposureIncrement_eq`: pointwise telescoping
  `∑ k, D_k = M_n - M_0` (Finset-level identity, pure algebra).
* `sum_exposureIncrement_eq_ae`: a.e. corollary
  `∑ k, D_k =ᵐ f - ∫ f dμⁿ`,
  obtained by combining the pointwise telescoping with the endpoint
  identities `exposureMartingale_zero_ae` and
  `exposureMartingale_last_ae` of sub-PR 1.

These two identities are the algebraic / a.e. inputs that the
**analytic core** (prefix/tail integral representation, bounded-
increment range bound, conditional sub-Gaussian MGF) builds on, and
that the **concentration step** (Azuma + McDiarmid + genGap) ultimately
consumes.

Deliberately deferred to a follow-on commit / sub-PR (see plan doc):

* Prefix/tail integral representation
  `M_k S = ∫ tail, f (prefix S k, tail) dμ_tail`.
* Bounded-increment range bound (turning coordinate sensitivity `c_i`
  into a range bound on `D_i` of width `c_i`).
* Conditional sub-Gaussian MGF for `D_k` w.r.t. the coordinate
  filtration, in the form mathlib's `HasCondSubgaussianMGF` consumes.
  This depends on `StandardBorelSpace Z` and on a new conditional
  Hoeffding lemma (mathlib has only the unconditional version).
* Filtration-index adapter (`Fin (n+1)` → `ℕ`) so that mathlib's
  `Filtration ℕ`-indexed Azuma-Hoeffding can apply.

Constraints respected here:
* No `sorry`, no `admit`, no custom `axiom`. All lemmas close.
* No concentration claim, no high-probability claim, no McDiarmid
  claim. The strongest statement here is an a.e. equality of two
  real-valued functions on `Fin n → Z`.
* No manifest entry. No `/lean` dashboard update.
-/

namespace FormalSLT.Azuma.ExposureMartingale

open MeasureTheory Filter

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-! ### Exposure-martingale increments -/

/-- The `k`th martingale-difference increment of the exposure
martingale of `f`:
`exposureIncrement μ f k S = M_{k+1} S - M_k S`. -/
noncomputable def exposureIncrement
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) (k : Fin n) :
    (Fin n → Z) → ℝ :=
  fun S =>
    exposureMartingale μ f k.succ S - exposureMartingale μ f k.castSucc S

/-- Pointwise telescoping identity:
`∑ k : Fin n, D_k S = M_n S - M_0 S`. -/
lemma sum_exposureIncrement_eq
    (f : (Fin n → Z) → ℝ) (S : Fin n → Z) :
    ∑ k : Fin n, exposureIncrement μ f k S
      = exposureMartingale μ f (Fin.last n) S
        - exposureMartingale μ f 0 S := by
  set g : Fin (n + 1) → ℝ := fun i => exposureMartingale μ f i S with hg
  show ∑ k : Fin n, (g k.succ - g k.castSucc) = g (Fin.last n) - g 0
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ i, g i = g 0 + ∑ i : Fin n, g i.succ := Fin.sum_univ_succ g
  have h2 : ∑ i, g i = (∑ i : Fin n, g i.castSucc) + g (Fin.last n) :=
    Fin.sum_univ_castSucc g
  linarith

/-- A.e. telescoping identity:
`∑ k, D_k =ᵐ f - ∫ f dμⁿ`. Combines pointwise telescoping
(`sum_exposureIncrement_eq`) with the endpoint identities
(`exposureMartingale_zero_ae`, `exposureMartingale_last_ae`). -/
lemma sum_exposureIncrement_eq_ae
    [IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ))]
    {f : (Fin n → Z) → ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    (fun S => ∑ k : Fin n, exposureIncrement μ f k S)
      =ᵐ[Measure.pi (fun _ : Fin n => μ)]
        fun S => f S - ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) := by
  -- M_n S =ᵐ f S, M_0 S =ᵐ ∫ f. Combine with the pointwise identity.
  have h_last := exposureMartingale_last_ae (μ := μ) hf hfi
  have h_zero := exposureMartingale_zero_ae (μ := μ) f
  have h_pt :
      ∀ S, ∑ k : Fin n, exposureIncrement μ f k S
        = exposureMartingale μ f (Fin.last n) S
          - exposureMartingale μ f 0 S :=
    fun S => sum_exposureIncrement_eq f S
  filter_upwards [h_last, h_zero] with S hS_last hS_zero
  rw [h_pt S, hS_last, hS_zero]

end FormalSLT.Azuma.ExposureMartingale
