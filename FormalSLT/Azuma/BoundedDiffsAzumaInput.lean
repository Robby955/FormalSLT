import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import FormalSLT.Azuma.ExposureMartingale

/-!
# Prefix/tail integral representation of the exposure martingale

Stage B sub-PR 2c of `docs/plans/mcdiarmid-rademacher-plan.md`.

For an integrable real-valued function `f : (Fin n → Z) → ℝ` and a
probability measure `μ` on `Z`, the Doob exposure martingale value
`M_k = E[f | F_k]` admits a prefix/tail integral representation:
conditioning on the first `k` coordinates equals integrating out the
last `n - k` coordinates pointwise.

Mathlib has no `condExp_pi` machinery, so we build the structural
prefix/tail decomposition and the partial-integral candidate from
scratch in this PR. The full conditional-expectation identification
itself, the bounded-increment range bound, the conditional Hoeffding
lemma, and the `Filtration ℕ` adapter are explicit follow-ups.

## Contents (this module)

* `splice k S T` — combine prefix coords from `S` and tail coords from
  `T` along the predicate `(i : ℕ) < (k : ℕ)`.
* `splice_zero`, `splice_last` — boundary identities.
* `measurable_splice` — joint measurability of `splice` in `(S, T)`.
* `partialIntegral μ k f S` — the prefix/tail integral candidate
  `∫ T, f(splice k S T) ∂μⁿ`.
* `partialIntegral_zero` — at `k = 0`, equals `∫ f dμⁿ` pointwise (no
  prefix to condition on).
* `partialIntegral_last` — at `k = Fin.last n`, equals `f S` pointwise
  under a probability measure (full prefix recovers `f`).
* `partialIntegral_invariant_on_tail_update` — the invariance
  `partialIntegral S = partialIntegral (Function.update S i z')` for
  any tail index `i ≥ k`. This is the structural property that makes
  `partialIntegral` `coordinateSubAlgebra k`-measurable in spirit; the
  full strongly-measurable statement is deferred to a follow-up sub-PR
  of B2c.

## Constraints

* No `sorry`, no `admit`, no custom `axiom`. All lemmas close.
* No manifest entry. No `/lean` dashboard update.
* No concentration claim. The strongest identity here is a pointwise
  equality of two real-valued functions on `Fin n → Z`.
* `[StandardBorelSpace Z]` is **not** assumed in this module. It will
  appear only in the conditional-Hoeffding sub-PR (B2c-3) where
  `condExpKernel` enters.
-/

namespace FormalSLT.Azuma.ExposureMartingale

open MeasureTheory MeasurableSpace Filter

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-! ### Splice: combine prefix and tail coordinates

`splice k S T : Fin n → Z` agrees with `S` on indices in the prefix
`{i | (i : ℕ) < (k : ℕ)}` and with `T` on the tail. -/

/-- Splice prefix coords from `S` with tail coords from `T`. -/
def splice (k : Fin (n + 1)) (S T : Fin n → Z) : Fin n → Z :=
  fun i => if (i : ℕ) < (k : ℕ) then S i else T i

@[simp]
lemma splice_zero (S T : Fin n → Z) : splice (0 : Fin (n + 1)) S T = T := by
  funext i
  unfold splice
  simp

@[simp]
lemma splice_last (S T : Fin n → Z) : splice (Fin.last n) S T = S := by
  funext i
  unfold splice
  have hi : (i : ℕ) < ((Fin.last n) : ℕ) := by
    simp [Fin.val_last]
  exact if_pos hi

/-- Joint measurability of `splice` in `(S, T)`. -/
lemma measurable_splice (k : Fin (n + 1)) :
    Measurable (fun ST : (Fin n → Z) × (Fin n → Z) => splice k ST.1 ST.2) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  show Measurable (fun ST : (Fin n → Z) × (Fin n → Z) =>
    if (i : ℕ) < (k : ℕ) then ST.1 i else ST.2 i)
  by_cases h : (i : ℕ) < (k : ℕ)
  · simp only [h, if_true]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [h, if_false]
    exact (measurable_pi_apply i).comp measurable_snd

/-- `splice` is unaffected by changing `S` at any tail index. -/
lemma splice_update_tail (k : Fin (n + 1)) (S T : Fin n → Z)
    {i : Fin n} (hi : ¬ ((i : ℕ) < (k : ℕ))) (z' : Z) :
    splice k (Function.update S i z') T = splice k S T := by
  funext j
  unfold splice
  by_cases hjk : (j : ℕ) < (k : ℕ)
  · simp only [hjk, if_true]
    have hji : j ≠ i := by
      intro hji
      subst hji
      exact hi hjk
    rw [Function.update_of_ne hji]
  · simp [hjk]

/-- `splice` is unaffected by changing `T` at any prefix index. -/
lemma splice_update_prefix (k : Fin (n + 1)) (S T : Fin n → Z)
    {i : Fin n} (hi : (i : ℕ) < (k : ℕ)) (z' : Z) :
    splice k S (Function.update T i z') = splice k S T := by
  funext j
  unfold splice
  by_cases hjk : (j : ℕ) < (k : ℕ)
  · simp [hjk]
  · simp only [hjk, if_false]
    have hji : j ≠ i := by
      intro hji
      subst hji
      exact hjk hi
    rw [Function.update_of_ne hji]

/-! ### Partial-integral candidate for `M_k`

`partialIntegral μ k f S = ∫ T, f(splice k S T) ∂μⁿ` is the natural
prefix/tail integral candidate for the Doob exposure martingale.

Note: we integrate over the whole `μⁿ` rather than just the tail
factor `μⁿ⁻ᵏ`. Under any probability measure `μ`, by Fubini this
equals integrating only over tail coords (the prefix coords of `T` do
not enter `splice k S T`). Using `μⁿ` keeps the type signature simple
and avoids subtype arithmetic on `Fin n`. -/

variable (μ) in
/-- The prefix/tail integral candidate for the Doob exposure martingale. -/
noncomputable def partialIntegral (k : Fin (n + 1)) (f : (Fin n → Z) → ℝ) :
    (Fin n → Z) → ℝ :=
  fun S => ∫ T, f (splice k S T) ∂(Measure.pi (fun _ : Fin n => μ))

/-- At `k = 0`, the prefix is empty, so the candidate equals the
unconditional expectation of `f`. -/
lemma partialIntegral_zero (f : (Fin n → Z) → ℝ) (S : Fin n → Z) :
    partialIntegral μ 0 f S = ∫ T, f T ∂(Measure.pi (fun _ : Fin n => μ)) := by
  simp [partialIntegral]

/-- At `k = Fin.last n`, the prefix is the full sample, so the
candidate equals `f S` (under a probability measure). -/
lemma partialIntegral_last
    [IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ))]
    (f : (Fin n → Z) → ℝ) (S : Fin n → Z) :
    partialIntegral μ (Fin.last n) f S = f S := by
  unfold partialIntegral
  have h_eq : (fun T => f (splice (Fin.last n) S T)) = (fun _ => f S) := by
    funext T
    rw [splice_last]
  rw [h_eq]
  simp

/-- Tail-update invariance: `partialIntegral` is unchanged by updating
`S` at any index in the tail `i ≥ k`. This is the structural property
that supports `partialIntegral` being measurable w.r.t. the
prefix-only σ-algebra `coordinateSubAlgebra n Z k`. -/
lemma partialIntegral_invariant_on_tail_update
    (k : Fin (n + 1)) (f : (Fin n → Z) → ℝ) (S : Fin n → Z)
    {i : Fin n} (hi : ¬ ((i : ℕ) < (k : ℕ))) (z' : Z) :
    partialIntegral μ k f (Function.update S i z') = partialIntegral μ k f S := by
  unfold partialIntegral
  congr 1
  funext T
  rw [splice_update_tail k S T hi z']

/-! ### Strong measurability w.r.t. the full pi σ-algebra

`partialIntegral μ k f` is strongly measurable w.r.t. the full product
σ-algebra on `Fin n → Z`. This follows from joint measurability of
`splice k` and mathlib's parametric integral measurability lemma
`MeasureTheory.StronglyMeasurable.integral_prod_right'`.

The strengthening to `coordinateSubAlgebra n Z k`-strong-measurability
is a separate sub-PR and uses the tail-update invariance lemma above
to factor `partialIntegral` through the prefix coordinates. -/

/-- Strong measurability of `partialIntegral` w.r.t. the full product
σ-algebra on `Fin n → Z`. -/
lemma stronglyMeasurable_partialIntegral
    [SFinite (Measure.pi (fun _ : Fin n => μ))]
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (partialIntegral μ k f) := by
  unfold partialIntegral
  have h_comp : StronglyMeasurable (fun ST : (Fin n → Z) × (Fin n → Z) =>
      f (splice k ST.1 ST.2)) :=
    hf.comp_measurable (measurable_splice k)
  exact h_comp.integral_prod_right'

/-! ### Prefix-agreement principle

`partialIntegral μ k f` depends only on the prefix coordinates of its
argument. This is the pointwise structural property that supports the
eventual `coordinateSubAlgebra n Z k`-strong-measurability of
`partialIntegral` (deferred to a follow-up sub-PR, where it is needed
for the conditional-expectation identification). -/

/-- Pointwise prefix-agreement principle: `partialIntegral μ k f`
depends only on the prefix coords of its argument. -/
lemma partialIntegral_eq_of_agree_prefix
    (k : Fin (n + 1)) (f : (Fin n → Z) → ℝ) (S S' : Fin n → Z)
    (hagree : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = S' i) :
    partialIntegral μ k f S = partialIntegral μ k f S' := by
  unfold partialIntegral
  congr 1
  funext T
  congr 1
  funext i
  unfold splice
  by_cases hi : (i : ℕ) < (k : ℕ)
  · simp only [hi, if_true]
    exact hagree i hi
  · simp only [hi, if_false]

/-! ### Prefix-σ-algebra strong measurability

The prefix-agreement principle above yields measurability of
`partialIntegral` w.r.t. `coordinateSubAlgebra n Z k`. We factor
`partialIntegral μ k f` through a prefix→full round-trip
`prefixToFull` that fills the tail with a default `Z`-value and prove
its measurability via the comap characterization of `Measurable`.

`[Nonempty Z]` is needed only for the default tail value. -/

variable [Nonempty Z]

/-- Round-trip prefix→full extension: keep prefix coords, fill tail
with `Classical.arbitrary Z`. Used to factor `partialIntegral μ k f`
through the prefix coordinates. -/
private noncomputable def prefixToFull (k : Fin (n + 1))
    (S : Fin n → Z) : Fin n → Z :=
  fun i => if (i : ℕ) < (k : ℕ) then S i else Classical.arbitrary Z

/-- `prefixToFull k` is measurable as a map
`(Fin n → Z, coordinateSubAlgebra k) → (Fin n → Z, full pi)`.

Proved via `measurable_iff_comap_le`: each `comap (eval i ∘ prefixToFull k)`
summand is bounded above by `coordinateSubAlgebra k`. For `i < k` the
summand is one of the iSup summands defining `coordinateSubAlgebra k`;
for `i ≥ k` the composite is constant, so the comap is `⊥`. -/
private lemma measurable_prefixToFull (k : Fin (n + 1)) :
    @Measurable _ _ (coordinateSubAlgebra n Z k) _ (prefixToFull k) := by
  rw [measurable_iff_comap_le]
  -- Goal: comap (prefixToFull k) (full pi) ≤ coordinateSubAlgebra k.
  -- Default pi instance unfolds to ⨆ i, comap (eval i) inferInstance.
  show MeasurableSpace.comap (prefixToFull k)
      (⨆ i, MeasurableSpace.comap (fun s : Fin n → Z => s i) inferInstance)
      ≤ coordinateSubAlgebra n Z k
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le (fun i => ?_)
  rw [MeasurableSpace.comap_comp]
  -- Goal: comap (fun S => prefixToFull k S i) inferInstance ≤ coordinateSubAlgebra k
  by_cases hi : (i : ℕ) < (k : ℕ)
  · -- (eval i ∘ prefixToFull k) S = S i, on the i < k branch.
    have h_eq : ((fun s : Fin n → Z => s i) ∘ prefixToFull k) =
        fun S : Fin n → Z => S i := by
      funext S
      simp only [Function.comp_apply, prefixToFull, hi, if_true]
    rw [h_eq]
    -- Goal: comap (eval i) MS_Z ≤ coordinateSubAlgebra k.
    -- This is one of the iSup summands by definition.
    unfold coordinateSubAlgebra
    exact le_iSup₂ (f := fun (j : Fin n) (_ : (j : ℕ) < (k : ℕ)) =>
      (inferInstance : MeasurableSpace Z).comap
        (fun s : Fin n → Z => s j)) i hi
  · -- (eval i ∘ prefixToFull k) is constant on the i ≥ k branch.
    have h_eq : ((fun s : Fin n → Z => s i) ∘ prefixToFull k) =
        fun _ : Fin n → Z => (Classical.arbitrary Z : Z) := by
      funext S
      simp only [Function.comp_apply, prefixToFull, hi, if_false]
    rw [h_eq, MeasurableSpace.comap_const]
    exact bot_le

private lemma partialIntegral_eq_comp_prefixToFull
    (k : Fin (n + 1)) (f : (Fin n → Z) → ℝ) (S : Fin n → Z) :
    partialIntegral μ k f S = partialIntegral μ k f (prefixToFull k S) := by
  apply partialIntegral_eq_of_agree_prefix
  intro i hi
  unfold prefixToFull
  simp [hi]

/-- Strong measurability of `partialIntegral μ k f` w.r.t.
`coordinateSubAlgebra n Z k`. The proof factors `partialIntegral`
through the prefix-only round-trip `prefixToFull`. -/
lemma stronglyMeasurable_coordinateSubAlgebra_partialIntegral
    [SFinite (Measure.pi (fun _ : Fin n => μ))]
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[coordinateSubAlgebra n Z k]
      (partialIntegral μ k f) := by
  -- Step 1: rewrite partialIntegral as a composition through prefixToFull.
  have h_eq : partialIntegral μ k f =
      (partialIntegral μ k f) ∘ (prefixToFull k) := by
    funext S
    exact partialIntegral_eq_comp_prefixToFull k f S
  rw [h_eq]
  -- Step 2: composition of strongly measurable function with a measurable
  -- map (in the source σ-algebra) is strongly measurable.
  exact (stronglyMeasurable_partialIntegral k hf).comp_measurable
    (measurable_prefixToFull k)

/-! ### Splice as a measure-preserving map

Under any probability measure `μ` on `Z`, the joint splice map
`(S, T) ↦ splice k S T` is measure-preserving from `μⁿ × μⁿ` to `μⁿ`.
We prove this by factoring `splice` through
`MeasurableEquiv.piEquivPiSubtypeProd` (mathlib's prefix/tail
equivalence). This is the change-of-variables tool needed for the
prefix/tail integral identification of the exposure martingale. -/

section SpliceMeasurePreserving

variable [IsProbabilityMeasure μ]

/-- The prefix/tail predicate viewed as a `DecidablePred`. -/
private abbrev splicePred (k : Fin (n + 1)) : Fin n → Prop :=
  fun i => (i : ℕ) < (k : ℕ)

private instance (k : Fin (n + 1)) : DecidablePred (splicePred (n := n) k) :=
  fun i => Nat.decLt _ _

/-- The mathlib prefix/tail equivalence specialized to our setup. -/
private noncomputable def spliceEquiv (k : Fin (n + 1)) :
    (Fin n → Z) ≃ᵐ
      ((i : {i : Fin n // (i : ℕ) < (k : ℕ)}) → Z) ×
        ((i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))}) → Z) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Z)
    (splicePred (n := n) k)

/-- Pointwise: `splice k S T` equals applying the inverse of
`spliceEquiv` to `(prefix of S, tail of T)`. -/
private lemma splice_eq_spliceEquiv_symm (k : Fin (n + 1)) (S T : Fin n → Z) :
    splice k S T =
      (spliceEquiv (Z := Z) k).symm
        ((fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val,
          fun i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => T i.val)) := by
  funext i
  unfold splice spliceEquiv
  -- The symm of MeasurableEquiv.piEquivPiSubtypeProd is the dite version.
  show (if (i : ℕ) < (k : ℕ) then S i else T i)
      = (Equiv.piEquivPiSubtypeProd (fun i : Fin n => (i : ℕ) < (k : ℕ))
          (fun _ : Fin n => Z)).symm
          (fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val,
            fun i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => T i.val) i
  by_cases hi : (i : ℕ) < (k : ℕ)
  · simp [Equiv.piEquivPiSubtypeProd, hi]
  · simp [Equiv.piEquivPiSubtypeProd, hi]

/-- The map `(S, T) ↦ (prefix of S, tail of T)` is measure-preserving from
`μⁿ × μⁿ` to `μ^prefix × μ^tail` under any probability measure `μ`. -/
private lemma measurePreserving_pairProj (k : Fin (n + 1)) :
    MeasurePreserving
      (fun ST : (Fin n → Z) × (Fin n → Z) =>
        ((fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => ST.1 i.val,
          fun i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => ST.2 i.val) :
          ((i : {i : Fin n // (i : ℕ) < (k : ℕ)}) → Z) ×
            ((i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))}) → Z)))
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))
      ((Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ)).prod
        (Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ))) := by
  -- ψ : μⁿ ≃ᵐ μ^prefix × μ^tail is MP.
  have hψ :
      MeasurePreserving (spliceEquiv (Z := Z) k)
        (Measure.pi (fun _ : Fin n => μ))
        ((Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ)).prod
          (Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ)
      (splicePred (n := n) k)
  -- proj_p := Prod.fst ∘ ψ, MP from μⁿ to μ^prefix (uses prob measure on tail).
  have hψ_fst :
      MeasurePreserving
        (fun S : Fin n → Z => fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val)
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ)) := by
    have h := (measurePreserving_fst
      (μ := Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ))
      (ν := Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ))).comp hψ
    exact h
  -- proj_q := Prod.snd ∘ ψ, MP from μⁿ to μ^tail.
  have hψ_snd :
      MeasurePreserving
        (fun T : Fin n → Z => fun i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => T i.val)
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ)) := by
    have h := (measurePreserving_snd
      (μ := Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ))
      (ν := Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ))).comp hψ
    exact h
  -- Combined product map is MP.
  exact MeasurePreserving.prod hψ_fst hψ_snd

/-- Under any probability measure `μ`, the joint splice map
`(S, T) ↦ splice k S T` is measure-preserving from `μⁿ × μⁿ` to `μⁿ`. -/
lemma measurePreserving_splice (k : Fin (n + 1)) :
    MeasurePreserving (fun ST : (Fin n → Z) × (Fin n → Z) => splice k ST.1 ST.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin n => μ)) := by
  -- ψ⁻¹ : μ^prefix × μ^tail → μⁿ is MP.
  have hψ_symm :
      MeasurePreserving (spliceEquiv (Z := Z) k).symm
        ((Measure.pi (fun _ : {i : Fin n // (i : ℕ) < (k : ℕ)} => μ)).prod
          (Measure.pi (fun _ : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => μ)))
        (Measure.pi (fun _ : Fin n => μ)) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ)
      (splicePred (n := n) k)).symm _
  -- Compose ψ⁻¹ with the pair-projection map; the composition is the splice.
  have h_fun :
      (fun ST : (Fin n → Z) × (Fin n → Z) => splice k ST.1 ST.2)
        = (spliceEquiv (Z := Z) k).symm ∘
          (fun ST : (Fin n → Z) × (Fin n → Z) =>
            ((fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => ST.1 i.val,
              fun i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))} => ST.2 i.val) :
              ((i : {i : Fin n // (i : ℕ) < (k : ℕ)}) → Z) ×
                ((i : {i : Fin n // ¬ ((i : ℕ) < (k : ℕ))}) → Z))) := by
    funext ST
    exact splice_eq_spliceEquiv_symm k ST.1 ST.2
  rw [h_fun]
  exact hψ_symm.comp (measurePreserving_pairProj (Z := Z) (μ := μ) k)

/-! ### `coordinateSubAlgebra` as a comap σ-algebra

`coordinateSubAlgebra n Z k` is the comap of the prefix-only product
σ-algebra under the prefix-restriction map. This characterization is
the structural fact that lets us turn ℱ_k-measurable sets into
preimages of prefix-measurable sets, and yields the set-invariance
lemma `mem_iff_of_agree_prefix`. -/

private lemma coordinateSubAlgebra_eq_comap_prefix (k : Fin (n + 1)) :
    coordinateSubAlgebra n Z k =
      MeasurableSpace.comap
        (fun S : Fin n → Z => fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val)
        (inferInstance :
          MeasurableSpace ({i : Fin n // (i : ℕ) < (k : ℕ)} → Z)) := by
  unfold coordinateSubAlgebra
  -- RHS = comap (π_p) (⨆ j, comap (eval j) MS_Z) by definition of pi MS.
  -- = ⨆ j, comap (π_p) (comap (eval j) MS_Z)  [comap_iSup]
  -- = ⨆ j, comap (eval j ∘ π_p) MS_Z          [comap_comp]
  -- = ⨆ j : Subtype p, comap (S → S j.val) MS_Z
  -- LHS = ⨆ (i : Fin n) (_ : i < k), comap (eval i) MS_Z.
  -- These match by the Subtype p ↔ {(i, h) : i < k} bijection.
  show (⨆ (i : Fin n) (_ : (i : ℕ) < (k : ℕ)),
          (inferInstance : MeasurableSpace Z).comap (fun s : Fin n → Z => s i))
      = MeasurableSpace.comap _ (MeasurableSpace.pi)
  rw [MeasurableSpace.pi]
  rw [MeasurableSpace.comap_iSup]
  apply le_antisymm
  · refine iSup_le (fun i => iSup_le (fun hi => ?_))
    refine le_iSup_of_le ⟨i, hi⟩ ?_
    rw [MeasurableSpace.comap_comp]
    -- The composition (eval ⟨i,hi⟩) ∘ (S ↦ fun j => S j.val) = (S ↦ S i).
    rfl
  · refine iSup_le (fun j => ?_)
    rw [MeasurableSpace.comap_comp]
    refine le_iSup₂ (f := fun (i : Fin n) (_ : (i : ℕ) < (k : ℕ)) =>
      (inferInstance : MeasurableSpace Z).comap
        (fun s : Fin n → Z => s i)) j.val j.property

/-- Set-invariance: an `ℱ_k`-measurable set's membership depends only
on prefix coordinates of its argument. -/
private lemma mem_iff_of_agree_prefix
    (k : Fin (n + 1)) {s : Set (Fin n → Z)}
    (hs : MeasurableSet[coordinateSubAlgebra n Z k] s)
    {S S' : Fin n → Z}
    (hagree : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = S' i) :
    S ∈ s ↔ S' ∈ s := by
  rw [coordinateSubAlgebra_eq_comap_prefix] at hs
  obtain ⟨A, _, hA_eq⟩ := hs
  -- s = π_p⁻¹(A). Membership ↔ π_p S ∈ A. Since π_p S = π_p S':
  have h_eq : (fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val)
            = fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S' i.val := by
    funext i
    exact hagree i.val i.property
  constructor
  · intro hSs
    rw [← hA_eq] at hSs ⊢
    show (fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S' i.val) ∈ A
    rw [← h_eq]
    exact hSs
  · intro hS's
    rw [← hA_eq] at hS's ⊢
    show (fun i : {i : Fin n // (i : ℕ) < (k : ℕ)} => S i.val) ∈ A
    rw [h_eq]
    exact hS's

/-! ### Integrability and the set-integral identity -/

/-- `partialIntegral μ k f` is integrable when `f` is. -/
lemma integrable_partialIntegral
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    Integrable (partialIntegral μ k f) (Measure.pi (fun _ : Fin n => μ)) := by
  -- g (S, T) := f (splice k S T) is integrable on μⁿ × μⁿ by splice MP.
  have hg :
      Integrable (fun ST : (Fin n → Z) × (Fin n → Z) => f (splice k ST.1 ST.2))
        ((Measure.pi (fun _ : Fin n => μ)).prod
          (Measure.pi (fun _ : Fin n => μ))) :=
    (measurePreserving_splice (Z := Z) (μ := μ) k).integrable_comp_of_integrable hf
  -- partialIntegral = inner integral of g; use Integrable.integral_prod_left.
  exact hg.integral_prod_left

/-- The set-integral identity: for any `ℱ_k`-measurable set `s`,
the set-integral of `partialIntegral μ k f` equals that of `f`. -/
lemma setIntegral_partialIntegral_eq
    [IsProbabilityMeasure μ]
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    {s : Set (Fin n → Z)}
    (hs : MeasurableSet[coordinateSubAlgebra n Z k] s) :
    ∫ x in s, partialIntegral μ k f x ∂(Measure.pi (fun _ : Fin n => μ))
      = ∫ x in s, f x ∂(Measure.pi (fun _ : Fin n => μ)) := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  have hs_pi : MeasurableSet s := coordinateSubAlgebra_le_pi k s hs
  have hMP := measurePreserving_splice (Z := Z) (μ := μ) k
  -- Joint integrability of (S, T) ↦ f(splice k S T) on μn × μn.
  have hg_joint : Integrable (fun ST : (Fin n → Z) × (Fin n → Z) =>
      f (splice k ST.1 ST.2)) (μn.prod μn) :=
    hMP.integrable_comp_of_integrable hfi
  -- Joint integrability of (S, T) ↦ 1_s(S) · f(splice k S T).
  have hsg_joint : Integrable (fun ST : (Fin n → Z) × (Fin n → Z) =>
      s.indicator (fun S' => f (splice k S' ST.2)) ST.1) (μn.prod μn) := by
    have hs_prod : MeasurableSet (s ×ˢ (Set.univ : Set (Fin n → Z))) :=
      hs_pi.prod MeasurableSet.univ
    have h_eq : (fun ST : (Fin n → Z) × (Fin n → Z) =>
          s.indicator (fun S' => f (splice k S' ST.2)) ST.1)
        = (s ×ˢ (Set.univ : Set (Fin n → Z))).indicator
            (fun ST => f (splice k ST.1 ST.2)) := by
      funext ST
      by_cases hST1 : ST.1 ∈ s
      · simp [Set.indicator, Set.mem_prod, hST1]
      · simp [Set.indicator, Set.mem_prod, hST1]
    rw [h_eq]
    exact hg_joint.indicator hs_prod
  -- LHS: convert setIntegral to integral with indicator.
  rw [← integral_indicator (μ := μn) hs_pi, ← integral_indicator (μ := μn) hs_pi]
  -- Step 1: pull the indicator into the inner integral on the LHS.
  have h_lhs_pointwise :
      ∀ S, s.indicator (partialIntegral μ k f) S
          = ∫ T, s.indicator (fun S' => f (splice k S' T)) S ∂μn := by
    intro S
    by_cases hS : S ∈ s
    · simp only [Set.indicator_of_mem hS, partialIntegral]; rfl
    · simp only [Set.indicator_of_notMem hS, integral_zero]
  -- Apply h_lhs_pointwise to rewrite the outer integral.
  rw [show (fun S => s.indicator (partialIntegral μ k f) S)
        = (fun S => ∫ T, s.indicator (fun S' => f (splice k S' T)) S ∂μn)
        from funext h_lhs_pointwise]
  -- Step 2: Fubini on the LHS.
  rw [← integral_prod _ hsg_joint]
  -- Step 3: set-invariance — replace `1_s(ST.1)` by `1_s(splice k ST.1 ST.2)`.
  -- For all (S, T), splice k S T agrees with S on the first k coords (by splice_zero/last
  -- partial pattern: splice keeps prefix from S). So S ∈ s ↔ splice k S T ∈ s.
  have h_invariance :
      (fun ST : (Fin n → Z) × (Fin n → Z) =>
          s.indicator (fun S' => f (splice k S' ST.2)) ST.1)
        = (fun ST : (Fin n → Z) × (Fin n → Z) =>
            s.indicator f (splice k ST.1 ST.2)) := by
    funext ST
    obtain ⟨S, T⟩ := ST
    -- Set-invariance: splice k S T agrees with S on prefix; s is ℱ_k-measurable.
    have hagree : ∀ i : Fin n, (i : ℕ) < (k : ℕ) → S i = splice k S T i := by
      intro i hi
      simp [splice, hi]
    have h_iff : S ∈ s ↔ splice k S T ∈ s :=
      mem_iff_of_agree_prefix k hs hagree
    by_cases hS : S ∈ s
    · have hsplice : splice k S T ∈ s := h_iff.mp hS
      simp [Set.indicator_of_mem hS, Set.indicator_of_mem hsplice]
    · have hsplice : splice k S T ∉ s := fun h => hS (h_iff.mpr h)
      simp [Set.indicator_of_notMem hS, Set.indicator_of_notMem hsplice]
  rw [h_invariance]
  -- Step 4: splice MP gives ∫ ST, g(splice ST) ∂(μn × μn) = ∫ x, g x ∂μn.
  -- Use integral_map with hMP.map_eq.
  have h_indicator_meas : AEStronglyMeasurable (s.indicator f) μn :=
    (hf.indicator hs_pi).aestronglyMeasurable
  have h_map_indicator : AEStronglyMeasurable (s.indicator f)
      (Measure.map (fun ST : (Fin n → Z) × (Fin n → Z) => splice k ST.1 ST.2)
        (μn.prod μn)) := by
    rw [hMP.map_eq]
    exact h_indicator_meas
  rw [← integral_map hMP.measurable.aemeasurable h_map_indicator, hMP.map_eq]

/-- The exposure martingale is the partial integral, almost everywhere.
This is the conditional-expectation identification: it says that
`M_k S = E[f | first k coords](S)` admits the explicit prefix/tail
integral representation `partialIntegral μ k f S = ∫ T, f(splice k S T) ∂μⁿ`. -/
theorem partialIntegral_eq_condExp_ae
    [IsProbabilityMeasure μ]
    (k : Fin (n + 1)) {f : (Fin n → Z) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    partialIntegral μ k f
      =ᵐ[Measure.pi (fun _ : Fin n => μ)]
        (Measure.pi (fun _ : Fin n => μ))[f | coordinateSubAlgebra n Z k] := by
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with hμn
  have hm : coordinateSubAlgebra n Z k ≤
      (inferInstance : MeasurableSpace (Fin n → Z)) :=
    coordinateSubAlgebra_le_pi k
  -- Apply ae_eq_condExp_of_forall_setIntegral_eq.
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfi
    (fun s _ _ => (integrable_partialIntegral k hfi).integrableOn)
    (fun s hs _ => ?_)
    (stronglyMeasurable_coordinateSubAlgebra_partialIntegral
      k hf).aestronglyMeasurable
  exact setIntegral_partialIntegral_eq k hf hfi hs

end SpliceMeasurePreserving

end FormalSLT.Azuma.ExposureMartingale
