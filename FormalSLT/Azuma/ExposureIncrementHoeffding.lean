/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.BoundedIncrementBound
import FormalSLT.Azuma.BoundedDiffMartingale

/-!
# Conditional sub-Gaussian MGF scaffolding for the exposure martingale

Stage B2c-3 part 2 (scaffolding). Establishes the three foundational
properties of the exposure-martingale increments
`exposureIncrement μ f k S = M_{k.succ} S - M_{k.castSucc} S`
on which a kernel-level conditional Hoeffding bound will be built in
the next sub-PR:

1. **Conditionally mean-zero**: the kth increment has conditional
   expectation zero w.r.t. the prefix-only σ-algebra
   `coordinateSubAlgebra n Z k.castSucc`. This is a direct corollary
   of the tower property of conditional expectation applied to
   `M_{k.succ} = E[f | F_{k.succ}]` and
   `M_{k.castSucc} = E[f | F_{k.castSucc}]`.

2. **Conditional sup-norm range bound (a.e.)**: the kth increment has
   sup-norm bounded by `c k` almost surely. Direct corollary of
   `abs_partialIntegral_step_le` and the increment representation
   `exposureIncrement_eq_partialIntegral_diff_ae`.

3. **`Filtration ℕ` adapter**: mathlib's
   `measure_sum_ge_le_of_hasCondSubgaussianMGF` is hardcoded to a
   `Filtration ℕ`, while `coordinateFiltration n Z` is indexed by
   `Fin (n + 1)`. The adapter caps at `Fin.last n` for `k > n`, so
   beyond the time horizon the σ-algebra equals the full one.

Out of scope here (deferred to the next sub-PR):
- `HasCondSubgaussianMGF` proper for the increments
- Hoeffding's lemma applied fiberwise via `condExpKernel`
- McDiarmid's inequality
- Any high-probability Rademacher / Massart / VC-PAC claim

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory Filter
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)

noncomputable section

namespace FormalSLT.Azuma.ExposureMartingale

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Fin n → Measure Z}

/-! ### Step 1: Conditional mean-zero of the increment -/

/-- The kth exposure-martingale increment has conditional expectation
zero w.r.t. the prefix-only σ-algebra
`coordinateSubAlgebra n Z k.castSucc`, almost surely under `μⁿ`.

Proof: `M_{k.succ} = E[f | F_{k.succ}]` and
`M_{k.castSucc} = E[f | F_{k.castSucc}]` by definition. By the tower
property (mathlib's `Filtration.condExp_condExp`),
`E[E[f | F_{k.succ}] | F_{k.castSucc}] =ᵐ E[f | F_{k.castSucc}]`,
since `F_{k.castSucc} ≤ F_{k.succ}` (`Fin.castSucc_lt_succ`).
The difference is therefore zero a.e. -/
theorem exposureIncrement_condExp_eq_zero_ae
    [IsFiniteMeasure (Measure.pi μ)]
    (f : (Fin n → Z) → ℝ) (k : Fin n) :
    (Measure.pi μ)[
      exposureIncrement μ f k
        | coordinateSubAlgebra n Z k.castSucc]
      =ᵐ[Measure.pi μ] 0 := by
  set μn : Measure (Fin n → Z) := Measure.pi μ
  set ℱ := coordinateFiltration n Z
  have h_le : k.castSucc ≤ k.succ := Fin.castSucc_lt_succ.le
  -- Tower: μⁿ[μⁿ[f | ℱ k.succ] | ℱ k.castSucc] =ᵐ μⁿ[f | ℱ k.castSucc].
  have h_tower :
      μn[μn[f | ℱ k.succ] | ℱ k.castSucc] =ᵐ[μn] μn[f | ℱ k.castSucc] :=
    ℱ.condExp_condExp f h_le
  -- Linearity of conditional expectation on the difference.
  have h_lin :
      μn[exposureIncrement μ f k | ℱ k.castSucc]
        =ᵐ[μn]
          μn[exposureMartingale μ f k.succ | ℱ k.castSucc]
            - μn[exposureMartingale μ f k.castSucc | ℱ k.castSucc] := by
    unfold exposureIncrement
    exact condExp_sub integrable_condExp integrable_condExp (ℱ k.castSucc)
  -- The first term equals M_{k.castSucc} by tower.
  have h_first :
      μn[exposureMartingale μ f k.succ | ℱ k.castSucc]
        =ᵐ[μn] exposureMartingale μ f k.castSucc := by
    unfold exposureMartingale
    exact h_tower
  -- The second term equals M_{k.castSucc} (self conditional expectation).
  -- Since `M_{k.castSucc} = μⁿ[f | ℱ k.castSucc]` is strongly measurable
  -- w.r.t. `ℱ k.castSucc`, condExp returns it unchanged.
  have h_self :
      μn[exposureMartingale μ f k.castSucc | ℱ k.castSucc]
        = exposureMartingale μ f k.castSucc := by
    unfold exposureMartingale
    exact condExp_of_stronglyMeasurable (ℱ.le k.castSucc)
      stronglyMeasurable_condExp integrable_condExp
  -- Combine.
  filter_upwards [h_lin, h_first] with S h_lin_S h_first_S
  show μn[exposureIncrement μ f k | coordinateSubAlgebra n Z k.castSucc] S = 0
  -- ↑ℱ k.castSucc ≡ coordinateSubAlgebra n Z k.castSucc by def of ℱ.
  rw [show (coordinateSubAlgebra n Z k.castSucc : MeasurableSpace (Fin n → Z))
        = (ℱ k.castSucc : MeasurableSpace (Fin n → Z)) from rfl]
  rw [h_lin_S]
  show μn[exposureMartingale μ f k.succ | ℱ k.castSucc] S
      - μn[exposureMartingale μ f k.castSucc | ℱ k.castSucc] S = 0
  rw [h_first_S, h_self, sub_self]

/-! ### Step 2: Sup-norm range bound on the increment, almost surely -/

/-- The kth exposure-martingale increment is bounded in absolute value
by `c k`, almost surely under `μⁿ`, whenever `f` has bounded differences
with widths `c`.

Proof: by `exposureIncrement_eq_partialIntegral_diff_ae`, the increment
equals `partialIntegral_{k.succ} f - partialIntegral_{k.castSucc} f`
a.e., and `abs_partialIntegral_step_le` gives the pointwise bound by
`c k` for the partial-integral difference. -/
theorem abs_exposureIncrement_le_ae
    [Nonempty Z] [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi μ))
    (k : Fin n) (hck : 0 ≤ c k) :
    ∀ᵐ S ∂(Measure.pi μ),
      |exposureIncrement μ f k S| ≤ c k := by
  -- Rewrite Δ_k as partialIntegral diff (a.e.).
  have h_eq :=
    exposureIncrement_eq_partialIntegral_diff_ae (μ := μ) k hf hfi
  -- Pointwise bound on the partialIntegral diff.
  have h_bnd : ∀ S,
      |partialIntegral μ k.succ f S - partialIntegral μ k.castSucc f S|
        ≤ c k :=
    fun S => abs_partialIntegral_step_le hbdd hf hfi k hck S
  filter_upwards [h_eq] with S hS
  rw [hS]
  exact h_bnd S

/-! ### Step 3: ℕ-indexed coordinate filtration adapter

mathlib's Azuma-Hoeffding theorem
`measure_sum_ge_le_of_hasCondSubgaussianMGF` is stated for a
`Filtration ℕ`. The exposure filtration is naturally indexed by
`Fin (n + 1)`. The adapter caps at `Fin.last n` for `k > n`. -/

/-- Cast a natural number to `Fin (n + 1)` by capping at `n`. -/
def finOfNatCapped (n k : ℕ) : Fin (n + 1) :=
  ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩

@[simp] lemma finOfNatCapped_val (n k : ℕ) :
    (finOfNatCapped n k : ℕ) = min k n := rfl

lemma finOfNatCapped_mono (n : ℕ) :
    Monotone (finOfNatCapped n) := by
  intro a b hab
  show (finOfNatCapped n a : ℕ) ≤ (finOfNatCapped n b : ℕ)
  simp only [finOfNatCapped_val]
  exact min_le_min hab le_rfl

variable (n Z) in
/-- ℕ-indexed extension of the coordinate filtration on `Fin n → Z`.

For `k ≤ n`, this returns `coordinateSubAlgebra n Z ⟨k, _⟩`.
For `k > n`, this returns `coordinateSubAlgebra n Z (Fin.last n)`,
which equals the full σ-algebra `MeasurableSpace.pi`. -/
def coordinateFiltrationNat :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → Z)) where
  seq := fun k => coordinateSubAlgebra n Z (finOfNatCapped n k)
  mono' := fun _ _ hij =>
    coordinateSubAlgebra_mono (finOfNatCapped_mono n hij)
  le' := fun k => coordinateSubAlgebra_le_pi (finOfNatCapped n k)

@[simp]
lemma coordinateFiltrationNat_apply (k : ℕ) :
    (coordinateFiltrationNat n Z) k =
      coordinateSubAlgebra n Z (finOfNatCapped n k) := rfl

/-- For `k ≤ n`, the ℕ-filtration matches the `Fin (n + 1)`-filtration
at the corresponding index. -/
lemma coordinateFiltrationNat_eq_of_le {k : ℕ} (hk : k ≤ n) :
    (coordinateFiltrationNat n Z) k =
      coordinateSubAlgebra n Z ⟨k, Nat.lt_succ_of_le hk⟩ := by
  show coordinateSubAlgebra n Z (finOfNatCapped n k) = _
  congr 1
  apply Fin.ext
  show min k n = k
  exact min_eq_left hk

/-- Beyond the horizon `k ≥ n`, the ℕ-filtration stabilises at the
full σ-algebra `coordinateSubAlgebra n Z (Fin.last n)`. -/
lemma coordinateFiltrationNat_of_ge {k : ℕ} (hk : n ≤ k) :
    (coordinateFiltrationNat n Z) k =
      coordinateSubAlgebra n Z (Fin.last n) := by
  show coordinateSubAlgebra n Z (finOfNatCapped n k) = _
  congr 1
  apply Fin.ext
  show min k n = (Fin.last n : ℕ)
  rw [Fin.val_last]
  exact min_eq_right hk

end FormalSLT.Azuma.ExposureMartingale
