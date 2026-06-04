/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.Azuma.ExposureIncrementCondMGF
import FormalSLT.Azuma.HasBoundedDifferences
import FormalSLT.GhostSample
import Mathlib.Probability.Process.Adapted

/-!
# Azuma-style tail bound for the generalisation gap

Stage B2c-4 of `docs/plans/mcdiarmid-rademacher-plan.md`.

Feeds the exposure-increment conditional MGF theorems into mathlib's
Azuma-Hoeffding theorem `measure_sum_ge_le_of_hasCondSubgaussianMGF`,
through the ℕ-indexed filtration `coordinateFiltrationNat` and the
exposure-martingale telescoping identity, to obtain one-sided
tail bounds for any function `f : (Fin n → Z) → ℝ` satisfying
`HasBoundedDifferences f c`. Specialises to the generalisation gap.

## Two constants: Azuma and sharp McDiarmid

The historical theorem `hasBoundedDifferences_tail_azuma` uses the symmetric
increment parameter from `exposureIncrement_hasCondSubgaussianMGF`. The
exposure-increment sub-Gaussian parameter is `‖c k‖₊²`, and after summing over
`k : Fin n` mathlib's Azuma yields

    μⁿ {S | ∫ f dμⁿ + t ≤ f S}  ≤  exp (- t² / (2 * ∑ k, ‖c k‖₊²))

For the generalisation gap with `c k = 2B/n` (constant) the sum is
`∑ k, ‖2B/n‖₊² = n · (2B/n)² = 4B²/n`, giving

    μⁿ {S | E[genGap] + t ≤ genGap S}  ≤  exp (- n · t² / (8 · B²)).

The sharp theorem `hasBoundedDifferences_tail_sharp` uses the range-width
parameter from `exposureIncrement_hasCondSubgaussianMGF_sharp`. The
per-increment proxy is `(‖c k‖₊ / 2)²`, so the same martingale engine yields

    μⁿ {S | ∫ f dμⁿ + t ≤ f S}  ≤  exp (-2 * t² / ∑ k, (c k)²)

when the supplied widths are nonnegative. For the generalisation gap with
`c k = 2B/n`, this is `exp(-n * t² / (2 * B²))`.

## ℕ-filtration / `Fin (n+1)`-filtration shift

Mathlib's Azuma is indexed by `Filtration ℕ`; our exposure martingale
is indexed by `Fin (n + 1)`. The off-by-one match between the two:

* mathlib's spec: `Y (i + 1)` is conditionally sub-Gaussian given `ℱ i`.
* our spec: `exposureIncrement μ f k` is conditionally sub-Gaussian
  given `coordinateSubAlgebra n Z k.castSucc = σ(coord 0..k-1)`.

The natural pairing is `Y (k.val + 1) = exposureIncrement μ f k` with
`ℱ k.val = coordinateSubAlgebra n Z ⟨k.val, _⟩`. We pad with `Y 0 = 0`
so the sum runs over `Finset.range (n + 1)` and equals
`f - ∫ f dμⁿ` almost surely (telescoping identity
`sum_exposureIncrement_eq_ae`).

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory Filter ProbabilityTheory Real
open FormalSLT.Azuma.BoundedDifferences
  (HasBoundedDifferences genGap_hasBoundedDifferences)
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap integrable_genGap)

noncomputable section

namespace FormalSLT.Azuma.ExposureMartingale

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-! ### Padded ℕ-indexed exposure increments

We pack the `Fin n`-indexed exposure increments `Δ_0, ..., Δ_{n-1}`
into an `ℕ`-indexed sequence `Y` with `Y 0 = 0` and
`Y (k + 1) = Δ_k` for `k < n` (and `Y k = 0` for `k > n`). The shift
matches the off-by-one in mathlib's Azuma spec. -/

/-- ℕ-indexed exposure increments: `Y 0 = 0`,
`Y (k + 1) = exposureIncrement μ f ⟨k, h⟩` for `k < n`, else `0`. -/
def shiftedExposureIncrement (μ : Measure Z) (f : (Fin n → Z) → ℝ) :
    ℕ → (Fin n → Z) → ℝ
  | 0 => 0
  | (k + 1) => fun S =>
      if h : k < n then exposureIncrement μ f ⟨k, h⟩ S else 0

@[simp] lemma shiftedExposureIncrement_zero
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) :
    shiftedExposureIncrement μ f 0 = 0 := rfl

lemma shiftedExposureIncrement_succ_of_lt
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) {k : ℕ} (hk : k < n) (S : Fin n → Z) :
    shiftedExposureIncrement μ f (k + 1) S =
      exposureIncrement μ f ⟨k, hk⟩ S := by
  simp [shiftedExposureIncrement, hk]

lemma shiftedExposureIncrement_succ_of_ge
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) {k : ℕ} (hk : n ≤ k) (S : Fin n → Z) :
    shiftedExposureIncrement μ f (k + 1) S = 0 := by
  have : ¬ k < n := not_lt.mpr hk
  simp [shiftedExposureIncrement, this]

/-- ℕ-indexed sub-Gaussian parameters: `cY 0 = 0`,
`cY (k + 1) = ‖c ⟨k, h⟩‖₊²` for `k < n`, else `0`. -/
def shiftedSubGaussianParam (c : Fin n → ℝ) : ℕ → ℝ≥0
  | 0 => 0
  | (k + 1) => if h : k < n then ‖c ⟨k, h⟩‖₊ ^ 2 else 0

@[simp] lemma shiftedSubGaussianParam_zero (c : Fin n → ℝ) :
    shiftedSubGaussianParam c 0 = 0 := rfl

lemma shiftedSubGaussianParam_succ_of_lt (c : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    shiftedSubGaussianParam c (k + 1) = ‖c ⟨k, hk⟩‖₊ ^ 2 := by
  simp [shiftedSubGaussianParam, hk]

lemma shiftedSubGaussianParam_succ_of_ge (c : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    shiftedSubGaussianParam c (k + 1) = 0 := by
  have : ¬ k < n := not_lt.mpr hk
  simp [shiftedSubGaussianParam, this]

/-- Sharp ℕ-indexed sub-Gaussian parameters: `cY 0 = 0`,
`cY (k + 1) = (‖c ⟨k, h⟩‖₊ / 2)²` for `k < n`, else `0`. -/
def shiftedSharpSubGaussianParam (c : Fin n → ℝ) : ℕ → ℝ≥0
  | 0 => 0
  | (k + 1) => if h : k < n then (‖c ⟨k, h⟩‖₊ / 2 : ℝ≥0) ^ 2 else 0

@[simp] lemma shiftedSharpSubGaussianParam_zero (c : Fin n → ℝ) :
    shiftedSharpSubGaussianParam c 0 = 0 := rfl

lemma shiftedSharpSubGaussianParam_succ_of_lt (c : Fin n → ℝ) {k : ℕ}
    (hk : k < n) :
    shiftedSharpSubGaussianParam c (k + 1) =
      (‖c ⟨k, hk⟩‖₊ / 2 : ℝ≥0) ^ 2 := by
  simp [shiftedSharpSubGaussianParam, hk]

lemma shiftedSharpSubGaussianParam_succ_of_ge (c : Fin n → ℝ) {k : ℕ}
    (hk : n ≤ k) :
    shiftedSharpSubGaussianParam c (k + 1) = 0 := by
  have : ¬ k < n := not_lt.mpr hk
  simp [shiftedSharpSubGaussianParam, this]

/-! ### Sum identities -/

/-- The sum of the ℕ-indexed `shiftedSubGaussianParam` over `range (n+1)`
collapses to the `Fin n`-indexed sum of `‖c k‖₊²`. -/
lemma sum_shiftedSubGaussianParam (c : Fin n → ℝ) :
    ∑ k ∈ Finset.range (n + 1), shiftedSubGaussianParam c k
      = ∑ k : Fin n, ‖c k‖₊ ^ 2 := by
  rw [Finset.sum_range_succ', shiftedSubGaussianParam_zero, add_zero]
  -- Reindex range n via Fin n.
  rw [← Fin.sum_univ_eq_sum_range (fun k => shiftedSubGaussianParam c (k + 1))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact shiftedSubGaussianParam_succ_of_lt c k.isLt

/-- The sum of the sharp ℕ-indexed parameters over `range (n+1)`
collapses to the `Fin n`-indexed sum of `(‖c k‖₊ / 2)²`. -/
lemma sum_shiftedSharpSubGaussianParam (c : Fin n → ℝ) :
    ∑ k ∈ Finset.range (n + 1), shiftedSharpSubGaussianParam c k
      = ∑ k : Fin n, (‖c k‖₊ / 2 : ℝ≥0) ^ 2 := by
  rw [Finset.sum_range_succ', shiftedSharpSubGaussianParam_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => shiftedSharpSubGaussianParam c (k + 1))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact shiftedSharpSubGaussianParam_succ_of_lt c k.isLt

/-- Pointwise: ∑ shiftedExposureIncrement = ∑_{k : Fin n} Δ_k. -/
lemma sum_shiftedExposureIncrement_eq
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) (S : Fin n → Z) :
    ∑ k ∈ Finset.range (n + 1), shiftedExposureIncrement μ f k S
      = ∑ k : Fin n, exposureIncrement μ f k S := by
  rw [Finset.sum_range_succ', shiftedExposureIncrement_zero, Pi.zero_apply, add_zero]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => shiftedExposureIncrement μ f (k + 1) S)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact shiftedExposureIncrement_succ_of_lt μ f k.isLt S

/-- The shifted-exposure sum a.e.-equals `f - ∫ f dμⁿ`. -/
lemma sum_shiftedExposureIncrement_eq_ae
    [IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ))]
    {f : (Fin n → Z) → ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    (fun S => ∑ k ∈ Finset.range (n + 1), shiftedExposureIncrement μ f k S)
      =ᵐ[Measure.pi (fun _ : Fin n => μ)]
        fun S => f S - ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) := by
  have h := sum_exposureIncrement_eq_ae (μ := μ) hf hfi
  filter_upwards [h] with S hS
  rw [sum_shiftedExposureIncrement_eq]
  exact hS

/-! ### Strong adaptedness of `shiftedExposureIncrement` to
`coordinateFiltrationNat` -/

lemma shiftedExposureIncrement_stronglyAdapted
    [IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ))]
    {f : (Fin n → Z) → ℝ} :
    StronglyAdapted (coordinateFiltrationNat n Z)
      (shiftedExposureIncrement μ f) := by
  intro k
  -- Show `shiftedExposureIncrement μ f k` is `(coordinateFiltrationNat n Z) k`-strongly-measurable.
  match k with
  | 0 =>
    -- Y 0 = 0, trivially strongly measurable.
    show StronglyMeasurable[(coordinateFiltrationNat n Z) 0] (shiftedExposureIncrement μ f 0)
    rw [shiftedExposureIncrement_zero]
    exact stronglyMeasurable_const
  | (j + 1) =>
    -- Y (j + 1) is exposureIncrement at index j (or 0 if j ≥ n).
    show StronglyMeasurable[(coordinateFiltrationNat n Z) (j + 1)]
      (shiftedExposureIncrement μ f (j + 1))
    by_cases hj : j < n
    · -- j < n: shiftedExposureIncrement μ f (j+1) S = exposureIncrement μ f ⟨j, hj⟩ S.
      -- exposureIncrement = M_{succ ⟨j,_⟩} - M_{castSucc ⟨j,_⟩}.
      -- M_{succ ⟨j,_⟩} = E[f | F_{⟨j+1,_⟩}], strongly meas. on F_{⟨j+1,_⟩} = ℱ_{j+1}.
      -- M_{castSucc ⟨j,_⟩} = E[f | F_{⟨j,_⟩}], strongly meas. on F_{⟨j,_⟩} ⊆ F_{⟨j+1,_⟩} = ℱ_{j+1}.
      have h_funext : shiftedExposureIncrement μ f (j + 1)
          = exposureIncrement μ f ⟨j, hj⟩ := by
        funext S
        exact shiftedExposureIncrement_succ_of_lt μ f hj S
      rw [h_funext]
      -- Δ_⟨j,_⟩ is F_{succ ⟨j,_⟩} = F_{⟨j+1,_⟩}-strongly-measurable.
      -- We need ℱ_{j+1}-strongly-measurable, where ℱ = coordinateFiltrationNat.
      have hjsucc : j + 1 ≤ n := hj
      have h_filt : (coordinateFiltrationNat n Z) (j + 1) =
          coordinateSubAlgebra n Z ⟨j + 1, Nat.lt_succ_of_le hjsucc⟩ :=
        coordinateFiltrationNat_eq_of_le hjsucc
      rw [h_filt]
      -- exposureIncrement = M_{succ} - M_{castSucc}.
      show StronglyMeasurable[coordinateSubAlgebra n Z ⟨j + 1, Nat.lt_succ_of_le hjsucc⟩]
        (fun S => exposureMartingale μ f (Fin.mk j hj).succ S
          - exposureMartingale μ f (Fin.mk j hj).castSucc S)
      refine StronglyMeasurable.sub ?_ ?_
      · -- M_{succ ⟨j,hj⟩} = M_{⟨j+1, _⟩} is strongly meas. on F_{⟨j+1,_⟩}.
        have : (Fin.mk j hj).succ = ⟨j + 1, Nat.lt_succ_of_le hjsucc⟩ := rfl
        rw [this]
        exact stronglyMeasurable_condExp
      · -- M_{castSucc ⟨j,hj⟩} = M_{⟨j, _⟩} on F_{⟨j,_⟩} ⊆ F_{⟨j+1,_⟩}.
        have : (Fin.mk j hj).castSucc = ⟨j, Nat.lt_succ_of_lt hj⟩ := rfl
        rw [this]
        refine stronglyMeasurable_condExp.mono ?_
        exact coordinateSubAlgebra_mono (by simp : (⟨j, _⟩ : Fin (n+1)) ≤ ⟨j+1, _⟩)
    · -- j ≥ n: shiftedExposureIncrement μ f (j+1) = 0.
      have hjge : n ≤ j := not_lt.mp hj
      have h_funext : shiftedExposureIncrement μ f (j + 1) = 0 := by
        funext S
        exact shiftedExposureIncrement_succ_of_ge μ f hjge S
      rw [h_funext]
      exact stronglyMeasurable_const

/-! ### Sub-Gaussian properties of the padded sequence -/

/-- Y 0 = 0 is unconditional sub-Gaussian with parameter 0. -/
lemma shiftedExposureIncrement_zero_hasSubgaussianMGF
    [IsProbabilityMeasure μ] {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ} :
    HasSubgaussianMGF (shiftedExposureIncrement μ f 0)
      (shiftedSubGaussianParam c 0)
      (Measure.pi (fun _ : Fin n => μ)) := by
  rw [shiftedExposureIncrement_zero, shiftedSubGaussianParam_zero]
  exact HasSubgaussianMGF.zero

/-- For `i < n`, the (i+1)-th shifted increment is conditionally sub-Gaussian
on `(coordinateFiltrationNat n Z) i` with parameter
`shiftedSubGaussianParam c (i+1) = ‖c ⟨i, _⟩‖₊²`. -/
lemma shiftedExposureIncrement_hasCondSubgaussianMGF
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {i : ℕ} (hi : i < n) :
    HasCondSubgaussianMGF
      ((coordinateFiltrationNat n Z) i)
      ((coordinateFiltrationNat n Z).le i)
      (shiftedExposureIncrement μ f (i + 1))
      (shiftedSubGaussianParam c (i + 1))
      (Measure.pi (fun _ : Fin n => μ)) := by
  -- ℱ i = coordinateSubAlgebra n Z ⟨i, _⟩ since i ≤ n.
  have hile : i ≤ n := hi.le
  have hfilt : (coordinateFiltrationNat n Z) i =
      coordinateSubAlgebra n Z ⟨i, Nat.lt_succ_of_le hile⟩ :=
    coordinateFiltrationNat_eq_of_le hile
  -- Y (i+1) = exposureIncrement at ⟨i, hi⟩.
  have hY : shiftedExposureIncrement μ f (i + 1) =
      exposureIncrement μ f ⟨i, hi⟩ := by
    funext S; exact shiftedExposureIncrement_succ_of_lt μ f hi S
  -- cY (i+1) = ‖c ⟨i, hi⟩‖₊².
  have hcY : shiftedSubGaussianParam c (i + 1) = ‖c ⟨i, hi⟩‖₊ ^ 2 :=
    shiftedSubGaussianParam_succ_of_lt c hi
  -- The Fin n increment: (Fin.mk i hi).castSucc = ⟨i, _⟩ as Fin (n+1).
  have hcast : (⟨i, hi⟩ : Fin n).castSucc =
      ⟨i, Nat.lt_succ_of_le hile⟩ := rfl
  rw [hY, hcY]
  -- Reduce to `exposureIncrement_hasCondSubgaussianMGF` at k = ⟨i, hi⟩.
  have h := exposureIncrement_hasCondSubgaussianMGF
    (μ := μ) hbdd hf hfi ⟨i, hi⟩ (hc ⟨i, hi⟩)
  rw [hcast] at h
  -- Goal has filtration `(coordinateFiltrationNat n Z) i`; `h` has the equal
  -- `coordinateSubAlgebra n Z ⟨i, _⟩`. The `.le` proofs are propositions and
  -- proof-irrelevant once the spaces match. `convert ... using 2` dispatches
  -- the space equality and HEq proof-irrelevance subgoals automatically.
  convert h using 2

/-- Sharp version of `shiftedExposureIncrement_hasCondSubgaussianMGF`, using
the per-coordinate proxy `(‖c k‖₊ / 2)²`. -/
lemma shiftedExposureIncrement_hasCondSubgaussianMGF_sharp
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {i : ℕ} (hi : i < n) :
    HasCondSubgaussianMGF
      ((coordinateFiltrationNat n Z) i)
      ((coordinateFiltrationNat n Z).le i)
      (shiftedExposureIncrement μ f (i + 1))
      (shiftedSharpSubGaussianParam c (i + 1))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hile : i ≤ n := hi.le
  have hfilt : (coordinateFiltrationNat n Z) i =
      coordinateSubAlgebra n Z ⟨i, Nat.lt_succ_of_le hile⟩ :=
    coordinateFiltrationNat_eq_of_le hile
  have hY : shiftedExposureIncrement μ f (i + 1) =
      exposureIncrement μ f ⟨i, hi⟩ := by
    funext S; exact shiftedExposureIncrement_succ_of_lt μ f hi S
  have hcY : shiftedSharpSubGaussianParam c (i + 1) =
      (‖c ⟨i, hi⟩‖₊ / 2 : ℝ≥0) ^ 2 :=
    shiftedSharpSubGaussianParam_succ_of_lt c hi
  have hcast : (⟨i, hi⟩ : Fin n).castSucc =
      ⟨i, Nat.lt_succ_of_le hile⟩ := rfl
  rw [hY, hcY]
  have h := exposureIncrement_hasCondSubgaussianMGF_sharp
    (μ := μ) hbdd hf hfi ⟨i, hi⟩ (hc ⟨i, hi⟩)
  rw [hcast] at h
  convert h using 2

/-! ### Main theorem: Azuma-style tail for `HasBoundedDifferences` -/

/-- One-sided Azuma-style tail bound for any function with bounded
differences, on a product probability measure. The constant is the
Azuma one: `‖c k‖₊²` per coordinate. -/
theorem hasBoundedDifferences_tail_azuma
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (- ε ^ 2 / (2 * (∑ k : Fin n, ‖c k‖₊ ^ 2 : ℝ≥0))) := by
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)) := inferInstance
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with μn_def
  set ℱ := coordinateFiltrationNat n Z
  set Y := shiftedExposureIncrement μ f
  set cY := shiftedSubGaussianParam c
  -- Strongly adapted.
  have h_adapted : StronglyAdapted ℱ Y :=
    shiftedExposureIncrement_stronglyAdapted (μ := μ) (f := f)
  -- Y 0 unconditional sub-Gaussian.
  have h0 : HasSubgaussianMGF (Y 0) (cY 0) μn :=
    shiftedExposureIncrement_zero_hasSubgaussianMGF (μ := μ) (f := f) (c := c)
  -- Y (i+1) conditional sub-Gaussian for i < n.
  have h_subG : ∀ i, i < (n + 1) - 1 →
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μn := by
    intro i hi
    have hi' : i < n := by simpa using hi
    exact shiftedExposureIncrement_hasCondSubgaussianMGF
      (μ := μ) hbdd hf hfi hc hi'
  -- Apply mathlib Azuma to get a tail bound on the sum of Y_k.
  have h_azuma :
      μn.real {ω | ε ≤ ∑ i ∈ Finset.range (n + 1), Y i ω}
        ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range (n + 1), cY i)) :=
    measure_sum_ge_le_of_hasCondSubgaussianMGF
      h_adapted h0 (n + 1) h_subG hε
  -- The sum collapses: ∑ cY = ∑_{k : Fin n} ‖c k‖₊².
  have h_sum_cY : ∑ i ∈ Finset.range (n + 1), cY i
      = ∑ k : Fin n, ‖c k‖₊ ^ 2 :=
    sum_shiftedSubGaussianParam c
  -- The set under μn equals (a.e.) {S | E[f] + ε ≤ f S}.
  have h_telescope : (fun S => ∑ k ∈ Finset.range (n + 1), Y k S)
      =ᵐ[μn] fun S => f S - ∫ s, f s ∂μn :=
    sum_shiftedExposureIncrement_eq_ae hf hfi
  have h_set_eq : {ω | ε ≤ ∑ i ∈ Finset.range (n + 1), Y i ω}
      =ᵐ[μn] {S | ∫ s, f s ∂μn + ε ≤ f S} := by
    filter_upwards [h_telescope] with S hS
    -- Goal is `{ω | P ω} S = {ω | Q ω} S` i.e. `P S = Q S` (Prop = Prop).
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · -- h : ε ≤ ∑ Y k S, hS : ∑ Y k S = f S - ∫ f. Conclude ∫ f + ε ≤ f S.
      change ε ≤ ∑ k ∈ Finset.range (n + 1), Y k S at h
      change ∫ s, f s ∂μn + ε ≤ f S
      rw [hS] at h; linarith
    · -- h : ∫ f + ε ≤ f S. Conclude ε ≤ ∑ Y k S = f S - ∫ f.
      change ∫ s, f s ∂μn + ε ≤ f S at h
      change ε ≤ ∑ k ∈ Finset.range (n + 1), Y k S
      rw [hS]; linarith
  rw [Measure.real, MeasureTheory.measure_congr h_set_eq,
      ← Measure.real, h_sum_cY] at h_azuma
  exact h_azuma

/-! ### Sharp McDiarmid tail for `HasBoundedDifferences` -/

/-- One-sided sharp McDiarmid tail bound for any function with bounded
differences on a product probability measure.

This is the bounded-differences theorem with the McDiarmid constant:
the kth exposure increment is conditionally sub-Gaussian with proxy
`(‖c k‖₊ / 2)²`, and summing those proxies gives the exponent
`-2 * ε² / ∑ k, (c k)²` when the supplied widths are nonnegative. -/
theorem hasBoundedDifferences_tail_sharp
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hbdd : HasBoundedDifferences f c)
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    (hc : ∀ k, 0 ≤ c k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)) + ε ≤ f S}
      ≤ Real.exp (-2 * ε ^ 2 / ∑ k : Fin n, (c k) ^ 2) := by
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)) := inferInstance
  set μn : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => μ) with μn_def
  set ℱ := coordinateFiltrationNat n Z
  set Y := shiftedExposureIncrement μ f
  set cY := shiftedSharpSubGaussianParam c
  have h_adapted : StronglyAdapted ℱ Y :=
    shiftedExposureIncrement_stronglyAdapted (μ := μ) (f := f)
  have h0 : HasSubgaussianMGF (Y 0) (cY 0) μn := by
    dsimp [Y, cY, shiftedExposureIncrement, shiftedSharpSubGaussianParam]
    exact HasSubgaussianMGF.zero
  have h_subG : ∀ i, i < (n + 1) - 1 →
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μn := by
    intro i hi
    have hi' : i < n := by simpa using hi
    exact shiftedExposureIncrement_hasCondSubgaussianMGF_sharp
      (μ := μ) hbdd hf hfi hc hi'
  have h_engine :
      μn.real {ω | ε ≤ ∑ i ∈ Finset.range (n + 1), Y i ω}
        ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range (n + 1), cY i)) :=
    measure_sum_ge_le_of_hasCondSubgaussianMGF
      h_adapted h0 (n + 1) h_subG hε
  have h_sum_cY : ∑ i ∈ Finset.range (n + 1), cY i
      = ∑ k : Fin n, (‖c k‖₊ / 2 : ℝ≥0) ^ 2 :=
    sum_shiftedSharpSubGaussianParam c
  have h_telescope : (fun S => ∑ k ∈ Finset.range (n + 1), Y k S)
      =ᵐ[μn] fun S => f S - ∫ s, f s ∂μn :=
    sum_shiftedExposureIncrement_eq_ae hf hfi
  have h_set_eq : {ω | ε ≤ ∑ i ∈ Finset.range (n + 1), Y i ω}
      =ᵐ[μn] {S | ∫ s, f s ∂μn + ε ≤ f S} := by
    filter_upwards [h_telescope] with S hS
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · change ∫ s, f s ∂μn + ε ≤ f S
      change ε ≤ ∑ k ∈ Finset.range (n + 1), Y k S at h
      rw [hS] at h; linarith
    · change ε ≤ ∑ k ∈ Finset.range (n + 1), Y k S
      change ∫ s, f s ∂μn + ε ≤ f S at h
      rw [hS]; linarith
  rw [Measure.real, MeasureTheory.measure_congr h_set_eq,
      ← Measure.real, h_sum_cY] at h_engine
  refine h_engine.trans (le_of_eq ?_)
  congr 1
  have hcoe : ∀ k : Fin n, ((‖c k‖₊ : ℝ≥0) : ℝ) = c k := fun k => by
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hc k)]
  have hsum_cast : ((∑ k : Fin n, (‖c k‖₊ / 2 : ℝ≥0) ^ 2 : ℝ≥0) : ℝ)
      = (∑ k : Fin n, (c k) ^ 2) / 4 := by
    push_cast [hcoe]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum_cast]
  ring

/-! ### Specialisation: Azuma tail for the generalisation gap -/

/-- Azuma-style one-sided tail bound for the generalisation gap on the iid
product measure. Specialises `hasBoundedDifferences_tail_azuma` to
`genGap μ ℓ` via `genGap_hasBoundedDifferences`, with the bounded-difference
constant `c k = 2 * B / n` from a uniformly `B`-bounded loss class.

The sub-Gaussian sum `∑_k ‖2*B/n‖₊²` evaluates to `4*B²/n` as a real
(see `genGap_tail_bound_azuma_explicit` for the simplified form). -/
theorem genGap_tail_bound_azuma {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, genGap μ ℓ s ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 / (2 *
          (∑ _k : Fin n, ‖(2 * B / n : ℝ)‖₊ ^ 2 : ℝ≥0))) := by
  have hbdd : HasBoundedDifferences (fun S : Fin n → Z => genGap μ ℓ S)
      (fun _ : Fin n => 2 * B / n) :=
    genGap_hasBoundedDifferences μ ℓ hB hℓ_bdd hn
  have hf : StronglyMeasurable (fun S : Fin n → Z => genGap μ ℓ S) :=
    (measurable_genGap μ hℓ_meas).stronglyMeasurable
  have hfi : Integrable (fun S : Fin n → Z => genGap μ ℓ S)
      (Measure.pi (fun _ : Fin n => μ)) := by
    have h := integrable_genGap μ hB hℓ_meas hℓ_bdd hn
    simpa [piMeasure] using h
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hc : ∀ _k : Fin n, 0 ≤ (2 * B / n : ℝ) := fun _ =>
    div_nonneg (by linarith) hn_real
  exact hasBoundedDifferences_tail_azuma hbdd hf hfi hc hε

/-- Explicit form of the Azuma genGap tail bound: with `c_k = 2 * B / n`,
the sub-Gaussian sum reduces to `4 * B² / n`, giving the exponent
`-n * ε² / (8 * B²)`.

Stated as `Real.exp (- ε^2 * n / (8 * B^2))` to keep the argument a single
real expression. Requires `0 < B` to make the denominator non-degenerate;
the `B = 0` case is the trivial deterministic bound `genGap = 0`. -/
theorem genGap_tail_bound_azuma_explicit {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, genGap μ ℓ s ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 * n / (8 * B ^ 2)) := by
  have hbase := genGap_tail_bound_azuma (μ := μ)
    hB.le hℓ_meas hℓ_bdd hn hε
  -- Identify the literal sub-Gaussian sum with `4 * B^2 / n`.
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  have hc_nonneg : (0 : ℝ) ≤ 2 * B / n :=
    div_nonneg (by linarith) hn_real.le
  -- The NNReal coercion of `‖2*B/n‖₊` back to ℝ recovers `2*B/n` since it is ≥ 0.
  have h_coe : ((‖(2 * B / n : ℝ)‖₊ : ℝ≥0) : ℝ) = 2 * B / n := by
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  -- ∑_k ‖2*B/n‖₊² as a real equals 4*B²/n.
  have hsum_cast : ((∑ _k : Fin n, ‖(2 * B / n : ℝ)‖₊ ^ 2 : ℝ≥0) : ℝ)
      = 4 * B ^ 2 / n := by
    rw [NNReal.coe_sum]
    simp only [NNReal.coe_pow, h_coe]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- Compare exponents: -ε²/(2 * (4B²/n)) = -ε² * n / (8 * B²).
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hexp_eq : (-ε ^ 2) / (2 *
      ((∑ _k : Fin n, ‖(2 * B / n : ℝ)‖₊ ^ 2 : ℝ≥0) : ℝ))
      = -ε ^ 2 * n / (8 * B ^ 2) := by
    rw [hsum_cast]
    field_simp
    ring
  rw [hexp_eq] at hbase
  exact hbase

/-! ### Specialisation: sharp McDiarmid tail for the generalisation gap -/

/-- Sharp McDiarmid one-sided tail bound for the generalisation gap on the iid
product measure. This specialises `hasBoundedDifferences_tail_sharp` to
`genGap μ ℓ` via `genGap_hasBoundedDifferences`, with bounded-difference width
`c k = 2 * B / n`. -/
theorem genGap_tail_bound_sharp {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, genGap μ ℓ s ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ genGap μ ℓ S}
      ≤ Real.exp (-2 * ε ^ 2 /
          (∑ _k : Fin n, (2 * B / n : ℝ) ^ 2)) := by
  have hbdd : HasBoundedDifferences (fun S : Fin n → Z => genGap μ ℓ S)
      (fun _ : Fin n => 2 * B / n) :=
    genGap_hasBoundedDifferences μ ℓ hB hℓ_bdd hn
  have hf : StronglyMeasurable (fun S : Fin n → Z => genGap μ ℓ S) :=
    (measurable_genGap μ hℓ_meas).stronglyMeasurable
  have hfi : Integrable (fun S : Fin n → Z => genGap μ ℓ S)
      (Measure.pi (fun _ : Fin n => μ)) := by
    have h := integrable_genGap μ hB hℓ_meas hℓ_bdd hn
    simpa [piMeasure] using h
  have hn_real : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hc : ∀ _k : Fin n, 0 ≤ (2 * B / n : ℝ) := fun _ =>
    div_nonneg (by linarith) hn_real
  exact hasBoundedDifferences_tail_sharp hbdd hf hfi hc hε

/-- Explicit sharp McDiarmid genGap tail bound. With `c_k = 2 * B / n`,
the squared-width sum is `4 * B² / n`, so the exponent simplifies to
`-n * ε² / (2 * B²)`. -/
theorem genGap_tail_bound_sharp_explicit {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {S | ∫ s, genGap μ ℓ s ∂(Measure.pi (fun _ : Fin n => μ)) + ε
              ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 * n / (2 * B ^ 2)) := by
  have hbase := genGap_tail_bound_sharp (μ := μ)
    hB.le hℓ_meas hℓ_bdd hn hε
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hsum : (∑ _k : Fin n, (2 * B / n : ℝ) ^ 2) = 4 * B ^ 2 / n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hexp_eq : -2 * ε ^ 2 / (4 * B ^ 2 / n)
      = - ε ^ 2 * n / (2 * B ^ 2) := by
    field_simp
    ring
  rw [hsum, hexp_eq] at hbase
  exact hbase

end FormalSLT.Azuma.ExposureMartingale
