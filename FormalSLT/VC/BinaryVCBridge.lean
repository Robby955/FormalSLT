import FormalSLT.VC.Rademacher
import FormalSLT.VC.PACBridge

/-!
# Binary classifier VC → effective loss-pattern bridge

Connects binary classifier traces (`binaryClassTrace`) to the
effective loss-pattern class (`effectiveClass`) for 0-1 loss.

## Main result

`effectiveClass_zeroOneLoss_card_eq_binaryClassTrace`:
  For binary classifiers `h : ι → α → Bool` and a feature sample
  `x : Fin n → α`, the zero-one loss class on the feature sample has
  exactly the same number of distinct loss patterns as the binary trace
  has distinct labeling patterns.

## Strategy

Both the effective class and the binary trace are images of `Finset.univ`
under maps that factor through the *prediction pattern*
`predictionPattern h x : ι → (Fin n → Bool)`:

  effectiveClass = (univ.image predPat).image toLossVec
  binaryClassTrace = (univ.image predPat).image toFilterSet

Both `toLossVec` and `toFilterSet` are injective, so applying
`card_image_of_injective` gives the result.

## Scope

- Binary classifiers only (`h : ι → α → Bool`)
- Zero-one loss only
- Finite hypothesis index (`[Fintype ι]`)
- Finite sample (`Fin n → α`)
- No real-valued loss classes
- No infinite-class measurability
- No generic PAC equivalence
- No contraction

No `sorry`, no `admit`, no custom `axiom`.
-/

open Finset

namespace FormalSLT.VC.BinaryVCBridge

open FormalSLT.VC.Rademacher (lossVector effectiveClass)
open FormalSLT.VC.PACBridge (binaryClassTrace)

variable {ι α : Type*} [Fintype ι] [Nonempty ι]
variable {n : ℕ}

/-- The zero-one loss induced by a binary classifier on feature data.
    `zeroOneLoss h i x = if h i x = true then 0 else 1`. -/
def zeroOneLoss (h : ι → α → Bool) : ι → α → ℝ :=
  fun i x => if h i x = true then (0 : ℝ) else 1

/-- The prediction pattern: for each hypothesis, its Boolean output on
    every sample point. -/
def predictionPattern (h : ι → α → Bool) (x : Fin n → α) (i : ι) : Fin n → Bool :=
  fun k => h i (x k)

/-- Convert a prediction pattern to its zero-one loss vector. -/
def toLossVec : (Fin n → Bool) → (Fin n → ℝ) :=
  fun p k => if p k = true then (0 : ℝ) else 1

/-- Convert a prediction pattern to its filter set (indices where true). -/
def toFilterSet : (Fin n → Bool) → Finset (Fin n) :=
  fun p => (Finset.univ : Finset (Fin n)).filter (fun k => p k = true)

omit [Fintype ι] [Nonempty ι] in
/-- The loss-vector map factors as `toLossVec ∘ predictionPattern`. -/
lemma lossVector_eq_toLossVec_comp (h : ι → α → Bool) (x : Fin n → α) :
    lossVector (zeroOneLoss h) x = toLossVec ∘ predictionPattern h x := by
  funext i k; rfl

omit [Fintype ι] [Nonempty ι] in
/-- The filter-set map factors as `toFilterSet ∘ predictionPattern`. -/
lemma binaryTrace_map_eq_toFilterSet_comp (h : ι → α → Bool) (x : Fin n → α) :
    (fun i => (Finset.univ : Finset (Fin n)).filter (fun k => h i (x k) = true))
      = toFilterSet ∘ predictionPattern h x := by
  funext i; rfl

/-- `toLossVec` is injective: distinct prediction patterns yield distinct loss vectors. -/
lemma toLossVec_injective : Function.Injective (toLossVec : (Fin n → Bool) → (Fin n → ℝ)) := by
  intro p q heq
  ext k
  have hk := congr_fun heq k
  simp only [toLossVec] at hk
  by_cases hp : p k = true
  · simp [hp] at hk
    by_cases hq : q k = true
    · exact hp ▸ hq ▸ rfl
    · simp [hq] at hk
  · simp [hp] at hk
    by_cases hq : q k = true
    · simp [hq] at hk
    · exact (Bool.eq_false_iff.mpr hp) ▸ (Bool.eq_false_iff.mpr hq) ▸ rfl

/-- `toFilterSet` is injective: distinct prediction patterns yield distinct filter sets. -/
lemma toFilterSet_injective : Function.Injective (toFilterSet : (Fin n → Bool) → Finset (Fin n)) := by
  intro p q heq
  funext k
  have : (k ∈ toFilterSet p) ↔ (k ∈ toFilterSet q) := by rw [heq]
  simp only [toFilterSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
  -- this : p k = true ↔ q k = true
  cases hp : p k <;> cases hq : q k <;> simp_all

omit [Nonempty ι] in
/-- The effective class (as an image) equals the image of the prediction-pattern
    image through `toLossVec`. -/
lemma effectiveClass_eq_image_toLossVec (h : ι → α → Bool) (x : Fin n → α) :
    effectiveClass (zeroOneLoss h) x =
      ((Finset.univ : Finset ι).image (predictionPattern h x)).image toLossVec := by
  unfold effectiveClass
  rw [lossVector_eq_toLossVec_comp, Finset.image_image]

omit [Nonempty ι] in
/-- The binary class trace (as an image) equals the image of the prediction-pattern
    image through `toFilterSet`. -/
lemma binaryClassTrace_eq_image_toFilterSet (h : ι → α → Bool) (x : Fin n → α) :
    binaryClassTrace h x =
      ((Finset.univ : Finset ι).image (predictionPattern h x)).image toFilterSet := by
  unfold binaryClassTrace
  rw [binaryTrace_map_eq_toFilterSet_comp, Finset.image_image]

omit [Nonempty ι] in
/-- **Binary VC → effective loss-pattern bridge (equality).**

For binary classifiers `h : ι → α → Bool` and a feature sample
`x : Fin n → α`, the number of distinct zero-one loss patterns
equals the number of distinct binary labeling patterns.

Both factor through the prediction-pattern image with injective
final maps, so they have the same cardinality. -/
theorem effectiveClass_zeroOneLoss_card_eq_binaryClassTrace
    (h : ι → α → Bool) (x : Fin n → α) :
    (effectiveClass (zeroOneLoss h) x).card = (binaryClassTrace h x).card := by
  rw [effectiveClass_eq_image_toLossVec, binaryClassTrace_eq_image_toFilterSet]
  let S := (Finset.univ : Finset ι).image (predictionPattern h x)
  show (S.image toLossVec).card = (S.image toFilterSet).card
  rw [Finset.card_image_of_injOn (Set.InjOn.mono (Finset.coe_subset.mpr (Finset.subset_univ _))
        (Set.injOn_of_injective toLossVec_injective)),
      Finset.card_image_of_injOn (Set.InjOn.mono (Finset.coe_subset.mpr (Finset.subset_univ _))
        (Set.injOn_of_injective toFilterSet_injective))]

omit [Nonempty ι] in
/-- **Corollary: effective-class growth bound from binary trace.**

For binary classifiers with 0-1 loss, the effective class satisfies
the Sauer-Shelah bound inherited from the binary trace. This removes
the "growth bound supplied externally" caveat for binary classification. -/
theorem effectiveClass_zeroOneLoss_card_le_sauerShelah
    (h : ι → α → Bool) (x : Fin n → α) :
    (effectiveClass (zeroOneLoss h) x).card ≤
      ∑ k ∈ Finset.Iic (binaryClassTrace h x).vcDim, n.choose k := by
  rw [effectiveClass_zeroOneLoss_card_eq_binaryClassTrace]
  exact FormalSLT.VC.PACBridge.card_binaryClassTrace_le_sauerShelah' h x

end FormalSLT.VC.BinaryVCBridge
