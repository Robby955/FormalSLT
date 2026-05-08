import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import FormalSLT.VC.Dimension

/-!
# VC dimension to PAC: trace family bridge

Connects the existing mathlib VC machinery (`Finset.vcDim`,
`Finset.shatterer`, Sauer-Shelah) and the existing
`FormalSLT.VC.Dimension.sauerShelahFiniteSetFamily`
wrapper to a "binary hypothesis class on a finite sample" picture
typically used in PAC theory.

What this module provides (all closed, no `sorry`, no `admit`):

* `binaryClassTrace` — for a binary hypothesis class
  `h : ι → α → Bool`, a finite sample `z : Fin n → α`, returns the
  finite set family `𝒜 : Finset (Finset (Fin n))` whose elements are
  the subsets `{k | h i (z k) = true}` as `i` ranges over the index
  type. This is the standard "labeling pattern" set produced by the
  hypothesis class restricted to the sample.

* `card_binaryClassTrace_le_two_pow_n` — the trivial growth-function
  bound: the number of distinct labeling patterns is at most `2^n`,
  the total number of subsets of the sample.

* `card_binaryClassTrace_le_sauerShelah` — Sauer-Shelah growth-function
  bound: the number of distinct labeling patterns is at most
  `∑_{k ≤ d} C(n, k)` where `d` is the VC dimension of the trace
  family.

Out of scope (deferred to a later PR):

- The polynomial closed form `(en/d)^d` of the Sauer-Shelah bound.
- Symmetrization+contraction chain that converts the growth-function
  bound to a Rademacher-complexity bound.
- Massart's lemma (`Rademacher ≤ √(2 log Π / n)`) and the full PAC
  sample complexity statement.
- Connection to the existing `Risk` / `ERMGeneralization` /
  `FiniteSampleRademacher` chains. Those are intentionally separate;
  the bridge is one combinatorial step at a time.
-/

namespace FormalSLT.VC.PACBridge

open Finset

variable {ι α : Type*} [Fintype ι]
variable {n : ℕ}

/-- The finite set family of "labeling patterns" produced by a binary
hypothesis class `h : ι → α → Bool` restricted to a finite sample
`z : Fin n → α`. Each hypothesis `i : ι` produces the subset
`{k : Fin n | h i (z k) = true}`, and `binaryClassTrace` collects all
distinct such subsets. -/
def binaryClassTrace
    (h : ι → α → Bool) (z : Fin n → α) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset ι).image
    (fun i => (Finset.univ : Finset (Fin n)).filter (fun k => h i (z k) = true))

/-- The trivial growth-function bound: the number of distinct labeling
patterns produced by *any* hypothesis class on a sample of size `n` is
bounded by `2^n`, the total number of subsets of the sample. -/
lemma card_binaryClassTrace_le_two_pow_n
    (h : ι → α → Bool) (z : Fin n → α) :
    (binaryClassTrace h z).card ≤ 2 ^ n := by
  -- The trace is a subset of `(univ : Finset (Fin n)).powerset`, whose
  -- cardinality is `2 ^ Fintype.card (Fin n) = 2 ^ n`.
  have h_subset :
      binaryClassTrace h z ⊆ (Finset.univ : Finset (Fin n)).powerset := by
    intro s hs
    simp only [binaryClassTrace, Finset.mem_image] at hs
    obtain ⟨i, _, rfl⟩ := hs
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  calc (binaryClassTrace h z).card
      ≤ ((Finset.univ : Finset (Fin n)).powerset).card :=
        Finset.card_le_card h_subset
    _ = 2 ^ (Finset.univ : Finset (Fin n)).card := Finset.card_powerset _
    _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_fin]

/-- **Sauer-Shelah growth-function bound for binary hypothesis classes.**

For a binary hypothesis class `h : ι → α → Bool` and a finite sample
`z : Fin n → α`, the number of distinct labeling patterns produced is
bounded by `∑_{k ≤ d} C(n, k)`, where `d` is the VC dimension of the
*trace family* on the sample.

Direct application of `FormalSLT.VC.Dimension.sauerShelahFiniteSetFamily`
to the trace family. The VC dimension of the trace is bounded by the
"intrinsic" VC dimension of the class (the dimension realized by *some*
sample); we deliberately state the bound in terms of the
sample-dependent trace VC dimension to keep the PR strict-scope. -/
theorem card_binaryClassTrace_le_sauerShelah
    (h : ι → α → Bool) (z : Fin n → α) :
    (binaryClassTrace h z).card ≤
      ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim,
        (Fintype.card (Fin n)).choose k :=
  FormalSLT.VC.Dimension.sauerShelahFiniteSetFamily
    (binaryClassTrace h z)

/-- Restated `card_binaryClassTrace_le_sauerShelah` with `n` directly
in the binomial-coefficient sum (using `Fintype.card_fin`). -/
theorem card_binaryClassTrace_le_sauerShelah'
    (h : ι → α → Bool) (z : Fin n → α) :
    (binaryClassTrace h z).card ≤
      ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim, n.choose k := by
  have h_eq : Fintype.card (Fin n) = n := Fintype.card_fin n
  calc (binaryClassTrace h z).card
      ≤ ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim,
          (Fintype.card (Fin n)).choose k :=
        card_binaryClassTrace_le_sauerShelah h z
    _ = ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim, n.choose k := by
        rw [h_eq]

end FormalSLT.VC.PACBridge
