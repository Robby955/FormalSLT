import FormalSLT.Rademacher.Massart
import FormalSLT.VC.PACBridge

/-!
# Effective-class Rademacher bound and VC connection

The empirical Rademacher complexity depends only on the *distinct loss vectors*
on a sample, not on the total hypothesis-class size. This module formalizes
this reduction and connects it to the Sauer-Shelah growth-function bound.

## Main results

1. `empiricalRademacherComplexity_le_massart_effective`: The Massart bound
   with effective cardinality (number of distinct loss patterns on the sample)
   replacing `Fintype.card ι`.

2. A direct connection showing that for any finite hypothesis class with
   effective cardinality K on sample z:

       empiricalRademacherComplexity ℓ z ≤ B · √(2 · log K / n)

   This strictly improves on `massart_finite_class` when the class has many
   hypotheses that induce identical loss patterns on the sample.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace FormalSLT.VC.Rademacher

open FormalSLT.Rademacher.FiniteSample (signOfBool empiricalRademacherComplexity)
open FormalSLT.Rademacher.Massart (massart_finite_class)

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]

/-- The loss-vector map: sends each hypothesis to its loss pattern on a sample. -/
def lossVector (ℓ : ι → Z → ℝ) (z : Fin n → Z) (i : ι) : Fin n → ℝ :=
  fun k => ℓ i (z k)

/-- The effective class on a sample: the set of distinct loss vectors. -/
def effectiveClass (ℓ : ι → Z → ℝ) (z : Fin n → Z) : Finset (Fin n → ℝ) :=
  (Finset.univ : Finset ι).image (lossVector ℓ z)

/-- The effective class is nonempty (since ι is nonempty). -/
lemma effectiveClass_nonempty (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    (effectiveClass ℓ z).Nonempty :=
  Finset.Nonempty.image Finset.univ_nonempty _

omit [Nonempty ι] in
/-- The effective class cardinality is at most the full class size. -/
lemma effectiveClass_card_le (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    (effectiveClass ℓ z).card ≤ Fintype.card ι :=
  Finset.card_image_le

/-- The inner sup in the empirical Rademacher complexity factors through the
loss-vector map, so it equals the sup over the effective class.

This is the key reduction: the signed-average sup depends on i only through
the loss pattern `(ℓ i (z 0), ..., ℓ i (z (n-1)))`. -/
lemma sup'_eq_sup'_effectiveClass (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    (σ : Fin n → Bool) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
      = (effectiveClass ℓ z).sup' (effectiveClass_nonempty ℓ z)
          (fun v => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * v k) := by
  -- Rewrite the LHS function as a composition with lossVector.
  have h_comp : (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k))
      = (fun v => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * v k) ∘ (lossVector ℓ z) := by
    ext i; simp [lossVector]
  rw [h_comp, Finset.sup'_comp_eq_image]
  rfl

/-- **Massart bound with effective cardinality.**

The empirical Rademacher complexity is bounded by the Massart expression
with `|effectiveClass|` (number of distinct loss patterns on the sample)
in place of `Fintype.card ι`.

This improves on `massart_finite_class` whenever the hypothesis class has
redundant hypotheses that agree on the sample. -/
theorem empiricalRademacherComplexity_le_massart_effective
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (z : Fin n → Z) (hn : 0 < n)
    (hEffCard : 1 < (effectiveClass ℓ z).card) :
    empiricalRademacherComplexity ℓ z
      ≤ B * Real.sqrt (2 * Real.log ((effectiveClass ℓ z).card : ℝ) / (n : ℝ)) := by
  set S := effectiveClass ℓ z
  -- The effective class as a type, with Nonempty and Fintype instances.
  haveI hS_nonempty : Nonempty ↥S :=
    Finset.nonempty_coe_sort.mpr (effectiveClass_nonempty ℓ z)
  -- The reduced loss function on the effective class.
  let ℓ_eff : ↥S → (Fin n) → ℝ := fun ⟨v, _⟩ k => v k
  -- Boundedness of the reduced loss.
  have hℓ_eff_bdd : ∀ (j : ↥S) (k : Fin n), |ℓ_eff j k| ≤ B := by
    intro ⟨v, hv⟩ k
    simp only [S, effectiveClass, Finset.mem_image] at hv
    obtain ⟨i, _, rfl⟩ := hv
    simp only [lossVector, ℓ_eff]
    exact hℓ_bdd i (z k)
  -- Cardinality: 1 < Fintype.card ↥S.
  have hCard' : 1 < Fintype.card ↥S := by
    rw [Fintype.card_coe]; exact hEffCard
  -- Apply Massart to the reduced class (with z := id : Fin n → Fin n).
  have h_massart : empiricalRademacherComplexity ℓ_eff id
      ≤ B * Real.sqrt (2 * Real.log (Fintype.card ↥S : ℝ) / (n : ℝ)) :=
    massart_finite_class (z := id) hB (fun j k => hℓ_eff_bdd j k) hn hCard'
  -- Rewrite the card to S.card.
  rw [Fintype.card_coe] at h_massart
  -- Suffices to show the original Rademacher complexity equals the reduced one.
  suffices h_eq : empiricalRademacherComplexity ℓ z = empiricalRademacherComplexity ℓ_eff id by
    rw [h_eq]; exact h_massart
  -- Prove the equality of Rademacher complexities.
  unfold empiricalRademacherComplexity
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  -- For each σ, show the sup over ι equals the sup over ↥S.
  -- Step 1: sup over ι = sup over S (as a Finset).
  rw [sup'_eq_sup'_effectiveClass ℓ z σ]
  -- Step 2: sup over ↥S (as a type) = sup over S (as a Finset).
  symm
  -- The function on ↥S factors through Subtype.val.
  have h_comp : (fun (j : ↥S) => (↑n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ_eff j (id k))
      = (fun v => (↑n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * v k) ∘ Subtype.val := rfl
  rw [h_comp, Finset.sup'_comp_eq_image]
  -- Goal: (univ.image Subtype.val).sup' _ g = S.sup' _ g
  -- It suffices to show (univ : Finset ↥S).image Subtype.val = S.
  congr 1
  rw [Finset.univ_eq_attach]
  exact Finset.attach_image_val

end FormalSLT.VC.Rademacher
