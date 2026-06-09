import FormalSLT.VC.SampleComplexity
import FormalSLT.VC.BinaryVCBridge

/-!
# Unconditional binary 0/1-loss VC-ERM capstone

Composes the binary 0/1-loss bridge
(`FormalSLT.VC.BinaryVCBridge.effectiveClass_zeroOneLoss_card_le_sauerShelah`)
into the audited VC-ERM excess-risk tail bound
(`FormalSLT.VC.SampleComplexity.vc_erm_excessRisk_tail`), discharging its two
growth-function hypotheses `hGrowth_uniform` and `hGrowth_neg` for binary
classifiers under 0-1 loss.

## Main result

`vc_erm_excessRisk_tail_binary_zeroOneLoss`: for a binary classifier
`h : ι → α → Bool` whose trace VC dimension is bounded by `d` on every sample,
the ERM excess-risk tail bound holds with no externally supplied growth
hypotheses. The 0-1 loss is bounded by `1`, so the constant `B` specializes to
`1`. The only combinatorial input is `(binaryClassTrace h z).vcDim ≤ d`, which
Sauer-Shelah turns into the growth-function bound internally.

## How the growth hypotheses are discharged

* `hGrowth_uniform`: the bridge gives
  `(effectiveClass (zeroOneLoss h) z).card ≤ ∑_{k ≤ trace.vcDim} C(n,k)`.
  Monotonicity of the binomial sum in the upper index, plus `trace.vcDim ≤ d`,
  raises the index to `d`; `Nat.range_succ_eq_Iic` rewrites `Iic d` as
  `range (d+1)`.

* `hGrowth_neg`: negating the loss is a bijection on effective classes
  (`effectiveClass_neg_card_eq`), so the negated growth bound reduces to the
  positive one.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter ProbabilityTheory Real Finset

open FormalSLT.VC.Rademacher (effectiveClass lossVector)
open FormalSLT.VC.PACBridge (binaryClassTrace)
open FormalSLT.VC.BinaryVCBridge (zeroOneLoss effectiveClass_zeroOneLoss_card_le_sauerShelah)
open FormalSLT.GhostSample (piMeasure)
open FormalSLT.Risk (risk empiricalRisk)
open FormalSLT.ERM (IsERM)

noncomputable section

namespace FormalSLT.VC.SampleComplexity

/-- Negating the loss preserves the effective-class cardinality: the map
`v ↦ -v` is a bijection between `effectiveClass (-ℓ) z` and `effectiveClass ℓ z`,
since `lossVector (-ℓ) z = (-·) ∘ lossVector ℓ z` and pointwise negation is
injective. -/
lemma effectiveClass_neg_card_eq {ι α : Type*} [Fintype ι] {n : ℕ}
    (ℓ : ι → α → ℝ) (z : Fin n → α) :
    (effectiveClass (fun i w => -ℓ i w) z).card = (effectiveClass ℓ z).card := by
  have hneg_inj : Function.Injective (fun v : Fin n → ℝ => -v) := by
    intro a b hab
    have h2 := congrArg (fun w : Fin n → ℝ => -w) hab
    simpa only [neg_neg] using h2
  have hfun : lossVector (fun i w => -ℓ i w) z
      = (fun v : Fin n → ℝ => -v) ∘ lossVector ℓ z := by
    funext i k
    simp only [lossVector, Function.comp_apply, Pi.neg_apply]
  unfold effectiveClass
  rw [hfun, ← Finset.image_image, Finset.card_image_of_injective _ hneg_inj]

/-- **Unconditional VC-ERM excess-risk tail bound for binary 0-1 loss.**

For a binary classifier `h : ι → α → Bool` with measurable per-hypothesis 0-1
loss, an iid sample `S ~ μⁿ`, any exact empirical-risk minimizer `hhat(S)`, and
a trace VC dimension bounded by `d` on every sample:

    P(risk(hhat(S)) - risk(i*) ≥ 4·√(2d·log(en/d)/n) + 2ε) ≤ 2·exp(-ε²n/8)

This is `vc_erm_excessRisk_tail` specialized to the binary 0-1 loss (`B = 1`)
with both growth-function hypotheses discharged by the Sauer-Shelah bridge. The
only structural input is the combinatorial VC-dimension bound
`(binaryClassTrace h z).vcDim ≤ d`. -/
theorem vc_erm_excessRisk_tail_binary_zeroOneLoss
    {ι α : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (h : ι → α → Bool)
    (hℓ_meas : ∀ i, Measurable (zeroOneLoss h i))
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hVC : ∀ z : Fin n → α, (binaryClassTrace h z).vcDim ≤ d)
    (hhat : (Fin n → α) → ι)
    (hERM : ∀ S : Fin n → α, IsERM (empiricalRisk S (zeroOneLoss h)) (hhat S))
    (i_star : ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | risk μ (zeroOneLoss h) i_star
              + 4 * Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑n / ↑d) / (n : ℝ))
              + 2 * ε
            ≤ risk μ (zeroOneLoss h) (hhat S)}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / 8) := by
  -- The 0-1 loss is bounded by 1, so the capstone's `B` specializes to `1`.
  have hℓ_bdd : ∀ i (w : α), |zeroOneLoss h i w| ≤ 1 := by
    intro i w
    simp only [zeroOneLoss]
    split <;> simp
  -- `Iic d = range (d + 1)` for ℕ.
  have hIic_range : Finset.Iic d = Finset.range (d + 1) := (Nat.range_succ_eq_Iic d).symm
  -- `hGrowth_uniform`: bridge + trace VC-dimension bound `≤ d`.
  have growth : ∀ z : Fin n → α,
      (effectiveClass (zeroOneLoss h) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k := by
    intro z
    calc (effectiveClass (zeroOneLoss h) z).card
        ≤ ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim, n.choose k :=
          effectiveClass_zeroOneLoss_card_le_sauerShelah h z
      _ ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
          Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr (hVC z))
      _ = ∑ k ∈ Finset.range (d + 1), n.choose k := by rw [hIic_range]
  -- `hGrowth_neg`: negation preserves effective-class cardinality.
  have growth_neg : ∀ z : Fin n → α,
      (effectiveClass (fun i w => -zeroOneLoss h i w) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k := by
    intro z
    rw [effectiveClass_neg_card_eq]
    exact growth z
  -- Apply the audited capstone with `B := 1`.
  have key := vc_erm_excessRisk_tail (μ := μ) (ℓ := zeroOneLoss h) (B := 1)
    one_pos hℓ_meas hℓ_bdd hn hd hdn growth growth_neg hhat hERM i_star hε
  simpa only [mul_one, one_pow] using key

end FormalSLT.VC.SampleComplexity
