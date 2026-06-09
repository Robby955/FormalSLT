import FormalSLT.VC.SampleComplexity
import FormalSLT.VC.BinaryVCBridge

/-!
# Unconditional VC-ERM excess-risk tail for binary 0/1 loss

The general `vc_erm_excessRisk_tail` (in `FormalSLT.VC.SampleComplexity`) takes
two *undischarged* growth hypotheses, `hGrowth_uniform` and `hGrowth_neg`, which
assert that for every sample the effective loss-pattern class is bounded by the
Sauer-Shelah growth function `∑_{k≤d} C(n,k)`. For a general bounded loss these
must be supplied by the caller.

For a **binary classifier** `h : ι → α → Bool` under the **0/1 indicator loss**,
the bridge lemma
`FormalSLT.VC.BinaryVCBridge.effectiveClass_zeroOneLoss_card_le_sauerShelah`
already proves the per-sample growth bound from the binary trace's VC dimension.
Composing it (uniformly over samples, via a fixed VC-dimension bound on the
trace) discharges *both* growth hypotheses, yielding an unconditional capstone:

    P( risk(ĥ(S)) − risk(i★) ≥ 4·√(2d·log(en/d)/n) + 2ε ) ≤ 2·exp(−ε²n/8)

The bound uses `B = 1` because the 0/1 indicator loss is bounded by `1`.

The only inputs are: a uniform bound `d` on the trace VC dimension
(`∀ x, (binaryClassTrace h x).vcDim ≤ d`) and measurability of each decision
region (`∀ i, MeasurableSet {x | h i x = true}`). No growth hypothesis is
supplied externally.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal BigOperators
open MeasureTheory Real Finset

open FormalSLT.VC.Rademacher (effectiveClass lossVector)
open FormalSLT.VC.PACBridge (binaryClassTrace)
open FormalSLT.VC.BinaryVCBridge
  (zeroOneLoss effectiveClass_zeroOneLoss_card_le_sauerShelah)
open FormalSLT.Risk (risk empiricalRisk)
open FormalSLT.ERM (IsERM)
open FormalSLT.GhostSample (piMeasure)
open FormalSLT.VC.SampleComplexity (vc_erm_excessRisk_tail)

noncomputable section

namespace FormalSLT.VC.SampleComplexityBinary

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The effective loss-pattern class of a negated loss has the same cardinality
as that of the original loss: pointwise negation on loss vectors is injective,
so it is a bijection between the two effective classes. -/
lemma effectiveClass_neg_card {Z : Type*} (ℓ : ι → Z → ℝ) {n : ℕ} (z : Fin n → Z) :
    (effectiveClass (fun i w => -ℓ i w) z).card = (effectiveClass ℓ z).card := by
  classical
  have h_eq : lossVector (fun i w => -ℓ i w) z
      = (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) ∘ lossVector ℓ z := by
    funext i k; rfl
  unfold effectiveClass
  rw [h_eq, ← Finset.image_image]
  exact Finset.card_image_of_injective _ neg_injective

/-- **Unconditional VC-ERM excess-risk tail for binary 0/1 loss.**

For a binary classifier `h : ι → α → Bool` whose decision regions are measurable
and whose induced trace family has VC dimension at most `d` on every sample of
size `n`, the 0/1-loss empirical-risk minimizer `ĥ(S)` satisfies, for an iid
sample `S ~ μⁿ` and any tolerance `ε ≥ 0`:

    P( risk(ĥ(S)) − risk(i★) ≥ 4·√(2d·log(en/d)/n) + 2ε ) ≤ 2·exp(−ε²n/8).

This is `vc_erm_excessRisk_tail` specialised to `ℓ := zeroOneLoss h` and `B := 1`,
with the two Sauer-Shelah growth hypotheses discharged internally by the binary
bridge lemma `effectiveClass_zeroOneLoss_card_le_sauerShelah`. No growth bound is
supplied by the caller. -/
theorem vc_erm_excessRisk_tail_binary_zeroOneLoss
    {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (h : ι → α → Bool)
    (hh_meas : ∀ i, MeasurableSet {x : α | h i x = true})
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hVC : ∀ x : Fin n → α, (binaryClassTrace h x).vcDim ≤ d)
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
  -- The 0/1 indicator loss is bounded by `B = 1`.
  have hℓ_bdd : ∀ i (x : α), |zeroOneLoss h i x| ≤ (1 : ℝ) := by
    intro i x
    unfold zeroOneLoss
    by_cases hx : h i x = true <;> simp [hx]
  -- Each decision region is measurable, so each 0/1 loss coordinate is measurable.
  have hℓ_meas : ∀ i, Measurable (zeroOneLoss h i) := by
    intro i
    unfold zeroOneLoss
    exact Measurable.ite (hh_meas i) measurable_const measurable_const
  -- `Finset.range (d+1) = Finset.Iic d` lets us reuse the binomial-sum growth shape.
  have hIic : Finset.range (d + 1) = Finset.Iic d := by
    ext k; simp
  -- Per-sample growth bound from the binary bridge, uniformized via `hVC`.
  have hGrowth_uniform : ∀ z : Fin n → α,
      (effectiveClass (zeroOneLoss h) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k := by
    intro z
    rw [hIic]
    calc (effectiveClass (zeroOneLoss h) z).card
        ≤ ∑ k ∈ Finset.Iic (binaryClassTrace h z).vcDim, n.choose k :=
          effectiveClass_zeroOneLoss_card_le_sauerShelah h z
      _ ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
          Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr (hVC z))
  -- The negated-loss growth bound follows from the same bound by injectivity of negation.
  have hGrowth_neg : ∀ z : Fin n → α,
      (effectiveClass (fun i w => -(zeroOneLoss h) i w) z).card
        ≤ ∑ k ∈ Finset.range (d + 1), n.choose k := by
    intro z
    rw [effectiveClass_neg_card]
    exact hGrowth_uniform z
  -- Specialise the general capstone at `B := 1`, then clean up `4*1` and `8*1²`.
  have hbase := vc_erm_excessRisk_tail (μ := μ) (B := 1) one_pos hℓ_meas hℓ_bdd
    hn hd hdn hGrowth_uniform hGrowth_neg hhat hERM i_star hε
  simpa only [mul_one, one_pow] using hbase

end FormalSLT.VC.SampleComplexityBinary
