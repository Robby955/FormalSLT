import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import FormalSLT.Probability.FiniteUnionBound
import FormalSLT.Probability.Concentration

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace FormalSLT.UniformConvergence

noncomputable section

/--
Deterministic ERM triangle lemma behind the epsilon-representative sample claim.

This theorem deliberately abstracts away probability: once empirical and
population risks are uniformly within `ε`, any empirical-risk minimizer is
within `2ε` of any comparator's population risk. Stochastic finite-class
uniform convergence should remain a separate governed claim.
-/
theorem epsilonRepresentativeERMWorks
    {H : Type*} {risk empiricalRisk : H → ℝ} {ε : ℝ}
    {hERM hComparator : H}
    (hRepresentative : ∀ h, |risk h - empiricalRisk h| ≤ ε)
    (hERMmin : ∀ h, empiricalRisk hERM ≤ empiricalRisk h) :
    risk hERM ≤ risk hComparator + 2 * ε := by
  have hERMUpper : risk hERM ≤ empiricalRisk hERM + ε := by
    have h := (abs_le.mp (hRepresentative hERM)).2
    linarith
  have hComparatorUpper : empiricalRisk hComparator ≤ risk hComparator + ε := by
    have h := (abs_le.mp (hRepresentative hComparator)).1
    linarith
  have hEmpirical : empiricalRisk hERM ≤ empiricalRisk hComparator :=
    hERMmin hComparator
  linarith

/--
Finite-class uniform-deviation union-bound bridge.

This theorem is intentionally scoped: it starts from a pointwise tail bound for
each hypothesis and proves the simultaneous bad-event bound by the finite
measure union bound. It does not encode iid sampling, bounded losses, the
Hoeffding step, or the closed-form `sqrt(log |H| / n)` rearrangement.
-/
theorem finiteClassUniformDeviationUnionBound
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (badEvent : H → Set Ω) {pointwiseTail : ℝ≥0∞}
    (hPointwiseTail : ∀ h, μ (badEvent h) ≤ pointwiseTail) :
    μ (⋃ h, badEvent h) ≤ Fintype.card H • pointwiseTail := by
  calc
    μ (⋃ h, badEvent h) ≤ ∑ h, μ (badEvent h) :=
      FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound badEvent
    _ ≤ ∑ _h : H, pointwiseTail := by
      exact Finset.sum_le_sum (fun h _ => hPointwiseTail h)
    _ = Fintype.card H • pointwiseTail := by
      simp

/--
Finite-class two-sided uniform-deviation union-bound bridge.

This is the theorem-shaped bridge used by the finite-class uniform-convergence
claim: pointwise two-sided deviation tails imply a simultaneous finite-class
bad-event bound. It still does not formalize iid bounded losses, the
Hoeffding step that supplies the pointwise tail, or the closed-form
sample-complexity rearrangement.
-/
theorem finiteClassTwoSidedUniformDeviationUnionBound
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (deviation : H → Ω → ℝ) {ε : ℝ} {pointwiseTail : ℝ≥0∞}
    (hPointwiseTail : ∀ h, μ {ω | ε ≤ |deviation h ω|} ≤ pointwiseTail) :
    μ (⋃ h, {ω | ε ≤ |deviation h ω|}) ≤ Fintype.card H • pointwiseTail := by
  exact finiteClassUniformDeviationUnionBound
    (fun h => {ω | ε ≤ |deviation h ω|})
    hPointwiseTail

/--
Two-sided absolute-deviation tail bound from one-sided upper and lower tails.

This is the missing formal adapter between one-sided Hoeffding-style
concentration facts and the absolute-deviation events used by uniform
convergence statements.
-/
theorem twoSidedDeviationTailFromOneSidedTails
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (deviation : Ω → ℝ) {ε : ℝ} {upperTail lowerTail : ℝ≥0∞}
    (hUpperTail : μ {ω | ε ≤ deviation ω} ≤ upperTail)
    (hLowerTail : μ {ω | ε ≤ -deviation ω} ≤ lowerTail) :
    μ {ω | ε ≤ |deviation ω|} ≤ upperTail + lowerTail := by
  have hSubset :
      {ω | ε ≤ |deviation ω|}
        ⊆ {ω | ε ≤ deviation ω} ∪ {ω | ε ≤ -deviation ω} := by
    intro ω hAbs
    by_cases hNonneg : 0 ≤ deviation ω
    · exact Or.inl (by simpa [abs_of_nonneg hNonneg] using hAbs)
    · have hNonpos : deviation ω ≤ 0 := le_of_not_ge hNonneg
      exact Or.inr (by simpa [abs_of_nonpos hNonpos] using hAbs)
  calc
    μ {ω | ε ≤ |deviation ω|}
        ≤ μ ({ω | ε ≤ deviation ω} ∪ {ω | ε ≤ -deviation ω}) :=
          measure_mono hSubset
    _ ≤ μ {ω | ε ≤ deviation ω} + μ {ω | ε ≤ -deviation ω} :=
          measure_union_le _ _
    _ ≤ upperTail + lowerTail :=
          add_le_add hUpperTail hLowerTail

/--
Finite-class absolute-deviation union-bound bridge from one-sided tails.

This is still intentionally scoped. It proves the probability-combinatorics
part of finite-class uniform convergence once each hypothesis has matching
upper and lower one-sided deviation tails. It does not formalize iid sampling,
bounded empirical losses, or the closed-form `sqrt(log |H| / n)` rearrangement.
-/
theorem finiteClassUniformDeviationUnionBoundFromOneSidedTails
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (deviation : H → Ω → ℝ) {ε : ℝ} {pointwiseTail : ℝ≥0∞}
    (hUpperTail : ∀ h, μ {ω | ε ≤ deviation h ω} ≤ pointwiseTail)
    (hLowerTail : ∀ h, μ {ω | ε ≤ -deviation h ω} ≤ pointwiseTail) :
    μ (⋃ h, {ω | ε ≤ |deviation h ω|})
      ≤ Fintype.card H • (pointwiseTail + pointwiseTail) := by
  exact finiteClassTwoSidedUniformDeviationUnionBound
    deviation
    (fun h =>
      twoSidedDeviationTailFromOneSidedTails
        (deviation h)
        (hUpperTail h)
        (hLowerTail h))

/--
Finite-class epsilon-representative failure bound from one-sided risk tails.

This is the risk-facing bridge for finite-class uniform convergence: paired
one-sided pointwise tail bounds for the true-risk/empirical-risk deviation
imply a simultaneous absolute-deviation failure bound over the finite class.
It still does not formalize iid samples, bounded losses, or the closed-form
sample-complexity rearrangement.
-/
theorem finiteClassEpsilonRepresentativeFailureBoundFromOneSidedTails
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (risk : H → ℝ) (empiricalRisk : H → Ω → ℝ)
    {ε : ℝ} {pointwiseTail : ℝ≥0∞}
    (hUpperTail :
      ∀ h, μ {ω | ε ≤ risk h - empiricalRisk h ω} ≤ pointwiseTail)
    (hLowerTail :
      ∀ h, μ {ω | ε ≤ empiricalRisk h ω - risk h} ≤ pointwiseTail) :
    μ (⋃ h, {ω | ε ≤ |risk h - empiricalRisk h ω|})
      ≤ Fintype.card H • (pointwiseTail + pointwiseTail) := by
  exact finiteClassUniformDeviationUnionBoundFromOneSidedTails
    (fun h ω => risk h - empiricalRisk h ω)
    hUpperTail
    (fun h => by
      simpa [neg_sub] using hLowerTail h)

/--
Finite-class high-probability epsilon-representative bridge.

If the paired one-sided pointwise tails are small enough that the finite-class
union-bound expression is at most `δ`, then the simultaneous
epsilon-representative failure event has measure at most `δ`. This isolates the
last probability step before any closed-form sample-complexity algebra.
-/
theorem finiteClassEpsilonRepresentativeHighProbabilityFromOneSidedTails
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (risk : H → ℝ) (empiricalRisk : H → Ω → ℝ)
    {ε : ℝ} {pointwiseTail δ : ℝ≥0∞}
    (hUpperTail :
      ∀ h, μ {ω | ε ≤ risk h - empiricalRisk h ω} ≤ pointwiseTail)
    (hLowerTail :
      ∀ h, μ {ω | ε ≤ empiricalRisk h ω - risk h} ≤ pointwiseTail)
    (hDelta : Fintype.card H • (pointwiseTail + pointwiseTail) ≤ δ) :
    μ (⋃ h, {ω | ε ≤ |risk h - empiricalRisk h ω|}) ≤ δ :=
  le_trans
    (finiteClassEpsilonRepresentativeFailureBoundFromOneSidedTails
      risk empiricalRisk hUpperTail hLowerTail)
    hDelta

/--
Convert a probability event bound stated with `μ.real` into an `ENNReal` event
bound. Mathlib concentration inequalities often return real-valued probability
bounds, while measure-union statements consume `ℝ≥0∞` bounds.
-/
theorem probabilityMeasureEventLeOfRealLe
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {event : Set Ω} {bound : ℝ}
    (hTail : μ.real event ≤ bound) :
    μ event ≤ ENNReal.ofReal bound := by
  rw [← MeasureTheory.ofReal_measureReal (μ := μ) (s := event)]
  exact ENNReal.ofReal_le_ofReal hTail

/--
Fixed-hypothesis empirical-average upper-tail bridge from Hoeffding.

This is a sampling-facing step toward finite-class uniform convergence:
for one fixed hypothesis, a finite independent family of bounded losses gives a
one-sided tail bound for the true-risk minus empirical-risk average. The theorem
keeps the ordinary true-risk sum and makes the expectation-negation step
explicit. The normalizer is tied to the finite sample size by `hSampleSize`;
iid sampling and the finite-class union bound remain separate declarations.
-/
theorem fixedHypothesisEmpiricalAverageUpperTailFromHoeffding
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {loss : ι → Ω → ℝ} (hIndep : iIndepFun loss μ)
    {a b : ι → ℝ} {s : Finset ι} {n ε risk : ℝ}
    (hMeas : ∀ i ∈ s, AEMeasurable (loss i) μ)
    (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc (a i) (b i))
    (hRisk : risk = ∑ i ∈ s, μ[loss i])
    (hNegExpectation : ∀ i ∈ s, μ[fun ω => -loss i ω] = - μ[loss i])
    (hSampleSize : n = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ risk / n - (∑ i ∈ s, loss i ω) / n}
      ≤ Real.exp
          (-(n * ε) ^ 2 /
            (2 * (↑(∑ i ∈ s, ((‖(-a i) - (-b i)‖₊ / 2) ^ (2 : ℕ))) : ℝ))) := by
  have hn : 0 < n := by
    rw [hSampleSize]
    exact Nat.cast_pos.mpr hNonemptySample
  have hScaledEvent :
      {ω | ε ≤ risk / n - (∑ i ∈ s, loss i ω) / n}
        = {ω | n * ε ≤ ∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x])} := by
    ext ω
    constructor
    · intro hω
      change ε ≤ risk / n - (∑ i ∈ s, loss i ω) / n at hω
      have hMul : n * ε ≤ n * (risk / n - (∑ i ∈ s, loss i ω) / n) :=
        mul_le_mul_of_nonneg_left hω (le_of_lt hn)
      have hSum :
          ∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x])
            = risk - ∑ i ∈ s, loss i ω := by
        rw [hRisk]
        have hNegSum :
            ∑ i ∈ s, μ[fun x => -loss i x] = ∑ i ∈ s, -μ[loss i] := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hNegExpectation i hi
        rw [Finset.sum_sub_distrib, hNegSum]
        simp [Finset.sum_neg_distrib]
        ring
      calc
        n * ε ≤ n * (risk / n - (∑ i ∈ s, loss i ω) / n) := hMul
        _ = risk - ∑ i ∈ s, loss i ω := by
          field_simp [ne_of_gt hn]
        _ = ∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x]) := by
          rw [← hSum]
    · intro hω
      change n * ε ≤ ∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x]) at hω
      have hDiv :
          (n * ε) / n
            ≤ (∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x])) / n :=
        div_le_div_of_nonneg_right hω (le_of_lt hn)
      have hSum :
          ∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x])
            = risk - ∑ i ∈ s, loss i ω := by
        rw [hRisk]
        have hNegSum :
            ∑ i ∈ s, μ[fun x => -loss i x] = ∑ i ∈ s, -μ[loss i] := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hNegExpectation i hi
        rw [Finset.sum_sub_distrib, hNegSum]
        simp [Finset.sum_neg_distrib]
        ring
      calc
        ε = (n * ε) / n := by
          field_simp [ne_of_gt hn]
        _ ≤ (∑ i ∈ s, (-loss i ω - μ[fun x => -loss i x])) / n := hDiv
        _ = (risk - ∑ i ∈ s, loss i ω) / n := by
          rw [hSum]
        _ = risk / n - (∑ i ∈ s, loss i ω) / n := by
          ring
  rw [hScaledEvent]
  have hIndepNeg : iIndepFun (fun i ω => -loss i ω) μ := by
    simpa [Function.comp_def] using
      hIndep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hMeasNeg :
      ∀ i ∈ s, AEMeasurable (fun ω => -loss i ω) μ := by
    intro i hi
    exact (hMeas i hi).neg
  have hBoundNeg :
      ∀ i ∈ s, ∀ᵐ ω ∂μ, -loss i ω ∈ Set.Icc (-b i) (-a i) := by
    intro i hi
    exact (hBound i hi).mono (by
      intro ω hω
      exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩)
  exact FormalSLT.Probability.Concentration.hoeffdingBoundedFiniteSumTail
    (X := fun i ω => -loss i ω)
    hIndepNeg hMeasNeg hBoundNeg (mul_nonneg (le_of_lt hn) hε)

/--
Fixed-hypothesis empirical-average lower-tail bridge from Hoeffding.

This is the companion to `fixedHypothesisEmpiricalAverageUpperTailFromHoeffding`:
for one fixed hypothesis, a finite independent family of bounded losses gives a
one-sided tail bound for the empirical-risk average above the true-risk
average. Together, the two wrappers supply the paired pointwise tails consumed
by the finite-class uniform-convergence bridge.
-/
theorem fixedHypothesisEmpiricalAverageLowerTailFromHoeffding
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {loss : ι → Ω → ℝ} (hIndep : iIndepFun loss μ)
    {a b : ι → ℝ} {s : Finset ι} {n ε risk : ℝ}
    (hMeas : ∀ i ∈ s, AEMeasurable (loss i) μ)
    (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc (a i) (b i))
    (hRisk : risk = ∑ i ∈ s, μ[loss i])
    (hSampleSize : n = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ (∑ i ∈ s, loss i ω) / n - risk / n}
      ≤ Real.exp
          (-(n * ε) ^ 2 /
            (2 * (↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ))) := by
  have hn : 0 < n := by
    rw [hSampleSize]
    exact Nat.cast_pos.mpr hNonemptySample
  have hScaledEvent :
      {ω | ε ≤ (∑ i ∈ s, loss i ω) / n - risk / n}
        = {ω | n * ε ≤ ∑ i ∈ s, (loss i ω - μ[loss i])} := by
    ext ω
    constructor
    · intro hω
      change ε ≤ (∑ i ∈ s, loss i ω) / n - risk / n at hω
      have hMul :
          n * ε ≤ n * ((∑ i ∈ s, loss i ω) / n - risk / n) :=
        mul_le_mul_of_nonneg_left hω (le_of_lt hn)
      have hSum :
          ∑ i ∈ s, (loss i ω - μ[loss i])
            = ∑ i ∈ s, loss i ω - risk := by
        rw [hRisk]
        rw [Finset.sum_sub_distrib]
      calc
        n * ε ≤ n * ((∑ i ∈ s, loss i ω) / n - risk / n) := hMul
        _ = ∑ i ∈ s, loss i ω - risk := by
          field_simp [ne_of_gt hn]
        _ = ∑ i ∈ s, (loss i ω - μ[loss i]) := by
          rw [← hSum]
    · intro hω
      change n * ε ≤ ∑ i ∈ s, (loss i ω - μ[loss i]) at hω
      have hDiv :
          (n * ε) / n
            ≤ (∑ i ∈ s, (loss i ω - μ[loss i])) / n :=
        div_le_div_of_nonneg_right hω (le_of_lt hn)
      have hSum :
          ∑ i ∈ s, (loss i ω - μ[loss i])
            = ∑ i ∈ s, loss i ω - risk := by
        rw [hRisk]
        rw [Finset.sum_sub_distrib]
      calc
        ε = (n * ε) / n := by
          field_simp [ne_of_gt hn]
        _ ≤ (∑ i ∈ s, (loss i ω - μ[loss i])) / n := hDiv
        _ = (∑ i ∈ s, loss i ω - risk) / n := by
          rw [hSum]
        _ = (∑ i ∈ s, loss i ω) / n - risk / n := by
          ring
  rw [hScaledEvent]
  exact FormalSLT.Probability.Concentration.hoeffdingBoundedFiniteSumTail
    hIndep hMeas hBound (mul_nonneg (le_of_lt hn) hε)

/--
`ENNReal` form of the fixed-hypothesis empirical-average upper-tail bridge.

This adapter lets the real-valued Hoeffding wrapper feed directly into the
finite-class union-bound bridge, whose event probabilities live in `ℝ≥0∞`.
-/
theorem fixedHypothesisEmpiricalAverageUpperTailFromHoeffdingENNReal
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {loss : ι → Ω → ℝ} (hIndep : iIndepFun loss μ)
    {a b : ι → ℝ} {s : Finset ι} {n ε risk : ℝ}
    (hMeas : ∀ i ∈ s, AEMeasurable (loss i) μ)
    (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc (a i) (b i))
    (hRisk : risk = ∑ i ∈ s, μ[loss i])
    (hNegExpectation : ∀ i ∈ s, μ[fun ω => -loss i ω] = - μ[loss i])
    (hSampleSize : n = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε) :
    μ {ω | ε ≤ risk / n - (∑ i ∈ s, loss i ω) / n}
      ≤ ENNReal.ofReal
          (Real.exp
            (-(n * ε) ^ 2 /
              (2 * (↑(∑ i ∈ s, ((‖(-a i) - (-b i)‖₊ / 2) ^ (2 : ℕ))) : ℝ)))) := by
  refine probabilityMeasureEventLeOfRealLe ?_
  exact fixedHypothesisEmpiricalAverageUpperTailFromHoeffding
    hIndep hMeas hBound hRisk hNegExpectation hSampleSize hNonemptySample hε

/--
`ENNReal` form of the fixed-hypothesis empirical-average lower-tail bridge.

Together with the upper-tail adapter, this supplies the measure-valued
one-hypothesis facts consumed by finite-class uniform-convergence bridges.
-/
theorem fixedHypothesisEmpiricalAverageLowerTailFromHoeffdingENNReal
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {loss : ι → Ω → ℝ} (hIndep : iIndepFun loss μ)
    {a b : ι → ℝ} {s : Finset ι} {n ε risk : ℝ}
    (hMeas : ∀ i ∈ s, AEMeasurable (loss i) μ)
    (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc (a i) (b i))
    (hRisk : risk = ∑ i ∈ s, μ[loss i])
    (hSampleSize : n = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε) :
    μ {ω | ε ≤ (∑ i ∈ s, loss i ω) / n - risk / n}
      ≤ ENNReal.ofReal
          (Real.exp
            (-(n * ε) ^ 2 /
              (2 * (↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ)))) := by
  refine probabilityMeasureEventLeOfRealLe ?_
  exact fixedHypothesisEmpiricalAverageLowerTailFromHoeffding
    hIndep hMeas hBound hRisk hSampleSize hNonemptySample hε

end

end FormalSLT.UniformConvergence
