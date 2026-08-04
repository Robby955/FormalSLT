import Mathlib.Analysis.SpecificLimits.Basic
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
Finite-class uniform-deviation union bound with an equal split of a target
failure budget.

If each hypothesis receives budget `δ / card(H)`, then the simultaneous
finite-class bad event has mass at most `δ`.
-/
theorem finiteClassUniformDeviationUnionBound_cardInv
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H] [Nonempty H]
    (badEvent : H → Set Ω) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ h, μ (badEvent h) ≤ δ * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ h, badEvent h) ≤ δ :=
  FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_cardInv
    badEvent hPointwiseTail

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
Finite-class two-sided uniform-deviation union-bound bridge with the total
failure budget split equally across hypotheses.
-/
theorem finiteClassTwoSidedUniformDeviationUnionBound_cardInv
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H] [Nonempty H]
    (deviation : H → Ω → ℝ) {ε : ℝ} {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ h, μ {ω | ε ≤ |deviation h ω|}
        ≤ δ * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ h, {ω | ε ≤ |deviation h ω|}) ≤ δ :=
  finiteClassUniformDeviationUnionBound_cardInv
    (fun h => {ω | ε ≤ |deviation h ω|})
    hPointwiseTail

/--
Finite time-horizon and finite-class union bound with the target budget split
across all `(time, hypothesis)` pairs.
-/
theorem finiteTimeClassUnionBound_cardInv
    {Ω Time H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype Time] [Nonempty Time] [Fintype H] [Nonempty H]
    (badEvent : Time → H → Set Ω) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ (badEvent t h) ≤ δ * (Fintype.card (Time × H) : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Time × H, badEvent p.1 p.2) ≤ δ :=
  FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_cardInv
    (fun p : Time × H => badEvent p.1 p.2)
    (fun p => hPointwiseTail p.1 p.2)

/--
Finite time-horizon and finite-class absolute-deviation bridge.

This is the finite-horizon probability shell for later anytime-valid
finite-class statements: pointwise tails over every `(time, hypothesis)` pair
imply a simultaneous bound over all pairs.
-/
theorem finiteTimeClassTwoSidedUniformDeviationUnionBound_cardInv
    {Ω Time H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype Time] [Nonempty Time] [Fintype H] [Nonempty H]
    (deviation : Time → H → Ω → ℝ) {ε : ℝ} {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ {ω | ε ≤ |deviation t h ω|}
        ≤ δ * (Fintype.card (Time × H) : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Time × H, {ω | ε ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassUnionBound_cardInv
    (fun t h => {ω | ε ≤ |deviation t h ω|})
    hPointwiseTail

/--
Finite time-horizon and finite-class union bound with a supplied time-budget
sequence.

At each time `t`, the hypotheses share the budget `timeBudget t`; the finite
time budgets then sum to the total failure budget `δ`.
-/
theorem finiteTimeClassUnionBound_timeBudget
    {Ω Time H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype Time] [Fintype H] [Nonempty H]
    (badEvent : Time → H → Set Ω) (timeBudget : Time → ℝ≥0∞) {δ : ℝ≥0∞}
    (hBudgetSum : ∑ t, timeBudget t ≤ δ)
    (hPointwiseTail :
      ∀ t h, μ (badEvent t h) ≤ timeBudget t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Time × H, badEvent p.1 p.2) ≤ δ := by
  calc
    μ (⋃ p : Time × H, badEvent p.1 p.2) = μ (⋃ t, ⋃ h, badEvent t h) := by
      rw [Set.iUnion_prod']
    _ ≤ δ :=
      FormalSLT.Probability.FiniteUnionBound.finiteMeasureUnionBound_budget
        (fun t => ⋃ h, badEvent t h)
        timeBudget
        (fun t =>
          finiteClassUniformDeviationUnionBound_cardInv
            (badEvent t)
            (hPointwiseTail t))
        hBudgetSum

/--
Finite time-horizon and finite-class absolute-deviation bridge with a supplied
time-budget sequence.
-/
theorem finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget
    {Ω Time H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype Time] [Fintype H] [Nonempty H]
    (deviation : Time → H → Ω → ℝ) (timeBudget : Time → ℝ≥0∞)
    {ε : ℝ} {δ : ℝ≥0∞}
    (hBudgetSum : ∑ t, timeBudget t ≤ δ)
    (hPointwiseTail :
      ∀ t h, μ {ω | ε ≤ |deviation t h ω|}
        ≤ timeBudget t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Time × H, {ω | ε ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassUnionBound_timeBudget
    (fun t h => {ω | ε ≤ |deviation t h ω|})
    timeBudget
    hBudgetSum
    hPointwiseTail

/--
Finite time-horizon and finite-class absolute-deviation bridge with supplied
time budgets and a threshold depending on `(time, hypothesis)`.

This is the event-shaped variant needed before anytime-valid finite-class
statements: a dyadic schedule naturally gives each time its own displayed
radius, not one common `ε` for the whole finite prefix.
-/
theorem finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget_threshold
    {Ω Time H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype Time] [Fintype H] [Nonempty H]
    (deviation : Time → H → Ω → ℝ)
    (threshold : Time → H → ℝ)
    (timeBudget : Time → ℝ≥0∞) {δ : ℝ≥0∞}
    (hBudgetSum : ∑ t, timeBudget t ≤ δ)
    (hPointwiseTail :
      ∀ t h, μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ timeBudget t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Time × H,
        {ω | threshold p.1 p.2 ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassUnionBound_timeBudget
    (fun t h => {ω | threshold t h ≤ |deviation t h ω|})
    timeBudget
    hBudgetSum
    hPointwiseTail

/--
The standard dyadic time budget used by finite-prefix anytime-valid wrappers.

At time `t`, the total time budget is `δ * 2^(-1-t)`. The infinite sum over
all natural times is exactly `δ`, and every finite prefix is bounded by `δ`.
-/
def finiteDyadicTimeBudget (δ : ℝ≥0∞) (t : ℕ) : ℝ≥0∞ :=
  δ * (2 : ℝ≥0∞) ^ (-1 - (t : ℤ))

/-- A finite prefix of the dyadic time-budget schedule is bounded by `δ`. -/
theorem finiteDyadicTimeBudget_sum_fin_le (n : ℕ) (δ : ℝ≥0∞) :
    (∑ t : Fin n, finiteDyadicTimeBudget δ t.val) ≤ δ := by
  calc
    (∑ t : Fin n, finiteDyadicTimeBudget δ t.val)
        = ∑ k ∈ Finset.range n, finiteDyadicTimeBudget δ k := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]
    _ ≤ ∑' k : ℕ, finiteDyadicTimeBudget δ k :=
      ENNReal.sum_le_tsum (Finset.range n)
    _ = δ := by
      simp_rw [finiteDyadicTimeBudget]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one]

/-- The full dyadic time-budget schedule is summable with total at most `δ`. -/
theorem finiteDyadicTimeBudget_tsum_le (δ : ℝ≥0∞) :
    (∑' t : ℕ, finiteDyadicTimeBudget δ t) ≤ δ := by
  calc
    (∑' t : ℕ, finiteDyadicTimeBudget δ t) = δ := by
      simp_rw [finiteDyadicTimeBudget]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one]
    _ ≤ δ := le_rfl

/--
Countable-time and finite-class union bound with a supplied time-budget
sequence.

At each natural time `t`, the finite hypothesis class shares `timeBudget t`.
If the infinite time-budget sum is bounded by `δ`, the bad event over all
`(t, h)` has mass at most `δ`.
-/
theorem countableTimeClassUnionBound_timeBudget
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype H] [Nonempty H]
    (badEvent : ℕ → H → Set Ω) (timeBudget : ℕ → ℝ≥0∞) {δ : ℝ≥0∞}
    (hBudgetSum : (∑' t : ℕ, timeBudget t) ≤ δ)
    (hPointwiseTail :
      ∀ t h, μ (badEvent t h) ≤
        timeBudget t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : ℕ × H, badEvent p.1 p.2) ≤ δ := by
  calc
    μ (⋃ p : ℕ × H, badEvent p.1 p.2) =
        μ (⋃ t : ℕ, ⋃ h : H, badEvent t h) := by
          rw [Set.iUnion_prod']
    _ ≤ ∑' t : ℕ, μ (⋃ h : H, badEvent t h) :=
      FormalSLT.Probability.FiniteUnionBound.countableMeasureUnionBound
        (fun t : ℕ => ⋃ h : H, badEvent t h)
    _ ≤ ∑' t : ℕ, timeBudget t := by
      exact ENNReal.tsum_le_tsum (fun t =>
        finiteClassUniformDeviationUnionBound_cardInv
          (badEvent t)
          (hPointwiseTail t))
    _ ≤ δ := hBudgetSum

/--
Countable-time and finite-class union bound using the standard dyadic schedule.
-/
theorem countableTimeClassUnionBound_dyadicBudget
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype H] [Nonempty H]
    (badEvent : ℕ → H → Set Ω) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ (badEvent t h) ≤
        finiteDyadicTimeBudget δ t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : ℕ × H, badEvent p.1 p.2) ≤ δ :=
  countableTimeClassUnionBound_timeBudget
    badEvent
    (fun t : ℕ => finiteDyadicTimeBudget δ t)
    (finiteDyadicTimeBudget_tsum_le δ)
    hPointwiseTail

/--
Countable-time and finite-class absolute-deviation bridge with dyadic
time-varying thresholds.

This is the reusable anytime shell behind the route-facing finite-class
Hoeffding theorem: each natural time can carry its own confidence radius.
-/
theorem countableTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype H] [Nonempty H]
    (deviation : ℕ → H → Ω → ℝ)
    (threshold : ℕ → H → ℝ) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ finiteDyadicTimeBudget δ t * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : ℕ × H,
        {ω | threshold p.1 p.2 ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  countableTimeClassUnionBound_dyadicBudget
    (fun t h => {ω | threshold t h ≤ |deviation t h ω|})
    hPointwiseTail

/-- Rewrite a countable time-class union as an existential event. -/
theorem countableTimeClass_iUnion_eq_exists
    {Ω H : Type*} (event : ℕ → H → Set Ω) :
    (⋃ p : ℕ × H, event p.1 p.2) =
      {ω | ∃ t : ℕ, ∃ h : H, ω ∈ event t h} := by
  ext ω
  simp

/--
Displayed dyadic confidence radius for `[0,1]` finite-class empirical-average
deviation at natural time `t`.
-/
def zeroOneDyadicFiniteClassConfidenceRadius {H : Type*} [Fintype H]
    (sampleSize δ_real : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt
    ((Real.log 2 -
      Real.log
        (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
          (Fintype.card H : ℝ))) /
      (2 * sampleSize))

/--
Failure of the all-times/all-hypotheses strict confidence event is exactly the
existential crossing event used by the probability bound.
-/
theorem countableTimeClass_not_forall_lt_eq_exists_ge
    {Ω H : Type*} (deviation : ℕ → H → Ω → ℝ)
    (threshold : ℕ → H → ℝ) :
    {ω | ¬ ∀ t : ℕ, ∀ h : H, |deviation t h ω| < threshold t h} =
      {ω | ∃ t : ℕ, ∃ h : H, threshold t h ≤ |deviation t h ω|} := by
  ext ω
  simp [not_lt]

/--
Finite-prefix dyadic schedule for time-horizon and finite-class union bounds.

This wrapper removes the need to supply a finite-sum certificate: the time
budgets are fixed to `δ * 2^(-1-t)` over `Fin n`.
-/
theorem finiteTimeClassUnionBound_dyadicBudget
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} [Fintype H] [Nonempty H]
    (badEvent : Fin n → H → Set Ω) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ (badEvent t h)
        ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin n × H, badEvent p.1 p.2) ≤ δ :=
  finiteTimeClassUnionBound_timeBudget
    badEvent
    (fun t : Fin n => finiteDyadicTimeBudget δ t.val)
    (finiteDyadicTimeBudget_sum_fin_le n δ)
    hPointwiseTail

/--
Finite-prefix dyadic schedule for finite-class absolute-deviation events.
-/
theorem finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} [Fintype H] [Nonempty H]
    (deviation : Fin n → H → Ω → ℝ) {ε : ℝ} {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ {ω | ε ≤ |deviation t h ω|}
        ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin n × H, {ω | ε ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassUnionBound_dyadicBudget
    (fun t h => {ω | ε ≤ |deviation t h ω|})
    hPointwiseTail

/--
Finite-prefix dyadic schedule for finite-class absolute-deviation events with
a threshold depending on `(time, hypothesis)`.

This is the finite-prefix union shell used by time-varying confidence radii.
-/
theorem finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} [Fintype H] [Nonempty H]
    (deviation : Fin n → H → Ω → ℝ)
    (threshold : Fin n → H → ℝ) {δ : ℝ≥0∞}
    (hPointwiseTail :
      ∀ t h, μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin n × H,
        {ω | threshold p.1 p.2 ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassUnionBound_dyadicBudget
    (fun t h => {ω | threshold t h ≤ |deviation t h ω|})
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
Finite-prefix dyadic schedule for absolute-deviation events supplied through
one-sided upper and lower pointwise tails.

This is a direct finite-horizon bridge from one-sided concentration inputs to a
simultaneous finite-class event over all `(time, hypothesis)` pairs.
-/
theorem finiteTimeClassTwoSidedUnionBoundFromOneSidedTails_dyadicBudget
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} [Fintype H] [Nonempty H]
    (deviation : Fin n → H → Ω → ℝ) {ε : ℝ} {δ : ℝ≥0∞}
    {upperTail lowerTail : Fin n → H → ℝ≥0∞}
    (hUpperTail :
      ∀ t h, μ {ω | ε ≤ deviation t h ω} ≤ upperTail t h)
    (hLowerTail :
      ∀ t h, μ {ω | ε ≤ -deviation t h ω} ≤ lowerTail t h)
    (hTailBudget :
      ∀ t h, upperTail t h + lowerTail t h
        ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin n × H, {ω | ε ≤ |deviation p.1 p.2 ω|}) ≤ δ :=
  finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget
    deviation
    (fun t h =>
      (twoSidedDeviationTailFromOneSidedTails
        (deviation t h)
        (hUpperTail t h)
        (hLowerTail t h)).trans
        (hTailBudget t h))

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

/--
`ENNReal` upper-tail budget supplied by the fixed-hypothesis Hoeffding wrapper.

This is a named expression, not a new concentration inequality. It packages the
bound produced by `fixedHypothesisEmpiricalAverageUpperTailFromHoeffdingENNReal`
so finite-horizon wrappers can state budget hypotheses without repeating the
full exponential expression inline.
-/
def empiricalAverageUpperHoeffdingTail {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (sampleSize ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-(sampleSize * ε) ^ 2 /
        (2 * (↑(∑ i ∈ s, ((‖(-a i) - (-b i)‖₊ / 2) ^ (2 : ℕ))) : ℝ))))

/--
`ENNReal` lower-tail budget supplied by the fixed-hypothesis Hoeffding wrapper.

This is the lower-tail companion to `empiricalAverageUpperHoeffdingTail`.
-/
def empiricalAverageLowerHoeffdingTail {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (sampleSize ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-(sampleSize * ε) ^ 2 /
        (2 * (↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ))))

/--
The fixed-hypothesis upper and lower Hoeffding tail budgets have the same
closed form. The upper-tail wrapper applies Hoeffding to negated losses, so its
range term is written as `(-a)-(-b)`; this lemma normalizes that expression.
-/
theorem empiricalAverageUpperHoeffdingTail_eq_lower {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (sampleSize ε : ℝ) :
    empiricalAverageUpperHoeffdingTail s a b sampleSize ε =
      empiricalAverageLowerHoeffdingTail s a b sampleSize ε := by
  simp [empiricalAverageUpperHoeffdingTail, empiricalAverageLowerHoeffdingTail,
    sub_eq_add_neg, add_comm]

/--
Two-sided fixed-hypothesis Hoeffding tail budget for an empirical average.

This is the readable budget expression used by finite-class wrappers after
combining matching upper and lower one-sided Hoeffding tails.
-/
def empiricalAverageTwoSidedHoeffdingTail {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (sampleSize ε : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) * empiricalAverageLowerHoeffdingTail s a b sampleSize ε

/--
Uniform-range two-sided Hoeffding budget for empirical averages.

The parameter `rangeVarianceProxy` is the single denominator proxy replacing the
per-hypothesis finite sum of squared half-ranges.
-/
def empiricalAverageUniformRangeTwoSidedHoeffdingTail
    (sampleSize ε rangeVarianceProxy : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp (-(sampleSize * ε) ^ 2 / (2 * rangeVarianceProxy)))

/--
Uniform-range two-sided Hoeffding budget displayed by sample size and range.

When the range proxy is `sampleSize * (R / 2)^2`, this is the usual
`2 * exp(-2 * sampleSize * ε^2 / R^2)` expression.
-/
def empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
    (sampleSize ε : ℝ) (R : ℝ≥0) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp (-2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ))))

/--
The range-proxy Hoeffding budget specializes to the usual sample-size display.
-/
theorem empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail
    {sampleSize ε : ℝ} {R : ℝ≥0}
    (hSampleSize_pos : 0 < sampleSize) (hR_pos : 0 < (R : ℝ)) :
    empiricalAverageUniformRangeTwoSidedHoeffdingTail
        sampleSize ε (sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ))) =
      empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail sampleSize ε R := by
  unfold empiricalAverageUniformRangeTwoSidedHoeffdingTail
  unfold empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
  congr 2
  congr 1
  have hSampleSize_ne : sampleSize ≠ 0 := ne_of_gt hSampleSize_pos
  have hR_ne : (R : ℝ) ≠ 0 := ne_of_gt hR_pos
  field_simp [hSampleSize_ne, hR_ne]

/--
Displayed sample-size Hoeffding budget from a real log-budget inequality.

This is the algebraic inversion hook for later sample-complexity statements:
once the exponent satisfies
`log 2 - 2 * sampleSize * ε^2 / R^2 <= log target`, the displayed
two-sided tail is bounded by `target`.
-/
theorem empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget
    {sampleSize ε target : ℝ} {R : ℝ≥0}
    (hTarget_pos : 0 < target)
    (hLogBudget :
      Real.log 2 - 2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ))
        ≤ Real.log target) :
    empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail sampleSize ε R
      ≤ ENNReal.ofReal target := by
  have hRealExp :
      2 * Real.exp (-2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ)))
        ≤ target := by
    calc
      2 * Real.exp (-2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ)))
          = Real.exp
              (Real.log 2 - 2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ))) := by
            rw [sub_eq_add_neg, Real.exp_add,
              Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            ring_nf
      _ ≤ Real.exp (Real.log target) := Real.exp_le_exp.mpr hLogBudget
      _ = target := Real.exp_log hTarget_pos
  unfold empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
  rw [← ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal hRealExp

/--
Displayed sample-size Hoeffding budget at its square-root confidence radius.

For unit-range losses, the radius
`sqrt((log 2 - log target) / (2 * sampleSize))` is exactly the inversion of the
two-sided Hoeffding display. The nonpositive log-budget case is harmless: the
radius is then zero and the tail bound is already at most `target`.
-/
theorem empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_explicitRadius
    {sampleSize target : ℝ}
    (hSampleSize_pos : 0 < sampleSize)
    (hTarget_pos : 0 < target) :
    empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
        sampleSize
        (Real.sqrt ((Real.log 2 - Real.log target) / (2 * sampleSize)))
        (1 : ℝ≥0)
      ≤ ENNReal.ofReal target := by
  refine
    empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget
      (R := (1 : ℝ≥0))
      hTarget_pos
      ?_
  let logBudget : ℝ := Real.log 2 - Real.log target
  by_cases hLogBudget_nonpos : logBudget ≤ 0
  · have hSq_nonneg :
        0 ≤
          (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) :=
      sq_nonneg _
    have hSubtract_nonpos :
        0 ≤
          2 * sampleSize *
            (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) := by
      positivity
    change
      Real.log 2 -
          2 * sampleSize *
            (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) /
            ((1 : ℝ) ^ (2 : ℕ)) ≤
        Real.log target
    norm_num
    linarith [hLogBudget_nonpos, hSubtract_nonpos]
  · have hLogBudget_pos : 0 < logBudget := lt_of_not_ge hLogBudget_nonpos
    have hDen_pos : 0 < 2 * sampleSize := by
      positivity
    have hInside_nonneg :
        0 ≤ logBudget / (2 * sampleSize) :=
      (div_pos hLogBudget_pos hDen_pos).le
    have hSqrt_sq :
        (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) =
          logBudget / (2 * sampleSize) := by
      exact Real.sq_sqrt hInside_nonneg
    have hProd :
        2 * sampleSize *
            (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) =
          logBudget := by
      rw [hSqrt_sq]
      field_simp [hDen_pos.ne']
    change
      Real.log 2 -
          2 * sampleSize *
            (Real.sqrt (logBudget / (2 * sampleSize))) ^ (2 : ℕ) /
            ((1 : ℝ) ^ (2 : ℕ)) ≤
        Real.log target
    norm_num
    rw [hProd]
    dsimp [logBudget]
    rw [show Real.log target + (Real.log 2 - Real.log target) = Real.log 2 by ring]

/--
Displayed sample-size Hoeffding budget from a sample-size lower bound.

This is the user-facing algebraic form of
`empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget`:
if the sample size clears the usual
`R^2 / (2 * ε^2) * (log 2 - log target)` threshold, then the displayed
two-sided Hoeffding tail is at most `target`.
-/
theorem empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_sampleSize_ge
    {sampleSize ε target : ℝ} {R : ℝ≥0}
    (hTarget_pos : 0 < target)
    (hε_pos : 0 < ε)
    (hR_pos : 0 < (R : ℝ))
    (hSampleSize_ge :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          (Real.log 2 - Real.log target) ≤ sampleSize) :
    empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail sampleSize ε R
      ≤ ENNReal.ofReal target := by
  refine
    empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget
      (R := R) hTarget_pos ?_
  have hε_sq_pos : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε_pos
  have hR_sq_pos : 0 < (R : ℝ) ^ (2 : ℕ) := sq_pos_of_pos hR_pos
  have hden_pos : 0 < 2 * ε ^ (2 : ℕ) :=
    mul_pos (by norm_num : (0 : ℝ) < 2) hε_sq_pos
  have hscale_nonneg :
      0 ≤ (2 * ε ^ (2 : ℕ)) / ((R : ℝ) ^ (2 : ℕ)) :=
    (div_pos hden_pos hR_sq_pos).le
  have hscaled :=
    mul_le_mul_of_nonneg_left hSampleSize_ge hscale_nonneg
  have hscaled' :
      Real.log 2 - Real.log target
        ≤ (2 * ε ^ (2 : ℕ)) / ((R : ℝ) ^ (2 : ℕ)) * sampleSize := by
    have hcancel :
        (2 * ε ^ (2 : ℕ)) / ((R : ℝ) ^ (2 : ℕ)) *
            (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ)) *
              (Real.log 2 - Real.log target)) =
          Real.log 2 - Real.log target := by
      field_simp [hden_pos.ne', hR_sq_pos.ne']
    calc
      Real.log 2 - Real.log target =
          (2 * ε ^ (2 : ℕ)) / ((R : ℝ) ^ (2 : ℕ)) *
            (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ)) *
              (Real.log 2 - Real.log target)) := hcancel.symm
      _ ≤ (2 * ε ^ (2 : ℕ)) / ((R : ℝ) ^ (2 : ℕ)) * sampleSize := hscaled
  have hscaled'' :
      Real.log 2 - Real.log target
        ≤ 2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ)) := by
    convert hscaled' using 1
    ring
  linarith

/--
The concrete two-sided Hoeffding budget is bounded by the uniform-range budget
when the concrete finite sum of squared half-ranges is positive and bounded by
the supplied range proxy.

This is the algebraic bridge that discharges the `hRangeEnvelope` hypothesis in
uniform-range wrappers, except for the degenerate zero-range case.
-/
theorem empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {sampleSize ε rangeVarianceProxy : ℝ}
    (hRangeSum_pos :
      0 <
        ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ))
    (hRangeSum_le :
      ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ)
        ≤ rangeVarianceProxy) :
    empiricalAverageTwoSidedHoeffdingTail s a b sampleSize ε
      ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize ε rangeVarianceProxy := by
  unfold empiricalAverageTwoSidedHoeffdingTail
  unfold empiricalAverageLowerHoeffdingTail
  unfold empiricalAverageUniformRangeTwoSidedHoeffdingTail
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  apply (Real.exp_le_exp).mpr
  let rangeSum : ℝ :=
    ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ)
  let numerator : ℝ := (sampleSize * ε) ^ 2
  have hNumerator_nonneg : 0 ≤ numerator := sq_nonneg _
  have hDen_pos : 0 < 2 * rangeSum := by
    nlinarith [hRangeSum_pos]
  have hDen_le : 2 * rangeSum ≤ 2 * rangeVarianceProxy := by
    nlinarith [hRangeSum_le]
  have hDiv :
      numerator / (2 * rangeVarianceProxy) ≤ numerator / (2 * rangeSum) :=
    div_le_div_of_nonneg_left hNumerator_nonneg hDen_pos hDen_le
  have hNeg :
      -(numerator / (2 * rangeSum)) ≤ -(numerator / (2 * rangeVarianceProxy)) :=
    neg_le_neg hDiv
  have hNegDiv :
      -numerator / (2 * rangeSum) ≤ -numerator / (2 * rangeVarianceProxy) := by
    simpa [neg_div] using hNeg
  simpa [rangeSum, numerator] using hNegDiv

/--
Finite-sum range envelope from a pointwise uniform range bound.

If every sample coordinate has half-range at most `R / 2`, then the concrete
Hoeffding denominator sum is bounded by `card(s) * (R / 2)^2`.
-/
theorem empiricalAverageRangeSum_le_card_mul_uniformRange
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {R : ℝ≥0}
    (hRange : ∀ i, i ∈ s → ‖b i - a i‖₊ ≤ R) :
    ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ)
      ≤ (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) := by
  have hNN :
      (∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) ≤
        s.card • ((R / 2) ^ (2 : ℕ)) := by
    calc
      (∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ)))
          ≤ ∑ _i ∈ s, ((R / 2) ^ (2 : ℕ)) := by
            exact Finset.sum_le_sum (fun i hi => by
              have hHalf : ‖b i - a i‖₊ / 2 ≤ R / 2 := by
                exact div_le_div_of_nonneg_right (hRange i hi) (by positivity)
              exact pow_le_pow_left₀ (by positivity) hHalf 2)
      _ = s.card • ((R / 2) ^ (2 : ℕ)) := by
            simp
  have hReal := NNReal.coe_le_coe.mpr hNN
  simpa [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat] using hReal

/--
The concrete Hoeffding denominator is positive once one sampled coordinate has
positive range.
-/
theorem empiricalAverageRangeSum_pos_of_exists_range_pos
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hExists : ∃ i, i ∈ s ∧ 0 < ‖b i - a i‖₊) :
    0 <
      ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ) := by
  rcases hExists with ⟨i, hi, hpos⟩
  have hhalf_pos : 0 < ‖b i - a i‖₊ / 2 := by
    exact div_pos hpos (by norm_num)
  have hterm_pos : 0 < (‖b i - a i‖₊ / 2) ^ (2 : ℕ) :=
    pow_pos hhalf_pos _
  have hsum_pos :
      0 < ∑ j ∈ s, ((‖b j - a j‖₊ / 2) ^ (2 : ℕ)) := by
    exact Finset.sum_pos'
      (fun j hj => by
        positivity)
      ⟨i, hi, hterm_pos⟩
  exact NNReal.coe_pos.mpr hsum_pos

/--
Uniform-range tail bridge from a pointwise range-width condition.

This combines `empiricalAverageRangeSum_le_card_mul_uniformRange` with the
algebraic uniform-range tail comparison. The positive concrete range-sum
assumption excludes the degenerate denominator-zero case.
-/
theorem empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {sampleSize ε rangeVarianceProxy : ℝ} {R : ℝ≥0}
    (hRangeSum_pos :
      0 <
        ((↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ))
    (hRange : ∀ i, i ∈ s → ‖b i - a i‖₊ ≤ R)
    (hProxy :
      (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) ≤ rangeVarianceProxy) :
    empiricalAverageTwoSidedHoeffdingTail s a b sampleSize ε
      ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize ε rangeVarianceProxy :=
  empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail
    s a b hRangeSum_pos
    ((empiricalAverageRangeSum_le_card_mul_uniformRange s a b hRange).trans hProxy)

/--
Uniform-range tail bridge from a pointwise range-width condition and a
nondegenerate sampled coordinate.

This packages the positivity side condition of
`empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound`
as the more checkable claim that one sampled coordinate has positive range.
-/
theorem empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound_of_exists_range_pos
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {sampleSize ε rangeVarianceProxy : ℝ} {R : ℝ≥0}
    (hExists : ∃ i, i ∈ s ∧ 0 < ‖b i - a i‖₊)
    (hRange : ∀ i, i ∈ s → ‖b i - a i‖₊ ≤ R)
    (hProxy :
      (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) ≤ rangeVarianceProxy) :
    empiricalAverageTwoSidedHoeffdingTail s a b sampleSize ε
      ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize ε rangeVarianceProxy :=
  empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound
    s a b
    (empiricalAverageRangeSum_pos_of_exists_range_pos s a b hExists)
    hRange
    hProxy

/--
Finite-horizon, finite-class empirical-average deviation bound from Hoeffding.

For every finite time `t` and hypothesis `h`, assume an independent finite
sample of bounded losses. The fixed-hypothesis Hoeffding wrappers provide the
upper and lower one-sided empirical-average tails. If those two tails fit the
dyadic time budget after splitting across the finite hypothesis class, then the
absolute deviation event is controlled simultaneously over all `(t, h)` pairs
in the finite horizon.

This is still a finite-prefix theorem. It does not optimize the threshold,
derive a closed-form sample-complexity display, or assert an infinite-time
claim.
-/
theorem finiteTimeClassEmpiricalAverageDeviationFromHoeffding_dyadicBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Fin T → H → Finset ι}
    {sampleSize : Fin T → H → ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞}
    (hMeas :
      ∀ t h i, i ∈ s t h → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s t h →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s t h, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s t h → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : ∀ t h, sampleSize t h = ((s t h).card : ℝ))
    (hNonemptySample : ∀ t h, 0 < (s t h).card)
    (hε : 0 ≤ ε)
    (hTailBudget :
      ∀ t h,
        empiricalAverageUpperHoeffdingTail (s t h) (a t h) (b t h)
            (sampleSize t h) ε
          + empiricalAverageLowerHoeffdingTail (s t h) (a t h) (b t h)
            (sampleSize t h) ε
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize p.1 p.2 -
              (∑ i ∈ s p.1 p.2, loss p.1 p.2 i ω) /
                sampleSize p.1 p.2|}) ≤ δ :=
  finiteTimeClassTwoSidedUnionBoundFromOneSidedTails_dyadicBudget
    (deviation := fun t h ω =>
      risk t h / sampleSize t h -
        (∑ i ∈ s t h, loss t h i ω) / sampleSize t h)
    (upperTail := fun t h =>
      empiricalAverageUpperHoeffdingTail (s t h) (a t h) (b t h)
        (sampleSize t h) ε)
    (lowerTail := fun t h =>
      empiricalAverageLowerHoeffdingTail (s t h) (a t h) (b t h)
        (sampleSize t h) ε)
    (fun t h => by
      simpa [empiricalAverageUpperHoeffdingTail] using
        fixedHypothesisEmpiricalAverageUpperTailFromHoeffdingENNReal
          (μ := μ)
          (loss := loss t h)
          (a := a t h)
          (b := b t h)
          (s := s t h)
          (n := sampleSize t h)
          (ε := ε)
          (risk := risk t h)
          (hIndep t h)
          (hMeas t h)
          (hBound t h)
          (hRisk t h)
          (hNegExpectation t h)
          (hSampleSize t h)
          (hNonemptySample t h)
          hε)
    (fun t h => by
      simpa [empiricalAverageLowerHoeffdingTail, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using
        fixedHypothesisEmpiricalAverageLowerTailFromHoeffdingENNReal
          (μ := μ)
          (loss := loss t h)
          (a := a t h)
          (b := b t h)
          (s := s t h)
          (n := sampleSize t h)
          (ε := ε)
          (risk := risk t h)
          (hIndep t h)
          (hMeas t h)
          (hBound t h)
          (hRisk t h)
          (hSampleSize t h)
          (hNonemptySample t h)
          hε)
    hTailBudget

/--
Shared-sample version of the finite-horizon Hoeffding-to-dyadic bridge.

This specialization keeps one finite sample index set and one sample size across
all times and hypotheses, while still allowing the bounded loss family and risk
to depend on `(t, h)`. It is the cleaner finite-class SLT-facing wrapper over
`finiteTimeClassEmpiricalAverageDeviationFromHoeffding_dyadicBudget`.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_dyadicBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hTailBudget :
      ∀ t h,
        empiricalAverageUpperHoeffdingTail s (a t h) (b t h) sampleSize ε
          + empiricalAverageLowerHoeffdingTail s (a t h) (b t h) sampleSize ε
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassEmpiricalAverageDeviationFromHoeffding_dyadicBudget
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := fun _ _ => s)
    (sampleSize := fun _ _ => sampleSize)
    (risk := risk)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    (fun _ _ => hSampleSize)
    (fun _ _ => hNonemptySample)
    hε
    hTailBudget

/--
Shared-sample finite-horizon Hoeffding bridge with a two-sided tail budget.

This is a closed-budget corollary of
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_dyadicBudget`.
Instead of asking callers to separately budget the upper and lower one-sided
Hoeffding tails, it uses the combined expression
`empiricalAverageTwoSidedHoeffdingTail`.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_twoSidedTailBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hTailBudget :
      ∀ t h,
        empiricalAverageTwoSidedHoeffdingTail s (a t h) (b t h) sampleSize ε
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_dyadicBudget
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (risk := risk)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε
    (fun t h => by
      calc
        empiricalAverageUpperHoeffdingTail s (a t h) (b t h) sampleSize ε
            + empiricalAverageLowerHoeffdingTail s (a t h) (b t h) sampleSize ε
            = empiricalAverageLowerHoeffdingTail s (a t h) (b t h) sampleSize ε
              + empiricalAverageLowerHoeffdingTail s (a t h) (b t h) sampleSize ε := by
                rw [empiricalAverageUpperHoeffdingTail_eq_lower]
        _ = empiricalAverageTwoSidedHoeffdingTail s (a t h) (b t h) sampleSize ε := by
              simp [empiricalAverageTwoSidedHoeffdingTail, two_mul]
        _ ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹ :=
              hTailBudget t h)

/--
Shared-sample finite-horizon Hoeffding bridge with a uniform range proxy.

This wrapper replaces the concrete per-hypothesis Hoeffding denominator by one
uniform proxy. The hypothesis `hRangeEnvelope` is the explicit bridge obligation:
the concrete two-sided Hoeffding tail for each `(time, hypothesis)` must be
bounded by the uniform-range budget. The result then only asks the caller to
budget that uniform expression against the dyadic time schedule.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize rangeVarianceProxy : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hRangeEnvelope :
      ∀ t h,
        empiricalAverageTwoSidedHoeffdingTail s (a t h) (b t h) sampleSize ε
          ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
              sampleSize ε rangeVarianceProxy)
    (hUniformTailBudget :
      ∀ (t : Fin T) (_h : H),
        empiricalAverageUniformRangeTwoSidedHoeffdingTail
            sampleSize ε rangeVarianceProxy
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_twoSidedTailBudget
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (risk := risk)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε
    (fun (t : Fin T) (h : H) => (hRangeEnvelope t h).trans (hUniformTailBudget t h))

/--
Shared-sample finite-horizon Hoeffding bridge with a pointwise uniform range
bound.

This is the closed-form range-envelope version of
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget`.
The concrete finite range-sum remains required to be positive for each
`(time, hypothesis)` pair, while the upper envelope is the single proxy
`card(s) * (R / 2)^2`.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize rangeVarianceProxy : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hRangeSum_pos :
      ∀ t h,
        0 <
          ((↑(∑ i ∈ s, ((‖b t h i - a t h i‖₊ / 2) ^ (2 : ℕ))) : ℝ≥0) : ℝ))
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hProxy :
      (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) ≤ rangeVarianceProxy)
    (hUniformTailBudget :
      ∀ (t : Fin T) (_h : H),
        empiricalAverageUniformRangeTwoSidedHoeffdingTail
            sampleSize ε rangeVarianceProxy
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (rangeVarianceProxy := rangeVarianceProxy)
    (risk := risk)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε
    (fun t h =>
      empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound
        s (a t h) (b t h) (hRangeSum_pos t h) (hRange t h) hProxy)
    hUniformTailBudget

/--
Shared-sample finite-horizon Hoeffding bridge with pointwise uniform range and
a nondegenerate sampled coordinate.

This is the range-bound wrapper with the positive denominator supplied by the
more concrete condition that each `(time, hypothesis)` pair has some sampled
coordinate with positive range.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound_of_exists_range_pos
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize rangeVarianceProxy : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hProxy :
      (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) ≤ rangeVarianceProxy)
    (hUniformTailBudget :
      ∀ (t : Fin T) (_h : H),
        empiricalAverageUniformRangeTwoSidedHoeffdingTail
            sampleSize ε rangeVarianceProxy
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (rangeVarianceProxy := rangeVarianceProxy)
    (risk := risk)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε
    (fun t h => empiricalAverageRangeSum_pos_of_exists_range_pos s (a t h) (b t h) (hExists t h))
    hRange
    hProxy
    hUniformTailBudget

/--
Shared-sample finite-horizon Hoeffding bridge with the tail budget displayed in
the usual finite-class sample-size form.

The caller supplies the sample size, range width `R`, threshold `ε`, and dyadic
failure budget condition
`2 * exp(-2 * sampleSize * ε^2 / R^2) <= budget(t) / card(H)`. The theorem
then routes that readable budget through the nondegenerate uniform-range
Hoeffding wrapper.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hSampleSizeTailBudget :
      ∀ (t : Fin T) (_h : H),
        empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail sampleSize ε R
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ := by
  have hSampleSize_pos : 0 < sampleSize := by
    rw [hSampleSize]
    exact_mod_cast hNonemptySample
  exact
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound_of_exists_range_pos
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (rangeVarianceProxy := sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ)))
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε
      hExists
      hRange
      (by
        rw [hSampleSize])
      (fun t h => by
        rw [empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail
          hSampleSize_pos hR_pos]
        exact hSampleSizeTailBudget t h)

/--
Shared-sample finite-horizon Hoeffding bridge with a threshold depending on
`(time, hypothesis)`.

This is the variable-radius version of
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize`.
It discharges the pointwise absolute-deviation tails from the fixed-hypothesis
Hoeffding wrappers, then feeds the resulting per-time thresholds through the
dyadic finite-prefix union shell.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_threshold
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {threshold : Fin T → H → ℝ}
    {δ : ℝ≥0∞} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hThreshold_nonneg : ∀ t h, 0 ≤ threshold t h)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hSampleSizeTailBudget :
      ∀ (t : Fin T) (h : H),
        empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
            sampleSize (threshold t h) R
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          threshold p.1 p.2 ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ := by
  have hSampleSize_pos : 0 < sampleSize := by
    rw [hSampleSize]
    exact_mod_cast hNonemptySample
  have hProxy :
      (s.card : ℝ) * (((R : ℝ) / 2) ^ (2 : ℕ)) ≤
        sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ)) := by
    rw [hSampleSize]
  refine
    finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold
      (μ := μ)
      (deviation := fun t h ω =>
        risk t h / sampleSize -
          (∑ i ∈ s, loss t h i ω) / sampleSize)
      (threshold := threshold)
      (δ := δ)
      ?_
  intro t h
  have hUpper :
      μ {ω |
          threshold t h ≤
            risk t h / sampleSize - (∑ i ∈ s, loss t h i ω) / sampleSize}
        ≤ empiricalAverageUpperHoeffdingTail
            s (a t h) (b t h) sampleSize (threshold t h) := by
    simpa [empiricalAverageUpperHoeffdingTail] using
      fixedHypothesisEmpiricalAverageUpperTailFromHoeffdingENNReal
        (μ := μ)
        (loss := loss t h)
        (a := a t h)
        (b := b t h)
        (s := s)
        (n := sampleSize)
        (ε := threshold t h)
        (risk := risk t h)
        (hIndep t h)
        (hMeas t h)
        (hBound t h)
        (hRisk t h)
        (hNegExpectation t h)
        hSampleSize
        hNonemptySample
        (hThreshold_nonneg t h)
  have hLower :
      μ {ω |
          threshold t h ≤
            - (risk t h / sampleSize - (∑ i ∈ s, loss t h i ω) / sampleSize)}
        ≤ empiricalAverageLowerHoeffdingTail
            s (a t h) (b t h) sampleSize (threshold t h) := by
    simpa [empiricalAverageLowerHoeffdingTail, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using
      fixedHypothesisEmpiricalAverageLowerTailFromHoeffdingENNReal
        (μ := μ)
        (loss := loss t h)
        (a := a t h)
        (b := b t h)
        (s := s)
        (n := sampleSize)
        (ε := threshold t h)
        (risk := risk t h)
        (hIndep t h)
        (hMeas t h)
        (hBound t h)
        (hRisk t h)
        hSampleSize
        hNonemptySample
        (hThreshold_nonneg t h)
  have hTwoSided :
      μ {ω |
          threshold t h ≤
            |risk t h / sampleSize - (∑ i ∈ s, loss t h i ω) / sampleSize|}
        ≤ empiricalAverageTwoSidedHoeffdingTail
            s (a t h) (b t h) sampleSize (threshold t h) := by
    calc
      μ {ω |
          threshold t h ≤
            |risk t h / sampleSize - (∑ i ∈ s, loss t h i ω) / sampleSize|}
          ≤ empiricalAverageUpperHoeffdingTail
                s (a t h) (b t h) sampleSize (threshold t h)
              + empiricalAverageLowerHoeffdingTail
                s (a t h) (b t h) sampleSize (threshold t h) :=
            twoSidedDeviationTailFromOneSidedTails
              (fun ω =>
                risk t h / sampleSize -
                  (∑ i ∈ s, loss t h i ω) / sampleSize)
              hUpper
              hLower
      _ = empiricalAverageTwoSidedHoeffdingTail
            s (a t h) (b t h) sampleSize (threshold t h) := by
            rw [empiricalAverageUpperHoeffdingTail_eq_lower]
            simp [empiricalAverageTwoSidedHoeffdingTail, two_mul]
  have hUniformRange :
      empiricalAverageTwoSidedHoeffdingTail
          s (a t h) (b t h) sampleSize (threshold t h)
        ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
            sampleSize (threshold t h)
            (sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ))) :=
    empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound_of_exists_range_pos
      s (a t h) (b t h) (R := R) (hExists t h) (hRange t h) hProxy
  have hSampleTail :
      empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize (threshold t h)
          (sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ)))
        =
        empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
          sampleSize (threshold t h) R :=
    empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail
      hSampleSize_pos
      hR_pos
  calc
    μ {ω |
        threshold t h ≤
          |risk t h / sampleSize - (∑ i ∈ s, loss t h i ω) / sampleSize|}
        ≤ empiricalAverageTwoSidedHoeffdingTail
            s (a t h) (b t h) sampleSize (threshold t h) := hTwoSided
    _ ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize (threshold t h)
          (sampleSize * (((R : ℝ) / 2) ^ (2 : ℕ))) := hUniformRange
    _ = empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
          sampleSize (threshold t h) R := hSampleTail
    _ ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹ :=
          hSampleSizeTailBudget t h

/--
Shared-sample finite-horizon Hoeffding bridge from a real log-budget interface.

The theorem separates real-valued algebra from the `ENNReal` probability
budget: each `(time, hypothesis)` receives a positive real budget whose
`ENNReal.ofReal` value is below the dyadic budget split. A log-budget inequality
then implies the displayed sample-size Hoeffding tail fits that real budget.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_from_logBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞} {R : ℝ≥0}
    {realBudget : Fin T → H → ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε : 0 ≤ ε)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hRealBudget_pos : ∀ t h, 0 < realBudget t h)
    (hLogBudget :
      ∀ t h,
        Real.log 2 - 2 * sampleSize * ε ^ (2 : ℕ) / ((R : ℝ) ^ (2 : ℕ))
          ≤ Real.log (realBudget t h))
    (hRealBudget_le :
      ∀ (t : Fin T) (h : H),
        ENNReal.ofReal (realBudget t h)
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (risk := risk)
    (R := R)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε
    hR_pos
    hExists
    hRange
    (fun t h =>
      (empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget
        (R := R)
        (hRealBudget_pos t h)
        (hLogBudget t h)).trans
        (hRealBudget_le t h))

/--
Shared-sample finite-horizon Hoeffding bridge from a sample-size lower bound.

This packages the usual displayed finite-class sample-size condition: for each
`(time, hypothesis)` real budget, it is enough that
`sampleSize >= R^2 / (2 * ε^2) * (log 2 - log realBudget)`, together with the
comparison from that real budget into the dyadic `ENNReal` budget split.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε : ℝ} {δ : ℝ≥0∞} {R : ℝ≥0}
    {realBudget : Fin T → H → ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hRealBudget_pos : ∀ t h, 0 < realBudget t h)
    (hSampleSize_ge :
      ∀ (t : Fin T) (h : H),
        (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
            (Real.log 2 - Real.log (realBudget t h)) ≤ sampleSize)
    (hRealBudget_le :
      ∀ (t : Fin T) (h : H),
        ENNReal.ofReal (realBudget t h)
          ≤ finiteDyadicTimeBudget δ t.val * (Fintype.card H : ℝ≥0∞)⁻¹) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤ δ :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize
    (μ := μ)
    (loss := loss)
    (a := a)
    (b := b)
    (s := s)
    (sampleSize := sampleSize)
    (risk := risk)
    (R := R)
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε_pos.le
    hR_pos
    hExists
    hRange
    (fun t h =>
      (empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_sampleSize_ge
        (R := R)
        (hRealBudget_pos t h)
        hε_pos
        hR_pos
        (hSampleSize_ge t h)).trans
        (hRealBudget_le t h))

/--
The concrete real dyadic class budget maps to the `ENNReal` dyadic
time-budget split.

This isolates the `ofReal`/integer-power algebra used by the dyadic
sample-size wrappers.
-/
theorem finiteDyadicRealBudget_classBudget_ofReal
    {H : Type*} [Fintype H] [Nonempty H]
    {δ_real : ℝ} (hδ_real_pos : 0 < δ_real) (t : ℕ) :
    ENNReal.ofReal
        (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
          (Fintype.card H : ℝ)) =
      finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t *
        (Fintype.card H : ℝ≥0∞)⁻¹ := by
  have hDyadic_pos :
      0 < (2 : ℝ) ^ (-1 - (t : ℤ)) :=
    zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have hDyadic_ofReal :
      ENNReal.ofReal ((2 : ℝ) ^ (-1 - (t : ℤ))) =
        (2 : ℝ≥0∞) ^ (-1 - (t : ℤ)) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hDyadic_pos.le]
    rw [← Real.toNNReal_of_nonneg hDyadic_pos.le]
    change
      (↑(Real.toNNReal ((2 : ℝ) ^ (-1 - (t : ℤ)))) : ℝ≥0∞) =
        (((2 : ℝ≥0) : ℝ≥0∞) ^ (-1 - (t : ℤ)))
    rw [← ENNReal.coe_zpow (by norm_num : (2 : ℝ≥0) ≠ 0)]
    congr 1
    simpa using
      Real.toNNReal_zpow (by norm_num : (0 : ℝ) ≤ 2) (-1 - (t : ℤ))
  calc
    ENNReal.ofReal
        (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
          (Fintype.card H : ℝ))
        = ENNReal.ofReal
            (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ))) /
          ENNReal.ofReal (Fintype.card H : ℝ) := by
            rw [ENNReal.ofReal_div_of_pos hCard_pos]
    _ = (ENNReal.ofReal δ_real *
            ENNReal.ofReal ((2 : ℝ) ^ (-1 - (t : ℤ)))) /
          ENNReal.ofReal (Fintype.card H : ℝ) := by
            rw [ENNReal.ofReal_mul hδ_real_pos.le]
    _ = (ENNReal.ofReal δ_real *
            (2 : ℝ≥0∞) ^ (-1 - (t : ℤ))) /
          (Fintype.card H : ℝ≥0∞) := by
            rw [hDyadic_ofReal]
            norm_num
    _ = finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t *
          (Fintype.card H : ℝ≥0∞)⁻¹ := by
            simp [finiteDyadicTimeBudget, div_eq_mul_inv, mul_assoc]

/--
Shared-sample finite-horizon Hoeffding bridge with an explicit dyadic real
budget.

This removes the caller-supplied `realBudget` comparison from
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge`:
each `(time, hypothesis)` pair receives the concrete real budget
`δ * 2^(-1-t) / card(H)`, and Lean checks that its `ENNReal.ofReal` image fits
the dyadic time/class split.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hSampleSize_ge :
      ∀ (t : Fin T) (_h : H),
        (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
            (Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                  (Fintype.card H : ℝ))) ≤ sampleSize) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real := by
  refine
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (risk := risk)
      (R := R)
      (δ := ENNReal.ofReal δ_real)
      (realBudget := fun t _ =>
        δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) / (Fintype.card H : ℝ))
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε_pos
      hR_pos
      hExists
      hRange
      ?_
      hSampleSize_ge
      ?_
  · intro t _h
    have hDyadic_pos :
        0 < (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
    have hCard_pos : 0 < (Fintype.card H : ℝ) := by
      exact_mod_cast hCard_pos_nat
    exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
  · intro t _h
    have hDyadic_pos :
        0 < (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
    have hCard_pos : 0 < (Fintype.card H : ℝ) := by
      exact_mod_cast hCard_pos_nat
    have hDyadic_ofReal :
        ENNReal.ofReal ((2 : ℝ) ^ (-1 - (t.val : ℤ))) =
          (2 : ℝ≥0∞) ^ (-1 - (t.val : ℤ)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hDyadic_pos.le]
      rw [← Real.toNNReal_of_nonneg hDyadic_pos.le]
      change
        (↑(Real.toNNReal ((2 : ℝ) ^ (-1 - (t.val : ℤ)))) : ℝ≥0∞) =
          (((2 : ℝ≥0) : ℝ≥0∞) ^ (-1 - (t.val : ℤ)))
      rw [← ENNReal.coe_zpow (by norm_num : (2 : ℝ≥0) ≠ 0)]
      congr 1
      simpa using
        Real.toNNReal_zpow (by norm_num : (0 : ℝ) ≤ 2) (-1 - (t.val : ℤ))
    calc
      ENNReal.ofReal
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ))
          = ENNReal.ofReal
              (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ))) /
            ENNReal.ofReal (Fintype.card H : ℝ) := by
              rw [ENNReal.ofReal_div_of_pos hCard_pos]
      _ = (ENNReal.ofReal δ_real *
              ENNReal.ofReal ((2 : ℝ) ^ (-1 - (t.val : ℤ)))) /
            ENNReal.ofReal (Fintype.card H : ℝ) := by
              rw [ENNReal.ofReal_mul hδ_real_pos.le]
      _ = (ENNReal.ofReal δ_real *
              (2 : ℝ≥0∞) ^ (-1 - (t.val : ℤ))) /
            (Fintype.card H : ℝ≥0∞) := by
              rw [hDyadic_ofReal]
              norm_num
      _ = finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t.val *
            (Fintype.card H : ℝ≥0∞)⁻¹ := by
              simp [finiteDyadicTimeBudget, div_eq_mul_inv, mul_assoc]
      _ ≤ finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t.val *
            (Fintype.card H : ℝ≥0∞)⁻¹ := le_rfl

/--
Algebraic radius-to-sample-size bridge for the uniform-range Hoeffding display.

If the square-root radius expression is at most `ε`, then the corresponding
sample-size lower bound used by
`empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_sampleSize_ge`
holds. When the log-budget term is nonpositive, the lower bound is immediate;
otherwise the result follows by squaring the displayed radius inequality.
-/
theorem empiricalAverageUniformRangeSampleSize_ge_of_sqrtBudget_le
    {sampleSize ε logBudget : ℝ} {R : ℝ≥0}
    (hSampleSize_pos : 0 < sampleSize)
    (hε_pos : 0 < ε)
    (hRadius :
      Real.sqrt ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) * logBudget) ≤ ε) :
    (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) * logBudget ≤ sampleSize := by
  by_cases hLogBudget_nonpos : logBudget ≤ 0
  · have hscale_nonneg :
        0 ≤ ((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ)) := by
      positivity
    have hleft_nonpos :
        (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) * logBudget ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hLogBudget_nonpos
    linarith
  · have hA_le_eps_sq :
        (((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) * logBudget ≤ ε ^ (2 : ℕ) :=
      (Real.sqrt_le_iff.mp hRadius).2
    have hε_sq_pos : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε_pos
    have hden_sample_pos : 0 < 2 * sampleSize :=
      mul_pos (by norm_num : (0 : ℝ) < 2) hSampleSize_pos
    have hden_eps_pos : 0 < 2 * ε ^ (2 : ℕ) :=
      mul_pos (by norm_num : (0 : ℝ) < 2) hε_sq_pos
    have hfactor_nonneg : 0 ≤ sampleSize / (ε ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_right hA_le_eps_sq hfactor_nonneg
    have hleft :
        ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) * logBudget) *
            (sampleSize / ε ^ (2 : ℕ)) =
          (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) * logBudget := by
      field_simp [hSampleSize_pos.ne', hε_sq_pos.ne']
    have hright :
        ε ^ (2 : ℕ) * (sampleSize / ε ^ (2 : ℕ)) = sampleSize := by
      field_simp [hε_sq_pos.ne']
    calc
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) * logBudget =
          ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) * logBudget) *
            (sampleSize / ε ^ (2 : ℕ)) := hleft.symm
      _ ≤ ε ^ (2 : ℕ) * (sampleSize / ε ^ (2 : ℕ)) := hmul
      _ = sampleSize := hright

/--
Shared-sample finite-horizon Hoeffding bridge with a radius-style sample-size
condition and an explicit dyadic real budget.

This is a user-facing algebra layer over
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget`:
instead of supplying the sample-size lower bound directly, callers may bound the
usual square-root radius expression by `ε`.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hRadius :
      ∀ (t : Fin T) (_h : H),
        Real.sqrt
          ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) *
            (Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                  (Fintype.card H : ℝ)))) ≤ ε) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real := by
  have hSampleSize_pos : 0 < sampleSize := by
    rw [hSampleSize]
    exact_mod_cast hNonemptySample
  exact
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε_pos
      hδ_real_pos
      hR_pos
      hExists
      hRange
      (fun t h =>
        empiricalAverageUniformRangeSampleSize_ge_of_sqrtBudget_le
          (R := R)
          hSampleSize_pos
          hε_pos
          (hRadius t h))

/--
The finite-horizon dyadic real budget is no larger than any per-time dyadic
budget in the prefix.

For `t : Fin T`, the final dyadic exponent in the prefix is `-T`, while the
per-time exponent is `-1 - t`. Since `t < T`, monotonicity of `2^n` over
integer exponents gives the budget comparison.
-/
theorem finiteDyadicRealBudget_horizon_le_time
    {H : Type*} [Fintype H] [Nonempty H]
    {δ_real : ℝ} (hδ_real_pos : 0 < δ_real)
    {T : ℕ} (t : Fin T) :
    δ_real * (2 : ℝ) ^ (-(T : ℤ)) / (Fintype.card H : ℝ) ≤
      δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) / (Fintype.card H : ℝ) := by
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have ht_succ_le : t.val + 1 ≤ T := Nat.succ_le_of_lt t.isLt
  have ht_succ_le_int : (t.val : ℤ) + 1 ≤ (T : ℤ) := by
    exact_mod_cast ht_succ_le
  have hexp : -(T : ℤ) ≤ -1 - (t.val : ℤ) := by
    linarith
  have hpow :
      (2 : ℝ) ^ (-(T : ℤ)) ≤ (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hscale_nonneg : 0 ≤ δ_real / (Fintype.card H : ℝ) := by
    positivity
  calc
    δ_real * (2 : ℝ) ^ (-(T : ℤ)) / (Fintype.card H : ℝ)
        = (δ_real / (Fintype.card H : ℝ)) * (2 : ℝ) ^ (-(T : ℤ)) := by
          ring
    _ ≤ (δ_real / (Fintype.card H : ℝ)) * (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
          mul_le_mul_of_nonneg_left hpow hscale_nonneg
    _ = δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
          (Fintype.card H : ℝ) := by
          ring

/--
Shared-sample finite-horizon Hoeffding bridge with one horizon-level radius
condition.

This is a readability wrapper over
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget`.
It replaces the per-time radius assumptions by one finite-prefix radius using
the smallest dyadic budget in the prefix. It is still only a finite-horizon
statement.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hHorizonRadius :
      Real.sqrt
        ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
                (Fintype.card H : ℝ)))) ≤ ε) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real := by
  have hSampleSize_pos : 0 < sampleSize := by
    rw [hSampleSize]
    exact_mod_cast hNonemptySample
  have hcoeff_nonneg :
      0 ≤ ((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize) := by
    positivity
  refine
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε_pos
      hδ_real_pos
      hR_pos
      hExists
      hRange
      ?_
  intro t _h
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have hTimeBudget_pos :
      0 <
        δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
          (Fintype.card H : ℝ) := by
    have hDyadic_pos : 0 < (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
  have hHorizonBudget_pos :
      0 <
        δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
          (Fintype.card H : ℝ) := by
    have hDyadic_pos : 0 < (2 : ℝ) ^ (-(T : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
  have hBudget_le :
      δ_real * (2 : ℝ) ^ (-(T : ℤ)) / (Fintype.card H : ℝ) ≤
        δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
          (Fintype.card H : ℝ) :=
    finiteDyadicRealBudget_horizon_le_time
      (H := H)
      hδ_real_pos
      t
  have hLog_mono :
      Real.log
          (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
            (Fintype.card H : ℝ)) ≤
        Real.log
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ)) :=
    Real.log_le_log hHorizonBudget_pos hBudget_le
  have hLogBudget_le :
      Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
              (Fintype.card H : ℝ)) ≤
        Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
              (Fintype.card H : ℝ)) := by
    linarith
  have hInside_le :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                (Fintype.card H : ℝ))) ≤
        (((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
                (Fintype.card H : ℝ))) :=
    mul_le_mul_of_nonneg_left hLogBudget_le hcoeff_nonneg
  exact (Real.sqrt_le_sqrt hInside_le).trans hHorizonRadius

/--
Closed-form rewrite for the finite-horizon dyadic real-budget log term.
-/
theorem finiteDyadicRealBudget_horizon_logBudget_eq_closedForm
    {H : Type*} [Fintype H] [Nonempty H]
    {δ_real : ℝ} (hδ_real_pos : 0 < δ_real) (T : ℕ) :
    Real.log 2 -
        Real.log
          (δ_real * ((2 : ℝ) ^ T)⁻¹ /
            (Fintype.card H : ℝ)) =
      Real.log (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) / δ_real) := by
  have hdyadic_eq : ((2 : ℝ) ^ T)⁻¹ = (2 : ℝ) ^ (-(T : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
  rw [hdyadic_eq]
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have hpow_pos : 0 < (2 : ℝ) ^ (-(T : ℤ)) :=
    zpow_pos (by norm_num : (0 : ℝ) < 2) _
  rw [Real.log_div (mul_ne_zero hδ_real_pos.ne' hpow_pos.ne') hCard_pos.ne']
  rw [Real.log_mul hδ_real_pos.ne' hpow_pos.ne']
  rw [Real.log_zpow]
  rw [Real.log_div
    (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hCard_pos.ne')
    hδ_real_pos.ne']
  rw [Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hCard_pos.ne']
  rw [Real.log_pow]
  norm_num
  ring

/--
Shared-sample finite-horizon Hoeffding bridge with a closed-form horizon radius.

This is the displayed finite-prefix form of
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget`.
It rewrites the horizon dyadic log budget as
`log((2 : ℝ) ^ (T + 1) * card H / δ_real)`.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hClosedFormRadius :
      Real.sqrt
        ((((R : ℝ) ^ (2 : ℕ)) / (2 * sampleSize)) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real)) ≤ ε) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real := by
  refine
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε_pos
      hδ_real_pos
      hR_pos
      hExists
      hRange
      ?_
  have hLog_eq :=
    finiteDyadicRealBudget_horizon_logBudget_eq_closedForm
      (H := H)
      hδ_real_pos
      T
  simpa [hLog_eq] using hClosedFormRadius

/--
Shared-sample finite-horizon Hoeffding bridge with a closed-form sample-size
condition.

This is the displayed sample-complexity form of the finite-prefix theorem. It
uses one sufficient sample-size lower bound with the closed horizon/class/budget
log term, then recovers the per-time dyadic sample-size hypotheses by
monotonicity of the finite-horizon budget.
-/
theorem finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hClosedFormSampleSize :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) ≤ sampleSize) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real := by
  refine
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := sampleSize)
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hSampleSize
      hNonemptySample
      hε_pos
      hδ_real_pos
      hR_pos
      hExists
      hRange
      ?_
  intro t _h
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have hHorizonBudget_pos :
      0 <
        δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
          (Fintype.card H : ℝ) := by
    have hDyadic_pos : 0 < (2 : ℝ) ^ (-(T : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
  have hBudget_le :
      δ_real * (2 : ℝ) ^ (-(T : ℤ)) / (Fintype.card H : ℝ) ≤
        δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
          (Fintype.card H : ℝ) :=
    finiteDyadicRealBudget_horizon_le_time
      (H := H)
      hδ_real_pos
      t
  have hLog_mono :
      Real.log
          (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
            (Fintype.card H : ℝ)) ≤
        Real.log
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ)) := by
    exact Real.log_le_log hHorizonBudget_pos hBudget_le
  have hLogBudget_le :
      Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
              (Fintype.card H : ℝ)) ≤
        Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
              (Fintype.card H : ℝ)) := by
    linarith
  have hscale_nonneg :
      0 ≤ ((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ)) := by
    positivity
  have hPerTime_le_horizon :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                (Fintype.card H : ℝ))) ≤
        (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
                (Fintype.card H : ℝ))) :=
    mul_le_mul_of_nonneg_left hLogBudget_le hscale_nonneg
  have hLog_eq :=
    finiteDyadicRealBudget_horizon_logBudget_eq_closedForm
      (H := H)
      hδ_real_pos
      T
  have hHorizonSampleSize :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          (Real.log 2 -
            Real.log
              (δ_real * (2 : ℝ) ^ (-(T : ℤ)) /
                (Fintype.card H : ℝ))) ≤ sampleSize := by
    simpa [zpow_neg, zpow_natCast, hLog_eq] using hClosedFormSampleSize
  exact hPerTime_le_horizon.trans hHorizonSampleSize

/--
Finite-prefix finite-class Hoeffding deviation bound in the closed-form
sample-size shape used by the route-facing notes.

This theorem is a short API wrapper around
`finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget`.
It keeps the statement tied to the checked shared-sample chain while exposing a
compact name for the verified-SLT program outline.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_closedForm
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι} {sampleSize : ℝ}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hSampleSize : sampleSize = (s.card : ℝ))
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hClosedFormSampleSize :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) ≤ sampleSize) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / sampleSize -
              (∑ i ∈ s, loss p.1 p.2 i ω) / sampleSize|}) ≤
      ENNReal.ofReal δ_real :=
  finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget
    hIndep
    hMeas
    hBound
    hRisk
    hNegExpectation
    hSampleSize
    hNonemptySample
    hε_pos
    hδ_real_pos
    hR_pos
    hExists
    hRange
    hClosedFormSampleSize

/--
Finite-prefix finite-class Hoeffding deviation bound with the sample
denominator written directly as `(s.card : ℝ)`.

This is the most route-facing version of the current finite-prefix theorem: it
removes the separate `sampleSize` parameter from the statement while preserving
the same checked closed-form sample-size condition.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ} {R : ℝ≥0}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hR_pos : 0 < (R : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ R)
    (hClosedFormSampleSize :
      (((R : ℝ) ^ (2 : ℕ)) / (2 * ε ^ (2 : ℕ))) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) ≤ (s.card : ℝ)) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  simpa using
    finitePrefixFiniteClassDeviationFromHoeffding_closedForm
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := (s.card : ℝ))
      (risk := risk)
      (R := R)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      rfl
      hNonemptySample
      hε_pos
      hδ_real_pos
      hR_pos
      hExists
      hRange
      hClosedFormSampleSize

/--
Finite-prefix finite-class Hoeffding deviation bound for unit-range losses.

This specializes the route-facing card-sample theorem to the common teaching
case `‖b - a‖₊ ≤ 1`, exposing the sample-size condition without a separate
range parameter.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_closedForm_unitRange
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ (1 : ℝ≥0))
    (hClosedFormSampleSize :
      Real.log
          (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
            δ_real) /
          (2 * ε ^ (2 : ℕ)) ≤ (s.card : ℝ)) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  have hClosedFormSampleSize' :
      (((1 : ℝ≥0) : ℝ) ^ (2 : ℕ) / (2 * ε ^ (2 : ℕ))) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) ≤ (s.card : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hClosedFormSampleSize
  exact
    finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (risk := risk)
      (R := (1 : ℝ≥0))
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hNonemptySample
      hε_pos
      hδ_real_pos
      (by norm_num)
      hExists
      hRange
      hClosedFormSampleSize'

/--
Finite-prefix finite-class Hoeffding deviation bound in unit-range
confidence-radius form.

This is the route-facing radius presentation of the current finite-prefix
chain: the caller supplies the displayed closed-form radius bound, and the
conclusion is the simultaneous finite-horizon, finite-class deviation event.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {ε δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hε_pos : 0 < ε)
    (hδ_real_pos : 0 < δ_real)
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ (1 : ℝ≥0))
    (hClosedFormRadius :
      √(Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) /
          (2 * (s.card : ℝ))) ≤ ε) :
    μ (⋃ p : Fin T × H,
        {ω |
          ε ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  have hClosedFormRadius' :
      √(((1 : ℝ≥0) : ℝ) ^ (2 : ℕ) / (2 * (s.card : ℝ)) *
          Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real)) ≤ ε := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hClosedFormRadius
  simpa using
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (sampleSize := (s.card : ℝ))
      (risk := risk)
      (R := (1 : ℝ≥0))
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      rfl
      hNonemptySample
      hε_pos
      hδ_real_pos
      (by norm_num)
      hExists
      hRange
      hClosedFormRadius'

/--
Finite-prefix finite-class Hoeffding deviation bound with the unit-range
confidence radius written directly in the event.

This removes the caller-supplied deviation threshold from the route-facing
statement. The only extra side condition is positivity of the displayed radius,
needed by the underlying Hoeffding wrapper.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real)
    (hRadius_pos :
      0 <
        √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ (1 : ℝ≥0)) :
    μ (⋃ p : Fin T × H,
        {ω |
          √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  exact
    finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (risk := risk)
      (ε :=
        √(Real.log
            (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
              δ_real) /
          (2 * (s.card : ℝ))))
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hNonemptySample
      hRadius_pos
      hδ_real_pos
      hExists
      hRange
      le_rfl

/--
Explicit-radius finite-prefix finite-class Hoeffding bound with the radius
positivity discharged from a strict confidence-budget condition.

The new assumption `δ_real < 2^(T+1) * card(H)` is exactly what makes the
closed-form log term positive. The proof is otherwise only an algebra wrapper
around `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius`.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {a b : Fin T → H → ι → ℝ}
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (a t h i) (b t h i))
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNegExpectation :
      ∀ t h i, i ∈ s → μ[fun ω => -loss t h i ω] = - μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real)
    (hδ_real_lt :
      δ_real < (2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ))
    (hExists : ∀ t h, ∃ i, i ∈ s ∧ 0 < ‖b t h i - a t h i‖₊)
    (hRange : ∀ t h i, i ∈ s → ‖b t h i - a t h i‖₊ ≤ (1 : ℝ≥0)) :
    μ (⋃ p : Fin T × H,
        {ω |
          √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  have hSampleCard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hNonemptySample
  have hDenom_pos : 0 < 2 * (s.card : ℝ) := by
    positivity
  have hRatio_gt_one :
      1 <
        ((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) / δ_real := by
    calc
      1 = δ_real / δ_real := by
        field_simp [ne_of_gt hδ_real_pos]
      _ < ((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) / δ_real :=
        div_lt_div_of_pos_right hδ_real_lt hδ_real_pos
  have hLog_pos :
      0 <
        Real.log (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
          δ_real) :=
    Real.log_pos hRatio_gt_one
  have hRadius_pos :
      0 <
        √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) := by
    exact Real.sqrt_pos.2 (div_pos hLog_pos hDenom_pos)
  exact
    finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius
      (μ := μ)
      (loss := loss)
      (a := a)
      (b := b)
      (s := s)
      (risk := risk)
      hIndep
      hMeas
      hBound
      hRisk
      hNegExpectation
      hNonemptySample
      hδ_real_pos
      hRadius_pos
      hExists
      hRange

/--
Explicit-radius finite-prefix finite-class Hoeffding bound for losses bounded
in `[0,1]`.

This is the first route-facing bounded-loss surface: callers provide a direct
`loss ∈ [0,1]` almost-everywhere assumption instead of separate lower and upper
range functions. The negative-integral identity used by the two-sided Hoeffding
step is discharged internally by `integral_neg`.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real)
    (hδ_real_lt :
      δ_real < (2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) :
    μ (⋃ p : Fin T × H,
        {ω |
          √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  have hExists :
      ∀ (_t : Fin T) (_h : H),
        ∃ i, i ∈ s ∧ 0 < ‖(1 : ℝ) - 0‖₊ := by
    intro _t _h
    rcases Finset.card_pos.mp hNonemptySample with ⟨i, hi⟩
    refine ⟨i, hi, ?_⟩
    norm_num
  have hRange :
      ∀ (_t : Fin T) (_h : H) (_i : ι), _i ∈ s →
        ‖(1 : ℝ) - 0‖₊ ≤ (1 : ℝ≥0) := by
    intro _t _h _i _hi
    norm_num
  exact
    finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample
      (μ := μ)
      (loss := loss)
      (a := fun _t _h _i => (0 : ℝ))
      (b := fun _t _h _i => (1 : ℝ))
      (s := s)
      (risk := risk)
      hIndep
      hMeas
      hBound01
      hRisk
      (by
        intro _t _h _i _hi
        rw [integral_neg])
      hNonemptySample
      hδ_real_pos
      hδ_real_lt
      hExists
      hRange

/--
Explicit time-varying dyadic-radius finite-prefix finite-class Hoeffding bound
for losses bounded in `[0,1]`.

This is the finite-prefix surface needed before an anytime lift: instead of
using one horizon-uniform confidence radius, the event at time `t` uses the
actual dyadic budget `δ * 2^(-1-t) / card(H)`.

The pointwise tail at this radius is supplied as an input. The theorem proves
the finite-prefix union step and the `ofReal` dyadic-budget conversion.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H] {s : Finset ι}
    {loss : Fin T → H → ι → Ω → ℝ}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hδ_real_pos : 0 < δ_real)
    (hPointwiseTail :
      ∀ t h,
        μ {ω |
          Real.sqrt
            ((Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                  (Fintype.card H : ℝ))) /
              (2 * (s.card : ℝ))) ≤
            |risk t h / (s.card : ℝ) -
              (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)|}
          ≤ ENNReal.ofReal
            (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
              (Fintype.card H : ℝ))) :
    μ (⋃ p : Fin T × H,
        {ω |
          Real.sqrt
            ((Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (p.1.val : ℤ)) /
                  (Fintype.card H : ℝ))) /
              (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  let threshold : Fin T → H → ℝ := fun t _h =>
    Real.sqrt
      ((Real.log 2 -
        Real.log
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ))) /
        (2 * (s.card : ℝ)))
  let deviation : Fin T → H → Ω → ℝ := fun t h ω =>
    risk t h / (s.card : ℝ) -
      (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)
  change
    μ (⋃ p : Fin T × H,
        {ω | threshold p.1 p.2 ≤ |deviation p.1 p.2 ω|}) ≤
      ENNReal.ofReal δ_real
  refine
    finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold
      (μ := μ)
      (deviation := deviation)
      (threshold := threshold)
      (δ := ENNReal.ofReal δ_real)
      ?_
  intro t h
  calc
    μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ ENNReal.ofReal
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ)) := by
            simpa [threshold, deviation] using hPointwiseTail t h
    _ = finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t.val *
          (Fintype.card H : ℝ≥0∞)⁻¹ :=
            finiteDyadicRealBudget_classBudget_ofReal
              (H := H)
              hδ_real_pos
              t.val

/--
Explicit time-varying dyadic-radius finite-prefix finite-class Hoeffding bound
for losses bounded in `[0,1]`.

This discharges the pointwise tail assumption in
`finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius`
from the fixed-hypothesis Hoeffding wrappers, using the displayed per-time
dyadic radius directly.
-/
theorem finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real) :
    μ (⋃ p : Fin T × H,
        {ω |
          Real.sqrt
            ((Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (p.1.val : ℤ)) /
                  (Fintype.card H : ℝ))) /
              (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  let threshold : Fin T → H → ℝ := fun t _h =>
    Real.sqrt
      ((Real.log 2 -
        Real.log
          (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
            (Fintype.card H : ℝ))) /
        (2 * (s.card : ℝ)))
  have hSampleSize_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hNonemptySample
  have hExists :
      ∀ (_t : Fin T) (_h : H),
        ∃ i, i ∈ s ∧ 0 < ‖(1 : ℝ) - 0‖₊ := by
    intro _t _h
    rcases Finset.card_pos.mp hNonemptySample with ⟨i, hi⟩
    exact ⟨i, hi, by norm_num⟩
  have hRange :
      ∀ (_t : Fin T) (_h : H) (_i : ι), _i ∈ s →
        ‖(1 : ℝ) - 0‖₊ ≤ (1 : ℝ≥0) := by
    intro _t _h _i _hi
    norm_num
  change
    μ (⋃ p : Fin T × H,
        {ω |
          threshold p.1 p.2 ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real
  exact
    finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_threshold
      (μ := μ)
      (loss := loss)
      (a := fun _t _h _i => (0 : ℝ))
      (b := fun _t _h _i => (1 : ℝ))
      (s := s)
      (sampleSize := (s.card : ℝ))
      (risk := risk)
      (threshold := threshold)
      (δ := ENNReal.ofReal δ_real)
      (R := (1 : ℝ≥0))
      hIndep
      hMeas
      hBound01
      hRisk
      (by
        intro _t _h _i _hi
        rw [integral_neg])
      rfl
      hNonemptySample
      (fun _t _h => Real.sqrt_nonneg _)
      (by norm_num)
      hExists
      hRange
      (fun t _h => by
        have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
        have hCard_pos : 0 < (Fintype.card H : ℝ) := by
          exact_mod_cast hCard_pos_nat
        have hRealBudget_pos :
            0 <
              δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                (Fintype.card H : ℝ) := by
          have hDyadic_pos : 0 < (2 : ℝ) ^ (-1 - (t.val : ℤ)) :=
            zpow_pos (by norm_num : (0 : ℝ) < 2) _
          exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
        calc
          empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
              (s.card : ℝ) (threshold t _h) (1 : ℝ≥0)
              ≤ ENNReal.ofReal
                (δ_real * (2 : ℝ) ^ (-1 - (t.val : ℤ)) /
                  (Fintype.card H : ℝ)) := by
                    simpa [threshold] using
                      empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_explicitRadius
                        hSampleSize_pos
                        hRealBudget_pos
          _ = finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t.val *
                (Fintype.card H : ℝ≥0∞)⁻¹ :=
                  finiteDyadicRealBudget_classBudget_ofReal
                    (H := H)
                    hδ_real_pos
                    t.val)

/--
Anytime finite-class Hoeffding bound over all natural times for losses bounded
in `[0,1]`.

This is the countable-time version of
`finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`.
It uses the same dyadic per-time radius
`sqrt((log 2 - log(δ * 2^(-1-t) / card(H))) / (2 * card(s)))`, but the bad
event ranges over `ℕ × H` instead of a finite prefix.
-/
theorem anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype H] [Nonempty H]
    {loss : ℕ → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : ℕ → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real) :
    μ (⋃ p : ℕ × H,
        {ω |
          Real.sqrt
            ((Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (p.1 : ℤ)) /
                  (Fintype.card H : ℝ))) /
              (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real := by
  let sampleSize : ℝ := (s.card : ℝ)
  let threshold : ℕ → H → ℝ := fun t _h =>
    Real.sqrt
      ((Real.log 2 -
        Real.log
          (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
            (Fintype.card H : ℝ))) /
        (2 * sampleSize))
  let deviation : ℕ → H → Ω → ℝ := fun t h ω =>
    risk t h / sampleSize -
      (∑ i ∈ s, loss t h i ω) / sampleSize
  have hSampleSize_pos : 0 < sampleSize := by
    dsimp [sampleSize]
    exact_mod_cast hNonemptySample
  have hProxy :
      (s.card : ℝ) * ((((1 : ℝ≥0) : ℝ) / 2) ^ (2 : ℕ)) ≤
        sampleSize * ((((1 : ℝ≥0) : ℝ) / 2) ^ (2 : ℕ)) := by
    rfl
  have hExists :
      ∀ (_t : ℕ) (_h : H),
        ∃ i, i ∈ s ∧ 0 < ‖(1 : ℝ) - 0‖₊ := by
    intro _t _h
    rcases Finset.card_pos.mp hNonemptySample with ⟨i, hi⟩
    exact ⟨i, hi, by norm_num⟩
  have hRange :
      ∀ (_t : ℕ) (_h : H) (_i : ι), _i ∈ s →
        ‖(1 : ℝ) - 0‖₊ ≤ (1 : ℝ≥0) := by
    intro _t _h _i _hi
    norm_num
  change
    μ (⋃ p : ℕ × H,
        {ω | threshold p.1 p.2 ≤ |deviation p.1 p.2 ω|}) ≤
      ENNReal.ofReal δ_real
  refine
    countableTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold
      (μ := μ)
      (deviation := deviation)
      (threshold := threshold)
      (δ := ENNReal.ofReal δ_real)
      ?_
  intro t h
  have hCard_pos_nat : 0 < Fintype.card H := Fintype.card_pos
  have hCard_pos : 0 < (Fintype.card H : ℝ) := by
    exact_mod_cast hCard_pos_nat
  have hRealBudget_pos :
      0 <
        δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
          (Fintype.card H : ℝ) := by
    have hDyadic_pos : 0 < (2 : ℝ) ^ (-1 - (t : ℤ)) :=
      zpow_pos (by norm_num : (0 : ℝ) < 2) _
    exact div_pos (mul_pos hδ_real_pos hDyadic_pos) hCard_pos
  have hUpper :
      μ {ω | threshold t h ≤ deviation t h ω}
        ≤ empiricalAverageUpperHoeffdingTail
            s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
            sampleSize (threshold t h) := by
    simpa [empiricalAverageUpperHoeffdingTail, deviation, sampleSize] using
      fixedHypothesisEmpiricalAverageUpperTailFromHoeffdingENNReal
        (μ := μ)
        (loss := loss t h)
        (a := fun _i => (0 : ℝ))
        (b := fun _i => (1 : ℝ))
        (s := s)
        (n := sampleSize)
        (ε := threshold t h)
        (risk := risk t h)
        (hIndep t h)
        (hMeas t h)
        (hBound01 t h)
        (hRisk t h)
        (by
          intro _i _hi
          rw [integral_neg])
        rfl
        hNonemptySample
        (Real.sqrt_nonneg _)
  have hLower :
      μ {ω | threshold t h ≤ -deviation t h ω}
        ≤ empiricalAverageLowerHoeffdingTail
            s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
            sampleSize (threshold t h) := by
    simpa [empiricalAverageLowerHoeffdingTail, deviation, sampleSize,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      fixedHypothesisEmpiricalAverageLowerTailFromHoeffdingENNReal
        (μ := μ)
        (loss := loss t h)
        (a := fun _i => (0 : ℝ))
        (b := fun _i => (1 : ℝ))
        (s := s)
        (n := sampleSize)
        (ε := threshold t h)
        (risk := risk t h)
        (hIndep t h)
        (hMeas t h)
        (hBound01 t h)
        (hRisk t h)
        rfl
        hNonemptySample
        (Real.sqrt_nonneg _)
  have hTwoSided :
      μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ empiricalAverageTwoSidedHoeffdingTail
            s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
            sampleSize (threshold t h) := by
    calc
      μ {ω | threshold t h ≤ |deviation t h ω|}
          ≤ empiricalAverageUpperHoeffdingTail
                s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
                sampleSize (threshold t h)
              + empiricalAverageLowerHoeffdingTail
                s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
                sampleSize (threshold t h) :=
            twoSidedDeviationTailFromOneSidedTails
              (deviation t h)
              hUpper
              hLower
      _ = empiricalAverageTwoSidedHoeffdingTail
            s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
            sampleSize (threshold t h) := by
            rw [empiricalAverageUpperHoeffdingTail_eq_lower]
            simp [empiricalAverageTwoSidedHoeffdingTail, two_mul]
  have hUniformRange :
      empiricalAverageTwoSidedHoeffdingTail
          s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
          sampleSize (threshold t h)
        ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
            sampleSize (threshold t h)
            (sampleSize * ((((1 : ℝ≥0) : ℝ) / 2) ^ (2 : ℕ))) :=
    empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound_of_exists_range_pos
      s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
      (R := (1 : ℝ≥0)) (hExists t h) (hRange t h) hProxy
  have hSampleTail :
      empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize (threshold t h)
          (sampleSize * ((((1 : ℝ≥0) : ℝ) / 2) ^ (2 : ℕ)))
        =
        empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
          sampleSize (threshold t h) (1 : ℝ≥0) :=
    empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail
      hSampleSize_pos
      (by norm_num)
  calc
    μ {ω | threshold t h ≤ |deviation t h ω|}
        ≤ empiricalAverageTwoSidedHoeffdingTail
            s (fun _i => (0 : ℝ)) (fun _i => (1 : ℝ))
            sampleSize (threshold t h) := hTwoSided
    _ ≤ empiricalAverageUniformRangeTwoSidedHoeffdingTail
          sampleSize (threshold t h)
          (sampleSize * ((((1 : ℝ≥0) : ℝ) / 2) ^ (2 : ℕ))) := hUniformRange
    _ = empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail
          sampleSize (threshold t h) (1 : ℝ≥0) := hSampleTail
    _ ≤ ENNReal.ofReal
          (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
            (Fintype.card H : ℝ)) := by
            simpa [threshold, sampleSize] using
              empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_explicitRadius
                hSampleSize_pos
                hRealBudget_pos
    _ = finiteDyadicTimeBudget (ENNReal.ofReal δ_real) t *
          (Fintype.card H : ℝ≥0∞)⁻¹ :=
            finiteDyadicRealBudget_classBudget_ofReal
              (H := H)
              hδ_real_pos
              t

/--
Existential-event version of the anytime finite-class Hoeffding bound.

This is the route-facing form of
`anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding`:
instead of exposing a raw indexed union, it states that the probability of
there existing some natural time and hypothesis with a dyadic-radius deviation
is at most `δ`.
-/
theorem anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype H] [Nonempty H]
    {loss : ℕ → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : ℕ → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real) :
    μ {ω |
        ∃ t : ℕ, ∃ h : H,
          Real.sqrt
            ((Real.log 2 -
              Real.log
                (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
                  (Fintype.card H : ℝ))) /
              (2 * (s.card : ℝ))) ≤
            |risk t h / (s.card : ℝ) -
              (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)|} ≤
      ENNReal.ofReal δ_real := by
  let event : ℕ → H → Set Ω := fun t h =>
    {ω |
      Real.sqrt
        ((Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
              (Fintype.card H : ℝ))) /
          (2 * (s.card : ℝ))) ≤
        |risk t h / (s.card : ℝ) -
          (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)|}
  have hUnion :
      μ (⋃ p : ℕ × H, event p.1 p.2) ≤ ENNReal.ofReal δ_real := by
    simpa [event] using
      anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding
        (μ := μ)
        (loss := loss)
        hIndep
        (s := s)
        (risk := risk)
        (δ_real := δ_real)
        hMeas
        hBound01
        hRisk
        hNonemptySample
        hδ_real_pos
  change μ {ω | ∃ t : ℕ, ∃ h : H, ω ∈ event t h} ≤ ENNReal.ofReal δ_real
  rw [← countableTimeClass_iUnion_eq_exists event]
  exact hUnion

/--
Named-radius existential-event version of the anytime finite-class Hoeffding
bound.

This is definitionally the same probability statement as
`anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding`,
but the displayed radius is factored into
`zeroOneDyadicFiniteClassConfidenceRadius`.
-/
theorem anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype H] [Nonempty H]
    {loss : ℕ → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : ℕ → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real) :
    μ {ω |
        ∃ t : ℕ, ∃ h : H,
          zeroOneDyadicFiniteClassConfidenceRadius
              (H := H) (s.card : ℝ) δ_real t ≤
            |risk t h / (s.card : ℝ) -
              (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)|} ≤
      ENNReal.ofReal δ_real := by
  simpa [zeroOneDyadicFiniteClassConfidenceRadius] using
    anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding
      (μ := μ)
      (loss := loss)
      hIndep
      (s := s)
      (risk := risk)
      (δ_real := δ_real)
      hMeas
      hBound01
      hRisk
      hNonemptySample
      hδ_real_pos

/--
Failure event for the `[0,1]` finite-class dyadic confidence sequence.

This names the event used by
`anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding`.
-/
def finiteClassConfidenceSequenceFailureEvent
    {Ω ι H : Type*} [Fintype H]
    (loss : ℕ → H → ι → Ω → ℝ) (s : Finset ι)
    (risk : ℕ → H → ℝ) (δ_real : ℝ) : Set Ω :=
  {ω |
    ¬ ∀ t : ℕ, ∀ h : H,
      |risk t h / (s.card : ℝ) -
        (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)| <
        zeroOneDyadicFiniteClassConfidenceRadius
          (H := H) (s.card : ℝ) δ_real t}

/--
Bundled assumptions for the `[0,1]` finite-class dyadic confidence sequence.

The structure packages the independence, measurability, range, risk, sample-size,
and confidence-level hypotheses used by the countable-time Hoeffding wrapper.
-/
structure FiniteClassConfidenceSequence
    (Ω ι H : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [Fintype H] [Nonempty H]
    (loss : ℕ → H → ι → Ω → ℝ) (s : Finset ι)
    (risk : ℕ → H → ℝ) (δ_real : ℝ) : Prop where
  indep : ∀ t h, iIndepFun (loss t h) μ
  measurable : ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ
  bounded01 :
    ∀ t h i, i ∈ s →
      ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1
  risk_eq : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i]
  nonempty_sample : 0 < s.card
  delta_pos : 0 < δ_real

/--
Confidence-sequence form of the anytime finite-class Hoeffding theorem.

The event is phrased as failure of the simultaneous statement: for every
natural time and every hypothesis, the empirical-average deviation stays
strictly below the named dyadic radius. Its failure probability is bounded by
`δ`.
-/
theorem anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype H] [Nonempty H]
    {loss : ℕ → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : ℕ → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real) :
    μ {ω |
        ¬ ∀ t : ℕ, ∀ h : H,
          |risk t h / (s.card : ℝ) -
            (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)| <
            zeroOneDyadicFiniteClassConfidenceRadius
              (H := H) (s.card : ℝ) δ_real t} ≤
      ENNReal.ofReal δ_real := by
  let deviation : ℕ → H → Ω → ℝ := fun t h ω =>
    risk t h / (s.card : ℝ) -
      (∑ i ∈ s, loss t h i ω) / (s.card : ℝ)
  let threshold : ℕ → H → ℝ := fun t _h =>
    zeroOneDyadicFiniteClassConfidenceRadius (H := H) (s.card : ℝ) δ_real t
  have hCrossing :
      μ {ω | ∃ t : ℕ, ∃ h : H, threshold t h ≤ |deviation t h ω|} ≤
        ENNReal.ofReal δ_real := by
    simpa [threshold, deviation] using
      anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding
        (μ := μ)
        (loss := loss)
        hIndep
        (s := s)
        (risk := risk)
        (δ_real := δ_real)
        hMeas
        hBound01
        hRisk
        hNonemptySample
        hδ_real_pos
  change
    μ {ω | ¬ ∀ t : ℕ, ∀ h : H, |deviation t h ω| < threshold t h} ≤
      ENNReal.ofReal δ_real
  rw [countableTimeClass_not_forall_lt_eq_exists_ge deviation threshold]
  exact hCrossing

/--
Bundled API for the `[0,1]` finite-class dyadic confidence sequence.

Supplying a `FiniteClassConfidenceSequence` object gives the probability bound
for the named failure event without restating the full theorem signature.
-/
theorem FiniteClassConfidenceSequence.failure_probability_le
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype H] [Nonempty H]
    {loss : ℕ → H → ι → Ω → ℝ}
    {s : Finset ι}
    {risk : ℕ → H → ℝ} {δ_real : ℝ}
    (cfg : FiniteClassConfidenceSequence Ω ι H μ loss s risk δ_real) :
    μ (finiteClassConfidenceSequenceFailureEvent loss s risk δ_real) ≤
      ENNReal.ofReal δ_real := by
  simpa [finiteClassConfidenceSequenceFailureEvent] using
    anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding
      (μ := μ)
      (loss := loss)
      cfg.indep
      (s := s)
      (risk := risk)
      (δ_real := δ_real)
      cfg.measurable
      cfg.bounded01
      cfg.risk_eq
      cfg.nonempty_sample
      cfg.delta_pos

/--
Sample-size inversion for the displayed dyadic confidence radius.

If the sample size clears the usual
`(log 2 - log budget) / (2 * ε^2)` lower bound at time `t`, then the named
dyadic radius used in the confidence-sequence theorem is at most `ε`.
-/
theorem zeroOneDyadicFiniteClassConfidenceRadius_le_of_sampleSize_ge
    {H : Type*} [Fintype H] [Nonempty H]
    {sampleSize ε δ_real : ℝ} {t : ℕ}
    (hSampleSize_pos : 0 < sampleSize)
    (hε_pos : 0 < ε)
    (hSampleSize_ge :
      (Real.log 2 -
          Real.log
            (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
              (Fintype.card H : ℝ))) /
          (2 * ε ^ (2 : ℕ)) ≤ sampleSize) :
    zeroOneDyadicFiniteClassConfidenceRadius (H := H) sampleSize δ_real t ≤ ε := by
  unfold zeroOneDyadicFiniteClassConfidenceRadius
  rw [Real.sqrt_le_iff]
  constructor
  · exact hε_pos.le
  let logBudget : ℝ :=
    Real.log 2 -
      Real.log
        (δ_real * (2 : ℝ) ^ (-1 - (t : ℤ)) /
          (Fintype.card H : ℝ))
  have hε_sq_pos : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε_pos
  have hden_eps_pos : 0 < 2 * ε ^ (2 : ℕ) :=
    mul_pos (by norm_num : (0 : ℝ) < 2) hε_sq_pos
  have hden_sample_pos : 0 < 2 * sampleSize :=
    mul_pos (by norm_num : (0 : ℝ) < 2) hSampleSize_pos
  change logBudget / (2 * sampleSize) ≤ ε ^ (2 : ℕ)
  by_cases hLogBudget_nonpos : logBudget ≤ 0
  · have hInside_nonpos : logBudget / (2 * sampleSize) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hLogBudget_nonpos hden_sample_pos.le
    exact hInside_nonpos.trans (sq_nonneg ε)
  · have hLogBudget_pos : 0 < logBudget := lt_of_not_ge hLogBudget_nonpos
    have hLog_le_sample : logBudget ≤ sampleSize * (2 * ε ^ (2 : ℕ)) := by
      rw [div_le_iff₀ hden_eps_pos] at hSampleSize_ge
      simpa [logBudget, mul_comm, mul_left_comm, mul_assoc] using hSampleSize_ge
    rw [div_le_iff₀ hden_sample_pos]
    nlinarith

end

end FormalSLT.UniformConvergence
