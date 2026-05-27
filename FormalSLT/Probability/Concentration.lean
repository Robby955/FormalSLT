import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace FormalSLT.Probability.Concentration

noncomputable section

universe u

/-
These are finite statement/proof seeds, not verified page theorems.

They deliberately use finite weighted supports rather than the full
measure-theoretic random-variable setting from the topic page. This keeps an
initial Lean artifact small enough to audit while preserving the mathematical
shape that later proofs should refine.
-/

def weightedMean {ι : Type*} (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * x i

def upperTailMass {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ (s.filter fun i => t ≤ x i), w i

def centeredSecondMoment {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (μ : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (x i - μ) ^ 2

def twoSidedTailMass {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (μ t : ℝ) : ℝ :=
  ∑ i ∈ (s.filter fun i => t ≤ |x i - μ|), w i

/--
Markov's inequality, real-valued integrable form.

This is a claim-facing wrapper around mathlib's
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, divided by the positive
threshold. It matches the topic theorem after making the integrability
assumption explicit.
-/
theorem markovInequalityRealIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}
    (hNonneg : 0 ≤ᵐ[μ] X) (hIntegrable : Integrable X μ) (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂μ) / t := by
  exact (le_div_iff₀ ht).mpr
    (by
      simpa [mul_comm] using
        (MeasureTheory.mul_meas_ge_le_integral_of_nonneg hNonneg hIntegrable t))

/--
Chebyshev's inequality, variance form.

This is a claim-facing wrapper around mathlib's
`ProbabilityTheory.meas_ge_le_variance_div_sq`.
-/
theorem chebyshevInequalityVariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {t : ℝ} (hX : MemLp X 2 μ) (ht : 0 < t) :
    μ {ω | t ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / t ^ 2) :=
  ProbabilityTheory.meas_ge_le_variance_div_sq hX ht

/--
Finite-sum tail bound for independent sub-Gaussian random variables.

This is the exact mathlib-backed concentration theorem that sits immediately
above the finite-class union-bound pattern used in learning theory.
-/
theorem subGaussianFiniteSumTailBound
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (hIndep : iIndepFun X μ) {c : ι → ℝ≥0}
    {s : Finset ι} (hSubG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep hSubG hε

/--
Finite linear combinations of independent sub-Gaussian-MGF variables remain
sub-Gaussian in the MGF-parameter sense.

This is a scoped bridge for the public psi₂-norm closure theorem: mathlib's
formal vocabulary is the MGF parameter `c`, so the theorem proves the finite
MGF closure statement without claiming the Orlicz-norm equivalence constants.
-/
theorem subGaussianIndependentFiniteLinearCombinationMGF
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (hIndep : iIndepFun X μ)
    {c : ι → ℝ≥0} {a : ι → ℝ} {s : Finset ι}
    (hSubG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω)
      (∑ i ∈ s, (.mk ((a i) ^ 2) (sq_nonneg (a i)) : ℝ≥0) * c i) μ := by
  have hScaledIndep :
      iIndepFun (fun i ω => a i * X i ω) μ := by
    simpa [Function.comp_def] using
      hIndep.comp (fun i x => a i * x)
        (fun _ => measurable_const.mul measurable_id)
  exact HasSubgaussianMGF.sum_of_iIndepFun hScaledIndep
    (fun i hi => (hSubG i hi).const_mul (a i))

/--
Azuma-Hoeffding-style one-sided concentration for a finite martingale
difference sum under conditional sub-Gaussian MGF assumptions.

This is a scoped bridge for the public bounded-increment Azuma-Hoeffding
claims. Mathlib's theorem is stated in the stronger formal vocabulary of
conditional sub-Gaussian increments, so this wrapper is not a two-sided
bounded-difference claim verification.
-/
theorem azumaHoeffdingConditionalSubGaussianTail
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (hAdapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (hSubG :
      ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  measure_sum_ge_le_of_hasCondSubgaussianMGF hAdapted h0 n hSubG hε

/--
Right-tail Chernoff bound from the sub-Gaussian MGF condition.

This is the claim-facing wrapper for the basic MGF-implies-tail theorem in
the Sub-Gaussian page. The centering assumption in the prose theorem is
stronger than this implication needs; the MGF condition is the load-bearing
formal hypothesis.
-/
theorem subGaussianMGFImpliesRightTailBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {σ : ℝ≥0} {t : ℝ}
    (hSubG : HasSubgaussianMGF X (σ ^ 2) μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ Real.exp (-t ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
  simpa [NNReal.coe_pow] using hSubG.measure_ge_le ht

/--
Hoeffding's lemma for a bounded centered real random variable.

This wraps mathlib's sub-Gaussian MGF form directly. The public claim remains
claim-level only: the wrapper verifies the exact theorem statement, not the
whole Sub-Gaussian page.
-/
theorem hoeffdingLemmaBoundedCenteredSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hMeas : AEMeasurable X μ)
    (hBound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hCentered : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hMeas hBound hCentered

/--
One-sided Hoeffding bound for a finite independent family of bounded variables.

This composes mathlib's bounded-variable Hoeffding lemma with its finite
sub-Gaussian sum tail theorem. Average and two-sided textbook displays should
remain separate governed claims unless their exact statements are wrapped too.
-/
theorem hoeffdingBoundedFiniteSumTail
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hIndep : iIndepFun X μ)
    {a b : ι → ℝ} {s : Finset ι}
    (hMeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, (X i ω - μ[X i])}
      ≤ Real.exp
          (-ε ^ 2 / (2 * (↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ (2 : ℕ))) : ℝ))) := by
  have hCenteredIndep :
      iIndepFun (fun i ω => X i ω - μ[X i]) μ := by
    simpa [Function.comp_def] using
      hIndep.comp (fun i x => x - μ[X i])
        (fun _ => measurable_id.sub measurable_const)
  have hSubG :
      ∀ i ∈ s,
        HasSubgaussianMGF (fun ω => X i ω - μ[X i])
          ((‖b i - a i‖₊ / 2) ^ 2) μ := by
    intro i hi
    exact hasSubgaussianMGF_of_mem_Icc (hMeas i hi) (hBound i hi)
  exact HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hCenteredIndep hSubG hε

/--
Finite-support Markov inequality statement seed.

Scope note: this is a finite weighted specialization. It is a formal
stepping stone for the page claim, not the full measure-theoretic theorem.
-/
def markovInequalityFiniteWeightedStatement : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (w x : ι → ℝ) (t : ℝ),
    (∀ i, 0 ≤ w i) →
    (∀ i, 0 ≤ x i) →
    0 < t →
    upperTailMass s w x t ≤ weightedMean s w x / t

/--
Finite-support Chebyshev inequality statement seed.

Scope note: this is a finite weighted specialization. It is a formal
stepping stone for the page claim, not the full measure-theoretic theorem.
-/
def chebyshevInequalityFiniteWeightedStatement : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (w x : ι → ℝ) (μ σ2 t : ℝ),
    (∀ i, 0 ≤ w i) →
    σ2 = centeredSecondMoment s w x μ →
    0 < t →
    twoSidedTailMass s w x μ t ≤ σ2 / t ^ 2

/-- Canonical Lean declaration for the finite-support Markov statement seed. -/
def markovInequalityFiniteWeighted : Prop :=
  markovInequalityFiniteWeightedStatement.{0}

/-- Canonical Lean declaration for the finite-support Chebyshev statement seed. -/
def chebyshevInequalityFiniteWeighted : Prop :=
  chebyshevInequalityFiniteWeightedStatement.{0}

/--
Proof of the finite-support Markov statement seed.

This proves only the finite weighted specialization above; it is not the full
measure-theoretic page theorem.
-/
theorem markovInequalityFiniteWeighted_proof :
    markovInequalityFiniteWeightedStatement.{u} := by
  intro ι s w x t hw hx ht
  unfold upperTailMass weightedMean
  calc
    (∑ i ∈ s.filter fun i => t ≤ x i, w i)
        ≤ ∑ i ∈ s.filter fun i => t ≤ x i, (w i * x i) / t := by
          apply Finset.sum_le_sum
          intro i hi
          have hTail : t ≤ x i := (Finset.mem_filter.mp hi).2
          have hScaled : w i * t ≤ w i * x i :=
            mul_le_mul_of_nonneg_left hTail (hw i)
          exact (le_div_iff₀ ht).mpr hScaled
    _ ≤ ∑ i ∈ s, (w i * x i) / t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact (Finset.mem_filter.mp hi).1
          · intro i _ _
            exact div_nonneg (mul_nonneg (hw i) (hx i)) (le_of_lt ht)
    _ = (∑ i ∈ s, w i * x i) / t := by
          rw [Finset.sum_div]

/--
Proof of the finite-support Chebyshev statement seed.

This proves only the finite weighted specialization above; it is not the full
measure-theoretic page theorem.
-/
theorem chebyshevInequalityFiniteWeighted_proof :
    chebyshevInequalityFiniteWeightedStatement.{u} := by
  intro ι s w x μ σ2 t hw hσ2 ht
  unfold twoSidedTailMass
  calc
    (∑ i ∈ s.filter fun i => t ≤ |x i - μ|, w i)
        ≤ ∑ i ∈ s.filter fun i => t ≤ |x i - μ|, (w i * (x i - μ) ^ 2) / t ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hTail : t ≤ |x i - μ| := (Finset.mem_filter.mp hi).2
          have htNonneg : 0 ≤ t := le_of_lt ht
          have hSq : t ^ 2 ≤ (x i - μ) ^ 2 := by
            nlinarith [
              sq_nonneg (x i - μ),
              abs_nonneg (x i - μ),
              abs_mul_abs_self (x i - μ),
              hTail,
              htNonneg
            ]
          have hScaled : w i * t ^ 2 ≤ w i * (x i - μ) ^ 2 :=
            mul_le_mul_of_nonneg_left hSq (hw i)
          have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
          exact (le_div_iff₀ htSq).mpr hScaled
    _ ≤ ∑ i ∈ s, (w i * (x i - μ) ^ 2) / t ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact (Finset.mem_filter.mp hi).1
          · intro i _ _
            have htSqNonneg : 0 ≤ t ^ 2 := sq_nonneg t
            exact div_nonneg (mul_nonneg (hw i) (sq_nonneg (x i - μ))) htSqNonneg
    _ = σ2 / t ^ 2 := by
          rw [hσ2]
          unfold centeredSecondMoment
          rw [Finset.sum_div]

end

end FormalSLT.Probability.Concentration
