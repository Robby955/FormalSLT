import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators
open MeasureTheory

namespace FormalSLT.Probability.FiniteExpectation

noncomputable section

/-
Finite expectation seeds.

These declarations model expectation over a finite weighted support. They are
formal proof artifacts for finite-scope subclaims, not a replacement for the
measure-theoretic expectation statements on the topic page.
-/

def finiteExpectation {ι : Type} (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * x i

/--
Linearity of expectation for real-valued integrable random variables.

This is a claim-facing wrapper around mathlib's Bochner integral linearity
lemmas. It matches the topic theorem's integrability scope.
-/
theorem linearityOfExpectationIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {a b : ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ ω, (a * X ω + b * Y ω) ∂μ) =
      a * (∫ ω, X ω ∂μ) + b * (∫ ω, Y ω ∂μ) := by
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
  · exact hX.const_mul a
  · exact hY.const_mul b

/--
Finite weighted-support linearity of expectation.

Scope note: this is the finite weighted specialization of linearity. It covers
the finite-sum shape used by the assessment item, but it is not a full
measure-theoretic integrability theorem.
-/
def linearityOfFiniteExpectationStatement : Prop :=
  ∀ {ι : Type} (s : Finset ι) (w x y : ι → ℝ) (a b : ℝ),
    finiteExpectation s w (fun i => a * x i + b * y i)
      = a * finiteExpectation s w x + b * finiteExpectation s w y

/-- Canonical Lean declaration for the finite weighted-support linearity seed. -/
def linearityOfFiniteExpectation : Prop :=
  linearityOfFiniteExpectationStatement

/--
Proof of the finite weighted-support linearity seed.

This proves only the finite weighted specialization above; it is not the full
measure-theoretic expectation theorem.
-/
theorem linearityOfFiniteExpectation_proof :
    linearityOfFiniteExpectationStatement := by
  intro ι s w x y a b
  unfold finiteExpectation
  calc
    (∑ i ∈ s, w i * (a * x i + b * y i))
        = ∑ i ∈ s, (a * (w i * x i) + b * (w i * y i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (∑ i ∈ s, a * (w i * x i)) + ∑ i ∈ s, b * (w i * y i) := by
          rw [Finset.sum_add_distrib]
    _ = a * (∑ i ∈ s, w i * x i) + b * (∑ i ∈ s, w i * y i) := by
          rw [Finset.mul_sum, Finset.mul_sum]

end

end FormalSLT.Probability.FiniteExpectation
