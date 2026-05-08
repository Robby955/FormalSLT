import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import FormalSLT.Rademacher.FiniteSample
import FormalSLT.Rademacher.Massart
import FormalSLT.Covering.Rademacher

/-!
# Multi-scale chaining for Rademacher complexity

Iterated application of the ε-net peeling bound
(`rademacher_covering_bound`) at two scales, yielding a discrete
analogue of Dudley's entropy integral for finite hypothesis classes.

  `R̂_S(F) ≤ ε₁ + ε₂ + R̂_S(N₂)`

Combined with Massart on the finest net:

  `R̂_S(F) ≤ ε₁ + ε₂ + B · √(2 · log|N₂| / n)`

The two-scale version suffices for most applications: choose ε₁ as a
coarse covering (few net points) and ε₂ as a fine covering (more net
points, bounded by Massart).

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Covering.DudleyChaining

open Finset
open scoped BigOperators
open FormalSLT.Rademacher.FiniteSample FormalSLT.Covering.Rademacher

variable {n : ℕ}

/-! ## Two-step chaining -/

/-- **Two-step chaining**: if F has an ε₁-cover N₁ which itself has an
ε₂-cover N₂, then `R̂_S(F) ≤ ε₁ + ε₂ + R̂_S(N₂)`.

This is the simplest form of iterated peeling — two applications of
`rademacher_covering_bound` composed. -/
theorem rademacher_two_step_chaining
    {ι₁ ι₂ ι₃ Z : Type*}
    [Fintype ι₁] [Nonempty ι₁]
    [Fintype ι₂] [Nonempty ι₂]
    [Fintype ι₃] [Nonempty ι₃]
    (ℓ₁ : ι₁ → Z → ℝ) (ℓ₂ : ι₂ → Z → ℝ) (ℓ₃ : ι₃ → Z → ℝ)
    (z : Fin n → Z)
    (π₁ : ι₁ → ι₂) (π₂ : ι₂ → ι₃)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hn : 0 < (n : ℝ))
    (hcover₁ : ∀ i : ι₁, ∀ k : Fin n, |ℓ₁ i (z k) - ℓ₂ (π₁ i) (z k)| ≤ ε₁)
    (hcover₂ : ∀ j : ι₂, ∀ k : Fin n, |ℓ₂ j (z k) - ℓ₃ (π₂ j) (z k)| ≤ ε₂) :
    empiricalRademacherComplexity ℓ₁ z ≤
    ε₁ + ε₂ + empiricalRademacherComplexity ℓ₃ z := by
  calc empiricalRademacherComplexity ℓ₁ z
      ≤ ε₁ + empiricalRademacherComplexity ℓ₂ z :=
        rademacher_covering_bound ℓ₁ ℓ₂ z π₁ ε₁ hε₁ hn hcover₁
    _ ≤ ε₁ + (ε₂ + empiricalRademacherComplexity ℓ₃ z) := by
        have := rademacher_covering_bound ℓ₂ ℓ₃ z π₂ ε₂ hε₂ hn hcover₂
        linarith
    _ = ε₁ + ε₂ + empiricalRademacherComplexity ℓ₃ z := by ring

/-! ## Two-step chaining with Massart -/

/-- **Two-step chaining + Massart**: combining two peeling steps with
Massart on the finest net gives the bound
`R̂_S(F) ≤ ε₁ + ε₂ + B · √(2 · log|N₂| / n)`.

This is the workhorse bound for most practical applications: choose ε₁
as a coarse cover (controlling the first residual) and ε₂ as a fine
cover (controlling the second residual), then Massart bounds the
Rademacher complexity of the finite finest net. -/
theorem rademacher_two_step_massart
    {ι₁ ι₂ ι₃ Z : Type*}
    [Fintype ι₁] [Nonempty ι₁]
    [Fintype ι₂] [Nonempty ι₂]
    [Fintype ι₃] [Nonempty ι₃]
    (ℓ₁ : ι₁ → Z → ℝ) (ℓ₂ : ι₂ → Z → ℝ) (ℓ₃ : ι₃ → Z → ℝ)
    (z : Fin n → Z)
    (π₁ : ι₁ → ι₂) (π₂ : ι₂ → ι₃)
    (ε₁ ε₂ B : ℝ) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hB : 0 < B)
    (hn : 0 < n) (hCard : 1 < Fintype.card ι₃)
    (hcover₁ : ∀ i : ι₁, ∀ k : Fin n, |ℓ₁ i (z k) - ℓ₂ (π₁ i) (z k)| ≤ ε₁)
    (hcover₂ : ∀ j : ι₂, ∀ k : Fin n, |ℓ₂ j (z k) - ℓ₃ (π₂ j) (z k)| ≤ ε₂)
    (hBound : ∀ j : ι₃, ∀ k : Fin n, |ℓ₃ j (z k)| ≤ B) :
    empiricalRademacherComplexity ℓ₁ z ≤
    ε₁ + ε₂ + B * Real.sqrt (2 * Real.log (Fintype.card ι₃ : ℝ) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc empiricalRademacherComplexity ℓ₁ z
      ≤ ε₁ + ε₂ + empiricalRademacherComplexity ℓ₃ z :=
        rademacher_two_step_chaining ℓ₁ ℓ₂ ℓ₃ z π₁ π₂ ε₁ ε₂ hε₁ hε₂ hn_pos
          hcover₁ hcover₂
    _ ≤ ε₁ + ε₂ + B * Real.sqrt (2 * Real.log (Fintype.card ι₃ : ℝ) / (n : ℝ)) := by
        have := FormalSLT.Rademacher.Massart.massart_finite_class hB hBound hn hCard
        linarith

end FormalSLT.Covering.DudleyChaining
