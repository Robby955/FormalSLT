import FormalSLT.Covering.DudleyToRademacher

open FormalSLT.Covering.DudleyToRademacher
open FormalSLT.Covering.FiniteSubGaussianChaining

/-- Instantiation of the bridge on the two-point hypothesis class `Bool`. -/
example {Z : Type*} (ℓ : Bool → Z → ℝ) {n : ℕ} (z : Fin n → Z)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet Bool (A j))
    (m : ℕ) (t₀ : Bool) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ) :=
  dudley_rademacher_complexity_bound (ι := Bool) ℓ z N m t₀ radiusScale
    coveringNumberAtRadius

#check @dudley_rademacher_complexity_bound

#check @continuous_dudley_rademacher_complexity_bound

#print axioms dudley_rademacher_complexity_bound

#print axioms continuous_dudley_rademacher_complexity_bound
