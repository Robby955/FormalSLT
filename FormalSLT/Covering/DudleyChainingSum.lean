import Mathlib.Tactic.Linarith
import FormalSLT.Covering.FiniteSubGaussianChaining
import FormalSLT.Probability.SubGaussianFiniteMax

/-!
# Finite Dudley chaining sum

This module records the finite n-step chaining sum used by the Dudley
bridge. It keeps the statement finite: finite outcome space, finite index
class, finite nets, and a finite scale range.

The level bound uses the one-sided finite sub-Gaussian maximum inequality
from `FormalSLT.Probability.SubGaussianFiniteMax`.
-/

namespace FormalSLT.Covering.DudleyChainingSum

open Finset
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Probability.SubGaussianFiniteMax

noncomputable section

variable {Ω T : Type*}

/-- Exact telescoping identity for a chain of finite-net projections. -/
theorem dudley_chaining_telescope
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (X : T → ℝ) (m : ℕ) (t t₀ : T)
    (hroot : (N 0).projection t = t₀)
    (hlast : (N m).projection t = t) :
    X t - X t₀ =
      ∑ j ∈ Finset.range m,
        (X ((N (j + 1)).projection t) - X ((N j).projection t)) := by
  let π : ℕ → T → T := fun j => (N j).projection
  have ht :
      X t =
        X t₀ + ∑ j ∈ Finset.range m,
          (X ((N (j + 1)).projection t) - X ((N j).projection t)) := by
    simpa [π, hroot] using
      chain_telescope X π m t (by simpa [π] using hlast)
  rw [ht]
  ring

private lemma sqrt_variance_radius_sq
    (variance radius : ℝ) (hvariance : 0 ≤ variance) :
    (Real.sqrt variance * radius) ^ 2 = variance * radius ^ 2 := by
  rw [mul_pow, Real.sq_sqrt hvariance]

private lemma level_constant_rewrite
    (variance radius entropy : ℝ) :
    Real.sqrt variance * radius * Real.sqrt (2 * entropy) =
      Real.sqrt (2 * variance) * radius * Real.sqrt entropy := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/--
One finite-net level of the Dudley chain. The proof applies q085 to the
realized projection-pair family, then replaces pair entropy by the product of
the two covering numbers.
-/
theorem dudley_level_increment_max_bound
    [Fintype Ω] [Fintype T] [Nonempty T]
    {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteSubGaussianProcess Ω T)
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B)
    (hdist₀ : N₀.dist = P.dist)
    (hdist₁ : N₁.dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : 0 < N₀.radius + N₁.radius)
    (hcenter : ∀ pair : FiniteNet.ProjectionPair N₀ N₁,
      finiteExpectation P.weight
        (fun ω => P.X ω (N₁.center pair.1.2) - P.X ω (N₀.center pair.1.1)) = 0) :
    finiteExpectation P.weight
      (fun ω => finiteSup
        (fun t : T => P.X ω (N₁.projection t) - P.X ω (N₀.projection t))) ≤
      Real.sqrt (2 * P.varianceProxy) * (N₀.radius + N₁.radius) *
        Real.sqrt (Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) := by
  classical
  let Pair := FiniteNet.ProjectionPair N₀ N₁
  let left : Pair → T := fun pair => N₀.center pair.1.1
  let right : Pair → T := fun pair => N₁.center pair.1.2
  let radius : ℝ := N₀.radius + N₁.radius
  let sigma : ℝ := Real.sqrt P.varianceProxy * radius
  let pairProcess : Pair → Ω → ℝ := fun pair ω => P.X ω (right pair) - P.X ω (left pair)
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma, radius]
    exact mul_pos (Real.sqrt_pos_of_pos hvariance) hradius_pos
  have hpair_bound :
      finiteExpectation P.weight
          (fun ω => finiteSup (fun pair : Pair => pairProcess pair ω)) ≤
        sigma * Real.sqrt (2 * Real.log (Fintype.card Pair : ℝ)) := by
    refine subgaussian_finite_max
      P.weight P.weight_nonneg P.weight_sum_one pairProcess sigma hsigma_pos ?_ ?_
    · intro pair
      simpa [pairProcess, left, right] using hcenter pair
    · intro pair lam hlam
      have hdist_pair : P.dist (left pair) (right pair) ≤ radius := by
        have hpair :=
          FiniteNet.projectionPair_dist_le_radius_sum
            N₀ N₁ (by rw [hdist₀, hdist₁])
            (by
              intro s t
              rw [hdist₀]
              exact hsymm s t)
            (by
              intro x y z
              rw [hdist₀]
              exact htri x y z)
            pair
        simpa [left, right, radius, hdist₀] using hpair
      have hsigma_sq : sigma ^ 2 = P.varianceProxy * radius ^ 2 := by
        dsimp [sigma]
        exact sqrt_variance_radius_sq P.varianceProxy radius hvariance.le
      have hmgf :=
        FiniteSubGaussianProcess.increment_mgf_le_radius
          P (left pair) (right pair) radius hdist_pair hradius_pos.le lam
      calc
        finiteExpectation P.weight
            (fun ω => Real.exp (lam * pairProcess pair ω))
            ≤ Real.exp (lam ^ 2 * P.varianceProxy * radius ^ 2 / 2) := by
              simpa [pairProcess, left, right, mul_assoc, mul_left_comm, mul_comm]
                using hmgf
        _ = Real.exp (lam ^ 2 * sigma ^ 2 / 2) := by
              rw [hsigma_sq]
              ring_nf
  have hpoint : ∀ ω : Ω,
      finiteSup
          (fun t : T => P.X ω (N₁.projection t) - P.X ω (N₀.projection t)) ≤
        finiteSup (fun pair : Pair => pairProcess pair ω) := by
    intro ω
    unfold finiteSup
    apply Finset.sup'_le
    intro t _
    have hsel :=
      Finset.le_sup'
        (s := (Finset.univ : Finset Pair))
        (fun pair : Pair => pairProcess pair ω)
        (Finset.mem_univ (FiniteNet.projectionPairOf N₀ N₁ t))
    simpa [pairProcess, left, right, FiniteNet.projection, FiniteNet.projectionPairOf]
      using hsel
  have hselected :
      finiteExpectation P.weight
          (fun ω => finiteSup
            (fun t : T => P.X ω (N₁.projection t) - P.X ω (N₀.projection t))) ≤
        finiteExpectation P.weight
          (fun ω => finiteSup (fun pair : Pair => pairProcess pair ω)) :=
    finiteExpectation_mono P.weight_nonneg hpoint
  have hcard_log :
      Real.log (Fintype.card Pair : ℝ) ≤
        Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ) :=
    FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul N₀ N₁
  have hsqrt_log :
      Real.sqrt (2 * Real.log (Fintype.card Pair : ℝ)) ≤
        Real.sqrt (2 * Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) := by
    exact Real.sqrt_le_sqrt (by nlinarith [hcard_log])
  have hpair_to_cover :
      sigma * Real.sqrt (2 * Real.log (Fintype.card Pair : ℝ)) ≤
        sigma * Real.sqrt (2 * Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt_log hsigma_pos.le
  have hrewrite :
      sigma * Real.sqrt (2 * Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) =
        Real.sqrt (2 * P.varianceProxy) * (N₀.radius + N₁.radius) *
          Real.sqrt (Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) := by
    dsimp [sigma, radius]
    exact level_constant_rewrite P.varianceProxy (N₀.radius + N₁.radius)
      (Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ))
  exact hselected.trans ((hpair_bound.trans hpair_to_cover).trans_eq hrewrite)

private theorem dudley_pointwise_sum
    [Fintype T] [Nonempty T]
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (X : T → ℝ) (m : ℕ) (t₀ : T)
    (hroot : ∀ t : T, (N 0).projection t = t₀)
    (hlast : ∀ t : T, (N m).projection t = t) :
    finiteSup (fun t : T => X t - X t₀) ≤
      ∑ j ∈ Finset.range m,
        finiteSup
          (fun t : T => X ((N (j + 1)).projection t) - X ((N j).projection t)) := by
  unfold finiteSup
  apply Finset.sup'_le
  intro t _
  rw [dudley_chaining_telescope N X m t t₀ (hroot t) (hlast t)]
  apply Finset.sum_le_sum
  intro j _
  exact Finset.le_sup'
    (s := (Finset.univ : Finset T))
    (fun u : T => X ((N (j + 1)).projection u) - X ((N j).projection u))
    (Finset.mem_univ t)

/--
Finite n-step Dudley chaining sum for centered projection increments. The
coefficient is `sqrt (2 * varianceProxy)`: q085 contributes the finite maximum
factor `sqrt 2`, while the process MGF contributes `sqrt varianceProxy`.
-/
theorem dudley_chaining_sum
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (t₀ : T)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hroot : ∀ t : T, (N 0).projection t = t₀)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcenter : ∀ j ∈ Finset.range m, ∀ pair : FiniteNet.ProjectionPair (N j) (N (j + 1)),
      finiteExpectation P.weight
        (fun ω => P.X ω ((N (j + 1)).center pair.1.2) -
          P.X ω ((N j).center pair.1.1)) = 0) :
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀)) ≤
      Real.sqrt (2 * P.varianceProxy) *
        ∑ j ∈ Finset.range m,
          ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt
              (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  let levelSup : ℕ → Ω → ℝ := fun j ω =>
    finiteSup
      (fun t : T => P.X ω ((N (j + 1)).projection t) - P.X ω ((N j).projection t))
  have hpoint : ∀ ω : Ω,
      finiteSup (fun t : T => P.X ω t - P.X ω t₀) ≤
        ∑ j ∈ Finset.range m, levelSup j ω := by
    intro ω
    simpa [levelSup] using dudley_pointwise_sum N (P.X ω) m t₀ hroot hlast
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀))
        ≤ finiteExpectation P.weight (fun ω => ∑ j ∈ Finset.range m, levelSup j ω) :=
          finiteExpectation_mono P.weight_nonneg hpoint
    _ = ∑ j ∈ Finset.range m, finiteExpectation P.weight (levelSup j) := by
          rw [finiteExpectation_sum_range]
    _ ≤ ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
              Real.sqrt
                (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [levelSup] using
            dudley_level_increment_max_bound
              P (N j) (N (j + 1)) (hdist j) (hdist (j + 1)) hsymm htri
              hvariance (hradius_pos j hj) (hcenter j hj)
    _ = Real.sqrt (2 * P.varianceProxy) *
        ∑ j ∈ Finset.range m,
          ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt
              (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring

end

end FormalSLT.Covering.DudleyChainingSum
