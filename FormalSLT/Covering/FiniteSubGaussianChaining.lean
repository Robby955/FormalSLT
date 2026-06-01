import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite sub-Gaussian chaining foundations

This module starts the finite-process side of the chaining ladder. It is
finite-index throughout: finite outcome space, finite index class, finite nets,
and finite sums for expectation.

Main declarations:
* `FiniteNet`: a finite ε-net with an explicit nearest-net projection.
* `FiniteSubGaussianProcess`: a finite weighted process with an abstract
  sub-Gaussian MGF increment condition.
* `FiniteSubGaussianProcess.projection_increment_mgf`: the MGF bound along a
  chain of finite projections.
* `chain_telescope`: the multiscale telescoping identity.
* `finite_chaining_decomposition`: pointwise finite chaining by suprema.
* `finite_expectedSup_le_of_shifted_mgf`: finite-max entropy budget from
  shifted coordinate MGF bounds.
* `finite_chaining_expectation_bound`: finite weighted-expectation chaining
  once each scale increment has an expected-sup budget.
* `FiniteSubGaussianProcess.finite_dudley_entropy_sum_projection_pairs`:
  finite Dudley-style entropy sum over realized projection-pair families.
* `FiniteSubGaussianProcess.finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget`:
  finite dyadic entropy-integral budget wrapper for covering-number nets.
* `FiniteSubGaussianProcess.finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope`:
  finite covering-count wrapper with a monotone prefix-sup entropy envelope.
* `FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison`:
  projected finite-net wrapper comparing the finite dyadic budget with a
  supplied entropy-at-radius upper-sum/integral budget.
* `FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum`:
  analytic dyadic upper-sum domination by a finite shifted-annulus interval
  integral budget under antitonicity and interval-integrability assumptions.

This is not a continuous Dudley integral or a generic metric entropy theorem.
It records the finite decomposition and expectation
bookkeeping needed for later entropy estimates.
-/

namespace FormalSLT.Covering.FiniteSubGaussianChaining

open Finset
open scoped BigOperators Interval

noncomputable section

variable {Ω T A : Type*}

/-- Weighted expectation over a finite outcome space. The caller supplies the
weights and their probabilistic assumptions separately. -/
def finiteExpectation [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p ω * X ω

/-- Supremum over a finite nonempty index type. -/
def finiteSup [Fintype T] [Nonempty T] (f : T → ℝ) : ℝ :=
  (univ : Finset T).sup' univ_nonempty f

/-- A finite ε-net with an explicit nearest-net projection. `A` is the finite
type of net points, `center` realizes a net point in `T`, and `project` chooses
a nearest-net index for each target point. -/
structure FiniteNet (T A : Type*) [Fintype A] where
  dist : T → T → ℝ
  dist_nonneg : ∀ s t : T, 0 ≤ dist s t
  center : A → T
  project : T → A
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  covers : ∀ t : T, dist t (center (project t)) ≤ radius

namespace FiniteNet

/-- The nearest-net projection as a map back into the ambient index type. -/
def projection [Fintype A] (N : FiniteNet T A) : T → T :=
  fun t => N.center (N.project t)

/-- The projection selected by a finite net is within the net radius. -/
theorem projection_dist_le [Fintype A] (N : FiniteNet T A) (t : T) :
    N.dist t (N.projection t) ≤ N.radius :=
  N.covers t

/-- The cardinality of the finite net, i.e. the discrete covering number
represented by this chosen net. -/
def coveringNumber [Fintype A] (_N : FiniteNet T A) : ℕ :=
  Fintype.card A

/-- The finite set of net indices actually hit by the projection map. This is
a finite replacement for taking a supremum over an ambient index type `T`.
It is useful when `T` is not finite but a projected supremum only ranges over
the image of a finite net. -/
def ProjectedIndex [Fintype A] (N : FiniteNet T A) : Type _ :=
  {a : A // ∃ t : T, a = N.project t}

instance projectedIndexFintype [Fintype A] (N : FiniteNet T A) :
    Fintype (ProjectedIndex N) := by
  classical
  unfold ProjectedIndex
  infer_instance

instance projectedIndexNonempty [Fintype A] [Nonempty T] (N : FiniteNet T A) :
    Nonempty (ProjectedIndex N) := by
  classical
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  exact ⟨⟨N.project t, ⟨t, rfl⟩⟩⟩

namespace ProjectedIndex

/-- A chosen ambient source point whose projection realizes a projected net
index. The choice is finite-image bookkeeping only; later theorems use it to
build chains without assuming the ambient type is finite. -/
def source [Fintype A] (N : FiniteNet T A) (a : ProjectedIndex N) : T :=
  Classical.choose a.2

/-- The chosen source projects to the projected net index. -/
theorem project_source_eq [Fintype A] (N : FiniteNet T A) (a : ProjectedIndex N) :
    N.project (source N a) = a.1 := by
  exact (Classical.choose_spec a.2).symm

/-- Projecting the chosen source point gives the center indexed by the projected
net index. -/
theorem projection_source_eq_center [Fintype A] (N : FiniteNet T A)
    (a : ProjectedIndex N) :
    N.projection (source N a) = N.center a.1 := by
  simp [FiniteNet.projection, project_source_eq]

end ProjectedIndex

/-- Two finite net projections of the same point are within the sum of their
radii, assuming the shared distance is symmetric and satisfies the triangle
inequality. This is the finite-net geometry step used to turn net radii into
projection-chain increment radii. -/
theorem projection_pair_dist_le_radius_sum
    [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B)
    (hdist : N₁.dist = N₀.dist)
    (hsymm : ∀ s t : T, N₀.dist s t = N₀.dist t s)
    (htri : ∀ x y z : T, N₀.dist x z ≤ N₀.dist x y + N₀.dist y z)
    (t : T) :
    N₀.dist (N₀.projection t) (N₁.projection t) ≤ N₀.radius + N₁.radius := by
  have hfirst : N₀.dist (N₀.projection t) t ≤ N₀.radius := by
    rw [hsymm]
    exact N₀.projection_dist_le t
  have hsecond : N₀.dist t (N₁.projection t) ≤ N₁.radius := by
    simpa [FiniteNet.projection, hdist] using N₁.projection_dist_le t
  calc
    N₀.dist (N₀.projection t) (N₁.projection t)
        ≤ N₀.dist (N₀.projection t) t + N₀.dist t (N₁.projection t) :=
          htri (N₀.projection t) t (N₁.projection t)
    _ ≤ N₀.radius + N₁.radius := add_le_add hfirst hsecond

/-- The finite family of projection pairs realized by projecting the same
ambient point into two finite nets. This lets finite chaining pay entropy for
the realized increment family rather than for the full ambient index type. -/
def ProjectionPair [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) : Type _ :=
  {ab : A × B // ∃ t : T, ab = (N₀.project t, N₁.project t)}

instance projectionPairFintype
    [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Fintype (ProjectionPair N₀ N₁) := by
  classical
  unfold ProjectionPair
  infer_instance

/-- The projection pair selected by a point. -/
def projectionPairOf [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) (t : T) :
    ProjectionPair N₀ N₁ :=
  ⟨(N₀.project t, N₁.project t), ⟨t, rfl⟩⟩

instance projectionPairNonempty
    [Fintype A] {B : Type*} [Fintype B] [Nonempty T]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Nonempty (ProjectionPair N₀ N₁) :=
  ⟨projectionPairOf N₀ N₁ (Classical.choice (inferInstance : Nonempty T))⟩

/-- The realized projection-pair family is bounded by the product of the two
finite covering numbers. -/
theorem projectionPair_card_le_coveringNumber_mul
    [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Fintype.card (ProjectionPair N₀ N₁) ≤
      N₀.coveringNumber * N₁.coveringNumber := by
  calc
    Fintype.card (ProjectionPair N₀ N₁) ≤ Fintype.card (A × B) :=
      Fintype.card_le_of_injective
        (fun pair : ProjectionPair N₀ N₁ => pair.1)
        (by
          intro pair₀ pair₁ h
          exact Subtype.ext h)
    _ = N₀.coveringNumber * N₁.coveringNumber := by
      simp [coveringNumber, Fintype.card_prod]

/-- Log-cardinality of realized projection pairs is bounded by the log of the
product of the two finite covering numbers. -/
theorem projectionPair_log_card_le_log_coveringNumber_mul
    [Nonempty T] [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Real.log (Fintype.card (ProjectionPair N₀ N₁) : ℝ) ≤
      Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ) := by
  have hpos : 0 < (Fintype.card (ProjectionPair N₀ N₁) : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := ProjectionPair N₀ N₁))
  have hle :
      (Fintype.card (ProjectionPair N₀ N₁) : ℝ) ≤
        (N₀.coveringNumber * N₁.coveringNumber : ℝ) := by
    exact_mod_cast projectionPair_card_le_coveringNumber_mul N₀ N₁
  exact Real.log_le_log hpos hle

/-- Every realized projection pair inherits the sum-of-radii distance bound
from the shared point whose projections produced it. -/
theorem projectionPair_dist_le_radius_sum
    [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B)
    (hdist : N₁.dist = N₀.dist)
    (hsymm : ∀ s t : T, N₀.dist s t = N₀.dist t s)
    (htri : ∀ x y z : T, N₀.dist x z ≤ N₀.dist x y + N₀.dist y z)
    (pair : ProjectionPair N₀ N₁) :
    N₀.dist (N₀.center pair.1.1) (N₁.center pair.1.2) ≤
      N₀.radius + N₁.radius := by
  rcases pair with ⟨⟨a, b⟩, t, ht⟩
  cases ht
  simpa [FiniteNet.projection] using
    projection_pair_dist_le_radius_sum N₀ N₁ hdist hsymm htri t

end FiniteNet

/-- A finite weighted process with sub-Gaussian increment MGF control.

The process is indexed by a finite type `T` and observed on a finite outcome
space `Ω`. The MGF field is intentionally abstract: later modules can derive it
from concrete Gaussian/Rademacher constructions, while this module only needs a
clean finite-process interface. -/
structure FiniteSubGaussianProcess (Ω T : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω : Ω, 0 ≤ weight ω
  weight_sum_one : ∑ ω : Ω, weight ω = 1
  X : Ω → T → ℝ
  dist : T → T → ℝ
  dist_nonneg : ∀ s t : T, 0 ≤ dist s t
  varianceProxy : ℝ
  varianceProxy_nonneg : 0 ≤ varianceProxy
  mgf_increment :
    ∀ s t : T, ∀ lam : ℝ,
      finiteExpectation weight (fun ω => Real.exp (lam * (X ω t - X ω s))) ≤
        Real.exp (lam ^ 2 * varianceProxy * dist s t ^ 2 / 2)

namespace FiniteSubGaussianProcess

/-- The sub-Gaussian increment MGF bound packaged as a theorem. -/
theorem increment_mgf [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T) (s t : T) (lam : ℝ) :
    finiteExpectation P.weight (fun ω => Real.exp (lam * (P.X ω t - P.X ω s))) ≤
      Real.exp (lam ^ 2 * P.varianceProxy * P.dist s t ^ 2 / 2) :=
  P.mgf_increment s t lam

/-- Radius-bounded form of the sub-Gaussian increment MGF bound for a single
increment. This is the reusable finite-process primitive behind the finite
max/entropy estimates below. -/
theorem increment_mgf_le_radius [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (s t : T) (r : ℝ)
    (hr : P.dist s t ≤ r)
    (hr_nonneg : 0 ≤ r)
    (lam : ℝ) :
    finiteExpectation P.weight (fun ω => Real.exp (lam * (P.X ω t - P.X ω s))) ≤
      Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2) := by
  refine (increment_mgf P s t lam).trans ?_
  apply Real.exp_le_exp.mpr
  have hdist_sq : P.dist s t ^ 2 ≤ r ^ 2 := by
    nlinarith [hr, P.dist_nonneg s t, hr_nonneg]
  have hcoef_nonneg : 0 ≤ lam ^ 2 * P.varianceProxy / 2 := by
    nlinarith [sq_nonneg lam, P.varianceProxy_nonneg]
  have hmul := mul_le_mul_of_nonneg_left hdist_sq hcoef_nonneg
  nlinarith

/-- The sub-Gaussian increment MGF bound along one level of a projection
chain. -/
theorem projection_increment_mgf [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (j : ℕ) (t : T) (lam : ℝ) :
    finiteExpectation P.weight
        (fun ω => Real.exp (lam * (P.X ω (π (j + 1) t) - P.X ω (π j t)))) ≤
      Real.exp (lam ^ 2 * P.varianceProxy *
        P.dist (π j t) (π (j + 1) t) ^ 2 / 2) :=
  P.mgf_increment (π j t) (π (j + 1) t) lam

/-- Radius-bounded version of `projection_increment_mgf`. If a projection
level moves every index point by at most `r`, the same MGF increment is bounded
using `r` in place of the pointwise distance. -/
theorem projection_increment_mgf_le_radius [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (j : ℕ) (r : ℝ)
    (hr : ∀ t : T, P.dist (π j t) (π (j + 1) t) ≤ r)
    (hr_nonneg : 0 ≤ r)
    (t : T) (lam : ℝ) :
    finiteExpectation P.weight
        (fun ω => Real.exp (lam * (P.X ω (π (j + 1) t) - P.X ω (π j t)))) ≤
      Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2) := by
  refine (projection_increment_mgf P π j t lam).trans ?_
  apply Real.exp_le_exp.mpr
  have hdist_sq : P.dist (π j t) (π (j + 1) t) ^ 2 ≤ r ^ 2 := by
    nlinarith [hr t, P.dist_nonneg (π j t) (π (j + 1) t), hr_nonneg]
  have hcoef_nonneg : 0 ≤ lam ^ 2 * P.varianceProxy / 2 := by
    nlinarith [sq_nonneg lam, P.varianceProxy_nonneg]
  have hmul := mul_le_mul_of_nonneg_left hdist_sq hcoef_nonneg
  nlinarith [hmul]

end FiniteSubGaussianProcess

/-! ## Finite expectation algebra -/

/-- Monotonicity of finite weighted expectation under nonnegative weights. -/
lemma finiteExpectation_mono [Fintype Ω]
    {p : Ω → ℝ} (hp : ∀ ω : Ω, 0 ≤ p ω)
    {X Y : Ω → ℝ} (hXY : ∀ ω : Ω, X ω ≤ Y ω) :
    finiteExpectation p X ≤ finiteExpectation p Y := by
  unfold finiteExpectation
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hXY ω) (hp ω)

/-- Additivity of finite weighted expectation. -/
lemma finiteExpectation_add [Fintype Ω]
    (p : Ω → ℝ) (X Y : Ω → ℝ) :
    finiteExpectation p (fun ω => X ω + Y ω) =
      finiteExpectation p X + finiteExpectation p Y := by
  unfold finiteExpectation
  calc
    (∑ ω : Ω, p ω * (X ω + Y ω))
        = ∑ ω : Ω, (p ω * X ω + p ω * Y ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = (∑ ω : Ω, p ω * X ω) + ∑ ω : Ω, p ω * Y ω := by
          rw [Finset.sum_add_distrib]

/-- Expectation of a constant under finite weights with total mass one. -/
lemma finiteExpectation_const_of_sum_one [Fintype Ω]
    (p : Ω → ℝ) (c : ℝ) (hsum : ∑ ω : Ω, p ω = 1) :
    finiteExpectation p (fun _ω => c) = c := by
  unfold finiteExpectation
  calc
    (∑ ω : Ω, p ω * c) = (∑ ω : Ω, p ω) * c := by
      rw [Finset.sum_mul]
    _ = c := by rw [hsum, one_mul]

/--
Finite expectation adapter from a supplied supremum functional to a projected
finite-supremum surrogate, under an explicit terminal approximation error.

This is only finite expectation bookkeeping. It deliberately does not define
or prove measurability for a supremum over an arbitrary class: callers must
supply the scalar `supFunctional` and the pointwise approximation hypothesis.
-/
lemma finiteExpectation_supFunctional_le_projected_add_terminalError
    [Fintype Ω]
    {p : Ω → ℝ} (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (supFunctional projectedSup : Ω → ℝ) (terminalError : ℝ)
    (hterminal : ∀ ω : Ω, supFunctional ω ≤ projectedSup ω + terminalError) :
    finiteExpectation p supFunctional ≤
      finiteExpectation p projectedSup + terminalError := by
  have hmono :
      finiteExpectation p supFunctional ≤
        finiteExpectation p (fun ω => projectedSup ω + terminalError) :=
    finiteExpectation_mono hp hterminal
  calc
    finiteExpectation p supFunctional
        ≤ finiteExpectation p (fun ω => projectedSup ω + terminalError) := hmono
    _ = finiteExpectation p projectedSup +
          finiteExpectation p (fun _ω => terminalError) := by
          rw [finiteExpectation_add]
    _ = finiteExpectation p projectedSup + terminalError := by
          rw [finiteExpectation_const_of_sum_one p terminalError hsum]

/--
Finite-skeleton terminal approximation adapter. If every point in a finite
separable skeleton is pointwise controlled by its terminal finite-net
projection up to `terminalError`, then the skeleton supremum is controlled by
the projected finite-net supremum up to the same error.

This is still a finite statement: `K` is a finite skeleton supplied by the
caller, and `N` is a finite terminal net. It does not construct a supremum over
an arbitrary infinite class.
-/
lemma finiteSup_skeleton_le_projectedSup_add_terminalError
    [Nonempty T] {K : Type*} [Fintype K] [Nonempty K] [Fintype A]
    (N : FiniteNet T A) (embed : K → T) (Y : T → ℝ) (terminalError : ℝ)
    (hterminal : ∀ k : K,
      Y (embed k) ≤ Y (N.projection (embed k)) + terminalError) :
    finiteSup (fun k : K => Y (embed k)) ≤
      finiteSup (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1)) +
        terminalError := by
  classical
  unfold finiteSup
  apply Finset.sup'_le
  intro k _
  let u : FiniteNet.ProjectedIndex N :=
    ⟨N.project (embed k), ⟨embed k, rfl⟩⟩
  have hproj :
      Y (N.center (N.project (embed k))) ≤
        (Finset.univ : Finset (FiniteNet.ProjectedIndex N)).sup'
          Finset.univ_nonempty
          (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1)) := by
    simpa [u] using
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1))
        (Finset.mem_univ u)
  have hterminal' :
      Y (embed k) ≤ Y (N.center (N.project (embed k))) + terminalError := by
    simpa [FiniteNet.projection] using hterminal k
  linarith

/--
Pointwise projected-sup adapter for a supplied supremum functional.

The caller supplies a scalar `supFunctional`, a finite skeleton `K`, and two
explicit approximation hypotheses:
* a separability/dense-net budget from `supFunctional` to the finite skeleton;
* a terminal projection budget from the finite skeleton to the terminal net.

The conclusion is exactly the `hterminal` hypothesis required by the
finite-expectation boundary theorem. No arbitrary measurable supremum is
defined here.
-/
lemma supFunctional_le_projectedSup_add_of_skeleton_terminal
    [Nonempty T] {K : Type*} [Fintype K] [Nonempty K] [Fintype A]
    (N : FiniteNet T A) (embed : K → T) (Y : T → ℝ)
    (supFunctional separabilityError terminalError : ℝ)
    (hseparable :
      supFunctional ≤ finiteSup (fun k : K => Y (embed k)) + separabilityError)
    (hterminal : ∀ k : K,
      Y (embed k) ≤ Y (N.projection (embed k)) + terminalError) :
    supFunctional ≤
      finiteSup (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1)) +
        (separabilityError + terminalError) := by
  have hskeleton :
      finiteSup (fun k : K => Y (embed k)) ≤
        finiteSup (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1)) +
          terminalError :=
    finiteSup_skeleton_le_projectedSup_add_terminalError
      N embed Y terminalError hterminal
  linarith

/--
Finite expectation form of the separable/dense-net boundary adapter.

This is a reusable projected-sup-to-true-sup bridge: the true supremum
is represented by a caller-supplied scalar functional, and all continuous
content is isolated in the explicit finite-skeleton and terminal-approximation
hypotheses.
-/
lemma finiteExpectation_supFunctional_le_projected_add_skeleton_terminalError
    [Fintype Ω] [Nonempty T] {K : Type*} [Fintype K] [Nonempty K] [Fintype A]
    {p : Ω → ℝ} (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (N : FiniteNet T A) (embed : K → T)
    (Y : Ω → T → ℝ) (supFunctional : Ω → ℝ)
    (separabilityError terminalError : ℝ)
    (hseparable : ∀ ω : Ω,
      supFunctional ω ≤
        finiteSup (fun k : K => Y ω (embed k)) + separabilityError)
    (hterminal : ∀ ω : Ω, ∀ k : K,
      Y ω (embed k) ≤ Y ω (N.projection (embed k)) + terminalError) :
    finiteExpectation p supFunctional ≤
      finiteExpectation p
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex N => Y ω (N.center u.1))) +
        (separabilityError + terminalError) := by
  refine finiteExpectation_supFunctional_le_projected_add_terminalError
    hp hsum supFunctional
    (fun ω => finiteSup
      (fun u : FiniteNet.ProjectedIndex N => Y ω (N.center u.1)))
    (separabilityError + terminalError) ?_
  intro ω
  exact supFunctional_le_projectedSup_add_of_skeleton_terminal
    N embed (Y ω) (supFunctional ω) separabilityError terminalError
    (hseparable ω) (hterminal ω)

/--
Terminal-projection approximation from a pathwise modulus at the terminal
net radius.

This is the direct helper for the `hterminalApprox` assumption in the
finite-skeleton Dudley adapter: if each sample path is one-sided continuous at
the terminal-net radius, then every skeleton point is controlled by its
terminal projection plus `terminalError`.
-/
lemma terminalApprox_of_pathwise_modulus
    {K : Type*} [Fintype A]
    (N : FiniteNet T A) (embed : K → T) (Y : Ω → T → ℝ)
    (terminalError : ℝ)
    (hmodulus : ∀ ω : Ω, ∀ s t : T,
      N.dist s t ≤ N.radius → Y ω s ≤ Y ω t + terminalError) :
    ∀ ω : Ω, ∀ k : K,
      Y ω (embed k) ≤ Y ω (N.projection (embed k)) + terminalError := by
  intro ω k
  exact hmodulus ω (embed k) (N.projection (embed k))
    (N.projection_dist_le (embed k))

/--
Terminal-projection approximation from a pathwise modulus at a larger radius
budget. This is useful when the modulus is stated with a named radius bound
rather than the exact net radius.
-/
lemma terminalApprox_of_pathwise_modulus_radiusBound
    {K : Type*} [Fintype A]
    (N : FiniteNet T A) (embed : K → T) (Y : Ω → T → ℝ)
    (radiusBound terminalError : ℝ)
    (hradius : N.radius ≤ radiusBound)
    (hmodulus : ∀ ω : Ω, ∀ s t : T,
      N.dist s t ≤ radiusBound → Y ω s ≤ Y ω t + terminalError) :
    ∀ ω : Ω, ∀ k : K,
      Y ω (embed k) ≤ Y ω (N.projection (embed k)) + terminalError := by
  intro ω k
  exact hmodulus ω (embed k) (N.projection (embed k))
    ((N.projection_dist_le (embed k)).trans hradius)

/--
Finite dense-skeleton approximation for a finite ambient supremum.

If every ambient point is controlled by a selected skeleton point up to
`skeletonError`, then the finite supremum over the ambient type is controlled
by the finite skeleton supremum plus the same error. This is a finite,
measurability-free version of the dense-net step.
-/
lemma finiteSup_le_skeletonSup_add_of_pointwise_approx
    [Fintype T] [Nonempty T] {K : Type*} [Fintype K] [Nonempty K]
    (embed : K → T) (nearest : T → K) (Y : T → ℝ) (skeletonError : ℝ)
    (happrox : ∀ t : T,
      Y t ≤ Y (embed (nearest t)) + skeletonError) :
    finiteSup Y ≤ finiteSup (fun k : K => Y (embed k)) + skeletonError := by
  classical
  unfold finiteSup
  apply Finset.sup'_le
  intro t _
  have hskel :
      Y (embed (nearest t)) ≤
        (Finset.univ : Finset K).sup' Finset.univ_nonempty
          (fun k : K => Y (embed k)) := by
    exact Finset.le_sup' (fun k : K => Y (embed k))
      (Finset.mem_univ (nearest t))
  have ht := happrox t
  linarith

/--
Finite-skeleton approximation for a caller-supplied supremum functional.

The caller supplies an approximate maximizer `witness : Ω → T` for the scalar
`supFunctional`, and a finite skeleton selector `nearest : T → K`. If the
witness is within `witnessError` of the supplied supremum and every ambient
point is within `skeletonError` of its skeleton representative, then
`hseparable` follows with error `witnessError + skeletonError`.

This avoids defining an arbitrary measurable supremum: all continuous content
is exposed as explicit witness and finite-skeleton hypotheses.
-/
lemma supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
    {K : Type*} [Fintype K] [Nonempty K]
    (embed : K → T) (nearest : T → K)
    (Y : Ω → T → ℝ) (supFunctional : Ω → ℝ) (witness : Ω → T)
    (witnessError skeletonError : ℝ)
    (hwitness : ∀ ω : Ω,
      supFunctional ω ≤ Y ω (witness ω) + witnessError)
    (happrox : ∀ ω : Ω, ∀ t : T,
      Y ω t ≤ Y ω (embed (nearest t)) + skeletonError) :
    ∀ ω : Ω,
      supFunctional ω ≤
        finiteSup (fun k : K => Y ω (embed k)) +
          (witnessError + skeletonError) := by
  intro ω
  have hskel :
      Y ω (embed (nearest (witness ω))) ≤
        finiteSup (fun k : K => Y ω (embed k)) := by
    unfold finiteSup
    exact Finset.le_sup' (fun k : K => Y ω (embed k))
      (Finset.mem_univ (nearest (witness ω)))
  have hw := hwitness ω
  have ha := happrox ω (witness ω)
  linarith

/-- Pull a finite sum through finite weighted expectation. -/
lemma finiteExpectation_sum_range [Fintype Ω]
    (p : Ω → ℝ) (Y : ℕ → Ω → ℝ) (m : ℕ) :
    finiteExpectation p (fun ω => ∑ j ∈ Finset.range m, Y j ω) =
      ∑ j ∈ Finset.range m, finiteExpectation p (fun ω => Y j ω) := by
  unfold finiteExpectation
  calc
    (∑ ω : Ω, p ω * ∑ j ∈ Finset.range m, Y j ω)
        = ∑ ω : Ω, ∑ j ∈ Finset.range m, p ω * Y j ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range m, ∑ ω : Ω, p ω * Y j ω := by
          rw [Finset.sum_comm]

/-- Pull a finite sum over an arbitrary finite index type through finite
weighted expectation. -/
lemma finiteExpectation_sum [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (Y : A → Ω → ℝ) :
    finiteExpectation p (fun ω => ∑ a : A, Y a ω) =
      ∑ a : A, finiteExpectation p (fun ω => Y a ω) := by
  unfold finiteExpectation
  calc
    (∑ ω : Ω, p ω * ∑ a : A, Y a ω)
        = ∑ ω : Ω, ∑ a : A, p ω * Y a ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ a : A, ∑ ω : Ω, p ω * Y a ω := by
          rw [Finset.sum_comm]

/-- Shift an exponential inside finite weighted expectation. -/
lemma finiteExpectation_exp_shift [Fintype Ω]
    (p : Ω → ℝ) (Z : Ω → ℝ) (lam c : ℝ) :
    finiteExpectation p (fun ω => Real.exp (lam * (Z ω - c))) =
      Real.exp (-(lam * c)) * finiteExpectation p (fun ω => Real.exp (lam * Z ω)) := by
  unfold finiteExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have harg : lam * (Z ω - c) = -(lam * c) + lam * Z ω := by ring
  change p ω * Real.exp (lam * (Z ω - c)) =
    Real.exp (-(lam * c)) * (p ω * Real.exp (lam * Z ω))
  rw [harg, Real.exp_add]
  ring

/-- A shifted exponential-moment bound controls the finite weighted mean. This
is the elementary Chernoff step used below to convert finite-max MGF control
into an expected-supremum budget. -/
theorem expectation_le_of_shifted_exp_mgf [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (Z : Ω → ℝ) (lam budget : ℝ) (hlam : 0 < lam)
    (hmgf : finiteExpectation p (fun ω => Real.exp (lam * (Z ω - budget))) ≤ 1) :
    finiteExpectation p Z ≤ budget := by
  have hpoint : ∀ ω : Ω,
      lam * (Z ω - budget) ≤ Real.exp (lam * (Z ω - budget)) - 1 := by
    intro ω
    have h := Real.add_one_le_exp (lam * (Z ω - budget))
    linarith
  have hmain :
      finiteExpectation p (fun ω => lam * (Z ω - budget)) ≤
        finiteExpectation p (fun ω => Real.exp (lam * (Z ω - budget)) - 1) :=
    finiteExpectation_mono hp hpoint
  have hleft :
      finiteExpectation p (fun ω => lam * (Z ω - budget)) =
        lam * (finiteExpectation p Z - budget) := by
    unfold finiteExpectation
    calc
      (∑ ω : Ω, p ω * (lam * (Z ω - budget)))
          = ∑ ω : Ω, (lam * (p ω * Z ω) - (lam * budget) * p ω) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
      _ = (∑ ω : Ω, lam * (p ω * Z ω)) -
            ∑ ω : Ω, (lam * budget) * p ω := by
            rw [Finset.sum_sub_distrib]
      _ = lam * (∑ ω : Ω, p ω * Z ω) - (lam * budget) * ∑ ω : Ω, p ω := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = lam * (∑ ω : Ω, p ω * Z ω) - lam * budget := by
            rw [hsum, mul_one]
      _ = lam * ((∑ ω : Ω, p ω * Z ω) - budget) := by ring
  have hright :
      finiteExpectation p (fun ω => Real.exp (lam * (Z ω - budget)) - 1) =
        finiteExpectation p (fun ω => Real.exp (lam * (Z ω - budget))) - 1 := by
    unfold finiteExpectation
    calc
      (∑ ω : Ω, p ω * (Real.exp (lam * (Z ω - budget)) - 1))
          = ∑ ω : Ω, (p ω * Real.exp (lam * (Z ω - budget)) - p ω) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
      _ = (∑ ω : Ω, p ω * Real.exp (lam * (Z ω - budget))) -
            ∑ ω : Ω, p ω := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ ω : Ω, p ω * Real.exp (lam * (Z ω - budget))) - 1 := by
            rw [hsum]
  rw [hleft, hright] at hmain
  have hnonpos :
      finiteExpectation p (fun ω => Real.exp (lam * (Z ω - budget))) - 1 ≤ 0 := by
    linarith
  have hscaled : lam * (finiteExpectation p Z - budget) ≤ 0 :=
    hmain.trans hnonpos
  nlinarith

/-! ## Multiscale chaining decomposition -/

/-- For a finite index set, the exponential of the finite maximum is bounded
by the sum of coordinate exponentials. -/
lemma exp_finiteSup_sub_le_sum_exp_sub
    [Fintype T] [Nonempty T]
    (Y : T → ℝ) (lam budget : ℝ) :
    Real.exp (lam * (finiteSup Y - budget)) ≤
      ∑ t : T, Real.exp (lam * (Y t - budget)) := by
  unfold finiteSup
  rcases Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset T))
      Finset.univ_nonempty Y with ⟨t, ht, hmax⟩
  rw [hmax]
  exact Finset.single_le_sum
    (fun u _ => Real.exp_nonneg (lam * (Y u - budget))) ht

/-- Finite-max entropy budget from shifted coordinate MGF bounds. If each
coordinate has shifted exponential moment at most `1 / |T|`, then the expected
finite supremum is at most `budget`. -/
theorem finite_expectedSup_le_of_shifted_mgf
    [Fintype Ω] [Fintype T] [Nonempty T]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (Y : Ω → T → ℝ) (lam budget : ℝ) (hlam : 0 < lam)
    (hcoord : ∀ t : T,
      finiteExpectation p (fun ω => Real.exp (lam * (Y ω t - budget))) ≤
        (Fintype.card T : ℝ)⁻¹) :
    finiteExpectation p (fun ω => finiteSup (Y ω)) ≤ budget := by
  refine expectation_le_of_shifted_exp_mgf p hp hsum (fun ω => finiteSup (Y ω))
    lam budget hlam ?_
  calc
    finiteExpectation p (fun ω => Real.exp (lam * (finiteSup (Y ω) - budget)))
        ≤ finiteExpectation p
            (fun ω => ∑ t : T, Real.exp (lam * (Y ω t - budget))) :=
          finiteExpectation_mono hp
            (fun ω => exp_finiteSup_sub_le_sum_exp_sub (Y ω) lam budget)
    _ = ∑ t : T, finiteExpectation p
            (fun ω => Real.exp (lam * (Y ω t - budget))) := by
          rw [finiteExpectation_sum]
    _ ≤ ∑ _t : T, (Fintype.card T : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro t _
          exact hcoord t
    _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hcard_ne : (Fintype.card T : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_ne_zero (α := T))
          field_simp [hcard_ne]

/-- Finite-max entropy bound from coordinate MGF control. If every coordinate
has moment generating function at most `exp q` at a fixed positive `λ`, then
the expected finite supremum is bounded by `(log |T| + q) / λ`.

This is the standalone finite-index bridge from an MGF condition to an
expected-supremum budget; later chaining theorems apply it to projection
increments. -/
theorem finite_expectedSup_le_of_mgf_log
    [Fintype Ω] [Fintype T] [Nonempty T]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (Y : Ω → T → ℝ) (lam q : ℝ) (hlam : 0 < lam)
    (hcoord : ∀ t : T,
      finiteExpectation p (fun ω => Real.exp (lam * Y ω t)) ≤ Real.exp q) :
    finiteExpectation p (fun ω => finiteSup (Y ω)) ≤
      (Real.log (Fintype.card T : ℝ) + q) / lam := by
  refine finite_expectedSup_le_of_shifted_mgf p hp hsum Y lam
    ((Real.log (Fintype.card T : ℝ) + q) / lam) hlam ?_
  intro t
  calc
    finiteExpectation p
        (fun ω => Real.exp
          (lam * (Y ω t - ((Real.log (Fintype.card T : ℝ) + q) / lam))))
        = Real.exp (-(lam * ((Real.log (Fintype.card T : ℝ) + q) / lam))) *
            finiteExpectation p (fun ω => Real.exp (lam * Y ω t)) := by
          rw [finiteExpectation_exp_shift]
    _ ≤ Real.exp (-(lam * ((Real.log (Fintype.card T : ℝ) + q) / lam))) *
          Real.exp q := by
          exact mul_le_mul_of_nonneg_left (hcoord t) (Real.exp_nonneg _)
    _ = Real.exp (q - lam * ((Real.log (Fintype.card T : ℝ) + q) / lam)) := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ (Fintype.card T : ℝ)⁻¹ := by
          have hcard_pos : 0 < (Fintype.card T : ℝ) := by
            exact_mod_cast (Fintype.card_pos (α := T))
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          have harg :
              q - lam * ((Real.log (Fintype.card T : ℝ) + q) / lam) =
                -Real.log (Fintype.card T : ℝ) := by
            field_simp [hlam_ne]
            ring
          rw [harg, Real.exp_neg, Real.exp_log hcard_pos]

/-- Optimizing `L / λ + λq / 2` at `λ = sqrt (2L/q)`, written in the
algebraic form used by the finite sub-Gaussian max bound. -/
lemma sqrt_entropy_optimizer_identity {L q : ℝ} (hL : 0 < L) (hq : 0 < q) :
    (L + (Real.sqrt (2 * L / q)) ^ 2 * q / 2) / Real.sqrt (2 * L / q) =
      Real.sqrt (2 * q * L) := by
  have harg_nonneg : 0 ≤ 2 * L / q := by positivity
  have hlam_pos : 0 < Real.sqrt (2 * L / q) :=
    Real.sqrt_pos_of_pos (by positivity)
  have hsq : (Real.sqrt (2 * L / q)) ^ 2 = 2 * L / q :=
    Real.sq_sqrt harg_nonneg
  rw [hsq]
  have hnum : L + (2 * L / q) * q / 2 = 2 * L := by
    field_simp [ne_of_gt hq]
    ring
  rw [hnum]
  have hleft_nonneg : 0 ≤ 2 * L / Real.sqrt (2 * L / q) := by positivity
  have hright_pos : 0 < Real.sqrt (2 * q * L) :=
    Real.sqrt_pos_of_pos (by positivity)
  have hsqeq :
      (2 * L / Real.sqrt (2 * L / q)) ^ 2 = (Real.sqrt (2 * q * L)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hq, ne_of_gt hlam_pos]
    rw [hsq]
    field_simp [ne_of_gt hq]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsqeq with h | h
  · exact h
  · nlinarith

/-- Pull the finite entropy term out of the square root in the form used by
the Dudley-style finite entropy-sum corollaries. The `radius` parameter is a
finite net radius or a sum of adjacent finite net radii, not a limiting
scale. -/
lemma sqrt_entropy_scale_eq (variance radius entropy : ℝ)
    (hvariance_nonneg : 0 ≤ variance) (hradius_nonneg : 0 ≤ radius) :
    Real.sqrt (2 * variance * radius ^ 2 * entropy) =
      Real.sqrt (2 * variance) * radius * Real.sqrt entropy := by
  have hcoef_nonneg : 0 ≤ 2 * variance * radius ^ 2 := by
    nlinarith [hvariance_nonneg, sq_nonneg radius]
  have htwo_var_nonneg : 0 ≤ 2 * variance := by
    nlinarith
  calc
    Real.sqrt (2 * variance * radius ^ 2 * entropy)
        = Real.sqrt ((2 * variance * radius ^ 2) * entropy) := by ring_nf
    _ = Real.sqrt (2 * variance * radius ^ 2) * Real.sqrt entropy := by
        rw [Real.sqrt_mul hcoef_nonneg entropy]
    _ = Real.sqrt ((2 * variance) * (radius * radius)) * Real.sqrt entropy := by
        ring_nf
    _ = (Real.sqrt (2 * variance) * Real.sqrt (radius * radius)) *
          Real.sqrt entropy := by
        rw [Real.sqrt_mul htwo_var_nonneg (radius * radius)]
    _ = Real.sqrt (2 * variance) * radius * Real.sqrt entropy := by
        rw [Real.sqrt_mul_self hradius_nonneg]

/-- Optimized finite sub-Gaussian max bound from coordinate MGF control. If
each coordinate satisfies `E exp(λ Y_t) ≤ exp(λ²σ²/2)` for every `λ`, then the
expected supremum over the finite index type is at most
`sqrt (2σ² log |T|)`.

This is finite-index and finite-support only; it is the entropy-budget lemma
that feeds the later multiscale chaining statements. -/
theorem finite_expectedSup_le_of_subGaussian_mgf_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (Y : Ω → T → ℝ) (variance : ℝ)
    (hvariance : 0 < variance)
    (hcoord : ∀ t : T, ∀ lam : ℝ,
      finiteExpectation p (fun ω => Real.exp (lam * Y ω t)) ≤
        Real.exp (lam ^ 2 * variance / 2))
    (hcard : 1 < Fintype.card T) :
    finiteExpectation p (fun ω => finiteSup (Y ω)) ≤
      Real.sqrt (2 * variance * Real.log (Fintype.card T : ℝ)) := by
  let L := Real.log (Fintype.card T : ℝ)
  let lam := Real.sqrt (2 * L / variance)
  have hL : 0 < L := by
    have hcard_real : (1 : ℝ) < (Fintype.card T : ℝ) := by exact_mod_cast hcard
    simpa [L] using Real.log_pos hcard_real
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos_of_pos (by positivity)
  calc
    finiteExpectation p (fun ω => finiteSup (Y ω))
        ≤ (Real.log (Fintype.card T : ℝ) + lam ^ 2 * variance / 2) / lam :=
          finite_expectedSup_le_of_mgf_log p hp hsum Y lam
            (lam ^ 2 * variance / 2) hlam (fun t => hcoord t lam)
    _ = Real.sqrt (2 * variance * Real.log (Fintype.card T : ℝ)) := by
          have hopt := sqrt_entropy_optimizer_identity hL hvariance
          dsimp [lam]
          simpa [L, mul_assoc, mul_left_comm, mul_comm] using hopt

/-- Telescoping identity for a chain of projections. The projection sequence is
indexed by natural-number levels; level `0` is the coarse approximation and
level `m` is the terminal approximation. -/
lemma chain_telescope_to_projection
    (X : T → ℝ) (π : ℕ → T → T) (m : ℕ) (t : T) :
    X (π m t) =
      X (π 0 t) + ∑ j ∈ Finset.range m, (X (π (j + 1) t) - X (π j t)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Telescoping identity for a projection chain parameterized by an arbitrary
finite domain. The process is still indexed by `T`; the chain is evaluated
along a finite parameter type such as a projected net image. -/
lemma chain_telescope_to_projection_over
    {U : Type*} (X : T → ℝ) (π : ℕ → U → T) (m : ℕ) (u : U) :
    X (π m u) =
      X (π 0 u) + ∑ j ∈ Finset.range m, (X (π (j + 1) u) - X (π j u)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Telescoping identity when the final projection is the original point. -/
lemma chain_telescope
    (X : T → ℝ) (π : ℕ → T → T) (m : ℕ) (t : T)
    (hlast : π m t = t) :
    X t =
      X (π 0 t) + ∑ j ∈ Finset.range m, (X (π (j + 1) t) - X (π j t)) := by
  calc X t
      = X (π m t) := by rw [hlast]
    _ = X (π 0 t) + ∑ j ∈ Finset.range m, (X (π (j + 1) t) - X (π j t)) :=
        chain_telescope_to_projection X π m t

/-- Pointwise finite multiscale chaining: the supremum of a process is bounded
by the supremum at the coarse projection plus the sum of suprema of scale
increments. -/
theorem finite_chaining_decomposition
    [Fintype T] [Nonempty T]
    (X : T → ℝ) (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t) :
    finiteSup X ≤
      finiteSup (fun t => X (π 0 t)) +
        ∑ j ∈ Finset.range m,
          finiteSup (fun t => X (π (j + 1) t) - X (π j t)) := by
  unfold finiteSup
  apply Finset.sup'_le
  intro t _
  rw [chain_telescope X π m t (hlast t)]
  apply add_le_add
  · exact Finset.le_sup' (s := (univ : Finset T)) (fun u => X (π 0 u)) (mem_univ t)
  · apply Finset.sum_le_sum
    intro j _
    exact Finset.le_sup' (s := (univ : Finset T))
      (fun u => X (π (j + 1) u) - X (π j u)) (mem_univ t)

/-- Finite weighted-expectation chaining bound. If every scale increment has
expected finite supremum at most `budget j`, then the expected supremum of the
full finite process is bounded by the expected coarse supremum plus the sum of
the scale budgets.

This is the finite-process scaffold that later sub-Gaussian increment estimates
feed into; it is not the continuous Dudley entropy integral. -/
theorem finite_chaining_expectation_bound
    [Fintype Ω] [Fintype T] [Nonempty T]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω)
    (X : Ω → T → ℝ) (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation p
        (fun ω => finiteSup (fun t => X ω (π (j + 1) t) - X ω (π j t))) ≤
      budget j) :
    finiteExpectation p (fun ω => finiteSup (X ω)) ≤
      finiteExpectation p (fun ω => finiteSup (fun t => X ω (π 0 t))) +
        ∑ j ∈ Finset.range m, budget j := by
  let coarse : Ω → ℝ := fun ω => finiteSup (fun t => X ω (π 0 t))
  let inc : ℕ → Ω → ℝ :=
    fun j ω => finiteSup (fun t => X ω (π (j + 1) t) - X ω (π j t))
  have hpoint : ∀ ω : Ω,
      finiteSup (X ω) ≤ coarse ω + ∑ j ∈ Finset.range m, inc j ω := by
    intro ω
    exact finite_chaining_decomposition (X ω) π m hlast
  calc finiteExpectation p (fun ω => finiteSup (X ω))
      ≤ finiteExpectation p (fun ω => coarse ω + ∑ j ∈ Finset.range m, inc j ω) :=
        finiteExpectation_mono hp hpoint
    _ = finiteExpectation p coarse + ∑ j ∈ Finset.range m, finiteExpectation p (inc j) := by
        rw [finiteExpectation_add, finiteExpectation_sum_range]
    _ ≤ finiteExpectation p coarse + ∑ j ∈ Finset.range m, budget j := by
        have hsum :
            (∑ j ∈ Finset.range m, finiteExpectation p (inc j)) ≤
              ∑ j ∈ Finset.range m, budget j := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [inc] using hbudget j hj
        linarith

/-- Pointwise finite projected chaining. This is the same finite telescoping
bookkeeping as `finite_chaining_decomposition`, but it stops at the terminal
projection `π m` instead of requiring `π m t = t`.

This is the finite projected-supremum scaffold used before passing to a
continuous or measurable supremum. -/
theorem finite_projected_chaining_decomposition
    [Fintype T] [Nonempty T]
    (X : T → ℝ) (π : ℕ → T → T) (m : ℕ) :
    finiteSup (fun t => X (π m t)) ≤
      finiteSup (fun t => X (π 0 t)) +
        ∑ j ∈ Finset.range m,
          finiteSup (fun t => X (π (j + 1) t) - X (π j t)) := by
  unfold finiteSup
  apply Finset.sup'_le
  intro t _
  rw [chain_telescope_to_projection X π m t]
  apply add_le_add
  · exact Finset.le_sup' (s := (univ : Finset T)) (fun u => X (π 0 u)) (mem_univ t)
  · apply Finset.sum_le_sum
    intro j _
    exact Finset.le_sup' (s := (univ : Finset T))
      (fun u => X (π (j + 1) u) - X (π j u)) (mem_univ t)

/-- Finite weighted-expectation projected chaining bound. It bounds the
expected supremum over the terminal projection `π m`, without assuming that
the terminal projection is the identity.

This is intentionally finite-index and finite-scale. It does not construct a
measurable supremum over an arbitrary class. -/
theorem finite_projected_chaining_expectation_bound
    [Fintype Ω] [Fintype T] [Nonempty T]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω)
    (X : Ω → T → ℝ) (π : ℕ → T → T) (m : ℕ)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation p
        (fun ω => finiteSup (fun t => X ω (π (j + 1) t) - X ω (π j t))) ≤
      budget j) :
    finiteExpectation p (fun ω => finiteSup (fun t => X ω (π m t))) ≤
      finiteExpectation p (fun ω => finiteSup (fun t => X ω (π 0 t))) +
        ∑ j ∈ Finset.range m, budget j := by
  let coarse : Ω → ℝ := fun ω => finiteSup (fun t => X ω (π 0 t))
  let inc : ℕ → Ω → ℝ :=
    fun j ω => finiteSup (fun t => X ω (π (j + 1) t) - X ω (π j t))
  have hpoint : ∀ ω : Ω,
      finiteSup (fun t => X ω (π m t)) ≤ coarse ω + ∑ j ∈ Finset.range m, inc j ω := by
    intro ω
    exact finite_projected_chaining_decomposition (X ω) π m
  calc finiteExpectation p (fun ω => finiteSup (fun t => X ω (π m t)))
      ≤ finiteExpectation p (fun ω => coarse ω + ∑ j ∈ Finset.range m, inc j ω) :=
        finiteExpectation_mono hp hpoint
    _ = finiteExpectation p coarse + ∑ j ∈ Finset.range m, finiteExpectation p (inc j) := by
        rw [finiteExpectation_add, finiteExpectation_sum_range]
    _ ≤ finiteExpectation p coarse + ∑ j ∈ Finset.range m, budget j := by
        have hsum :
            (∑ j ∈ Finset.range m, finiteExpectation p (inc j)) ≤
              ∑ j ∈ Finset.range m, budget j := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [inc] using hbudget j hj
        linarith

/-- Pointwise projected chaining over an arbitrary finite parameter domain.
The process itself may be indexed by an ambient type `T`; only the parameter
domain `U` over which the projected supremum is taken must be finite.

This is the finite-image bridge used to avoid assuming `[Fintype T]` for
projected finite-net suprema. -/
theorem finite_projected_chaining_decomposition_over
    {U : Type*} [Fintype U] [Nonempty U]
    (X : T → ℝ) (π : ℕ → U → T) (m : ℕ) :
    finiteSup (fun u => X (π m u)) ≤
      finiteSup (fun u => X (π 0 u)) +
        ∑ j ∈ Finset.range m,
          finiteSup (fun u => X (π (j + 1) u) - X (π j u)) := by
  unfold finiteSup
  apply Finset.sup'_le
  intro u _
  rw [chain_telescope_to_projection_over X π m u]
  apply add_le_add
  · exact Finset.le_sup' (s := (univ : Finset U)) (fun v => X (π 0 v)) (mem_univ u)
  · apply Finset.sum_le_sum
    intro j _
    exact Finset.le_sup' (s := (univ : Finset U))
      (fun v => X (π (j + 1) v) - X (π j v)) (mem_univ u)

/-- Finite weighted-expectation projected chaining over an arbitrary finite
parameter domain `U`. The ambient process index type `T` need not be finite. -/
theorem finite_projected_chaining_expectation_bound_over
    [Fintype Ω] {U : Type*} [Fintype U] [Nonempty U]
    (p : Ω → ℝ) (hp : ∀ ω : Ω, 0 ≤ p ω)
    (X : Ω → T → ℝ) (π : ℕ → U → T) (m : ℕ)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation p
        (fun ω => finiteSup (fun u => X ω (π (j + 1) u) - X ω (π j u))) ≤
      budget j) :
    finiteExpectation p (fun ω => finiteSup (fun u => X ω (π m u))) ≤
      finiteExpectation p (fun ω => finiteSup (fun u => X ω (π 0 u))) +
        ∑ j ∈ Finset.range m, budget j := by
  let coarse : Ω → ℝ := fun ω => finiteSup (fun u => X ω (π 0 u))
  let inc : ℕ → Ω → ℝ :=
    fun j ω => finiteSup (fun u => X ω (π (j + 1) u) - X ω (π j u))
  have hpoint : ∀ ω : Ω,
      finiteSup (fun u => X ω (π m u)) ≤ coarse ω + ∑ j ∈ Finset.range m, inc j ω := by
    intro ω
    exact finite_projected_chaining_decomposition_over (X ω) π m
  calc finiteExpectation p (fun ω => finiteSup (fun u => X ω (π m u)))
      ≤ finiteExpectation p (fun ω => coarse ω + ∑ j ∈ Finset.range m, inc j ω) :=
        finiteExpectation_mono hp hpoint
    _ = finiteExpectation p coarse + ∑ j ∈ Finset.range m, finiteExpectation p (inc j) := by
        rw [finiteExpectation_add, finiteExpectation_sum_range]
    _ ≤ finiteExpectation p coarse + ∑ j ∈ Finset.range m, budget j := by
        have hsum :
            (∑ j ∈ Finset.range m, finiteExpectation p (inc j)) ≤
              ∑ j ∈ Finset.range m, budget j := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [inc] using hbudget j hj
        linarith

namespace FiniteSubGaussianProcess

/-- Chaining bound specialized to a finite sub-Gaussian process record. The
sub-Gaussian MGF field is carried by `P`; the present theorem consumes the
finite expected-sup budgets for each scale, which later entropy lemmas will
derive from that MGF condition. -/
theorem finite_chaining_expectation_bound
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t))) ≤
      budget j) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m, budget j :=
  FormalSLT.Covering.FiniteSubGaussianChaining.finite_chaining_expectation_bound
    P.weight P.weight_nonneg P.X π m hlast budget hbudget

/-- Projected chaining bound specialized to a finite sub-Gaussian process.
The left side is the expected finite supremum over the terminal projection
`π m`, so no identity-terminal assumption is required. -/
theorem finite_projected_chaining_expectation_bound
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t))) ≤
      budget j) :
    finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π m t))) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m, budget j :=
  FormalSLT.Covering.FiniteSubGaussianChaining.finite_projected_chaining_expectation_bound
    P.weight P.weight_nonneg P.X π m budget hbudget

/-- Projected chaining bound for a finite parameter domain `U`, specialized to
a finite sub-Gaussian process over an ambient index type `T`. This is the
version used for projected finite-net images when `T` itself is not finite. -/
theorem finite_projected_chaining_expectation_bound_over
    [Fintype Ω] {U : Type*} [Fintype U] [Nonempty U]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → U → T) (m : ℕ)
    (budget : ℕ → ℝ)
    (hbudget : ∀ j ∈ Finset.range m,
      finiteExpectation P.weight
        (fun ω => finiteSup (fun u => P.X ω (π (j + 1) u) - P.X ω (π j u))) ≤
      budget j) :
    finiteExpectation P.weight (fun ω => finiteSup (fun u => P.X ω (π m u))) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun u => P.X ω (π 0 u))) +
        ∑ j ∈ Finset.range m, budget j :=
  FormalSLT.Covering.FiniteSubGaussianChaining.finite_projected_chaining_expectation_bound_over
    P.weight P.weight_nonneg P.X π m budget hbudget

/-- Expected supremum budget for one projection-increment level of a finite
sub-Gaussian process. The hypothesis
`exp(λ²σ²r²/2 - λ·budget) ≤ 1 / |T|` is the finite entropy accounting step:
the radius-bounded sub-Gaussian MGF leaves enough room for a union bound over
the finite index type. -/
theorem projection_increment_expectedSup_le_of_radius
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (j : ℕ)
    (lam r budget : ℝ) (hlam : 0 < lam)
    (hr : ∀ t : T, P.dist (π j t) (π (j + 1) t) ≤ r)
    (hr_nonneg : 0 ≤ r)
    (hbudget :
      Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2 - lam * budget) ≤
        (Fintype.card T : ℝ)⁻¹) :
    finiteExpectation P.weight
      (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t))) ≤
      budget := by
  refine finite_expectedSup_le_of_shifted_mgf
    P.weight P.weight_nonneg P.weight_sum_one
    (fun ω t => P.X ω (π (j + 1) t) - P.X ω (π j t))
    lam budget hlam ?_
  intro t
  calc
    finiteExpectation P.weight
        (fun ω => Real.exp (lam * (P.X ω (π (j + 1) t) - P.X ω (π j t) - budget)))
        = Real.exp (-(lam * budget)) *
            finiteExpectation P.weight
              (fun ω => Real.exp (lam * (P.X ω (π (j + 1) t) - P.X ω (π j t)))) := by
          rw [finiteExpectation_exp_shift]
    _ ≤ Real.exp (-(lam * budget)) *
          Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left
            (projection_increment_mgf_le_radius P π j r hr hr_nonneg t lam)
            (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2 - lam * budget) := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ (Fintype.card T : ℝ)⁻¹ := hbudget

/-- Log-cardinality version of
`projection_increment_expectedSup_le_of_radius`. This is the finite
sub-Gaussian max bound for one projection-increment level:
`E sup_t Δ_j(t) ≤ (log |T| + λ²σ²r²/2) / λ`. -/
theorem projection_increment_expectedSup_le_of_radius_log
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (j : ℕ)
    (lam r : ℝ) (hlam : 0 < lam)
    (hr : ∀ t : T, P.dist (π j t) (π (j + 1) t) ≤ r)
    (hr_nonneg : 0 ≤ r) :
    finiteExpectation P.weight
      (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t))) ≤
      (Real.log (Fintype.card T : ℝ) +
        lam ^ 2 * P.varianceProxy * r ^ 2 / 2) / lam := by
  let q := lam ^ 2 * P.varianceProxy * r ^ 2 / 2
  refine projection_increment_expectedSup_le_of_radius P π j lam r
    ((Real.log (Fintype.card T : ℝ) + q) / lam)
    hlam hr hr_nonneg ?_
  have hcard_pos : 0 < (Fintype.card T : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := T))
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have harg :
      q - lam * ((Real.log (Fintype.card T : ℝ) + q) / lam) =
        -Real.log (Fintype.card T : ℝ) := by
    field_simp [hlam_ne]
    ring
  calc
    Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2 -
        lam * ((Real.log (Fintype.card T : ℝ) + q) / lam))
        = Real.exp (q - lam * ((Real.log (Fintype.card T : ℝ) + q) / lam)) := by
          simp [q]
    _ = Real.exp (-Real.log (Fintype.card T : ℝ)) := by
          rw [harg]
    _ ≤ (Fintype.card T : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hcard_pos]

/-- Square-root version of the one-level finite sub-Gaussian max bound,
obtained by optimizing the positive λ parameter in
`projection_increment_expectedSup_le_of_radius_log`. -/
theorem projection_increment_expectedSup_le_of_radius_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (j : ℕ)
    (r : ℝ)
    (hvariance : 0 < P.varianceProxy)
    (hr : ∀ t : T, P.dist (π j t) (π (j + 1) t) ≤ r)
    (hr_pos : 0 < r)
    (hcard : 1 < Fintype.card T) :
    finiteExpectation P.weight
      (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t))) ≤
      Real.sqrt (2 * P.varianceProxy * r ^ 2 * Real.log (Fintype.card T : ℝ)) := by
  let L := Real.log (Fintype.card T : ℝ)
  let q := P.varianceProxy * r ^ 2
  have hL : 0 < L := by
    have hcard_real : (1 : ℝ) < (Fintype.card T : ℝ) := by exact_mod_cast hcard
    simpa [L] using Real.log_pos hcard_real
  have hq : 0 < q := by
    simp [q]
    positivity
  let lam := Real.sqrt (2 * L / q)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos_of_pos (by positivity)
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
        ≤ (Real.log (Fintype.card T : ℝ) +
            lam ^ 2 * P.varianceProxy * r ^ 2 / 2) / lam :=
          projection_increment_expectedSup_le_of_radius_log P π j lam r hlam hr hr_pos.le
    _ = Real.sqrt (2 * P.varianceProxy * r ^ 2 * Real.log (Fintype.card T : ℝ)) := by
          have hopt := sqrt_entropy_optimizer_identity hL hq
          dsimp [lam]
          simpa [L, q, mul_assoc, mul_left_comm, mul_comm] using hopt

/-- Log-cardinality finite-max bound for an arbitrary finite family of
sub-Gaussian increments. The index family `I` is finite but otherwise
abstract; this is still a finite-sample, finite-class statement, not a
measurable separability or Talagrand contraction theorem. -/
theorem increment_family_expectedSup_le_of_radius_log
    [Fintype Ω] {I : Type*} [Fintype I] [Nonempty I]
    (P : FiniteSubGaussianProcess Ω T)
    (left right : I → T)
    (lam r : ℝ) (hlam : 0 < lam)
    (hr : ∀ i : I, P.dist (left i) (right i) ≤ r)
    (hr_nonneg : 0 ≤ r) :
    finiteExpectation P.weight
      (fun ω => finiteSup (fun i : I => P.X ω (right i) - P.X ω (left i))) ≤
      (Real.log (Fintype.card I : ℝ) +
        lam ^ 2 * P.varianceProxy * r ^ 2 / 2) / lam := by
  let q := lam ^ 2 * P.varianceProxy * r ^ 2 / 2
  refine finite_expectedSup_le_of_shifted_mgf
    P.weight P.weight_nonneg P.weight_sum_one
    (fun ω i => P.X ω (right i) - P.X ω (left i))
    lam ((Real.log (Fintype.card I : ℝ) + q) / lam) hlam ?_
  intro i
  calc
    finiteExpectation P.weight
        (fun ω => Real.exp
          (lam * (P.X ω (right i) - P.X ω (left i) -
            ((Real.log (Fintype.card I : ℝ) + q) / lam))))
        = Real.exp (-(lam * ((Real.log (Fintype.card I : ℝ) + q) / lam))) *
            finiteExpectation P.weight
              (fun ω => Real.exp (lam * (P.X ω (right i) - P.X ω (left i)))) := by
          rw [finiteExpectation_exp_shift]
    _ ≤ Real.exp (-(lam * ((Real.log (Fintype.card I : ℝ) + q) / lam))) *
          Real.exp (lam ^ 2 * P.varianceProxy * r ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left
            (increment_mgf_le_radius P (left i) (right i) r (hr i) hr_nonneg lam)
            (Real.exp_nonneg _)
    _ = Real.exp (q - lam * ((Real.log (Fintype.card I : ℝ) + q) / lam)) := by
          rw [← Real.exp_add]
          simp [q]
          ring
    _ ≤ (Fintype.card I : ℝ)⁻¹ := by
          have hcard_pos : 0 < (Fintype.card I : ℝ) := by
            exact_mod_cast (Fintype.card_pos (α := I))
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          have harg :
              q - lam * ((Real.log (Fintype.card I : ℝ) + q) / lam) =
                -Real.log (Fintype.card I : ℝ) := by
            field_simp [hlam_ne]
            ring
          rw [harg, Real.exp_neg, Real.exp_log hcard_pos]

/-- Optimized square-root finite-max bound for an arbitrary finite family of
sub-Gaussian increments:
`E sup_i (X_{right i} - X_{left i}) ≤ sqrt(2 σ² r² log |I|)`.
The theorem is deliberately finite-index and finite-family. -/
theorem increment_family_expectedSup_le_of_radius_sqrt
    [Fintype Ω] {I : Type*} [Fintype I] [Nonempty I]
    (P : FiniteSubGaussianProcess Ω T)
    (left right : I → T)
    (r : ℝ)
    (hvariance : 0 < P.varianceProxy)
    (hr : ∀ i : I, P.dist (left i) (right i) ≤ r)
    (hr_pos : 0 < r)
    (hcard : 1 < Fintype.card I) :
    finiteExpectation P.weight
      (fun ω => finiteSup (fun i : I => P.X ω (right i) - P.X ω (left i))) ≤
      Real.sqrt (2 * P.varianceProxy * r ^ 2 * Real.log (Fintype.card I : ℝ)) := by
  let L := Real.log (Fintype.card I : ℝ)
  let q := P.varianceProxy * r ^ 2
  have hL : 0 < L := by
    have hcard_real : (1 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hcard
    simpa [L] using Real.log_pos hcard_real
  have hq : 0 < q := by
    simp [q]
    positivity
  let lam := Real.sqrt (2 * L / q)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos_of_pos (by positivity)
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun i : I => P.X ω (right i) - P.X ω (left i)))
        ≤ (Real.log (Fintype.card I : ℝ) +
            lam ^ 2 * P.varianceProxy * r ^ 2 / 2) / lam :=
          increment_family_expectedSup_le_of_radius_log P left right lam r
            hlam hr hr_pos.le
    _ = Real.sqrt (2 * P.varianceProxy * r ^ 2 * Real.log (Fintype.card I : ℝ)) := by
          have hopt := sqrt_entropy_optimizer_identity hL hq
          dsimp [lam]
          simpa [L, q, mul_assoc, mul_left_comm, mul_comm] using hopt

/-- Finite chaining bound with radius/MGF-derived scale budgets. Each scale
budget is justified by a radius bound and the finite entropy condition
`exp(λ²σ²r_j²/2 - λ·budget_j) ≤ 1 / |T|`; the existing chaining theorem then
sums those budgets. -/
theorem finite_chaining_expectation_bound_of_radius_budgets
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (lam : ℝ) (hlam : 0 < lam)
    (radius budget : ℕ → ℝ)
    (hradius_nonneg : ∀ j ∈ Finset.range m, 0 ≤ radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ t : T,
      P.dist (π j t) (π (j + 1) t) ≤ radius j)
    (hbudget : ∀ j ∈ Finset.range m,
      Real.exp (lam ^ 2 * P.varianceProxy * radius j ^ 2 / 2 - lam * budget j) ≤
        (Fintype.card T : ℝ)⁻¹) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m, budget j :=
  finite_chaining_expectation_bound P π m hlast budget
    (fun j hj =>
      projection_increment_expectedSup_le_of_radius P π j lam (radius j) (budget j)
        hlam (hradius j hj) (hradius_nonneg j hj) (hbudget j hj))

/-- Log-cardinality finite chaining bound. Radius-bounded sub-Gaussian
projection increments yield the explicit finite entropy budget
`(log |T| + λ²σ²r_j²/2) / λ` at each scale, and the finite chaining theorem
sums those budgets. -/
theorem finite_chaining_expectation_bound_of_radius_log
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (lam : ℝ) (hlam : 0 < lam)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ j ∈ Finset.range m, 0 ≤ radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ t : T,
      P.dist (π j t) (π (j + 1) t) ≤ radius j) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m,
          (Real.log (Fintype.card T : ℝ) +
            lam ^ 2 * P.varianceProxy * radius j ^ 2 / 2) / lam :=
  finite_chaining_expectation_bound P π m hlast
    (fun j =>
      (Real.log (Fintype.card T : ℝ) +
        lam ^ 2 * P.varianceProxy * radius j ^ 2 / 2) / lam)
    (fun j hj =>
      projection_increment_expectedSup_le_of_radius_log P π j lam (radius j)
        hlam (hradius j hj) (hradius_nonneg j hj))

/-- Square-root finite chaining bound. This is the optimized finite-index
sub-Gaussian chaining form for radius-bounded projection increments. -/
theorem finite_chaining_expectation_bound_of_radius_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (hvariance : 0 < P.varianceProxy)
    (radius : ℕ → ℝ)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ t : T,
      P.dist (π j t) (π (j + 1) t) ≤ radius j)
    (hcard : 1 < Fintype.card T) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
            Real.log (Fintype.card T : ℝ)) :=
  finite_chaining_expectation_bound P π m hlast
    (fun j =>
      Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
        Real.log (Fintype.card T : ℝ)))
    (fun j hj =>
      projection_increment_expectedSup_le_of_radius_sqrt P π j (radius j)
        hvariance (hradius j hj) (hradius_pos j hj) hcard)

/-- Finite chaining with an explicit finite increment family at each scale.

For each level `j`, the maps `left j`, `right j` describe a finite family of
candidate increments indexed by `I j`, and `select j` says every projection
increment in the chain is represented in that finite family. The result
combines finite chaining with the finite-max sub-Gaussian entropy budget
`sqrt(2 σ² r_j² log |I_j|)`.

This is a finite-sample, finite-index chaining theorem; it is a tutorial-grade
stepping stone toward Dudley-style arguments, not a continuous entropy
integral. -/
theorem finite_chaining_expectation_bound_of_increment_families_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hlast : ∀ t : T, π m t = t)
    (hvariance : 0 < P.varianceProxy)
    (I : ℕ → Type*) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (left right : ∀ j : ℕ, I j → T)
    (select : ∀ j : ℕ, T → I j)
    (hleft : ∀ j ∈ Finset.range m, ∀ t : T, left j (select j t) = π j t)
    (hright : ∀ j ∈ Finset.range m, ∀ t : T, right j (select j t) = π (j + 1) t)
    (radius : ℕ → ℝ)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ i : I j,
      P.dist (left j i) (right j i) ≤ radius j)
    (hcard : ∀ j ∈ Finset.range m, 1 < Fintype.card (I j)) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
            Real.log (Fintype.card (I j) : ℝ)) := by
  refine finite_chaining_expectation_bound P π m hlast
    (fun j =>
      Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
        Real.log (Fintype.card (I j) : ℝ))) ?_
  intro j hj
  have hpoint : ∀ ω : Ω,
      finiteSup (fun t : T => P.X ω (π (j + 1) t) - P.X ω (π j t)) ≤
        finiteSup (fun i : I j => P.X ω (right j i) - P.X ω (left j i)) := by
    intro ω
    unfold finiteSup
    apply Finset.sup'_le
    intro t _
    have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset (I j)))
      (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
      (Finset.mem_univ (select j t))
    simpa [hleft j hj t, hright j hj t] using hsel
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup
              (fun i : I j => P.X ω (right j i) - P.X ω (left j i))) :=
          finiteExpectation_mono P.weight_nonneg hpoint
    _ ≤ Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
          Real.log (Fintype.card (I j) : ℝ)) :=
          increment_family_expectedSup_le_of_radius_sqrt P (left j) (right j)
            (radius j) hvariance (hradius j hj) (hradius_pos j hj) (hcard j hj)

/-- Projected finite chaining over a finite parameter domain `U`, with an
explicit finite increment family at each scale. The process is indexed by an
ambient type `T`, which need not be finite. -/
theorem finite_projected_chaining_expectation_bound_of_increment_families_sqrt_over
    [Fintype Ω] {U : Type*} [Fintype U] [Nonempty U]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → U → T) (m : ℕ)
    (hvariance : 0 < P.varianceProxy)
    (I : ℕ → Type*) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (left right : ∀ j : ℕ, I j → T)
    (select : ∀ j : ℕ, U → I j)
    (hleft : ∀ j ∈ Finset.range m, ∀ u : U, left j (select j u) = π j u)
    (hright : ∀ j ∈ Finset.range m, ∀ u : U, right j (select j u) = π (j + 1) u)
    (radius : ℕ → ℝ)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ i : I j,
      P.dist (left j i) (right j i) ≤ radius j)
    (hcard : ∀ j ∈ Finset.range m, 1 < Fintype.card (I j)) :
    finiteExpectation P.weight (fun ω => finiteSup (fun u => P.X ω (π m u))) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun u => P.X ω (π 0 u))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
            Real.log (Fintype.card (I j) : ℝ)) := by
  refine finite_projected_chaining_expectation_bound_over P π m
    (fun j =>
      Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
        Real.log (Fintype.card (I j) : ℝ))) ?_
  intro j hj
  have hpoint : ∀ ω : Ω,
      finiteSup (fun u : U => P.X ω (π (j + 1) u) - P.X ω (π j u)) ≤
        finiteSup (fun i : I j => P.X ω (right j i) - P.X ω (left j i)) := by
    intro ω
    unfold finiteSup
    apply Finset.sup'_le
    intro u _
    have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset (I j)))
      (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
      (Finset.mem_univ (select j u))
    simpa [hleft j hj u, hright j hj u] using hsel
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun u => P.X ω (π (j + 1) u) - P.X ω (π j u)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup
              (fun i : I j => P.X ω (right j i) - P.X ω (left j i))) :=
          finiteExpectation_mono P.weight_nonneg hpoint
    _ ≤ Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
          Real.log (Fintype.card (I j) : ℝ)) :=
          increment_family_expectedSup_le_of_radius_sqrt P (left j) (right j)
            (radius j) hvariance (hradius j hj) (hradius_pos j hj) (hcard j hj)

/-- Projected finite chaining with an explicit finite increment family at each
scale. This version bounds the terminal projected supremum and therefore does
not require the final projection to be the identity. -/
theorem finite_projected_chaining_expectation_bound_of_increment_families_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (π : ℕ → T → T) (m : ℕ)
    (hvariance : 0 < P.varianceProxy)
    (I : ℕ → Type*) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (left right : ∀ j : ℕ, I j → T)
    (select : ∀ j : ℕ, T → I j)
    (hleft : ∀ j ∈ Finset.range m, ∀ t : T, left j (select j t) = π j t)
    (hright : ∀ j ∈ Finset.range m, ∀ t : T, right j (select j t) = π (j + 1) t)
    (radius : ℕ → ℝ)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < radius j)
    (hradius : ∀ j ∈ Finset.range m, ∀ i : I j,
      P.dist (left j i) (right j i) ≤ radius j)
    (hcard : ∀ j ∈ Finset.range m, 1 < Fintype.card (I j)) :
    finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π m t))) ≤
      finiteExpectation P.weight (fun ω => finiteSup (fun t => P.X ω (π 0 t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
            Real.log (Fintype.card (I j) : ℝ)) := by
  refine finite_projected_chaining_expectation_bound P π m
    (fun j =>
      Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
        Real.log (Fintype.card (I j) : ℝ))) ?_
  intro j hj
  have hpoint : ∀ ω : Ω,
      finiteSup (fun t : T => P.X ω (π (j + 1) t) - P.X ω (π j t)) ≤
        finiteSup (fun i : I j => P.X ω (right j i) - P.X ω (left j i)) := by
    intro ω
    unfold finiteSup
    apply Finset.sup'_le
    intro t _
    have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset (I j)))
      (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
      (Finset.mem_univ (select j t))
    simpa [hleft j hj t, hright j hj t] using hsel
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup
              (fun i : I j => P.X ω (right j i) - P.X ω (left j i))) :=
          finiteExpectation_mono P.weight_nonneg hpoint
    _ ≤ Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
          Real.log (Fintype.card (I j) : ℝ)) :=
          increment_family_expectedSup_le_of_radius_sqrt P (left j) (right j)
            (radius j) hvariance (hradius j hj) (hradius_pos j hj) (hcard j hj)

/-- One-step square-root entropy bound for increments between two finite-net
projections, paying `log` of the realized projection-pair family. This is the
finite-net entropy version of the one-level sub-Gaussian max bound. -/
theorem net_increment_expectedSup_le_pair_sqrt
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
    (hcard : 1 < Fintype.card (FiniteNet.ProjectionPair N₀ N₁)) :
    finiteExpectation P.weight
      (fun ω => finiteSup
        (fun t => P.X ω (N₁.projection t) - P.X ω (N₀.projection t))) ≤
      Real.sqrt (2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 *
        Real.log (Fintype.card (FiniteNet.ProjectionPair N₀ N₁) : ℝ)) := by
  let left : FiniteNet.ProjectionPair N₀ N₁ → T := fun pair => N₀.center pair.1.1
  let right : FiniteNet.ProjectionPair N₀ N₁ → T := fun pair => N₁.center pair.1.2
  have hpoint : ∀ ω : Ω,
      finiteSup (fun t => P.X ω (N₁.projection t) - P.X ω (N₀.projection t)) ≤
        finiteSup (fun pair : FiniteNet.ProjectionPair N₀ N₁ =>
          P.X ω (right pair) - P.X ω (left pair)) := by
    intro ω
    unfold finiteSup
    apply Finset.sup'_le
    intro t _
    have hsel := Finset.le_sup'
      (s := (Finset.univ : Finset (FiniteNet.ProjectionPair N₀ N₁)))
      (fun pair : FiniteNet.ProjectionPair N₀ N₁ =>
        P.X ω (right pair) - P.X ω (left pair))
      (Finset.mem_univ (FiniteNet.projectionPairOf N₀ N₁ t))
    simpa [left, right, FiniteNet.projection, FiniteNet.projectionPairOf] using hsel
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun t => P.X ω (N₁.projection t) - P.X ω (N₀.projection t)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup (fun pair : FiniteNet.ProjectionPair N₀ N₁ =>
              P.X ω (right pair) - P.X ω (left pair))) :=
          finiteExpectation_mono P.weight_nonneg hpoint
    _ ≤ Real.sqrt (2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 *
          Real.log (Fintype.card (FiniteNet.ProjectionPair N₀ N₁) : ℝ)) := by
          refine increment_family_expectedSup_le_of_radius_sqrt P left right
            (N₀.radius + N₁.radius) hvariance ?_ hradius_pos hcard
          intro pair
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
          simpa [left, right, hdist₀] using hpair

/-- One-step finite-net entropy bound using the product of the two finite
covering numbers. This is a readable corollary of the sharper projection-pair
bound. -/
theorem net_increment_expectedSup_le_coveringNumber_sqrt
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
    (hcard : 1 < Fintype.card (FiniteNet.ProjectionPair N₀ N₁)) :
    finiteExpectation P.weight
      (fun ω => finiteSup
        (fun t => P.X ω (N₁.projection t) - P.X ω (N₀.projection t))) ≤
      Real.sqrt (2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 *
        Real.log (N₀.coveringNumber * N₁.coveringNumber : ℝ)) := by
  refine (net_increment_expectedSup_le_pair_sqrt P N₀ N₁ hdist₀ hdist₁
    hsymm htri hvariance hradius_pos hcard).trans ?_
  apply Real.sqrt_le_sqrt
  have hcoef_nonneg : 0 ≤ 2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 := by
    nlinarith [P.varianceProxy_nonneg, sq_nonneg (N₀.radius + N₁.radius)]
  exact mul_le_mul_of_nonneg_left
    (FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul N₀ N₁)
    hcoef_nonneg

/-- Finite multiscale chaining for a sequence of finite nets, with each scale
paying entropy for the realized projection-pair family between consecutive
nets. This is a finite, scalar, finite-sample chaining statement and remains
short of the continuous Dudley entropy integral. -/
theorem finite_chaining_expectation_bound_of_net_sequence_pairs_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1)))) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log (Fintype.card
              (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
  let π : ℕ → T → T := fun j => (N j).projection
  let I : ℕ → Type _ := fun j => FiniteNet.ProjectionPair (N j) (N (j + 1))
  let left : ∀ j : ℕ, I j → T := fun j pair => (N j).center pair.1.1
  let right : ∀ j : ℕ, I j → T := fun j pair => (N (j + 1)).center pair.1.2
  let select : ∀ j : ℕ, T → I j := fun j t => FiniteNet.projectionPairOf (N j) (N (j + 1)) t
  let radius : ℕ → ℝ := fun j => (N j).radius + (N (j + 1)).radius
  have hleft : ∀ j ∈ Finset.range m, ∀ t : T, left j (select j t) = π j t := by
    intro j _ t
    simp [left, select, π, I, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hright : ∀ j ∈ Finset.range m, ∀ t : T, right j (select j t) = π (j + 1) t := by
    intro j _ t
    simp [right, select, π, I, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hradius : ∀ j ∈ Finset.range m, ∀ pair : I j,
      P.dist (left j pair) (right j pair) ≤ radius j := by
    intro j _ pair
    have hpair :=
      FiniteNet.projectionPair_dist_le_radius_sum
        (N j) (N (j + 1))
        (by rw [hdist (j + 1), hdist j])
        (by
          intro s t
          rw [hdist j]
          exact hsymm s t)
        (by
          intro x y z
          rw [hdist j]
          exact htri x y z)
        pair
    simpa [left, right, radius, hdist j] using hpair
  simpa [π, I, left, right, select, radius] using
    finite_chaining_expectation_bound_of_increment_families_sqrt
      P π m hlast hvariance I left right select hleft hright radius
      hradius_pos hradius hcard

/-- Finite multiscale chaining for a sequence of finite nets, stated with the
product of consecutive covering numbers at each scale. This follows from the
projection-pair version plus the finite cardinality bound
`|pairs_j| ≤ N_j * N_{j+1}`. -/
theorem finite_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1)))) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  refine (finite_chaining_expectation_bound_of_net_sequence_pairs_sqrt
    P A N m hdist hsymm htri hlast hvariance hradius_pos hcard).trans ?_
  have hsum :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))) ≤
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    have hcoef_nonneg :
        0 ≤ 2 * P.varianceProxy * ((N j).radius + (N (j + 1)).radius) ^ 2 := by
      nlinarith [P.varianceProxy_nonneg, sq_nonneg ((N j).radius + (N (j + 1)).radius)]
    exact mul_le_mul_of_nonneg_left
      (FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul (N j) (N (j + 1)))
      hcoef_nonneg
  exact add_le_add_right hsum _

/-- Projected finite multiscale chaining for a sequence of finite nets, stated
with products of consecutive covering numbers. The left side is the expected
supremum after the terminal projection `(N m).projection`, not the full
finite supremum of the original process. -/
theorem finite_projected_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1)))) :
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N m).projection t))) ≤
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  let π : ℕ → T → T := fun j => (N j).projection
  let I : ℕ → Type _ := fun j => FiniteNet.ProjectionPair (N j) (N (j + 1))
  let left : ∀ j : ℕ, I j → T := fun j pair => (N j).center pair.1.1
  let right : ∀ j : ℕ, I j → T := fun j pair => (N (j + 1)).center pair.1.2
  let select : ∀ j : ℕ, T → I j := fun j t => FiniteNet.projectionPairOf (N j) (N (j + 1)) t
  let radius : ℕ → ℝ := fun j => (N j).radius + (N (j + 1)).radius
  have hleft : ∀ j ∈ Finset.range m, ∀ t : T, left j (select j t) = π j t := by
    intro j _ t
    simp [left, select, π, I, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hright : ∀ j ∈ Finset.range m, ∀ t : T, right j (select j t) = π (j + 1) t := by
    intro j _ t
    simp [right, select, π, I, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hradius : ∀ j ∈ Finset.range m, ∀ pair : I j,
      P.dist (left j pair) (right j pair) ≤ radius j := by
    intro j _ pair
    have hpair :=
      FiniteNet.projectionPair_dist_le_radius_sum
        (N j) (N (j + 1))
        (by rw [hdist (j + 1), hdist j])
        (by
          intro s t
          rw [hdist j]
          exact hsymm s t)
        (by
          intro x y z
          rw [hdist j]
          exact htri x y z)
        pair
    simpa [left, right, radius, hdist j] using hpair
  have hpair_bound :
      finiteExpectation P.weight
          (fun ω => finiteSup (fun t => P.X ω ((N m).projection t))) ≤
        finiteExpectation P.weight
          (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
              Real.log (Fintype.card (I j) : ℝ)) := by
    simpa [π, I, left, right, select, radius] using
      finite_projected_chaining_expectation_bound_of_increment_families_sqrt
        P π m hvariance I left right select hleft hright radius
        hradius_pos hradius hcard
  refine hpair_bound.trans ?_
  have hsum :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))) ≤
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    have hcoef_nonneg :
        0 ≤ 2 * P.varianceProxy * ((N j).radius + (N (j + 1)).radius) ^ 2 := by
      nlinarith [P.varianceProxy_nonneg, sq_nonneg ((N j).radius + (N (j + 1)).radius)]
    exact mul_le_mul_of_nonneg_left
      (FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul (N j) (N (j + 1)))
      hcoef_nonneg
  exact add_le_add_right hsum _

/-- Projected finite multiscale chaining over the terminal finite-net image.
The ambient process index type `T` is not assumed finite; the finite supremum
ranges over the indices actually hit by the terminal net projection.

This is a projected-net boundary lift toward total-bounded Dudley:
finite terminal image, finite scale range, scalar process, no measurable
supremum over arbitrary classes. -/
theorem finite_projectedNet_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1)))) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))) ≤
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  let U := FiniteNet.ProjectedIndex (N m)
  let π : ℕ → U → T :=
    fun j u => (N j).projection (FiniteNet.ProjectedIndex.source (N m) u)
  let I : ℕ → Type _ := fun j => FiniteNet.ProjectionPair (N j) (N (j + 1))
  let left : ∀ j : ℕ, I j → T := fun j pair => (N j).center pair.1.1
  let right : ∀ j : ℕ, I j → T := fun j pair => (N (j + 1)).center pair.1.2
  let select : ∀ j : ℕ, U → I j :=
    fun j u => FiniteNet.projectionPairOf (N j) (N (j + 1))
      (FiniteNet.ProjectedIndex.source (N m) u)
  let radius : ℕ → ℝ := fun j => (N j).radius + (N (j + 1)).radius
  have hleft : ∀ j ∈ Finset.range m, ∀ u : U, left j (select j u) = π j u := by
    intro j _ u
    simp [left, select, π, I, U, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hright : ∀ j ∈ Finset.range m, ∀ u : U, right j (select j u) = π (j + 1) u := by
    intro j _ u
    simp [right, select, π, I, U, FiniteNet.projection, FiniteNet.projectionPairOf]
  have hradius : ∀ j ∈ Finset.range m, ∀ pair : I j,
      P.dist (left j pair) (right j pair) ≤ radius j := by
    intro j _ pair
    have hpair :=
      FiniteNet.projectionPair_dist_le_radius_sum
        (N j) (N (j + 1))
        (by rw [hdist (j + 1), hdist j])
        (by
          intro s t
          rw [hdist j]
          exact hsymm s t)
        (by
          intro x y z
          rw [hdist j]
          exact htri x y z)
        pair
    simpa [left, right, radius, hdist j] using hpair
  have hpair_bound :
      finiteExpectation P.weight
          (fun ω => finiteSup (fun u : U => P.X ω (π m u))) ≤
        finiteExpectation P.weight
          (fun ω => finiteSup (fun u : U => P.X ω (π 0 u))) +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy * radius j ^ 2 *
              Real.log (Fintype.card (I j) : ℝ)) := by
    simpa [π, I, left, right, select, radius] using
      finite_projected_chaining_expectation_bound_of_increment_families_sqrt_over
        P π m hvariance I left right select hleft hright radius
        hradius_pos hradius hcard
  refine ?_
  have hterminal :
      (fun ω => finiteSup
          (fun u : U => P.X ω ((N m).center u.1))) =
        (fun ω => finiteSup (fun u : U => P.X ω (π m u))) := by
    funext ω
    exact congrArg (fun f : U → ℝ => finiteSup f) (by
      funext u
      simp [π, U, FiniteNet.ProjectedIndex.projection_source_eq_center])
  rw [hterminal]
  refine hpair_bound.trans ?_
  have hsum :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))) ≤
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    have hcoef_nonneg :
        0 ≤ 2 * P.varianceProxy * ((N j).radius + (N (j + 1)).radius) ^ 2 := by
      nlinarith [P.varianceProxy_nonneg, sq_nonneg ((N j).radius + (N (j + 1)).radius)]
    exact mul_le_mul_of_nonneg_left
      (FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul (N j) (N (j + 1)))
      hcoef_nonneg
  exact add_le_add_right hsum _

/-- Finite Dudley-style entropy sum over realized projection-pair families.
For a finite sub-Gaussian process and a finite sequence of finite nets, the
expected finite supremum is bounded by a coarse-net term plus a finite entropy
sum. Each scale pays the adjacent-radius coefficient times the square root of
the log-cardinality of the realized projection pairs between consecutive nets.

This is a finite, scalar-valued, finite-index theorem. It is not the continuous
Dudley entropy integral; infinite classes, separability, and measurable suprema
over arbitrary function classes remain outside this statement. -/
theorem finite_dudley_entropy_sum_projection_pairs
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log (Fintype.card
              (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
  refine (finite_chaining_expectation_bound_of_net_sequence_pairs_sqrt
    P A N m hdist hsymm htri hlast hvariance hradius_pos hcard).trans ?_
  have hsum :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))) =
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log (Fintype.card
              (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hradius_nonneg : 0 ≤ (N j).radius + (N (j + 1)).radius := by
      nlinarith [(N j).radius_nonneg, (N (j + 1)).radius_nonneg]
    simpa [mul_assoc] using
      sqrt_entropy_scale_eq P.varianceProxy
        ((N j).radius + (N (j + 1)).radius)
        (Real.log (Fintype.card
          (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))
        P.varianceProxy_nonneg hradius_nonneg
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log (Fintype.card
              (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ))
        ≤ coarseBudget +
            ∑ j ∈ Finset.range m,
              Real.sqrt (2 * P.varianceProxy *
                ((N j).radius + (N (j + 1)).radius) ^ 2 *
                Real.log (Fintype.card
                  (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
          exact add_le_add_left hcoarse _
    _ = coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              Real.sqrt (Real.log (Fintype.card
                (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
        rw [hsum]

/-- Finite Dudley-style entropy sum stated with products of consecutive finite
covering numbers. This is the public-facing finite entropy-sum corollary of the
projection-pair theorem: each scale pays the adjacent-radius coefficient times
`sqrt (log (N_j * N_{j+1}))`.

The statement is intentionally finite: finite support, finite index set, finite
nets, finite number of scales, and scalar real-valued processes only. It is not
the continuous Dudley integral. -/
theorem finite_dudley_entropy_sum_coveringNumbers
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  refine (finite_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
    P A N m hdist hsymm htri hlast hvariance hradius_pos hcard).trans ?_
  have hsum :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))) =
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hradius_nonneg : 0 ≤ (N j).radius + (N (j + 1)).radius := by
      nlinarith [(N j).radius_nonneg, (N (j + 1)).radius_nonneg]
    simpa [mul_assoc] using
      sqrt_entropy_scale_eq P.varianceProxy
        ((N j).radius + (N (j + 1)).radius)
        (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
        P.varianceProxy_nonneg hradius_nonneg
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
        ≤ coarseBudget +
            ∑ j ∈ Finset.range m,
              Real.sqrt (2 * P.varianceProxy *
                ((N j).radius + (N (j + 1)).radius) ^ 2 *
                Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
          exact add_le_add_left hcoarse _
    _ = coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              Real.sqrt (Real.log
                ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
        rw [hsum]

/-- Finite Dudley-style entropy sum over realized projection-pair families
with an explicit geometric radius schedule. If each adjacent pair of finite
nets moves by at most `radiusScale / 2^j`, the entropy sum can be stated using
that dyadic radius budget directly.

This is still a finite theorem: finite support, finite index set, finitely many
nets, scalar real-valued process, and a finite sum. It is a bridge from the
projection-pair finite entropy sum toward a later Dudley-style integral, not a
continuous entropy integral. -/
theorem finite_dudley_entropy_sum_projection_pairs_geometric_radius
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            Real.sqrt (Real.log (Fintype.card
              (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
  refine (finite_dudley_entropy_sum_projection_pairs
    P A N m coarseBudget hdist hsymm htri hlast hvariance hradius_pos hcard hcoarse).trans ?_
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  have hcoef_nonneg : 0 ≤ Real.sqrt (2 * P.varianceProxy) :=
    Real.sqrt_nonneg _
  have hentropy_nonneg :
      0 ≤ Real.sqrt (Real.log (Fintype.card
        (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) :=
    Real.sqrt_nonneg _
  have hterm :
      Real.sqrt (2 * P.varianceProxy) *
          ((N j).radius + (N (j + 1)).radius) *
          Real.sqrt (Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          Real.sqrt (Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hradius_geometric j hj) hcoef_nonneg)
      hentropy_nonneg
  simpa [mul_assoc] using hterm

/-- Finite Dudley-style entropy sum with products of consecutive finite
covering numbers and an explicit geometric radius schedule. If each adjacent
pair of finite nets moves by at most `radiusScale / 2^j`, each scale pays that
dyadic radius budget times the square root of the log product of adjacent
finite covering numbers.

The statement is intentionally finite; continuous Dudley, infinite classes,
separability, and measurability of arbitrary suprema remain outside this
statement. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_radius
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
  refine (finite_dudley_entropy_sum_coveringNumbers
    P A N m coarseBudget hdist hsymm htri hlast hvariance hradius_pos hcard hcoarse).trans ?_
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  have hcoef_nonneg : 0 ≤ Real.sqrt (2 * P.varianceProxy) :=
    Real.sqrt_nonneg _
  have hentropy_nonneg :
      0 ≤ Real.sqrt (Real.log
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) :=
    Real.sqrt_nonneg _
  have hterm :
      Real.sqrt (2 * P.varianceProxy) *
          ((N j).radius + (N (j + 1)).radius) *
          Real.sqrt (Real.log
            ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          Real.sqrt (Real.log
            ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hradius_geometric j hj) hcoef_nonneg)
      hentropy_nonneg
  simpa [mul_assoc] using hterm

/-- Finite Dudley-style projection-pair entropy bound with a geometric radius
schedule and an explicit per-scale entropy envelope. This packages the finite
dyadic sum in a form suited for later comparison with entropy integrals:
provide `entropyBudget j` above the square-root log-cardinality at each finite
scale, and the theorem pays the finite weighted sum of those budgets.

This is not a continuous Dudley integral. The process, nets, index family, and
number of scales are all finite. -/
theorem finite_dudley_entropy_sum_projection_pairs_geometric_entropy_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ) (entropyBudget : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log (Fintype.card
        (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤ entropyBudget j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyBudget j := by
  refine (finite_dudley_entropy_sum_projection_pairs_geometric_radius
    P A N m coarseBudget radiusScale hdist hsymm htri hlast hvariance
    hradius_pos hradius_geometric hcard hcoarse).trans ?_
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  have hcoef_nonneg : 0 ≤ Real.sqrt (2 * P.varianceProxy) :=
    Real.sqrt_nonneg _
  have htwo_pow_pos : 0 < (2 : ℝ) ^ j := by
    positivity
  have hgeom_nonneg : 0 ≤ radiusScale / (2 : ℝ) ^ j :=
    div_nonneg hradiusScale_nonneg htwo_pow_pos.le
  have hscale_nonneg :
      0 ≤ Real.sqrt (2 * P.varianceProxy) * (radiusScale / (2 : ℝ) ^ j) :=
    mul_nonneg hcoef_nonneg hgeom_nonneg
  have hterm :
      Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          Real.sqrt (Real.log (Fintype.card
            (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyBudget j := by
    exact mul_le_mul_of_nonneg_left (hentropy j hj) hscale_nonneg
  simpa [mul_assoc] using hterm

/-- Finite Dudley-style covering-number entropy bound with a geometric radius
schedule and an explicit per-scale entropy envelope. At each finite scale,
`entropyBudget j` upper-bounds `sqrt (log (N_j * N_{j+1}))`; the conclusion is
a finite dyadic entropy-budget sum.

This remains finite and scalar-valued. It is a preparation lemma for a later
Dudley-style integral comparison, not an infinite-class or continuous-entropy
theorem. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_entropy_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ) (entropyBudget : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤ entropyBudget j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget +
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyBudget j := by
  refine (finite_dudley_entropy_sum_coveringNumbers_geometric_radius
    P A N m coarseBudget radiusScale hdist hsymm htri hlast hvariance
    hradius_pos hradius_geometric hcard hcoarse).trans ?_
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  have hcoef_nonneg : 0 ≤ Real.sqrt (2 * P.varianceProxy) :=
    Real.sqrt_nonneg _
  have htwo_pow_pos : 0 < (2 : ℝ) ^ j := by
    positivity
  have hgeom_nonneg : 0 ≤ radiusScale / (2 : ℝ) ^ j :=
    div_nonneg hradiusScale_nonneg htwo_pow_pos.le
  have hscale_nonneg :
      0 ≤ Real.sqrt (2 * P.varianceProxy) * (radiusScale / (2 : ℝ) ^ j) :=
    mul_nonneg hcoef_nonneg hgeom_nonneg
  have hterm :
      Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          Real.sqrt (Real.log
            ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyBudget j := by
    exact mul_le_mul_of_nonneg_left (hentropy j hj) hscale_nonneg
  simpa [mul_assoc] using hterm

/-- Finite dyadic geometric-series budget used by the public discrete Dudley
corollaries. It records the elementary fact `∑_{j < m} 2^{-j} ≤ 2` in the
same real-valued denominator form as the radius schedules below. -/
lemma dyadic_inverse_sum_le_two (m : ℕ) :
    (∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹) ≤ 2 := by
  simpa [one_div, inv_pow] using sum_geometric_two_le m

/-- Dyadic annulus identity for the geometric radius schedule. The radius at
scale `j` is twice the width of the dyadic annulus between scales `j` and
`j + 1`. This is the elementary bridge used to rewrite finite Dudley-style
dyadic sums in integral-comparison language. -/
lemma dyadic_radius_eq_two_mul_annulus_width (radiusScale : ℝ) (j : ℕ) :
    radiusScale / (2 : ℝ) ^ j =
      2 * (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) := by
  field_simp [pow_succ]
  ring

/-- Nonnegativity of dyadic annulus widths under a nonnegative top radius. -/
lemma dyadic_annulus_width_nonneg {radiusScale : ℝ} (hradiusScale_nonneg : 0 ≤ radiusScale)
    (j : ℕ) :
    0 ≤ radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1) := by
  have hpow_pos : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hwidth :
      radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1) =
        radiusScale / (2 : ℝ) ^ (j + 1) := by
    field_simp [pow_succ]
    ring
  rw [hwidth]
  exact div_nonneg hradiusScale_nonneg hpow_pos.le

/-- The dyadic annulus at scale `j` has twice the width of the next lower
annulus. This is the elementary constant-loss in the shifted integral
comparison for antitone entropy profiles. -/
lemma dyadic_annulus_width_eq_two_mul_next (radiusScale : ℝ) (j : ℕ) :
    radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1) =
      2 * (radiusScale / (2 : ℝ) ^ (j + 1) -
        radiusScale / (2 : ℝ) ^ (j + 2)) := by
  field_simp [pow_succ]
  ring

/-- If a function is bounded below by a constant on an interval, then its
interval integral dominates the rectangle with that height. This is a small
analysis adapter used to keep the Dudley integral-comparison hypotheses
explicit. -/
lemma interval_const_mul_le_integral_of_le_on
    {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hle : ∀ x ∈ Set.Icc a b, c ≤ f x) :
    (b - a) * c ≤ ∫ x in a..b, f x := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hmono :
      (∫ x in a..b, (fun _ : ℝ => c) x) ≤ ∫ x in a..b, f x := by
    exact intervalIntegral.integral_mono_on
      (μ := MeasureTheory.volume) hab hconst hf hle
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- For an antitone entropy profile, the value at the upper endpoint of a
shifted dyadic annulus is a lower bound throughout that annulus, so the
corresponding rectangle is bounded by the interval integral over the annulus.

This is finite-scale analysis only; it does not assert a continuous Dudley
integral or any measurable-supremum theorem. -/
lemma dyadic_lowerEndpoint_mul_width_le_intervalIntegral
    {radiusScale : ℝ} (entropyAtRadius : ℝ → ℝ) (j : ℕ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    (radiusScale / (2 : ℝ) ^ (j + 1) -
        radiusScale / (2 : ℝ) ^ (j + 2)) *
      entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) ≤
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε := by
  have hab :
      radiusScale / (2 : ℝ) ^ (j + 2) ≤
        radiusScale / (2 : ℝ) ^ (j + 1) := by
    have hwidth := dyadic_annulus_width_nonneg hradiusScale_nonneg (j + 1)
    linarith
  exact interval_const_mul_le_integral_of_le_on hab hintervalIntegrable
    (by
      intro ε hε
      exact hentropy_antitone hε.2)

/-- Finite dyadic entropy-integral budget. This is an upper Riemann-style sum
over dyadic annuli, not a continuous Dudley entropy integral. The term at
scale `j` is the annulus width
`radiusScale / 2^j - radiusScale / 2^(j+1)` times a supplied finite entropy
envelope. -/
def finiteDyadicEntropyIntegralBudget (radiusScale : ℝ) (m : ℕ)
    (entropyEnvelope : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range m,
    (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
      entropyEnvelope j

/-- One-step dyadic entropy budget for a constant entropy envelope. -/
theorem finiteDyadicEntropyIntegralBudget_one_const
    (radiusScale entropy : ℝ) :
    finiteDyadicEntropyIntegralBudget radiusScale 1 (fun _ : ℕ => entropy) =
      (radiusScale / 2) * entropy := by
  rw [finiteDyadicEntropyIntegralBudget]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero]
  ring

/-- Finite dyadic entropy-at-radius upper sum. The value
`entropyAtRadius (radiusScale / 2^(j+1))` is sampled at the lower endpoint of
the dyadic annulus `(radiusScale / 2^(j+1), radiusScale / 2^j]`.

This is a finite Riemann-style upper sum used as an interface to later
entropy-integral estimates. It is not a definition of a continuous integral. -/
def finiteDyadicEntropyAtRadiusUpperSum (radiusScale : ℝ) (m : ℕ)
    (entropyAtRadius : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range m,
    (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
      entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))

/-- Analytic domination of the finite dyadic entropy-at-radius upper sum by a
finite shifted-annulus interval-integral budget.

For antitone entropy profiles, the lower-endpoint upper sum on annulus `j` is
controlled by twice the interval integral over annulus `j + 1`. The theorem is
therefore a finite dyadic Riemann-step bridge toward Dudley-style integral
language. It is not a continuous Dudley integral theorem, does not involve
separability, and does not claim measurable suprema over arbitrary classes. -/
theorem finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤
      2 * ∑ j ∈ Finset.range m,
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε := by
  rw [finiteDyadicEntropyAtRadiusUpperSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hstep :=
    dyadic_lowerEndpoint_mul_width_le_intervalIntegral
      (entropyAtRadius := entropyAtRadius) (j := j) hradiusScale_nonneg
      hentropy_antitone (hintervalIntegrable j hj)
  have hwidth := dyadic_annulus_width_eq_two_mul_next radiusScale j
  calc
    (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))
        =
      2 * ((radiusScale / (2 : ℝ) ^ (j + 1) -
          radiusScale / (2 : ℝ) ^ (j + 2)) *
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) := by
          rw [hwidth]
          ring
    _ ≤ 2 * (∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε) := by
          exact mul_le_mul_of_nonneg_left hstep (by norm_num : 0 ≤ (2 : ℝ))

/-- Scalar-budget wrapper for the shifted-annulus interval-integral comparison.
The caller supplies the finite integral budget, which later can be discharged
from a true continuous entropy-integral estimate.

This theorem remains finite-scale and finite-sum; it is the analytic
domination layer needed before a continuous Dudley wrapper can be stated. -/
theorem finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_intervalIntegralBudget
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (integralBudget : ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintegralBudget :
      (∑ j ∈ Finset.range m,
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε) ≤ integralBudget) :
    finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤
      2 * integralBudget := by
  have hupper :=
    finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum
      (m := m) (entropyAtRadius := entropyAtRadius) hradiusScale_nonneg
      hentropy_antitone hintervalIntegrable
  exact hupper.trans
    (mul_le_mul_of_nonneg_left hintegralBudget (by norm_num : 0 ≤ (2 : ℝ)))

/--
The shifted dyadic annuli used by
`finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum`
compose into one truncated interval. This is a finite adjacent-interval
identity only: it does not assert any continuous Dudley theorem, separability
statement, or measurable supremum over an arbitrary class.
-/
lemma shiftedDyadicIntervalIntegrable_truncated
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    IntervalIntegrable entropyAtRadius MeasureTheory.volume
      (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hprev : ∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1)) := by
        intro j hj
        exact hintervalIntegrable j (Finset.mem_range.mpr
          (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self m)))
      have htail :
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (m + 2))
            (radiusScale / (2 : ℝ) ^ (m + 1)) := by
        simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
          hintervalIntegrable m (by simp)
      have hhead :
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
        ih hprev
      exact htail.trans hhead

/--
The finite shifted-annulus interval-integral budget is exactly the interval
integral over the truncated dyadic range `[radiusScale / 2^(m+1), radiusScale/2]`.

This is the analytic bookkeeping bridge from a finite dyadic annulus budget to
a single truncated interval integral. It remains finite-scale and makes no
continuous Dudley, separability, or arbitrary measurable-supremum claim.
-/
theorem shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    (∑ j ∈ Finset.range m,
      ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
        (radiusScale / (2 : ℝ) ^ (j + 1)),
        entropyAtRadius ε) =
      ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        entropyAtRadius ε := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hprev : ∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1)) := by
        intro j hj
        exact hintervalIntegrable j (Finset.mem_range.mpr
          (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self m)))
      have htail :
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (m + 2))
            (radiusScale / (2 : ℝ) ^ (m + 1)) := by
        simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
          hintervalIntegrable m (by simp)
      have hhead :
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
        shiftedDyadicIntervalIntegrable_truncated
          (m := m) (entropyAtRadius := entropyAtRadius) hprev
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals
          (μ := MeasureTheory.volume) htail hhead
      rw [Finset.sum_range_succ, ih hprev]
      simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using hadd

/--
Finite dyadic entropy-at-radius upper sum dominated by one truncated interval
integral. This composes the shifted-annulus comparison with adjacent-interval
additivity.

The statement is deliberately finite: a finite dyadic scale range, scalar
entropy profile, explicit antitonicity and interval-integrability hypotheses,
and no continuous Dudley, separability, or arbitrary measurable-supremum claim.
-/
theorem finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤
      2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        entropyAtRadius ε := by
  have hupper :=
    finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_shifted_intervalIntegral_sum
      (m := m) (entropyAtRadius := entropyAtRadius) hradiusScale_nonneg
      hentropy_antitone hintervalIntegrable
  have hsum :=
    shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral
      (m := m) (entropyAtRadius := entropyAtRadius) hintervalIntegrable
  simpa [hsum] using hupper

/-- Finite prefix-sup entropy envelope. At scale `j`, this records the maximum
of the first `j + 1` scale budgets. It is a finite, discrete monotone envelope;
it is not a continuous metric-entropy function. -/
def finitePrefixSupEnvelope (entropyAtScale : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (Finset.range (j + 1)).sup' (by simp) entropyAtScale

/-- The finite prefix-sup envelope of a constant scale budget is constant. -/
theorem finitePrefixSupEnvelope_const (entropy : ℝ) :
    finitePrefixSupEnvelope (fun _ : ℕ => entropy) =
      (fun _ : ℕ => entropy) := by
  funext j
  simp [finitePrefixSupEnvelope]

/-- Each scale budget is bounded by its finite prefix-sup envelope. -/
lemma le_finitePrefixSupEnvelope (entropyAtScale : ℕ → ℝ) (j : ℕ) :
    entropyAtScale j ≤ finitePrefixSupEnvelope entropyAtScale j := by
  unfold finitePrefixSupEnvelope
  exact Finset.le_sup' entropyAtScale (by simp)

/-- A monotone finite scale budget is already equal to its prefix-sup envelope. -/
theorem finitePrefixSupEnvelope_eq_self_of_monotone
    {entropyAtScale : ℕ → ℝ} (hmono : Monotone entropyAtScale) :
    finitePrefixSupEnvelope entropyAtScale = entropyAtScale := by
  funext j
  apply le_antisymm
  · unfold finitePrefixSupEnvelope
    exact Finset.sup'_le _ _ fun k hk =>
      hmono (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · exact le_finitePrefixSupEnvelope entropyAtScale j

/-- The finite prefix-sup envelope is monotone in the scale index. -/
lemma monotone_finitePrefixSupEnvelope (entropyAtScale : ℕ → ℝ) :
    Monotone (finitePrefixSupEnvelope entropyAtScale) := by
  intro i j hij
  unfold finitePrefixSupEnvelope
  have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ hij)
  have hnonempty : (Finset.range (i + 1)).Nonempty := by simp
  simpa using Finset.sup'_mono (f := entropyAtScale) hsubset hnonempty

/-- Compare the finite dyadic entropy budget with an entropy-at-radius upper
sum. The hypothesis only samples the external entropy envelope at the lower
dyadic endpoint for each finite annulus.

This is a finite upper-sum comparison, not a continuous Dudley integral
theorem and not an infinite-class statement. -/
theorem finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum
    {radiusScale : ℝ} (m : ℕ) (entropyEnvelope : ℕ → ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      entropyEnvelope j ≤ entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) :
    finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope ≤
      finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius := by
  rw [finiteDyadicEntropyIntegralBudget, finiteDyadicEntropyAtRadiusUpperSum]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hentropyAtRadius j hj)
    (dyadic_annulus_width_nonneg hradiusScale_nonneg j)

/-- Compare the finite dyadic entropy budget with a supplied scalar upper
budget. A later analytic layer can discharge `hupperSum` from an actual
entropy-integral estimate; this theorem itself remains finite and discrete. -/
theorem finiteDyadicEntropyIntegralBudget_le_of_entropyAtRadiusUpperSum_le
    {radiusScale : ℝ} (m : ℕ) (entropyEnvelope : ℕ → ℝ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      entropyEnvelope j ≤ entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hupperSum :
      finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤ integralBudget) :
    finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope ≤ integralBudget :=
  (finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum
    m entropyEnvelope entropyAtRadius hradiusScale_nonneg hentropyAtRadius).trans hupperSum

/-- Finite discrete Dudley-style projection-pair bound with a uniform entropy
cap across dyadic scales. If every scale's projection-pair entropy term is at
most `entropyCap`, the finite dyadic entropy-budget sum is bounded by the
geometric-series budget `2 * sqrt(2σ²) * radiusScale * entropyCap`.

This is still finite-index, finite-net, and scalar-valued. It is a discrete
finite entropy bound, not a continuous entropy integral. -/
theorem finite_dudley_entropy_sum_projection_pairs_geometric_uniform_entropy
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale entropyCap : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropyCap_nonneg : 0 ≤ entropyCap)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log (Fintype.card
        (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤ entropyCap)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap := by
  refine (finite_dudley_entropy_sum_projection_pairs_geometric_entropy_budget
    P A N m coarseBudget radiusScale (fun _ => entropyCap) hdist hsymm htri
    hlast hvariance hradiusScale_nonneg hradius_pos hradius_geometric hcard
    hentropy hcoarse).trans ?_
  refine add_le_add_right ?_ coarseBudget
  let c : ℝ := Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hradiusScale_nonneg)
      hentropyCap_nonneg
  have hgeom : (∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹) ≤ 2 :=
    dyadic_inverse_sum_le_two m
  have hsum_eq :
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyCap) =
        c * ∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyCap)
        = c * ∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹ := hsum_eq
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hgeom hc_nonneg
    _ = 2 * Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap := by
        ring

/-- Finite discrete Dudley-style covering-number bound with a uniform entropy
cap across dyadic scales. If
`sqrt (log (N_j * N_{j+1})) ≤ entropyCap` at every finite scale, the dyadic
covering-number entropy sum is bounded by
`2 * sqrt(2σ²) * radiusScale * entropyCap`.

This is the finite discrete refinement of the entropy-budget wrapper. It does
not introduce a continuous entropy integral or infinite-class assumptions. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_uniform_entropy
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale entropyCap : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropyCap_nonneg : 0 ≤ entropyCap)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤ entropyCap)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap := by
  refine (finite_dudley_entropy_sum_coveringNumbers_geometric_entropy_budget
    P A N m coarseBudget radiusScale (fun _ => entropyCap) hdist hsymm htri
    hlast hvariance hradiusScale_nonneg hradius_pos hradius_geometric hcard
    hentropy hcoarse).trans ?_
  refine add_le_add_right ?_ coarseBudget
  let c : ℝ := Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hradiusScale_nonneg)
      hentropyCap_nonneg
  have hgeom : (∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹) ≤ 2 :=
    dyadic_inverse_sum_le_two m
  have hsum_eq :
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyCap) =
        c * ∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyCap)
        = c * ∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹ := hsum_eq
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hgeom hc_nonneg
    _ = 2 * Real.sqrt (2 * P.varianceProxy) * radiusScale * entropyCap := by
        ring

/-- Finite discrete Dudley-style projection-pair bound rewritten through
dyadic annulus budgets. The hypothesis `hannulus` says each scale's
`annulus width * entropyBudget` is bounded by an explicit finite budget; the
conclusion pays `2 * sqrt(2σ²)` times the finite sum of those budgets.

This is an integral-comparison bridge for the finite chaining scaffold. It is
not a continuous entropy integral and does not introduce infinite classes,
separability assumptions, or arbitrary measurable suprema. -/
theorem finite_dudley_entropy_sum_projection_pairs_geometric_annulus_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyBudget annulusBudget : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log (Fintype.card
        (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤ entropyBudget j)
    (hannulus : ∀ j ∈ Finset.range m,
      (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
          entropyBudget j ≤ annulusBudget j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        ∑ j ∈ Finset.range m, annulusBudget j := by
  refine (finite_dudley_entropy_sum_projection_pairs_geometric_entropy_budget
    P A N m coarseBudget radiusScale entropyBudget hdist hsymm htri hlast hvariance
    hradiusScale_nonneg hradius_pos hradius_geometric hcard hentropy hcoarse).trans ?_
  refine add_le_add_right ?_ coarseBudget
  calc
    (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyBudget j)
        = ∑ j ∈ Finset.range m,
            2 * Real.sqrt (2 * P.varianceProxy) *
              ((radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
                entropyBudget j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [dyadic_radius_eq_two_mul_annulus_width radiusScale j]
          ring
    _ ≤ ∑ j ∈ Finset.range m,
            2 * Real.sqrt (2 * P.varianceProxy) * annulusBudget j := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hannulus j hj)
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 2 * Real.sqrt (2 * P.varianceProxy) *
          ∑ j ∈ Finset.range m, annulusBudget j := by
        rw [Finset.mul_sum]

/-- Finite discrete Dudley-style covering-number bound rewritten through
dyadic annulus budgets. This is the covering-number version of
`finite_dudley_entropy_sum_projection_pairs_geometric_annulus_budget`.

The theorem remains finite: finite outcome support, finite index class, finite
nets, scalar-valued process, and a finite dyadic scale range. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_annulus_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyBudget annulusBudget : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤ entropyBudget j)
    (hannulus : ∀ j ∈ Finset.range m,
      (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
          entropyBudget j ≤ annulusBudget j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        ∑ j ∈ Finset.range m, annulusBudget j := by
  refine (finite_dudley_entropy_sum_coveringNumbers_geometric_entropy_budget
    P A N m coarseBudget radiusScale entropyBudget hdist hsymm htri hlast hvariance
    hradiusScale_nonneg hradius_pos hradius_geometric hcard hentropy hcoarse).trans ?_
  refine add_le_add_right ?_ coarseBudget
  calc
    (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy) *
          (radiusScale / (2 : ℝ) ^ j) *
          entropyBudget j)
        = ∑ j ∈ Finset.range m,
            2 * Real.sqrt (2 * P.varianceProxy) *
              ((radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
                entropyBudget j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [dyadic_radius_eq_two_mul_annulus_width radiusScale j]
          ring
    _ ≤ ∑ j ∈ Finset.range m,
            2 * Real.sqrt (2 * P.varianceProxy) * annulusBudget j := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hannulus j hj)
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 2 * Real.sqrt (2 * P.varianceProxy) *
          ∑ j ∈ Finset.range m, annulusBudget j := by
        rw [Finset.mul_sum]

/-- Finite discrete Dudley-style projection-pair bound controlled by a finite
dyadic entropy-integral budget. The supplied `entropyEnvelope` dominates each
finite projection-pair entropy term, and the conclusion pays the finite
upper Riemann-style annulus sum
`finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope`.

This is still finite-index, finite-net, scalar-valued chaining. It is a bridge
toward Dudley-style integral language, not the continuous Dudley integral and
not an infinite-class theorem. -/
theorem finite_dudley_entropy_sum_projection_pairs_geometric_integral_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyBudget entropyEnvelope : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log (Fintype.card
        (FiniteNet.ProjectionPair (N j) (N (j + 1))) : ℝ)) ≤ entropyBudget j)
    (henvelope : ∀ j ∈ Finset.range m, entropyBudget j ≤ entropyEnvelope j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
  refine (finite_dudley_entropy_sum_projection_pairs_geometric_annulus_budget
    P A N m coarseBudget radiusScale entropyBudget
      (fun j =>
        (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
          entropyEnvelope j)
    hdist hsymm htri hlast hvariance hradiusScale_nonneg hradius_pos
    hradius_geometric hcard hentropy ?_ hcoarse)
  intro j hj
  exact mul_le_mul_of_nonneg_left (henvelope j hj)
    (dyadic_annulus_width_nonneg hradiusScale_nonneg j)

/-- Finite discrete Dudley-style covering-number bound controlled by a finite
dyadic entropy-integral budget. This is the covering-number version of
`finite_dudley_entropy_sum_projection_pairs_geometric_integral_budget`.

The theorem remains finite: finite outcome support, finite index class, finite
nets, scalar-valued process, and a finite dyadic scale range. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyBudget entropyEnvelope : ℕ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hentropy : ∀ j ∈ Finset.range m,
      Real.sqrt (Real.log
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤ entropyBudget j)
    (henvelope : ∀ j ∈ Finset.range m, entropyBudget j ≤ entropyEnvelope j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
  refine (finite_dudley_entropy_sum_coveringNumbers_geometric_annulus_budget
    P A N m coarseBudget radiusScale entropyBudget
      (fun j =>
        (radiusScale / (2 : ℝ) ^ j - radiusScale / (2 : ℝ) ^ (j + 1)) *
          entropyEnvelope j)
    hdist hsymm htri hlast hvariance hradiusScale_nonneg hradius_pos
    hradius_geometric hcard hentropy ?_ hcoarse)
  intro j hj
  exact mul_le_mul_of_nonneg_left (henvelope j hj)
    (dyadic_annulus_width_nonneg hradiusScale_nonneg j)

/-- Finite discrete Dudley-style covering-number bound where the entropy
envelope is constructed from finite covering-number upper bounds. The
`coverCount j` values are external finite upper bounds on the product
`N_j * N_{j+1}` at each dyadic scale; the theorem uses their finite prefix sup
as a monotone entropy envelope inside `finiteDyadicEntropyIntegralBudget`.

This is still finite-index, finite-net, scalar-valued chaining over finitely
many scales. It packages the finite entropy envelope needed for the
Dudley-style upper-sum wrapper; it is not a continuous Dudley integral and not
an infinite-class result. -/
theorem finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m
          (finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log (coverCount j : ℝ)))) := by
  refine finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget
    P A N m coarseBudget radiusScale
      (fun j => Real.sqrt (Real.log (coverCount j : ℝ)))
      (finitePrefixSupEnvelope
        (fun j => Real.sqrt (Real.log (coverCount j : ℝ))))
      hdist hsymm htri hlast hvariance hradiusScale_nonneg hradius_pos
      hradius_geometric hcard ?_ ?_ hcoarse
  · intro j hj
    have hpair_le_product :
        Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))) ≤
          (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      FiniteNet.projectionPair_card_le_coveringNumber_mul (N j) (N (j + 1))
    have hproduct_pos_nat :
        0 < (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      Nat.zero_lt_of_lt (lt_of_lt_of_le (hcard j hj) hpair_le_product)
    have hproduct_pos_real :
        0 < ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) := by
      exact_mod_cast hproduct_pos_nat
    have hproduct_le_cover_real :
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) ≤
          (coverCount j : ℝ) := by
      exact_mod_cast hcoverCount j hj
    exact Real.sqrt_le_sqrt (Real.log_le_log hproduct_pos_real hproduct_le_cover_real)
  · intro j _hj
    exact le_finitePrefixSupEnvelope
      (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j

/-- Projected finite Dudley-style covering-number bound with a dyadic
entropy-integral budget. The conclusion controls the finite supremum after the
terminal projection `(N m).projection`; unlike the full finite Dudley theorem,
it does not require `(N m).projection t = t`.

This remains a finite-index, finite-net, finite-scale theorem. It is a bridge
toward total-bounded Dudley statements, not a continuous Dudley integral and
not a measurable supremum over an arbitrary class. -/
theorem finite_projected_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N m).projection t))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m
          (finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log (coverCount j : ℝ)))) := by
  let entropyAtScale : ℕ → ℝ :=
    fun j => Real.sqrt (Real.log (coverCount j : ℝ))
  let entropyEnvelope : ℕ → ℝ := finitePrefixSupEnvelope entropyAtScale
  have hchain :=
    finite_projected_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
      P A N m hdist hsymm htri hvariance hradius_pos hcard
  have hsum_geometric :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))) ≤
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j := by
    apply Finset.sum_le_sum
    intro j hj
    have hradius_nonneg : 0 ≤ (N j).radius + (N (j + 1)).radius := by
      nlinarith [(N j).radius_nonneg, (N (j + 1)).radius_nonneg]
    have hpair_le_product :
        Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))) ≤
          (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      FiniteNet.projectionPair_card_le_coveringNumber_mul (N j) (N (j + 1))
    have hproduct_pos_nat :
        0 < (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      Nat.zero_lt_of_lt (lt_of_lt_of_le (hcard j hj) hpair_le_product)
    have hproduct_pos_real :
        0 < ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) := by
      exact_mod_cast hproduct_pos_nat
    have hproduct_le_cover_real :
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) ≤
          (coverCount j : ℝ) := by
      exact_mod_cast hcoverCount j hj
    have hentropy :
        Real.sqrt (Real.log
            ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
          entropyAtScale j := by
      exact Real.sqrt_le_sqrt
        (Real.log_le_log hproduct_pos_real hproduct_le_cover_real)
    have hscale_nonneg :
        0 ≤ Real.sqrt (2 * P.varianceProxy) * ((N j).radius + (N (j + 1)).radius) :=
      mul_nonneg (Real.sqrt_nonneg _) hradius_nonneg
    have hfirst :
        Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) =
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
      simpa [mul_assoc] using
        sqrt_entropy_scale_eq P.varianceProxy
          ((N j).radius + (N (j + 1)).radius)
          (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
          P.varianceProxy_nonneg hradius_nonneg
    have hentropy_step :
        Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            entropyAtScale j := by
      exact mul_le_mul_of_nonneg_left hentropy hscale_nonneg
    have hgeom_step :
        Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            entropyAtScale j ≤
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hradius_geometric j hj) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    calc
      Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
          = Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              Real.sqrt (Real.log
                ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := hfirst
      _ ≤ Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              entropyAtScale j := hentropy_step
      _ ≤ Real.sqrt (2 * P.varianceProxy) *
              (radiusScale / (2 : ℝ) ^ j) *
              entropyAtScale j := hgeom_step
  have hsum_integral :
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j) ≤
        2 * Real.sqrt (2 * P.varianceProxy) *
          finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
    calc
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j)
          =
        ∑ j ∈ Finset.range m,
          2 * Real.sqrt (2 * P.varianceProxy) *
            ((radiusScale / (2 : ℝ) ^ j -
                radiusScale / (2 : ℝ) ^ (j + 1)) *
              entropyAtScale j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [dyadic_radius_eq_two_mul_annulus_width radiusScale j]
          ring
      _ ≤
        ∑ j ∈ Finset.range m,
          2 * Real.sqrt (2 * P.varianceProxy) *
            ((radiusScale / (2 : ℝ) ^ j -
                radiusScale / (2 : ℝ) ^ (j + 1)) *
              entropyEnvelope j) := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (le_finitePrefixSupEnvelope entropyAtScale j)
              (dyadic_annulus_width_nonneg hradiusScale_nonneg j))
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      _ =
        2 * Real.sqrt (2 * P.varianceProxy) *
          finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
          rw [finiteDyadicEntropyIntegralBudget, Finset.mul_sum]
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t => P.X ω ((N m).projection t)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup (fun t => P.X ω ((N 0).projection t))) +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy *
              ((N j).radius + (N (j + 1)).radius) ^ 2 *
              Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := hchain
    _ ≤ coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy *
              ((N j).radius + (N (j + 1)).radius) ^ 2 *
              Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
          exact add_le_add hcoarse le_rfl
    _ ≤ coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy) *
              (radiusScale / (2 : ℝ) ^ j) *
              entropyAtScale j := by
          exact add_le_add le_rfl hsum_geometric
    _ ≤ coarseBudget +
          2 * Real.sqrt (2 * P.varianceProxy) *
            finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
          exact add_le_add le_rfl hsum_integral

/-- Projected finite-net Dudley-style covering-number bound with a dyadic
entropy-integral budget. The ambient index type `T` need not be finite: the
left side ranges over the finite image of the terminal net projection.

This is a finite-image, finite-scale bridge toward total-bounded Dudley
statements. It does not assert a continuous Dudley integral, separability, or
a measurable supremum over an arbitrary class. -/
theorem finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        finiteDyadicEntropyIntegralBudget radiusScale m
          (finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log (coverCount j : ℝ)))) := by
  let entropyAtScale : ℕ → ℝ :=
    fun j => Real.sqrt (Real.log (coverCount j : ℝ))
  let entropyEnvelope : ℕ → ℝ := finitePrefixSupEnvelope entropyAtScale
  have hchain :=
    finite_projectedNet_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt
      P A N m hdist hsymm htri hvariance hradius_pos hcard
  have hsum_geometric :
      (∑ j ∈ Finset.range m,
        Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))) ≤
        ∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j := by
    apply Finset.sum_le_sum
    intro j hj
    have hradius_nonneg : 0 ≤ (N j).radius + (N (j + 1)).radius := by
      nlinarith [(N j).radius_nonneg, (N (j + 1)).radius_nonneg]
    have hpair_le_product :
        Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))) ≤
          (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      FiniteNet.projectionPair_card_le_coveringNumber_mul (N j) (N (j + 1))
    have hproduct_pos_nat :
        0 < (N j).coveringNumber * (N (j + 1)).coveringNumber :=
      Nat.zero_lt_of_lt (lt_of_lt_of_le (hcard j hj) hpair_le_product)
    have hproduct_pos_real :
        0 < ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) := by
      exact_mod_cast hproduct_pos_nat
    have hproduct_le_cover_real :
        ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) ≤
          (coverCount j : ℝ) := by
      exact_mod_cast hcoverCount j hj
    have hentropy :
        Real.sqrt (Real.log
            ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
          entropyAtScale j := by
      exact Real.sqrt_le_sqrt
        (Real.log_le_log hproduct_pos_real hproduct_le_cover_real)
    have hscale_nonneg :
        0 ≤ Real.sqrt (2 * P.varianceProxy) * ((N j).radius + (N (j + 1)).radius) :=
      mul_nonneg (Real.sqrt_nonneg _) hradius_nonneg
    have hfirst :
        Real.sqrt (2 * P.varianceProxy *
            ((N j).radius + (N (j + 1)).radius) ^ 2 *
            Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) =
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
      simpa [mul_assoc] using
        sqrt_entropy_scale_eq P.varianceProxy
          ((N j).radius + (N (j + 1)).radius)
          (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
          P.varianceProxy_nonneg hradius_nonneg
    have hentropy_step :
        Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt (Real.log
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
          Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            entropyAtScale j := by
      exact mul_le_mul_of_nonneg_left hentropy hscale_nonneg
    have hgeom_step :
        Real.sqrt (2 * P.varianceProxy) *
            ((N j).radius + (N (j + 1)).radius) *
            entropyAtScale j ≤
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hradius_geometric j hj) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    calc
      Real.sqrt (2 * P.varianceProxy *
          ((N j).radius + (N (j + 1)).radius) ^ 2 *
          Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
          = Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              Real.sqrt (Real.log
                ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := hfirst
      _ ≤ Real.sqrt (2 * P.varianceProxy) *
              ((N j).radius + (N (j + 1)).radius) *
              entropyAtScale j := hentropy_step
      _ ≤ Real.sqrt (2 * P.varianceProxy) *
              (radiusScale / (2 : ℝ) ^ j) *
              entropyAtScale j := hgeom_step
  have hsum_integral :
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j) ≤
        2 * Real.sqrt (2 * P.varianceProxy) *
          finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
    calc
      (∑ j ∈ Finset.range m,
          Real.sqrt (2 * P.varianceProxy) *
            (radiusScale / (2 : ℝ) ^ j) *
            entropyAtScale j)
          =
        ∑ j ∈ Finset.range m,
          2 * Real.sqrt (2 * P.varianceProxy) *
            ((radiusScale / (2 : ℝ) ^ j -
                radiusScale / (2 : ℝ) ^ (j + 1)) *
              entropyAtScale j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [dyadic_radius_eq_two_mul_annulus_width radiusScale j]
          ring
      _ ≤
        ∑ j ∈ Finset.range m,
          2 * Real.sqrt (2 * P.varianceProxy) *
            ((radiusScale / (2 : ℝ) ^ j -
                radiusScale / (2 : ℝ) ^ (j + 1)) *
              entropyEnvelope j) := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (le_finitePrefixSupEnvelope entropyAtScale j)
              (dyadic_annulus_width_nonneg hradiusScale_nonneg j))
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      _ =
        2 * Real.sqrt (2 * P.varianceProxy) *
          finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
          rw [finiteDyadicEntropyIntegralBudget, Finset.mul_sum]
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1)))
        ≤ finiteExpectation P.weight
            (fun ω => finiteSup
              (fun u : FiniteNet.ProjectedIndex (N m) =>
                P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy *
              ((N j).radius + (N (j + 1)).radius) ^ 2 *
              Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := hchain
    _ ≤ coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy *
              ((N j).radius + (N (j + 1)).radius) ^ 2 *
              Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
          exact add_le_add hcoarse le_rfl
    _ ≤ coarseBudget +
          ∑ j ∈ Finset.range m,
            Real.sqrt (2 * P.varianceProxy) *
              (radiusScale / (2 : ℝ) ^ j) *
              entropyAtScale j := by
          exact add_le_add le_rfl hsum_geometric
    _ ≤ coarseBudget +
          2 * Real.sqrt (2 * P.varianceProxy) *
            finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope := by
          exact add_le_add le_rfl hsum_integral

/-- Projected finite-net Dudley-style covering-number bound compared against a
finite entropy-at-radius upper-sum/integral budget. The hypothesis
`hentropyAtRadius` says the finite prefix-sup covering envelope at scale `j` is
controlled by an external entropy function sampled at the lower dyadic
endpoint. The hypothesis `hupperSum` is where a later analytic layer can bound
that finite upper sum by a scalar integral budget.

This is still a finite-image, finite-scale theorem. It does not prove a
continuous Dudley integral, separability, infinite classes, or measurable
suprema over arbitrary index families. -/
theorem finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hupperSum :
      finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤ integralBudget)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
  let entropyEnvelope : ℕ → ℝ :=
    finitePrefixSupEnvelope (fun j => Real.sqrt (Real.log (coverCount j : ℝ)))
  have hbase :=
    finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
      (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (coverCount := coverCount) hdist hsymm htri
      hvariance hradiusScale_nonneg hradius_pos hradius_geometric hcard
      hcoverCount hcoarse
  have hbudget :
      finiteDyadicEntropyIntegralBudget radiusScale m entropyEnvelope ≤ integralBudget := by
    exact finiteDyadicEntropyIntegralBudget_le_of_entropyAtRadiusUpperSum_le
      m entropyEnvelope entropyAtRadius integralBudget hradiusScale_nonneg
      (by
        intro j hj
        simpa [entropyEnvelope] using hentropyAtRadius j hj)
      hupperSum
  have hcoeff_nonneg : 0 ≤ 2 * Real.sqrt (2 * P.varianceProxy) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  exact hbase.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget hcoeff_nonneg))

/-- Projected finite-net Dudley-style covering-number bound with the supplied
finite entropy-at-radius upper sum discharged by a shifted-annulus interval
integral budget.

The analytic hypotheses are explicit: `entropyAtRadius` is antitone, it is
interval-integrable on each shifted dyadic annulus used by the comparison, and
the finite sum of those annulus integrals is bounded by `integralBudget`.
The extra factor `2` comes from comparing each dyadic upper-sum rectangle to
the next lower dyadic annulus.

This is still finite-image and finite-scale. It is an analytic bridge toward
Dudley-style integral language, not a continuous Dudley theorem, not a
separability theorem, and not a measurable arbitrary-supremum theorem. -/
theorem finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_intervalIntegral_comparison
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintegralBudget :
      (∑ j ∈ Finset.range m,
        ∫ ε in (radiusScale / (2 : ℝ) ^ (j + 2))..
          (radiusScale / (2 : ℝ) ^ (j + 1)),
          entropyAtRadius ε) ≤ integralBudget)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
  have hupperSum :
      finiteDyadicEntropyAtRadiusUpperSum radiusScale m entropyAtRadius ≤
        2 * integralBudget := by
    exact finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_intervalIntegralBudget
      (m := m) (entropyAtRadius := entropyAtRadius)
      (integralBudget := integralBudget) hradiusScale_nonneg
      hentropy_antitone hintervalIntegrable hintegralBudget
  have hbase :=
    finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison
      (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (coverCount := coverCount)
      (entropyAtRadius := entropyAtRadius) (integralBudget := 2 * integralBudget)
      hdist hsymm htri hvariance hradiusScale_nonneg hradius_pos
      hradius_geometric hcard hcoverCount hentropyAtRadius hupperSum hcoarse
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1)))
        ≤ coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            (2 * integralBudget) := hbase
    _ = coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
          ring

/-- Projected finite-net Dudley-style covering-number bound with the finite
entropy-at-radius upper sum discharged by one truncated interval integral.

This composes the shifted-annulus comparison with adjacent-interval additivity:
the finite shifted-annulus integral budget is the integral over
`[radiusScale / 2^(m+1), radiusScale / 2]`. The statement is still finite-image
and finite-scale. It is a bridge toward continuous Dudley language, not a
continuous Dudley theorem, not a separability theorem, and not a measurable
arbitrary-supremum theorem. -/
theorem finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (entropyAtRadius : ℝ → ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) := by
  refine
    finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_intervalIntegral_comparison
      (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (coverCount := coverCount)
      (entropyAtRadius := entropyAtRadius)
      (integralBudget :=
        ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε)
      hdist hsymm htri hvariance hradiusScale_nonneg hradius_pos
      hradius_geometric hcard hcoverCount hentropyAtRadius hentropy_antitone
      hintervalIntegrable ?_ hcoarse
  exact le_of_eq
    (shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral
      (m := m) (entropyAtRadius := entropyAtRadius) hintervalIntegrable)

/-- Boundary adapter from projected finite-net Dudley to a supplied supremum
functional.

The caller supplies `supFunctional : Ω → ℝ` together with the explicit terminal
approximation hypothesis that it is pointwise bounded by the terminal projected
finite-net supremum plus `terminalError`. This keeps the theorem at the finite
continuous-boundary interface: no arbitrary measurable supremum, no
separability theorem, and no infinite-class supremum is constructed here. -/
theorem finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ) (terminalError : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hterminal :
      ∀ ω : Ω,
        supFunctional ω ≤
          finiteSup
            (fun u : FiniteNet.ProjectedIndex (N m) =>
              P.X ω ((N m).center u.1)) + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) + terminalError := by
  let projectedSup : Ω → ℝ :=
    fun ω => finiteSup
      (fun u : FiniteNet.ProjectedIndex (N m) => P.X ω ((N m).center u.1))
  have hadapter :
      finiteExpectation P.weight supFunctional ≤
        finiteExpectation P.weight projectedSup + terminalError :=
    finiteExpectation_supFunctional_le_projected_add_terminalError
      P.weight_nonneg P.weight_sum_one supFunctional projectedSup terminalError
      hterminal
  have hprojected :
      finiteExpectation P.weight projectedSup ≤
        coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) := by
    exact
      finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
        (P := P) (A := A) (N := N) (m := m)
        (coarseBudget := coarseBudget) (radiusScale := radiusScale)
        (coverCount := coverCount) (entropyAtRadius := entropyAtRadius)
        hdist hsymm htri hvariance hradiusScale_nonneg hradius_pos
        hradius_geometric hcard hcoverCount hentropyAtRadius hentropy_antitone
        hintervalIntegrable hcoarse
  linarith

/-- Boundary adapter from projected finite-net Dudley to a supplied supremum
functional through an explicit finite skeleton.

This is the next continuous-boundary layer after
`finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison`.
Instead of asking callers to provide the final terminal approximation in one
bundled hypothesis, it separates the assumptions:
* `hseparable` bounds the supplied supremum functional by a finite skeleton,
  with error `separabilityError`;
* `hterminalApprox` bounds each skeleton point by its terminal net projection,
  with error `terminalError`.

The theorem remains finite-scale and scalar-valued. It does not construct an
arbitrary measurable supremum, prove separability, or claim a full continuous
Dudley theorem.
-/
theorem finite_separableSupFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    [Fintype Ω] [Nonempty T]
    {K : Type*} [Fintype K] [Nonempty K]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (coverCount : ℕ → ℕ)
    (entropyAtRadius : ℝ → ℝ)
    (embed : K → T) (supFunctional : Ω → ℝ)
    (separabilityError terminalError : ℝ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1))))
    (hcoverCount : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log (coverCount j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hseparable :
      ∀ ω : Ω,
        supFunctional ω ≤
          finiteSup (fun k : K => P.X ω (embed k)) + separabilityError)
    (hterminalApprox :
      ∀ ω : Ω, ∀ k : K,
        P.X ω (embed k) ≤
          P.X ω ((N m).projection (embed k)) + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (N m) =>
            P.X ω ((N 0).projection (FiniteNet.ProjectedIndex.source (N m) u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) + (separabilityError + terminalError) := by
  have hterminal :
      ∀ ω : Ω,
        supFunctional ω ≤
          finiteSup
            (fun u : FiniteNet.ProjectedIndex (N m) =>
              P.X ω ((N m).center u.1)) +
            (separabilityError + terminalError) := by
    intro ω
    exact supFunctional_le_projectedSup_add_of_skeleton_terminal
      (N m) embed (P.X ω) (supFunctional ω)
      separabilityError terminalError (hseparable ω) (hterminalApprox ω)
  exact
    finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
      (P := P) (A := A) (N := N) (m := m)
      (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (coverCount := coverCount) (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional)
      (terminalError := separabilityError + terminalError)
      hdist hsymm htri hvariance hradiusScale_nonneg hradius_pos
      hradius_geometric hcard hcoverCount hentropyAtRadius hentropy_antitone
      hintervalIntegrable hterminal hcoarse

/-- One-step square-root entropy bound for increments between two finite-net
projections. This packages the finite-net geometry lemma with the optimized
sub-Gaussian max bound. -/
theorem net_increment_expectedSup_le_sqrt
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
    (hcard : 1 < Fintype.card T) :
    finiteExpectation P.weight
      (fun ω => finiteSup
        (fun t => P.X ω (N₁.projection t) - P.X ω (N₀.projection t))) ≤
      Real.sqrt (2 * P.varianceProxy * (N₀.radius + N₁.radius) ^ 2 *
        Real.log (Fintype.card T : ℝ)) := by
  let π : ℕ → T → T := fun k =>
    if k = 0 then N₀.projection else N₁.projection
  have hdist : ∀ t : T,
      P.dist (π 0 t) (π (0 + 1) t) ≤ N₀.radius + N₁.radius := by
    intro t
    have hpair :=
      FiniteNet.projection_pair_dist_le_radius_sum
        N₀ N₁ (by rw [hdist₀, hdist₁])
        (by
          intro s t
          rw [hdist₀]
          exact hsymm s t)
        (by
          intro x y z
          rw [hdist₀]
          exact htri x y z)
        t
    simpa [π, hdist₀] using hpair
  simpa [π] using
    projection_increment_expectedSup_le_of_radius_sqrt P π 0
      (N₀.radius + N₁.radius) hvariance hdist hradius_pos hcard

end FiniteSubGaussianProcess

end

end FormalSLT.Covering.FiniteSubGaussianChaining
