import Mathlib.Topology.MetricSpace.Pseudo.Basic
import FormalSLT.Covering.FiniteSubGaussianChaining

/-!
# Total-bounded Dudley bridge

This module starts the continuous/total-bounded Dudley lane without claiming a
continuous Dudley integral. The immediate goal is smaller and structural:
connect Mathlib's `TotallyBounded` metric-space API to the finite-net records
used by `FiniteSubGaussianChaining`.

The main construction extracts, from a totally bounded index space and a
positive radius, a bundled `FiniteNet` over the ambient metric distance. This
is the topology adapter needed before the finite dyadic chaining machinery can
be fed by total-bounded covering hypotheses.

Scope:

* metric index spaces, via `PseudoMetricSpace`;
* finite nets extracted at one positive scale;
* finite terminal wrappers that compose those nets with the existing finite
  Dudley entropy-budget theorem;
* no continuous entropy integral yet;
* no measurable supremum over arbitrary index classes yet.
-/

open Set
open scoped BigOperators Interval

namespace FormalSLT.Covering.TotalBoundedDudley

open FormalSLT.Covering.FiniteSubGaussianChaining

noncomputable section

universe u

variable {T : Type u}

/-- A finite net bundled with its finite index type.

`FiniteSubGaussianChaining.FiniteNet` is indexed by an explicit finite type of
centers. Mathlib's total-boundedness API returns finite sets of centers, so this
small bundle carries the finite subtype and the resulting `FiniteNet` together.
-/
structure BundledFiniteNet (T : Type u) where
  A : Type u
  instFintype : Fintype A
  instNonempty : Nonempty A
  net : @FiniteNet T A instFintype

namespace BundledFiniteNet

attribute [instance] instFintype instNonempty

/-- Cardinality of the bundled finite net. -/
def coveringNumber (B : BundledFiniteNet T) : ℕ :=
  @FiniteNet.coveringNumber T B.A B.instFintype B.net

end BundledFiniteNet

/-- Convert an explicit finite metric cover of the whole space into the
finite-net record used by the finite chaining layer. -/
def finiteNetOfCoverSet [PseudoMetricSpace T] [Nonempty T]
    (C : Set T) (hCfinite : C.Finite)
    (r : ℝ) (hr : 0 ≤ r)
    (hcover : ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ r) :
    BundledFiniteNet T := by
  classical
  let A : Type u := {c : T // c ∈ C}
  let instFintype : Fintype A := hCfinite.fintype
  have instNonempty : Nonempty A := by
    obtain ⟨t⟩ := (inferInstance : Nonempty T)
    obtain ⟨c, hc, _hc_dist⟩ := hcover t
    exact ⟨⟨c, hc⟩⟩
  let project : T → A := fun t =>
    ⟨Classical.choose (hcover t), (Classical.choose_spec (hcover t)).1⟩
  let N : @FiniteNet T A instFintype :=
    { dist := fun s t => dist s t
      dist_nonneg := fun s t => dist_nonneg
      center := fun a => a.1
      project := project
      radius := r
      radius_nonneg := hr
      covers := by
        intro t
        exact (Classical.choose_spec (hcover t)).2 }
  exact
    { A := A
      instFintype := instFintype
      instNonempty := instNonempty
      net := N }

/-- The identity finite net on a finite metric index type.

This is the terminal net used by the dyadic total-bounded wrapper: earlier
scales are supplied by total boundedness, while the final finite scale is exact
so the existing finite chaining telescope can close. -/
def identityBundledFiniteNet [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    BundledFiniteNet T := by
  classical
  let N : FiniteNet T T :=
    { dist := fun s t => dist s t
      dist_nonneg := fun s t => dist_nonneg
      center := id
      project := id
      radius := 0
      radius_nonneg := le_rfl
      covers := by
        intro t
        simp }
  exact
    { A := T
      instFintype := inferInstance
      instNonempty := inferInstance
      net := N }

@[simp] theorem identityBundledFiniteNet_radius
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    (identityBundledFiniteNet (T := T)).net.radius = 0 := by
  rfl

@[simp] theorem identityBundledFiniteNet_dist
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    (identityBundledFiniteNet (T := T)).net.dist = fun s t => dist s t := by
  rfl

@[simp] theorem identityBundledFiniteNet_projection
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] (t : T) :
    (identityBundledFiniteNet (T := T)).net.projection t = t := by
  rfl

/-- A totally bounded metric index space admits a finite metric cover at every
positive real radius. This is the Mathlib extraction step, stated with `dist`
and `≤` so it can feed `FiniteNet`. -/
theorem finiteMetricCoverOfTotallyBoundedUniv [PseudoMetricSpace T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set T, C.Finite ∧ ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ ε := by
  obtain ⟨C, _hC_subset, hCfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (s := Set.univ) hT ε hε
  refine ⟨C, hCfinite, ?_⟩
  intro t
  have ht : t ∈ (Set.univ : Set T) := by simp
  have ht_cover : t ∈ ⋃ y ∈ C, Metric.ball y ε := hcover ht
  simp only [mem_iUnion, Metric.mem_ball] at ht_cover
  obtain ⟨c, hc, hdist_lt⟩ := ht_cover
  exact ⟨c, hc, le_of_lt hdist_lt⟩

/-- Extract a bundled finite net from a totally bounded metric index space at
any positive radius. The net uses the ambient metric distance and covers every
point within radius `ε`. -/
def finiteNetOfTotallyBoundedUniv [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    BundledFiniteNet T := by
  classical
  let cover := finiteMetricCoverOfTotallyBoundedUniv (T := T) hT hε
  exact finiteNetOfCoverSet
    (Classical.choose cover)
    (Classical.choose_spec cover).1
    ε hε.le
    (Classical.choose_spec cover).2

/-- The finite net extracted from total boundedness uses the requested radius. -/
@[simp] theorem finiteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.radius = ε := by
  rfl

/-- The finite net extracted from total boundedness uses the ambient metric
distance. -/
@[simp] theorem finiteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.dist = fun s t => dist s t := by
  rfl

/-- The projection selected by the total-bounded finite net is within the
requested metric radius. -/
theorem finiteNetOfTotallyBoundedUniv_covers
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    (t : T) :
    dist t ((finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.projection t) ≤ ε := by
  simpa [finiteNetOfTotallyBoundedUniv_radius]
    using (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.projection_dist_le t

/-! ## Dyadic net schedule for the Dudley bridge -/

/-- Radius used for the dyadic finite-net schedule in the first
total-bounded Dudley bridge.

The extra `2^2` shrinkage leaves room for adjacent projection increments:
`r_j + r_{j+1} <= radiusScale / 2^j`. -/
def dyadicChainingNetRadius (radiusScale : ℝ) (j : ℕ) : ℝ :=
  radiusScale / (2 : ℝ) ^ (j + 2)

/-- Positivity of the dyadic net radius under a positive top scale. -/
theorem dyadicChainingNetRadius_pos {radiusScale : ℝ}
    (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < dyadicChainingNetRadius radiusScale j := by
  unfold dyadicChainingNetRadius
  exact div_pos hradiusScale (pow_pos (by norm_num) _)

/-- Nonnegativity of the dyadic net radius under a nonnegative top scale. -/
theorem dyadicChainingNetRadius_nonneg {radiusScale : ℝ}
    (hradiusScale : 0 ≤ radiusScale) (j : ℕ) :
    0 ≤ dyadicChainingNetRadius radiusScale j := by
  unfold dyadicChainingNetRadius
  exact div_nonneg hradiusScale (pow_pos (by norm_num) _).le

/-- Adjacent dyadic net radii fit inside the finite chaining radius budget. -/
theorem dyadicChainingNetRadius_pair_sum_le {radiusScale : ℝ}
    (hradiusScale_nonneg : 0 ≤ radiusScale) (j : ℕ) :
    dyadicChainingNetRadius radiusScale j +
        dyadicChainingNetRadius radiusScale (j + 1) ≤
      radiusScale / (2 : ℝ) ^ j := by
  unfold dyadicChainingNetRadius
  have hrewrite1 : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ j * 4 := by
    rw [pow_add]
    norm_num
  have hrewrite2 : (2 : ℝ) ^ (j + 1 + 2) = (2 : ℝ) ^ j * 8 := by
    have : j + 1 + 2 = j + 3 := by omega
    rw [this, pow_add]
    norm_num
  rw [hrewrite1, hrewrite2]
  have hbase_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  field_simp [hbase_pos.ne']
  nlinarith [hradiusScale_nonneg]

/-- The dyadic finite-net schedule extracted from total boundedness. -/
def dyadicChainingFiniteNetOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    BundledFiniteNet T :=
  finiteNetOfTotallyBoundedUniv
    (T := T) hT (dyadicChainingNetRadius radiusScale j)
    (dyadicChainingNetRadius_pos hradiusScale j)

/-- The dyadic finite-net schedule has the expected radius at each scale. -/
@[simp] theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.radius =
      dyadicChainingNetRadius radiusScale j := by
  rfl

/-- The dyadic finite-net schedule uses the ambient metric distance. -/
@[simp] theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.dist = fun s t => dist s t := by
  rfl

/-- Each dyadic finite net covers every index point at its scheduled radius. -/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (t : T) :
    dist t
        ((dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net.projection t) ≤
      dyadicChainingNetRadius radiusScale j := by
  simpa using
    (finiteNetOfTotallyBoundedUniv_covers
      (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) t)

/-- Adjacent extracted dyadic nets satisfy the radius hypothesis expected by
the existing finite Dudley chaining theorems. -/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius ≤
      radiusScale / (2 : ℝ) ^ j := by
  simpa using
    dyadicChainingNetRadius_pair_sum_le
      (radiusScale := radiusScale) hradiusScale.le j

/-- Adjacent extracted dyadic nets have positive combined radius. This is the
finite positivity condition needed by the finite sub-Gaussian max bound at
each projected-chaining scale. -/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 <
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius := by
  have hleft :
      0 <
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net.radius := by
    simp [dyadicChainingNetRadius_pos hradiusScale j]
  have hright :
      0 ≤
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net.radius :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale (j + 1)).net.radius_nonneg
  linarith

/-! ## Projected dyadic wrapper -/

/-- Product of adjacent covering numbers for the pure total-bounded dyadic
schedule, without adding an identity terminal net.

This records the chosen finite covers at adjacent scales; it is not a minimal
covering-number claim. -/
def dyadicChainingCoverCount
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℕ :=
  (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).net.coveringNumber *
  (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale (j + 1)).net.coveringNumber

/-- Finite projected-net total-bounded dyadic Dudley wrapper without a finite
ambient index type.

The supremum is over the finite image of the terminal dyadic net projection,
not over all of `T`. This is the next structural bridge toward a
total-bounded Dudley theorem: finite outcome support, finite dyadic scale
range, scalar process, and finite terminal image. It does not claim continuous
Dudley, separability, or measurable suprema over arbitrary classes. -/
theorem finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.center u.1))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget radiusScale m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log
              (dyadicChainingCoverCount
                (T := T) hT hradiusScale j : ℝ)))) := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · simpa [N] using hcoarse

/-- Projected total-bounded dyadic Dudley wrapper compared against a supplied
finite entropy-at-radius upper-sum/integral budget.

This composes the projected finite-net Dudley layer with the total-bounded
dyadic net schedule. The supremum remains over the finite image of the terminal
net projection, and `hupperSum` is an external finite upper-sum comparison
assumption. It does not claim continuous Dudley, separability, infinite
classes, or measurable suprema over arbitrary classes. -/
theorem finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_integral_comparison
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hupperSum :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤ integralBudget)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.center u.1))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius) (integralBudget := integralBudget)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hentropyAtRadius hupperSum ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · simpa [N] using hcoarse

/-- Projected total-bounded dyadic Dudley wrapper with the finite
entropy-at-radius upper sum discharged by a shifted-annulus interval-integral
budget.

This is the analytic domination layer for the total-bounded lane: it composes
the projected finite-net schedule with an antitone, interval-integrable entropy
profile and a finite shifted-annulus integral budget. The supremum remains over
the finite image of the terminal dyadic projection. It does not claim full
continuous Dudley, separability, infinite classes, or measurable suprema over
arbitrary classes. -/
theorem finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_intervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
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
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.center u.1))) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_intervalIntegral_comparison
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius) (integralBudget := integralBudget)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hentropyAtRadius
    hentropy_antitone hintervalIntegrable hintegralBudget ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · simpa [N] using hcoarse

/-- Projected total-bounded dyadic Dudley wrapper with the finite entropy
budget discharged by a single truncated interval integral.

This is the next finite bridge toward continuous Dudley: total boundedness
supplies dyadic finite nets, the finite Dudley theorem supplies the projected
finite supremum bound, and the shifted annulus budget is collapsed to the
truncated interval `[radiusScale / 2^(m+1), radiusScale / 2]`.

The boundaries are explicit: the supremum remains over the finite image of the
terminal projection; the scale range is finite; there is no separability
argument and no measurable supremum over an arbitrary infinite class. -/
theorem finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.center u.1))) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hentropyAtRadius
    hentropy_antitone hintervalIntegrable ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · simpa [N] using hcoarse

/-- Boundary-layer total-bounded Dudley wrapper for a supplied supremum
functional.

The theorem composes the projected finite-net total-bounded Dudley bound with
an explicit terminal approximation hypothesis. The caller supplies
`supFunctional : Ω → ℝ`; Lean does not construct an arbitrary measurable
supremum over `T` here. This is the intended continuous-boundary interface:
to use it for a true supremum, a later separability/dense-net argument must
prove the `hterminal` hypothesis.

Current boundaries: finite outcome support, finite dyadic scale range,
projected finite terminal net, scalar-valued process, and explicit terminal
error. No continuous Dudley theorem, no separability theorem, and no measurable
supremum over an arbitrary class are claimed. -/
theorem finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ) (terminalError : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
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
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net.center u.1)) +
            terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) + terminalError := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius) (supFunctional := supFunctional)
    (terminalError := terminalError)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hentropyAtRadius
    hentropy_antitone hintervalIntegrable ?hterminal ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · intro ω
    simpa [N] using hterminal ω
  · simpa [N] using hcoarse

/-- Boundary-layer total-bounded Dudley wrapper with an explicit finite
separability skeleton.

This is a more structured version of
`finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`.
The supplied supremum functional is first bounded by a finite skeleton through
`hseparable`; each skeleton point is then bounded by its terminal dyadic
projection through `hterminalApprox`.

The statement is deliberately scoped: finite outcome support, finite skeleton,
finite dyadic scale range, scalar-valued process, explicit separability error,
and explicit terminal projection error. It does not construct an arbitrary
measurable supremum, prove separability, or claim full continuous Dudley. -/
theorem finite_separableSupFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    {K : Type u} [Fintype K] [Nonempty K]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (embed : K → T) (supFunctional : Ω → ℝ)
    (separabilityError terminalError : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
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
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net.projection (embed k)) +
            terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) + (separabilityError + terminalError) := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_separableSupFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius) (embed := embed)
    (supFunctional := supFunctional)
    (separabilityError := separabilityError) (terminalError := terminalError)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hentropyAtRadius
    hentropy_antitone hintervalIntegrable ?hseparable ?hterminalApprox ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · intro ω
    simpa using hseparable ω
  · intro ω k
    simpa [N] using hterminalApprox ω k
  · simpa [N] using hcoarse

/-- Total-bounded Dudley boundary wrapper with usable finite-skeleton and
pathwise-modulus hypotheses.

This theorem discharges the two abstract assumptions in
`finite_separableSupFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`:
* `hwitness` plus `hskeletonApprox` provide the finite dense-skeleton
  approximation for the supplied supremum functional;
* `hpathwiseModulus` plus the terminal dyadic net cover provide the terminal
  projection approximation.

It remains a boundary theorem: finite outcome support, finite skeleton,
finite dyadic scale range, scalar-valued process, explicit approximation
errors. It does not construct arbitrary measurable suprema or prove a full
continuous Dudley theorem. -/
theorem finite_witnessedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    {K : Type u} [Fintype K] [Nonempty K]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (embed : K → T) (nearest : T → K) (witness : Ω → T)
    (supFunctional : Ω → ℝ)
    (witnessError skeletonError terminalError : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hwitness :
      ∀ ω : Ω,
        supFunctional ω ≤ P.X ω (witness ω) + witnessError)
    (hskeletonApprox :
      ∀ ω : Ω, ∀ t : T,
        P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError)
    (hpathwiseModulus :
      ∀ ω : Ω, ∀ s t : T,
        dist s t ≤ dyadicChainingNetRadius radiusScale m →
          P.X ω s ≤ P.X ω t + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε) + ((witnessError + skeletonError) + terminalError) := by
  refine finite_separableSupFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    (P := P) (hT := hT) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (embed := embed) (supFunctional := supFunctional)
    (separabilityError := witnessError + skeletonError)
    (terminalError := terminalError) hradiusScale hdistP hvariance hcard
    hentropyAtRadius hentropy_antitone hintervalIntegrable ?hseparable
    ?hterminalApprox hcoarse
  · exact supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
      embed nearest (P.X) supFunctional witness witnessError skeletonError
      hwitness hskeletonApprox
  · intro ω k
    exact hpathwiseModulus ω (embed k)
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale m).net.projection (embed k))
      (dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
        (T := T) hT hradiusScale m (embed k))

/-- A finite skeleton and terminal-scale certificate for an epsilonized
total-bounded Dudley boundary step.

For a requested error budget `eta` and dyadic terminal scale `m`, this predicate
packages exactly the data needed by
`finite_witnessedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`:
a finite skeleton, approximate maximizers for the supplied supremum functional,
a finite-skeleton selector, a pathwise terminal modulus, the finite entropy
side conditions at scale `m`, and a total approximation-error budget bounded by
`eta`.

The predicate is intentionally finite and explicit. It does not assert
separability, construct arbitrary measurable suprema, or claim a continuous
Dudley theorem.
-/
def EpsilonizedSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net)) ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ t : T,
      P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- Epsilonized total-bounded Dudley boundary adapter.

If every positive error budget `eta` admits a finite skeleton and terminal
dyadic scale satisfying `EpsilonizedSupremumBoundaryChoice`, then the supplied
supremum functional is bounded by the finite Dudley truncated-interval budget
at some chosen terminal scale, with the continuous-boundary approximation
compressed to `+ eta`.

This is the clean finite-choice interface for the continuous-boundary lane:
finite outcome support, finite skeletons, finite dyadic scales, scalar-valued
processes, and explicit approximation budgets. It still does not construct an
arbitrary measurable supremum, prove separability, or claim full continuous
Dudley.
-/
theorem finite_epsilonizedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        EpsilonizedSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        finiteExpectation P.weight supFunctional ≤
          coarseBudget m + 4 * Real.sqrt (2 * P.varianceProxy) *
            (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
              entropyAtRadius ε) + eta := by
  intro eta heta
  rcases hchoose eta heta with ⟨m, hchoice⟩
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonError, terminalError, herror, hcard,
      hentropyAtRadius, hintervalIntegrable, hwitness, hskeletonApprox,
      hpathwiseModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨m, ?_⟩
  have hbase :
      finiteExpectation P.weight supFunctional ≤
        coarseBudget m + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε) + ((witnessError + skeletonError) + terminalError) := by
    exact
      finite_witnessedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
        (P := P) (hT := hT) (m := m) (coarseBudget := coarseBudget m)
        (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
        (embed := embed) (nearest := nearest) (witness := witness)
        (supFunctional := supFunctional)
        (witnessError := witnessError) (skeletonError := skeletonError)
        (terminalError := terminalError)
        (hradiusScale := hradiusScale) (hdistP := hdistP)
        (hvariance := hvariance) (hcard := hcard)
        (hentropyAtRadius := hentropyAtRadius)
        (hentropy_antitone := hentropy_antitone)
        (hintervalIntegrable := hintervalIntegrable)
        (hwitness := hwitness) (hskeletonApprox := hskeletonApprox)
        (hpathwiseModulus := hpathwiseModulus) (hcoarse := hcoarse)
  have herrors : ((witnessError + skeletonError) + terminalError) ≤ eta := by
    simpa [add_assoc] using herror
  exact hbase.trans (add_le_add_right herrors _)

/-- A finite-cover skeleton gives the skeleton approximation required by the
epsilonized boundary certificate when sample paths have a one-sided modulus at
the cover radius.

This is the elementary bridge from finite-cover geometry to the finite-skeleton
assumption used by the Dudley boundary adapter.
-/
lemma skeletonApprox_of_finiteCover_pathwiseModulus
    {Ω : Type*} {K : Type u}
    [Fintype Ω] [PseudoMetricSpace T]
    (P : FiniteSubGaussianProcess Ω T)
    (embed : K → T) (nearest : T → K)
    (skeletonRadius skeletonError : ℝ)
    (hcover : ∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius)
    (hmodulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius → P.X ω s ≤ P.X ω t + skeletonError) :
    ∀ ω : Ω, ∀ t : T,
      P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError := by
  intro ω t
  exact hmodulus ω t (embed (nearest t)) (hcover t)

/-- A finite-cover/pathwise-modulus certificate for the epsilonized
total-bounded Dudley boundary step.

Compared with `EpsilonizedSupremumBoundaryChoice`, this predicate exposes the
recognizable continuous-boundary hypotheses:
* a finite skeleton and nearest-skeleton selector;
* a finite-cover radius for the selector;
* a pathwise modulus at that finite-cover radius;
* approximate witnesses for the supplied supremum functional;
* a terminal pathwise modulus at the dyadic terminal scale.

It remains a finite-choice certificate. It does not construct a dense sequence,
prove separability, construct arbitrary measurable suprema, or claim the full
continuous Dudley theorem.
-/
def FiniteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonRadius : ℝ),
  ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net)) ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius →
        P.X ω s ≤ P.X ω t + skeletonError) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- A finite-cover/pathwise-modulus certificate produces the epsilonized
supremum-boundary certificate used by the Dudley adapter.

This theorem is the reusable finite-cover bridge: finite-cover geometry plus
pathwise modulus discharges the explicit finite-skeleton approximation
hypothesis in `EpsilonizedSupremumBoundaryChoice`.
-/
theorem epsilonizedSupremumBoundaryChoice_of_finiteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (hchoice :
      FiniteCoverSupremumBoundaryChoice
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (hradiusScale := hradiusScale)
        (entropyAtRadius := entropyAtRadius)
        (supFunctional := supFunctional) eta m) :
    EpsilonizedSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonRadius, skeletonError, terminalError,
      herror, hcard, hentropyAtRadius, hintervalIntegrable, hcover,
      hskeletonModulus, hwitness, hterminalModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨K, instK, nonemptyK, embed, nearest, witness,
    witnessError, skeletonError, terminalError, herror, hcard,
    hentropyAtRadius, hintervalIntegrable, hwitness, ?_, hterminalModulus,
    hcoarse⟩
  exact skeletonApprox_of_finiteCover_pathwiseModulus
    (P := P) embed nearest skeletonRadius skeletonError hcover
    hskeletonModulus

/-- Epsilonized total-bounded Dudley bound from finite-cover/pathwise-modulus
certificates.

If every positive error budget has a finite-cover skeleton, approximate
supremum witnesses, a terminal dyadic scale, and pathwise moduli whose total
error is at most that budget, then the supplied supremum functional satisfies
the epsilonized truncated-interval Dudley bound.

This is still a finite-choice continuous-boundary theorem: it avoids arbitrary
measurable suprema and does not claim full continuous Dudley.
-/
theorem finite_epsilonizedSup_dudley_totalBounded_of_finiteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        FiniteCoverSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        finiteExpectation P.weight supFunctional ≤
          coarseBudget m + 4 * Real.sqrt (2 * P.varianceProxy) *
            (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
              entropyAtRadius ε) + eta := by
  refine
    finite_epsilonizedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) hradiusScale hdistP hvariance
      hentropy_antitone ?_
  intro eta heta
  rcases hchoose eta heta with ⟨m, hfiniteCover⟩
  exact ⟨m,
    epsilonizedSupremumBoundaryChoice_of_finiteCoverSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) hfiniteCover⟩

/-- Finite projected total-bounded dyadic Dudley wrapper.

This theorem composes the total-bounded dyadic finite-net schedule with the
projected finite Dudley entropy-budget theorem. The left side is the expected
finite supremum after the terminal dyadic projection `(N_m).projection`; unlike
`finite_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers`, this does not
close the telescope with an identity terminal net.

It is still finite-index and finite-scale: the supremum is over a finite index
type `T`, the terminal projection is finite-net valued, and the entropy budget
is a finite dyadic upper sum. It does not prove continuous Dudley, separability,
infinite classes, or measurable suprema over arbitrary classes. -/
theorem finite_projected_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun t => P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun t => P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net.projection t))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget radiusScale m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log
              (dyadicChainingCoverCount
                (T := T) hT hradiusScale j : ℝ)))) := by
  classical
  let A : ℕ → Type u := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A]
    exact (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).instFintype
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projected_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · simpa [N] using hcoarse

/-! ## Finite terminal dyadic wrapper -/

/-- Center type used by the finite terminal dyadic wrapper.

The second component carries the total-bounded dyadic net at scale `j`; the
first component lets the same type support the identity terminal net. -/
def dyadicTerminalNetCenterType
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : Type u :=
  T × (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).A

instance dyadicTerminalNetCenterType.instFintype
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Fintype (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Fintype D.A := D.instFintype
  change Fintype (T × D.A)
  infer_instance

instance dyadicTerminalNetCenterType.instNonempty
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Nonempty (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Nonempty D.A := D.instNonempty
  change Nonempty (T × D.A)
  infer_instance

/-- Finite net used by the finite terminal Dudley wrapper.

For `j < m`, this is the total-bounded dyadic net at scale `j`, padded with an
unused `T` coordinate. At and after the terminal level, it is the identity net,
so the existing finite chaining telescope closes exactly. -/
def dyadicTerminalFiniteNet
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    FiniteNet T (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  classical
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Fintype D.A := D.instFintype
  letI : Nonempty D.A := D.instNonempty
  by_cases hj : j < m
  · exact
      { dist := fun s t => dist s t
        dist_nonneg := fun s t => dist_nonneg
        center := fun a => D.net.center a.2
        project := fun t => (Classical.choice (inferInstance : Nonempty T), D.net.project t)
        radius := D.net.radius
        radius_nonneg := D.net.radius_nonneg
        covers := by
          intro t
          simpa [D, FiniteNet.projection] using D.net.projection_dist_le t }
  · exact
      { dist := fun s t => dist s t
        dist_nonneg := fun s t => dist_nonneg
        center := fun a => a.1
        project := fun t => (t, Classical.choice D.instNonempty)
        radius := 0
        radius_nonneg := le_rfl
        covers := by
          intro t
          simp }

@[simp] theorem dyadicTerminalFiniteNet_dist
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).dist =
      fun s t => dist s t := by
  unfold dyadicTerminalFiniteNet
  by_cases hj : j < m
  · simp [hj]
  · simp [hj]

/-- Before the terminal level, the wrapper net has the total-bounded dyadic
radius. -/
@[simp] theorem dyadicTerminalFiniteNet_radius_of_lt
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) {m j : ℕ}
    (hj : j < m) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius =
      dyadicChainingNetRadius radiusScale j := by
  unfold dyadicTerminalFiniteNet
  simp [hj]

/-- At the terminal level, the wrapper net is exact. -/
@[simp] theorem dyadicTerminalFiniteNet_projection_terminal
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ) (t : T) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m m).projection t = t := by
  unfold dyadicTerminalFiniteNet
  simp [FiniteNet.projection]

/-- Every radius in the finite terminal wrapper is bounded by the scheduled
dyadic radius at that level. -/
theorem dyadicTerminalFiniteNet_radius_le
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius ≤
      dyadicChainingNetRadius radiusScale j := by
  by_cases hj : j < m
  · simp [dyadicTerminalFiniteNet_radius_of_lt (T := T) hT hradiusScale hj]
  · have hnonneg : 0 ≤ dyadicChainingNetRadius radiusScale j :=
      (dyadicChainingNetRadius_pos hradiusScale j).le
    unfold dyadicTerminalFiniteNet
    simpa [hj] using hnonneg

/-- Adjacent radii in the finite terminal wrapper fit the geometric radius
budget used by the finite Dudley entropy-sum theorem. -/
theorem dyadicTerminalFiniteNet_pair_radius_le
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ)
    {j : ℕ} (_hj : j ∈ Finset.range m) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius ≤
      radiusScale / (2 : ℝ) ^ j := by
  have hleft :=
    dyadicTerminalFiniteNet_radius_le (T := T) hT hradiusScale m j
  have hright :=
    dyadicTerminalFiniteNet_radius_le (T := T) hT hradiusScale m (j + 1)
  calc
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius
        ≤ dyadicChainingNetRadius radiusScale j +
            dyadicChainingNetRadius radiusScale (j + 1) :=
          add_le_add hleft hright
    _ ≤ radiusScale / (2 : ℝ) ^ j :=
          dyadicChainingNetRadius_pair_sum_le
            (radiusScale := radiusScale) hradiusScale.le j

/-- Adjacent radii in the finite terminal wrapper are positive before the
terminal scale. -/
theorem dyadicTerminalFiniteNet_pair_radius_pos
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ)
    {j : ℕ} (hj : j ∈ Finset.range m) :
    0 <
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius := by
  have hj_lt : j < m := by simpa using hj
  have hleft :
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius =
        dyadicChainingNetRadius radiusScale j :=
    dyadicTerminalFiniteNet_radius_of_lt
      (T := T) hT hradiusScale hj_lt
  have hleft_pos : 0 <
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius := by
    rw [hleft]
    exact dyadicChainingNetRadius_pos hradiusScale j
  have hright_nonneg : 0 ≤
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius :=
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius_nonneg
  linarith

/-- Product of adjacent covering numbers in the finite terminal dyadic wrapper.

This is the finite entropy quantity used by the total-bounded dyadic wrapper.
It records the actual chosen finite covers; no minimal covering-number claim is
made. -/
def dyadicTerminalCoverCount
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) : ℕ :=
  (dyadicTerminalFiniteNet
    (T := T) hT hradiusScale m j).coveringNumber *
  (dyadicTerminalFiniteNet
    (T := T) hT hradiusScale m (j + 1)).coveringNumber

/-- Finite total-bounded dyadic Dudley wrapper.

This theorem composes the total-bounded dyadic finite-net schedule with the
existing finite Dudley entropy-budget theorem. It remains finite in the
terminal index type `T`: the final level is the identity finite net, which is
why the finite chaining telescope closes exactly.

It does not prove continuous Dudley, separability, measurable suprema over
arbitrary classes, or an entropy integral over an infinite index set. -/
theorem finite_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicTerminalFiniteNet
          (T := T) hT hradiusScale m j)
        (dyadicTerminalFiniteNet
          (T := T) hT hradiusScale m (j + 1))))
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun t => P.X ω
            ((dyadicTerminalFiniteNet
              (T := T) hT hradiusScale m 0).projection t))) ≤
      coarseBudget) :
    finiteExpectation P.weight (fun ω => finiteSup (P.X ω)) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget radiusScale m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j => Real.sqrt (Real.log
              (dyadicTerminalCoverCount
                (T := T) hT hradiusScale m j : ℝ)))) := by
  classical
  let A : ℕ → Type u := fun j =>
    dyadicTerminalNetCenterType (T := T) hT hradiusScale j
  letI : ∀ j, Fintype (A j) := by
    intro j
    dsimp [A, dyadicTerminalNetCenterType]
    infer_instance
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    dyadicTerminalFiniteNet (T := T) hT hradiusScale m j
  refine FiniteSubGaussianProcess.finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => dyadicTerminalCoverCount (T := T) hT hradiusScale m j)
    ?hdist ?hsymm ?htri ?hlast hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcard ?hcoverCount ?hcoarse
  · intro j
    dsimp [N]
    rw [dyadicTerminalFiniteNet_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro t
    dsimp [N]
    exact dyadicTerminalFiniteNet_projection_terminal
      (T := T) hT hradiusScale m t
  · intro j hj
    dsimp [N]
    exact dyadicTerminalFiniteNet_pair_radius_pos
      (T := T) hT hradiusScale m hj
  · intro j hj
    dsimp [N]
    exact dyadicTerminalFiniteNet_pair_radius_le
      (T := T) hT hradiusScale m hj
  · intro j hj
    dsimp [N]
    exact hcard j hj
  · intro j _hj
    rfl
  · simpa [N] using hcoarse

end

end FormalSLT.Covering.TotalBoundedDudley
