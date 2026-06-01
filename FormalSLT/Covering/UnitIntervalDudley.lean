import Mathlib.Topology.Order.Compact
import FormalSLT.Covering.TotalBoundedDudley
import FormalSLT.Rademacher.Massart

/-!
# Unit-interval example for the total-bounded Dudley bridge

This module instantiates the total-bounded finite-net layer on a concrete
non-finite metric index space: the unit interval. It also packages the zero
process over that index space as a finite sub-Gaussian process and routes it
through the global-budget boundary adapter.

The point is deliberately narrow: it proves that the total-bounded bridge can
be used on a non-finite ambient index type, without claiming the full
continuous Dudley theorem.
-/

open Set
open scoped BigOperators Interval

namespace FormalSLT.Covering.UnitIntervalDudley

open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Rademacher.FiniteSample
open FormalSLT.Rademacher.Massart

noncomputable section

/-- The unit interval as a non-finite metric index type. -/
abbrev UnitInterval : Type :=
  {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

/-- A concrete point of the unit interval. -/
def unitIntervalZero : UnitInterval :=
  ⟨0, by simp⟩

/-- The right endpoint of the unit interval. -/
def unitIntervalOne : UnitInterval :=
  ⟨1, by simp⟩

@[simp] theorem dist_unitIntervalZero_unitIntervalOne :
    dist unitIntervalZero unitIntervalOne = 1 := by
  norm_num [unitIntervalZero, unitIntervalOne, Subtype.dist_eq, Real.dist_eq]

/-- The unit interval is totally bounded. -/
theorem unitInterval_totallyBounded_univ :
    TotallyBounded (Set.univ : Set UnitInterval) := by
  simpa [UnitInterval] using
    (isCompact_univ
      (X := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})).totallyBounded

/-- The finite net extracted from total boundedness of the unit interval. -/
def unitIntervalFiniteNet (ε : ℝ) (hε : 0 < ε) :
    BundledFiniteNet UnitInterval :=
  finiteNetOfTotallyBoundedUniv
    (T := UnitInterval) unitInterval_totallyBounded_univ ε hε

/-- The extracted unit-interval finite net covers every point at the requested
radius. -/
theorem unitIntervalFiniteNet_covers {ε : ℝ} (hε : 0 < ε)
    (t : UnitInterval) :
    dist t ((unitIntervalFiniteNet ε hε).net.projection t) ≤ ε := by
  exact finiteNetOfTotallyBoundedUniv_covers
    (T := UnitInterval) unitInterval_totallyBounded_univ hε t

/-- The dyadic finite-net schedule on the unit interval. -/
def unitIntervalDyadicFiniteNet {radiusScale : ℝ}
    (hradiusScale : 0 < radiusScale) (j : ℕ) :
    BundledFiniteNet UnitInterval :=
  dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := UnitInterval) unitInterval_totallyBounded_univ hradiusScale j

/-- Every unit-interval point is covered by the dyadic finite net at each
scheduled radius. -/
theorem unitIntervalDyadicFiniteNet_covers {radiusScale : ℝ}
    (hradiusScale : 0 < radiusScale) (j : ℕ) (t : UnitInterval) :
    dist t ((unitIntervalDyadicFiniteNet hradiusScale j).net.projection t) ≤
      dyadicChainingNetRadius radiusScale j := by
  exact dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
    (T := UnitInterval) unitInterval_totallyBounded_univ hradiusScale j t

/-! ## Reusable dyadic grid skeleton -/

/-- Index type for the dyadic grid `{0, 1 / 2^level, ..., 1}`. -/
abbrev unitIntervalDyadicGridIndex (level : ℕ) : Type :=
  Fin ((2 : ℕ) ^ level + 1)

/-- The left endpoint index in the dyadic grid. -/
def unitIntervalDyadicGridLeftIndex (level : ℕ) :
    unitIntervalDyadicGridIndex level :=
  ⟨0, Nat.succ_pos _⟩

/-- The right endpoint index in the dyadic grid. -/
def unitIntervalDyadicGridRightIndex (level : ℕ) :
    unitIntervalDyadicGridIndex level :=
  ⟨(2 : ℕ) ^ level, Nat.lt_succ_self _⟩

/-- Center map for the dyadic grid `{0, 1 / 2^level, ..., 1}` on `[0,1]`. -/
def unitIntervalDyadicGridCenter (level : ℕ)
    (i : unitIntervalDyadicGridIndex level) : UnitInterval :=
  ⟨(i.1 : ℝ) / (((2 : ℕ) ^ level : ℕ) : ℝ), by
    have hden_nat_pos : 0 < (2 : ℕ) ^ level :=
      pow_pos (by norm_num : (0 : ℕ) < 2) level
    have hden_pos : 0 < (((2 : ℕ) ^ level : ℕ) : ℝ) := by
      exact_mod_cast hden_nat_pos
    have hden_nonneg : 0 ≤ (((2 : ℕ) ^ level : ℕ) : ℝ) :=
      le_of_lt hden_pos
    constructor
    · exact div_nonneg (Nat.cast_nonneg i.1) hden_nonneg
    · have hi_nat : i.1 ≤ (2 : ℕ) ^ level := Nat.le_of_lt_succ i.2
      have hi_real :
          (i.1 : ℝ) ≤ (((2 : ℕ) ^ level : ℕ) : ℝ) := by
        exact_mod_cast hi_nat
      have hle := div_le_div_of_nonneg_right hi_real hden_nonneg
      rw [div_self (ne_of_gt hden_pos)] at hle
      exact hle⟩

@[simp] theorem unitIntervalDyadicGridCenter_leftEndpoint (level : ℕ) :
    unitIntervalDyadicGridCenter level
        (unitIntervalDyadicGridLeftIndex level) =
      unitIntervalZero := by
  ext
  simp [unitIntervalDyadicGridCenter, unitIntervalDyadicGridLeftIndex,
    unitIntervalZero]

@[simp] theorem unitIntervalDyadicGridCenter_rightEndpoint (level : ℕ) :
    unitIntervalDyadicGridCenter level
        (unitIntervalDyadicGridRightIndex level) =
      unitIntervalOne := by
  ext
  change
    (((2 : ℕ) ^ level : ℕ) : ℝ) /
        (((2 : ℕ) ^ level : ℕ) : ℝ) = 1
  rw [div_self]
  exact_mod_cast pow_ne_zero level (by norm_num : (2 : ℕ) ≠ 0)

/-- Cardinality of the dyadic grid at level `level`. -/
theorem unitIntervalDyadicGrid_card (level : ℕ) :
    Fintype.card (unitIntervalDyadicGridIndex level) =
      (2 : ℕ) ^ level + 1 := by
  simp [unitIntervalDyadicGridIndex]

/-- Product cover-count for adjacent dyadic grids at levels `j + 1` and
`j + 2`. -/
def unitIntervalDyadicGridPairCoverCount (j : ℕ) : ℕ :=
  ((2 : ℕ) ^ (j + 1) + 1) * ((2 : ℕ) ^ (j + 2) + 1)

/-- The first adjacent dyadic grid pair, levels `1` and `2`, has product count
`15`. -/
theorem unitIntervalDyadicGridPairCoverCount_zero :
    unitIntervalDyadicGridPairCoverCount 0 = 15 := by
  norm_num [unitIntervalDyadicGridPairCoverCount]

/-- Left-bin projection to the dyadic grid. It sends `t` to
`floor (2^level * t) / 2^level`, clipped automatically by `t <= 1`. -/
def unitIntervalDyadicGridFloorProject (level : ℕ) (t : UnitInterval) :
    unitIntervalDyadicGridIndex level :=
  ⟨Nat.floor ((((2 : ℕ) ^ level : ℕ) : ℝ) * t.1), by
    have hden_nonneg :
        0 ≤ ((((2 : ℕ) ^ level : ℕ) : ℝ)) := by
      exact_mod_cast Nat.zero_le ((2 : ℕ) ^ level)
    have hmul_le :
        (((2 : ℕ) ^ level : ℕ) : ℝ) * t.1 ≤
          (((2 : ℕ) ^ level : ℕ) : ℝ) := by
      exact mul_le_of_le_one_right hden_nonneg t.2.2
    have hfloor_le :
        Nat.floor ((((2 : ℕ) ^ level : ℕ) : ℝ) * t.1) ≤
          (2 : ℕ) ^ level :=
      Nat.floor_le_of_le hmul_le
    exact Nat.lt_succ_of_le hfloor_le⟩

/-- The floor-projected dyadic grid covers `[0,1]` at the grid spacing
`1 / 2^level`. This is a reusable generic coverage theorem; the sharper
half-spacing nearest-grid theorem is left to the explicit half/quarter meshes
or a later rounded projection. -/
theorem unitIntervalDyadicGridFloorProject_dist_le
    (level : ℕ) (t : UnitInterval) :
    dist t
        (unitIntervalDyadicGridCenter level
          (unitIntervalDyadicGridFloorProject level t)) ≤
      (1 : ℝ) / (((2 : ℕ) ^ level : ℕ) : ℝ) := by
  let n : ℕ := (2 : ℕ) ^ level
  have hn_nat_pos : 0 < n := by
    dsimp [n]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) level
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_nat_pos
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  let a : ℝ := (n : ℝ) * t.1
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hn_nonneg t.2.1
  have hfloor_le :
      ((Nat.floor a : ℕ) : ℝ) ≤ a :=
    Nat.floor_le ha_nonneg
  have hlt_floor_add :
      a < ((Nat.floor a : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one a
  have hleft :
      ((Nat.floor a : ℕ) : ℝ) / (n : ℝ) ≤ t.1 := by
    have hmul :
        ((Nat.floor a : ℕ) : ℝ) ≤ (n : ℝ) * t.1 := by
      simpa [a] using hfloor_le
    rw [div_le_iff₀ hn_pos]
    simpa [mul_comm] using hmul
  have hright :
      t.1 - ((Nat.floor a : ℕ) : ℝ) / (n : ℝ) ≤
        (1 : ℝ) / (n : ℝ) := by
    have hmul :
        (n : ℝ) * t.1 < ((Nat.floor a : ℕ) : ℝ) + 1 := by
      simpa [a] using hlt_floor_add
    have ht_le :
        t.1 ≤ (((Nat.floor a : ℕ) : ℝ) + 1) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      simpa [mul_comm] using le_of_lt hmul
    calc
      t.1 - ((Nat.floor a : ℕ) : ℝ) / (n : ℝ) ≤
          (((Nat.floor a : ℕ) : ℝ) + 1) / (n : ℝ) -
            ((Nat.floor a : ℕ) : ℝ) / (n : ℝ) :=
        sub_le_sub_right ht_le _
      _ = (1 : ℝ) / (n : ℝ) := by
        field_simp [ne_of_gt hn_pos]
        ring
  have habs :
      |t.1 - ((Nat.floor a : ℕ) : ℝ) / (n : ℝ)| ≤
        (1 : ℝ) / (n : ℝ) := by
    apply abs_le.mpr
    constructor
    · have hnonneg :
          0 ≤ t.1 - ((Nat.floor a : ℕ) : ℝ) / (n : ℝ) := by
        linarith [hleft]
      have hradius_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) :=
        div_nonneg zero_le_one hn_nonneg
      linarith
    · exact hright
  rw [Subtype.dist_eq, Real.dist_eq]
  simpa [unitIntervalDyadicGridCenter, unitIntervalDyadicGridFloorProject,
    n, a] using habs

/-- The generic dyadic grid as a finite net over `[0,1]`, with the floor
projection and spacing radius `1 / 2^level`. -/
def unitIntervalDyadicGridNet (level : ℕ) :
    FiniteNet UnitInterval (unitIntervalDyadicGridIndex level) :=
  { dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    center := unitIntervalDyadicGridCenter level
    project := unitIntervalDyadicGridFloorProject level
    radius := (1 : ℝ) / (((2 : ℕ) ^ level : ℕ) : ℝ)
    radius_nonneg := by
      have hden_nat_pos : 0 < (2 : ℕ) ^ level :=
        pow_pos (by norm_num : (0 : ℕ) < 2) level
      have hden_nonneg :
          0 ≤ ((((2 : ℕ) ^ level : ℕ) : ℝ)) := by
        exact_mod_cast (le_of_lt hden_nat_pos)
      exact div_nonneg zero_le_one hden_nonneg
    covers := unitIntervalDyadicGridFloorProject_dist_le level }

/-- The generic dyadic grid finite net covers the unit interval at spacing
`1 / 2^level`. -/
theorem unitIntervalDyadicGridNet_covers (level : ℕ) (t : UnitInterval) :
    dist t ((unitIntervalDyadicGridNet level).projection t) ≤
      (1 : ℝ) / (((2 : ℕ) ^ level : ℕ) : ℝ) :=
  (unitIntervalDyadicGridNet level).projection_dist_le t

/-- The generic dyadic grid finite net has `2^level + 1` centers. -/
theorem unitIntervalDyadicGridNet_coveringNumber (level : ℕ) :
    (unitIntervalDyadicGridNet level).coveringNumber =
      (2 : ℕ) ^ level + 1 := by
  simp [FiniteNet.coveringNumber, unitIntervalDyadicGridIndex]

/-- The level-`1` generic dyadic grid finite net has three centers. -/
theorem unitIntervalDyadicGridNet_coveringNumber_one :
    (unitIntervalDyadicGridNet 1).coveringNumber = 3 := by
  rw [unitIntervalDyadicGridNet_coveringNumber]
  norm_num

/-- The level-`2` generic dyadic grid finite net has five centers. -/
theorem unitIntervalDyadicGridNet_coveringNumber_two :
    (unitIntervalDyadicGridNet 2).coveringNumber = 5 := by
  rw [unitIntervalDyadicGridNet_coveringNumber]
  norm_num

/-- The first adjacent generic dyadic grid-net covering-number product is the
same `15` count used by the explicit half/quarter mesh pair. -/
theorem unitIntervalDyadicGridNet_coveringNumberPair_zero :
    (unitIntervalDyadicGridNet 1).coveringNumber *
        (unitIntervalDyadicGridNet 2).coveringNumber =
      unitIntervalDyadicGridPairCoverCount 0 := by
  rw [unitIntervalDyadicGridNet_coveringNumber_one,
    unitIntervalDyadicGridNet_coveringNumber_two,
    unitIntervalDyadicGridPairCoverCount_zero]

/-- Nearest-grid projection to the dyadic grid. It rounds `2^level * t` to the
nearest integer by taking `floor (2^level * t + 1/2)`. -/
def unitIntervalDyadicGridRoundProject (level : ℕ) (t : UnitInterval) :
    unitIntervalDyadicGridIndex level :=
  let n : ℕ := (2 : ℕ) ^ level
  ⟨Nat.floor ((n : ℝ) * t.1 + (1 : ℝ) / 2), by
    have hn_nat_pos : 0 < n := by
      dsimp [n]
      exact pow_pos (by norm_num : (0 : ℕ) < 2) level
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      exact_mod_cast le_of_lt hn_nat_pos
    have hmul_le : (n : ℝ) * t.1 ≤ (n : ℝ) := by
      exact mul_le_of_le_one_right hn_nonneg t.2.2
    have harg_nonneg : 0 ≤ (n : ℝ) * t.1 + (1 : ℝ) / 2 := by
      have hmul_nonneg : 0 ≤ (n : ℝ) * t.1 :=
        mul_nonneg hn_nonneg t.2.1
      linarith
    have harg_lt :
        (n : ℝ) * t.1 + (1 : ℝ) / 2 < ((n + 1 : ℕ) : ℝ) := by
      have : (n : ℝ) * t.1 + (1 : ℝ) / 2 < (n : ℝ) + 1 := by
        linarith
      simpa using this
    have hfloor_lt :
        Nat.floor ((n : ℝ) * t.1 + (1 : ℝ) / 2) < n + 1 :=
      (Nat.floor_lt harg_nonneg).2 harg_lt
    simpa [n, unitIntervalDyadicGridIndex] using hfloor_lt⟩

/-- The rounded dyadic grid projection covers `[0,1]` at half the grid spacing,
`1 / 2^(level + 1)`. -/
theorem unitIntervalDyadicGridRoundProject_dist_le
    (level : ℕ) (t : UnitInterval) :
    dist t
        (unitIntervalDyadicGridCenter level
          (unitIntervalDyadicGridRoundProject level t)) ≤
      (1 : ℝ) / (((2 : ℕ) ^ (level + 1) : ℕ) : ℝ) := by
  let n : ℕ := (2 : ℕ) ^ level
  have hn_nat_pos : 0 < n := by
    dsimp [n]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) level
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_nat_pos
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  let a : ℝ := (n : ℝ) * t.1
  let m : ℕ := Nat.floor (a + (1 : ℝ) / 2)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hn_nonneg t.2.1
  have harg_nonneg : 0 ≤ a + (1 : ℝ) / 2 := by
    linarith
  have hm_le :
      (m : ℝ) ≤ a + (1 : ℝ) / 2 := by
    dsimp [m]
    exact Nat.floor_le harg_nonneg
  have harg_lt :
      a + (1 : ℝ) / 2 < (m : ℝ) + 1 := by
    dsimp [m]
    exact Nat.lt_floor_add_one (a + (1 : ℝ) / 2)
  have hleft : -((1 : ℝ) / 2) ≤ a - (m : ℝ) := by
    linarith
  have hright : a - (m : ℝ) ≤ (1 : ℝ) / 2 := by
    linarith
  have habs_a : |a - (m : ℝ)| ≤ (1 : ℝ) / 2 :=
    abs_le.mpr ⟨hleft, hright⟩
  have hscaled :
      |t.1 - (m : ℝ) / (n : ℝ)| ≤ ((1 : ℝ) / 2) / (n : ℝ) := by
    have hrewrite :
        t.1 - (m : ℝ) / (n : ℝ) =
          (a - (m : ℝ)) / (n : ℝ) := by
      dsimp [a]
      field_simp [ne_of_gt hn_pos]
    rw [hrewrite]
    calc
      |(a - (m : ℝ)) / (n : ℝ)| =
          |a - (m : ℝ)| / (n : ℝ) := by
        rw [abs_div, abs_of_pos hn_pos]
      _ ≤ ((1 : ℝ) / 2) / (n : ℝ) :=
        div_le_div_of_nonneg_right habs_a hn_nonneg
  have hradius :
      ((1 : ℝ) / 2) / (n : ℝ) =
        (1 : ℝ) / (((2 : ℕ) ^ (level + 1) : ℕ) : ℝ) := by
    have hpow_nat :
        (2 : ℕ) ^ (level + 1) = (2 : ℕ) * (2 : ℕ) ^ level := by
      rw [pow_succ']
    have hpow_real :
        (((2 : ℕ) ^ (level + 1) : ℕ) : ℝ) = 2 * (n : ℝ) := by
      dsimp [n]
      norm_num [hpow_nat]
    rw [hpow_real]
    field_simp [ne_of_gt hn_pos]
  rw [hradius] at hscaled
  rw [Subtype.dist_eq, Real.dist_eq]
  simpa [unitIntervalDyadicGridCenter, unitIntervalDyadicGridRoundProject,
    n, a, m] using hscaled

@[simp] theorem unitIntervalDyadicGridRoundProject_zero (level : ℕ) :
    unitIntervalDyadicGridRoundProject level unitIntervalZero =
      unitIntervalDyadicGridLeftIndex level := by
  ext
  change
    Nat.floor
      ((((2 : ℕ) ^ level : ℕ) : ℝ) * (0 : ℝ) + (1 : ℝ) / 2) = 0
  norm_num [Nat.floor_eq_iff]

@[simp] theorem unitIntervalDyadicGridRoundProject_one (level : ℕ) :
    unitIntervalDyadicGridRoundProject level unitIntervalOne =
      unitIntervalDyadicGridRightIndex level := by
  ext
  change
    Nat.floor
      ((((2 : ℕ) ^ level : ℕ) : ℝ) * (1 : ℝ) + (1 : ℝ) / 2) =
        (2 : ℕ) ^ level
  have harg_nonneg :
      0 ≤ (((2 : ℕ) ^ level : ℕ) : ℝ) * (1 : ℝ) + (1 : ℝ) / 2 := by
    positivity
  rw [Nat.floor_eq_iff harg_nonneg]
  constructor
  · norm_num
  · have hpow_nonneg : 0 ≤ (((2 : ℕ) ^ level : ℕ) : ℝ) := by
      positivity
    linarith

/-- The generic dyadic grid as a rounded finite net over `[0,1]`, with
nearest-grid projection and half-spacing radius `1 / 2^(level + 1)`. -/
def unitIntervalDyadicRoundedGridNet (level : ℕ) :
    FiniteNet UnitInterval (unitIntervalDyadicGridIndex level) :=
  { dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    center := unitIntervalDyadicGridCenter level
    project := unitIntervalDyadicGridRoundProject level
    radius := (1 : ℝ) / (((2 : ℕ) ^ (level + 1) : ℕ) : ℝ)
    radius_nonneg := by
      have hden_nat_pos : 0 < (2 : ℕ) ^ (level + 1) :=
        pow_pos (by norm_num : (0 : ℕ) < 2) (level + 1)
      have hden_nonneg :
          0 ≤ ((((2 : ℕ) ^ (level + 1) : ℕ) : ℝ)) := by
        exact_mod_cast (le_of_lt hden_nat_pos)
      exact div_nonneg zero_le_one hden_nonneg
    covers := unitIntervalDyadicGridRoundProject_dist_le level }

/-- The rounded generic dyadic grid finite net covers `[0,1]` at half-spacing
radius `1 / 2^(level + 1)`. -/
theorem unitIntervalDyadicRoundedGridNet_covers (level : ℕ) (t : UnitInterval) :
    dist t ((unitIntervalDyadicRoundedGridNet level).projection t) ≤
      (1 : ℝ) / (((2 : ℕ) ^ (level + 1) : ℕ) : ℝ) :=
  (unitIntervalDyadicRoundedGridNet level).projection_dist_le t

/-- The rounded generic dyadic grid finite net has `2^level + 1` centers. -/
theorem unitIntervalDyadicRoundedGridNet_coveringNumber (level : ℕ) :
    (unitIntervalDyadicRoundedGridNet level).coveringNumber =
      (2 : ℕ) ^ level + 1 := by
  simp [FiniteNet.coveringNumber, unitIntervalDyadicGridIndex]

/-- The level-`1` rounded generic dyadic grid finite net has three centers. -/
theorem unitIntervalDyadicRoundedGridNet_coveringNumber_one :
    (unitIntervalDyadicRoundedGridNet 1).coveringNumber = 3 := by
  rw [unitIntervalDyadicRoundedGridNet_coveringNumber]
  norm_num

/-- The level-`2` rounded generic dyadic grid finite net has five centers. -/
theorem unitIntervalDyadicRoundedGridNet_coveringNumber_two :
    (unitIntervalDyadicRoundedGridNet 2).coveringNumber = 5 := by
  rw [unitIntervalDyadicRoundedGridNet_coveringNumber]
  norm_num

/-- The first adjacent rounded generic dyadic grid-net covering-number product
is the same `15` count used by the explicit half/quarter mesh pair. -/
theorem unitIntervalDyadicRoundedGridNet_coveringNumberPair_zero :
    (unitIntervalDyadicRoundedGridNet 1).coveringNumber *
        (unitIntervalDyadicRoundedGridNet 2).coveringNumber =
      unitIntervalDyadicGridPairCoverCount 0 := by
  rw [unitIntervalDyadicRoundedGridNet_coveringNumber_one,
    unitIntervalDyadicRoundedGridNet_coveringNumber_two,
    unitIntervalDyadicGridPairCoverCount_zero]

/-! ## Explicit finite meshes for the unit interval -/

/-- The five-point mesh `{0, 1/4, 1/2, 3/4, 1}` as centers in the unit
interval. -/
def unitIntervalQuarterMeshCenter (i : Fin 5) : UnitInterval :=
  ⟨(i.1 : ℝ) / 4, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg i.1) (by norm_num)
    · have hi_nat : i.1 ≤ 4 := Nat.le_of_lt_succ i.2
      have hi_real : (i.1 : ℝ) ≤ 4 := by exact_mod_cast hi_nat
      nlinarith⟩

/-- Nearest-bin projection to the five-point quarter mesh. -/
def unitIntervalQuarterMeshProject (t : UnitInterval) : Fin 5 :=
  if t.1 ≤ (1 : ℝ) / 8 then
    ⟨0, by norm_num⟩
  else if t.1 ≤ (3 : ℝ) / 8 then
    ⟨1, by norm_num⟩
  else if t.1 ≤ (5 : ℝ) / 8 then
    ⟨2, by norm_num⟩
  else if t.1 ≤ (7 : ℝ) / 8 then
    ⟨3, by norm_num⟩
  else
    ⟨4, by norm_num⟩

private lemma unitIntervalQuarterMeshProject_dist_le (t : UnitInterval) :
    dist t (unitIntervalQuarterMeshCenter (unitIntervalQuarterMeshProject t)) ≤
      (1 : ℝ) / 8 := by
  unfold unitIntervalQuarterMeshProject unitIntervalQuarterMeshCenter
  split_ifs with h0 h1 h2 h3
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h0 ⊢
    · linarith [t.2.1]
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h0 h1 ⊢
    · linarith
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h1 h2 ⊢
    · linarith
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h2 h3 ⊢
    · linarith
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h3 ⊢
    · linarith
    · linarith [t.2.2]

/-- An explicit five-point finite net over `[0,1]` with radius `1/8`. -/
def unitIntervalQuarterMeshNet : FiniteNet UnitInterval (Fin 5) :=
  { dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    center := unitIntervalQuarterMeshCenter
    project := unitIntervalQuarterMeshProject
    radius := (1 : ℝ) / 8
    radius_nonneg := by norm_num
    covers := unitIntervalQuarterMeshProject_dist_le }

/-- The explicit quarter mesh covers every unit-interval point at radius
`1/8`. -/
theorem unitIntervalQuarterMeshNet_covers (t : UnitInterval) :
    dist t (unitIntervalQuarterMeshNet.projection t) ≤ (1 : ℝ) / 8 :=
  unitIntervalQuarterMeshNet.projection_dist_le t

/-- The explicit quarter mesh has five centers. -/
theorem unitIntervalQuarterMeshNet_coveringNumber :
    unitIntervalQuarterMeshNet.coveringNumber = 5 := by
  simp [FiniteNet.coveringNumber]

/-- The three-point mesh `{0, 1/2, 1}` as centers in the unit interval. -/
def unitIntervalHalfMeshCenter (i : Fin 3) : UnitInterval :=
  ⟨(i.1 : ℝ) / 2, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg i.1) (by norm_num)
    · have hi_nat : i.1 ≤ 2 := Nat.le_of_lt_succ i.2
      have hi_real : (i.1 : ℝ) ≤ 2 := by exact_mod_cast hi_nat
      nlinarith⟩

/-- Nearest-bin projection to the three-point half mesh. -/
def unitIntervalHalfMeshProject (t : UnitInterval) : Fin 3 :=
  if t.1 ≤ (1 : ℝ) / 4 then
    ⟨0, by norm_num⟩
  else if t.1 ≤ (3 : ℝ) / 4 then
    ⟨1, by norm_num⟩
  else
    ⟨2, by norm_num⟩

private lemma unitIntervalHalfMeshProject_dist_le (t : UnitInterval) :
    dist t (unitIntervalHalfMeshCenter (unitIntervalHalfMeshProject t)) ≤
      (1 : ℝ) / 4 := by
  unfold unitIntervalHalfMeshProject unitIntervalHalfMeshCenter
  split_ifs with h0 h1
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h0 ⊢
    · linarith [t.2.1]
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h0 h1 ⊢
    · linarith
    · linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> norm_num at h1 ⊢
    · linarith
    · linarith [t.2.2]

/-- An explicit three-point finite net over `[0,1]` with radius `1/4`. -/
def unitIntervalHalfMeshNet : FiniteNet UnitInterval (Fin 3) :=
  { dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    center := unitIntervalHalfMeshCenter
    project := unitIntervalHalfMeshProject
    radius := (1 : ℝ) / 4
    radius_nonneg := by norm_num
    covers := unitIntervalHalfMeshProject_dist_le }

/-- The explicit half mesh covers every unit-interval point at radius `1/4`. -/
theorem unitIntervalHalfMeshNet_covers (t : UnitInterval) :
    dist t (unitIntervalHalfMeshNet.projection t) ≤ (1 : ℝ) / 4 :=
  unitIntervalHalfMeshNet.projection_dist_le t

/-- The explicit half mesh has three centers. -/
theorem unitIntervalHalfMeshNet_coveringNumber :
    unitIntervalHalfMeshNet.coveringNumber = 3 := by
  simp [FiniteNet.coveringNumber]

/-- The explicit adjacent half/quarter projection-pair family is nontrivial. -/
theorem unitIntervalHalfQuarterPair_card_gt_one :
    1 < Fintype.card
      (FiniteNet.ProjectionPair unitIntervalHalfMeshNet unitIntervalQuarterMeshNet) := by
  classical
  let p0 : FiniteNet.ProjectionPair unitIntervalHalfMeshNet unitIntervalQuarterMeshNet :=
    FiniteNet.projectionPairOf unitIntervalHalfMeshNet unitIntervalQuarterMeshNet unitIntervalZero
  let p1 : FiniteNet.ProjectionPair unitIntervalHalfMeshNet unitIntervalQuarterMeshNet :=
    FiniteNet.projectionPairOf unitIntervalHalfMeshNet unitIntervalQuarterMeshNet unitIntervalOne
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hproj :
      unitIntervalHalfMeshNet.project unitIntervalZero =
        unitIntervalHalfMeshNet.project unitIntervalOne := by
    exact congrArg
      (fun p : FiniteNet.ProjectionPair unitIntervalHalfMeshNet unitIntervalQuarterMeshNet =>
        p.1.1) hp
  norm_num [unitIntervalHalfMeshNet, unitIntervalHalfMeshProject,
    unitIntervalZero, unitIntervalOne] at hproj

/-- The product of the explicit half and quarter mesh covering numbers is
`15`. -/
theorem unitIntervalHalfQuarter_coveringNumber_product :
    unitIntervalHalfMeshNet.coveringNumber *
        unitIntervalQuarterMeshNet.coveringNumber = 15 := by
  simp [unitIntervalHalfMeshNet_coveringNumber,
    unitIntervalQuarterMeshNet_coveringNumber]

/-- The explicit half/quarter covering-number product is the first adjacent
dyadic grid pair count. -/
theorem unitIntervalHalfQuarter_coveringNumber_product_eq_dyadicGridPairCoverCount_zero :
    unitIntervalHalfMeshNet.coveringNumber *
        unitIntervalQuarterMeshNet.coveringNumber =
      unitIntervalDyadicGridPairCoverCount 0 := by
  rw [unitIntervalHalfQuarter_coveringNumber_product,
    unitIntervalDyadicGridPairCoverCount_zero]

/-- The zero process over the unit interval.

This is the plumbing example: the index type is non-finite, while the outcome
space is finite. The stronger nontrivial target is a Rademacher linear process
over the same index type.
-/
def unitIntervalZeroProcess :
    FiniteSubGaussianProcess Bool UnitInterval :=
  { weight := fun _ => (1 : ℝ) / 2
    weight_nonneg := by
      intro ω
      norm_num
    weight_sum_one := by
      simp
    X := fun _ _ => 0
    dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    varianceProxy := 1
    varianceProxy_nonneg := by norm_num
    mgf_increment := by
      intro s t lam
      simp [finiteExpectation]
      have hnonneg : 0 ≤ lam ^ 2 * dist s t ^ 2 / 2 := by
        nlinarith [sq_nonneg lam, sq_nonneg (dist s t)]
      simpa [mul_assoc] using Real.one_le_exp hnonneg }

/-- The zero process satisfies the finite sub-Gaussian increment MGF bound. -/
theorem unitIntervalZeroProcess_increment_mgf
    (s t : UnitInterval) (lam : ℝ) :
    finiteExpectation unitIntervalZeroProcess.weight
        (fun ω => Real.exp
          (lam * (unitIntervalZeroProcess.X ω t -
            unitIntervalZeroProcess.X ω s))) ≤
      Real.exp
        (lam ^ 2 * unitIntervalZeroProcess.varianceProxy *
          unitIntervalZeroProcess.dist s t ^ 2 / 2) :=
  unitIntervalZeroProcess.increment_mgf s t lam

/-- Supremum of a constant zero finite family. -/
private lemma finiteSup_zero {α : Type*} [Fintype α] [Nonempty α] :
    finiteSup (fun _ : α => (0 : ℝ)) = 0 := by
  unfold finiteSup
  simp

/-- The zero process satisfies the global-budget total-bounded Dudley boundary
adapter with budget zero.

The conclusion is numerically trivial, but the proof routes a concrete
non-finite index space and a concrete finite process through the same
total-bounded boundary adapter used by the general bridge.
-/
theorem unitIntervalZeroProcess_globalBudget :
    finiteExpectation unitIntervalZeroProcess.weight (fun _ : Bool => (0 : ℝ)) ≤ 0 := by
  classical
  let P := unitIntervalZeroProcess
  have hdistP : P.dist = fun s t : UnitInterval => dist s t := rfl
  have hvariance : 0 < P.varianceProxy := by
    norm_num [P, unitIntervalZeroProcess]
  have hentropy_antitone : Antitone (fun _ : ℝ => (0 : ℝ)) := by
    intro a b hab
    rfl
  have hchoose :
      ∀ eta : ℝ, 0 < eta →
        ∃ m : ℕ,
          EpsilonizedSupremumBoundaryChoice
            (P := P) (hT := unitInterval_totallyBounded_univ)
            (coarseBudget := fun _ : ℕ => (0 : ℝ))
            (radiusScale := (1 : ℝ)) (hradiusScale := by norm_num)
            (entropyAtRadius := fun _ : ℝ => (0 : ℝ))
            (supFunctional := fun _ : Bool => (0 : ℝ)) eta m := by
    intro eta heta
    refine ⟨0, ?_⟩
    unfold EpsilonizedSupremumBoundaryChoice
    refine ⟨PUnit, inferInstance, inferInstance,
      (fun _ => unitIntervalZero), (fun _ => PUnit.unit),
      (fun _ => unitIntervalZero), 0, 0, 0, ?_⟩
    refine ⟨by linarith, ?_⟩
    refine ⟨by simp, ?_⟩
    refine ⟨by simp, ?_⟩
    refine ⟨by simp, ?_⟩
    refine ⟨by intro ω; simp [P, unitIntervalZeroProcess], ?_⟩
    refine ⟨by intro ω t; simp [P, unitIntervalZeroProcess], ?_⟩
    refine ⟨by intro ω s t hst; simp [P, unitIntervalZeroProcess], ?_⟩
    simp [P, unitIntervalZeroProcess, finiteExpectation_const_of_sum_one,
      finiteSup_zero]
  have hbudget :
      ∀ m : ℕ,
        (fun _ : ℕ => (0 : ℝ)) m + 4 * Real.sqrt (2 * P.varianceProxy) *
            (∫ ε in ((1 : ℝ) / (2 : ℝ) ^ (m + 1))..((1 : ℝ) / 2),
              (fun _ : ℝ => (0 : ℝ)) ε) ≤
          (0 : ℝ) := by
    intro m
    simp
  exact
    finite_epsilonizedSup_modulus_dudley_totalBounded_globalBudget
      (P := P) (hT := unitInterval_totallyBounded_univ)
      (coarseBudget := fun _ : ℕ => (0 : ℝ))
      (radiusScale := (1 : ℝ))
      (entropyAtRadius := fun _ : ℝ => (0 : ℝ))
      (supFunctional := fun _ : Bool => (0 : ℝ))
      (globalBudget := (0 : ℝ))
      (by norm_num) hdistP hvariance hentropy_antitone hchoose hbudget

/-! ## Nontrivial next process: a Rademacher linear process -/

/-- Squared metric distance on the unit interval as a real square. -/
private lemma unitInterval_dist_sq_eq (s t : UnitInterval) :
    dist s t ^ 2 = (t.1 - s.1) ^ 2 := by
  change |(s : ℝ) - (t : ℝ)| ^ 2 = (t.1 - s.1) ^ 2
  rw [sq_abs]
  ring

/-- The one-coordinate Rademacher MGF bound for the unit-interval linear
process. -/
theorem unitInterval_rademacherLinear_mgf_bound
    (s t : UnitInterval) (lam : ℝ) :
    finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
        (fun ω => Real.exp
          (lam * (signOfBool ω * t.1 - signOfBool ω * s.1))) ≤
      Real.exp (lam ^ 2 * dist s t ^ 2 / 2) := by
  calc
    finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
        (fun ω => Real.exp
          (lam * (signOfBool ω * t.1 - signOfBool ω * s.1)))
        = (∑ b : Bool, Real.exp (lam * signOfBool b * (t.1 - s.1))) / 2 := by
          unfold finiteExpectation
          calc
            (∑ ω : Bool, (fun _ : Bool => (1 : ℝ) / 2) ω *
                (fun ω => Real.exp
                  (lam * (signOfBool ω * t.1 - signOfBool ω * s.1))) ω)
                = ∑ ω : Bool,
                    (1 / 2 : ℝ) *
                      Real.exp (lam * signOfBool ω * (t.1 - s.1)) := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  congr 1
                  ring_nf
            _ = (1 / 2 : ℝ) *
                  ∑ b : Bool, Real.exp
                    (lam * signOfBool b * (t.1 - s.1)) := by
                  rw [Finset.mul_sum]
            _ = (∑ b : Bool, Real.exp
                    (lam * signOfBool b * (t.1 - s.1))) / 2 := by
                  ring
    _ ≤ Real.exp (lam ^ 2 * (t.1 - s.1) ^ 2 / 2) := by
          rw [avg_exp_sign]
          exact cosh_le_exp_sq_half lam (t.1 - s.1)
    _ = Real.exp (lam ^ 2 * dist s t ^ 2 / 2) := by
          congr 1
          rw [unitInterval_dist_sq_eq]

/-- The Rademacher linear process over the unit interval.

This is the nontrivial follow-on process for the non-finite bridge:
`X(b,t) = signOfBool b * t`.
-/
def unitIntervalRademacherLinearProcess :
    FiniteSubGaussianProcess Bool UnitInterval :=
  { weight := fun _ => (1 : ℝ) / 2
    weight_nonneg := by
      intro ω
      norm_num
    weight_sum_one := by
      simp
    X := fun ω t => signOfBool ω * t.1
    dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    varianceProxy := 1
    varianceProxy_nonneg := by norm_num
    mgf_increment := by
      intro s t lam
      simpa [mul_assoc] using
        unitInterval_rademacherLinear_mgf_bound s t lam }

/-- The packaged Rademacher linear process satisfies the finite
sub-Gaussian increment MGF bound. -/
theorem unitIntervalRademacherLinearProcess_increment_mgf
    (s t : UnitInterval) (lam : ℝ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => Real.exp
          (lam * (unitIntervalRademacherLinearProcess.X ω t -
            unitIntervalRademacherLinearProcess.X ω s))) ≤
      Real.exp
        (lam ^ 2 * unitIntervalRademacherLinearProcess.varianceProxy *
          unitIntervalRademacherLinearProcess.dist s t ^ 2 / 2) :=
  unitIntervalRademacherLinearProcess.increment_mgf s t lam

/-- Explicit one-step increment bound between the half and quarter meshes.

The ambient index space is the non-finite unit interval, while the supremum
here is over the finite realized projection-pair family. The concrete mesh
sizes give the displayed `log 15` entropy term. -/
theorem unitIntervalRademacherLinear_halfQuarter_increment_log15_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun pair :
            FiniteNet.ProjectionPair unitIntervalHalfMeshNet
              unitIntervalQuarterMeshNet =>
          unitIntervalRademacherLinearProcess.X ω
              (unitIntervalQuarterMeshNet.center pair.1.2) -
            unitIntervalRademacherLinearProcess.X ω
              (unitIntervalHalfMeshNet.center pair.1.1))) ≤
      Real.sqrt
        (2 * unitIntervalRademacherLinearProcess.varianceProxy *
          (unitIntervalHalfMeshNet.radius + unitIntervalQuarterMeshNet.radius) ^ 2 *
            Real.log (15 : ℝ)) := by
  have hbase :=
    FiniteSubGaussianProcess.increment_family_expectedSup_le_of_radius_sqrt
      (P := unitIntervalRademacherLinearProcess)
      (left := fun pair :
          FiniteNet.ProjectionPair unitIntervalHalfMeshNet
            unitIntervalQuarterMeshNet =>
        unitIntervalHalfMeshNet.center pair.1.1)
      (right := fun pair :
          FiniteNet.ProjectionPair unitIntervalHalfMeshNet
            unitIntervalQuarterMeshNet =>
        unitIntervalQuarterMeshNet.center pair.1.2)
      (r := unitIntervalHalfMeshNet.radius + unitIntervalQuarterMeshNet.radius)
      (hvariance := by norm_num [unitIntervalRademacherLinearProcess])
      (hr := by
        intro pair
        simpa [unitIntervalRademacherLinearProcess, unitIntervalHalfMeshNet]
          using
            FiniteNet.projectionPair_dist_le_radius_sum
              unitIntervalHalfMeshNet unitIntervalQuarterMeshNet
              (by rfl)
              (by intro s t; exact dist_comm s t)
              (by intro x y z; exact dist_triangle x y z)
              pair)
      (hr_pos := by
        norm_num [unitIntervalHalfMeshNet, unitIntervalQuarterMeshNet])
      (hcard := unitIntervalHalfQuarterPair_card_gt_one)
  refine hbase.trans ?_
  apply Real.sqrt_le_sqrt
  have hcoef_nonneg :
      0 ≤
        2 * unitIntervalRademacherLinearProcess.varianceProxy *
          (unitIntervalHalfMeshNet.radius + unitIntervalQuarterMeshNet.radius) ^ 2 := by
    nlinarith [unitIntervalRademacherLinearProcess.varianceProxy_nonneg,
      sq_nonneg (unitIntervalHalfMeshNet.radius + unitIntervalQuarterMeshNet.radius)]
  refine mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
  calc
    Real.log
        (Fintype.card
          (FiniteNet.ProjectionPair unitIntervalHalfMeshNet
            unitIntervalQuarterMeshNet) : ℝ) ≤
        Real.log
          (unitIntervalHalfMeshNet.coveringNumber *
            unitIntervalQuarterMeshNet.coveringNumber : ℝ) :=
          FiniteNet.projectionPair_log_card_le_log_coveringNumber_mul
            unitIntervalHalfMeshNet unitIntervalQuarterMeshNet
    _ = Real.log (15 : ℝ) := by
          norm_num [unitIntervalHalfMeshNet_coveringNumber,
            unitIntervalQuarterMeshNet_coveringNumber]

/-! ## Nonzero supplied-supremum witness -/

/-- Supplied supremum functional for the Rademacher linear process over the
unit interval. It is `1` for the positive sign and `0` for the negative sign. -/
def unitIntervalRademacherLinearSup : Bool → ℝ :=
  fun b => if b then 1 else 0

@[simp] theorem unitIntervalRademacherLinearSup_true :
    unitIntervalRademacherLinearSup true = 1 := by
  rfl

@[simp] theorem unitIntervalRademacherLinearSup_false :
    unitIntervalRademacherLinearSup false = 0 := by
  rfl

/-- The supplied supremum has nonzero expectation under the fair-sign weights. -/
theorem unitIntervalRademacherLinearSup_expectation :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      unitIntervalRademacherLinearSup = (1 : ℝ) / 2 := by
  simp [unitIntervalRademacherLinearProcess, unitIntervalRademacherLinearSup,
    finiteExpectation]

private lemma unitInterval_value_nonneg (t : UnitInterval) : 0 ≤ (t : ℝ) :=
  t.2.1

private lemma unitInterval_value_le_one (t : UnitInterval) : (t : ℝ) ≤ 1 :=
  t.2.2

/-- The supplied supremum is an upper bound for the full non-finite
unit-interval index family. -/
theorem unitIntervalRademacherLinearSup_upper (ω : Bool) (t : UnitInterval) :
    unitIntervalRademacherLinearProcess.X ω t ≤
      unitIntervalRademacherLinearSup ω := by
  cases ω
  · have ht : 0 ≤ (t : ℝ) := unitInterval_value_nonneg t
    simp [unitIntervalRademacherLinearProcess, unitIntervalRademacherLinearSup,
      signOfBool]
    linarith
  · simpa [unitIntervalRademacherLinearProcess,
      unitIntervalRademacherLinearSup, signOfBool] using
      unitInterval_value_le_one t

/-- The supplied supremum is attained by an endpoint of the unit interval. -/
theorem unitIntervalRademacherLinearSup_attained (ω : Bool) :
    ∃ t : UnitInterval,
      unitIntervalRademacherLinearProcess.X ω t =
        unitIntervalRademacherLinearSup ω := by
  cases ω
  · refine ⟨unitIntervalZero, ?_⟩
    norm_num [unitIntervalRademacherLinearProcess,
      unitIntervalRademacherLinearSup, unitIntervalZero, signOfBool]
  · refine ⟨unitIntervalOne, ?_⟩
    norm_num [unitIntervalRademacherLinearProcess,
      unitIntervalRademacherLinearSup, unitIntervalOne, signOfBool]

/-- The supplied supremum is the least upper bound of the non-finite
unit-interval index family. -/
theorem unitIntervalRademacherLinearSup_isLeastUpperBound (ω : Bool) :
    IsLeast
      {c : ℝ | ∀ t : UnitInterval,
        unitIntervalRademacherLinearProcess.X ω t ≤ c}
      (unitIntervalRademacherLinearSup ω) := by
  constructor
  · exact unitIntervalRademacherLinearSup_upper ω
  · intro c hc
    obtain ⟨t, ht⟩ := unitIntervalRademacherLinearSup_attained ω
    rw [← ht]
    exact hc t

/-- The supplied supremum is the least upper bound of the actual range of the
unit-interval Rademacher process. -/
theorem unitIntervalRademacherLinearSup_isLUB_range (ω : Bool) :
    IsLUB
      (Set.range (fun t : UnitInterval =>
        unitIntervalRademacherLinearProcess.X ω t))
      (unitIntervalRademacherLinearSup ω) := by
  constructor
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact unitIntervalRademacherLinearSup_upper ω t
  · intro c hc
    obtain ⟨t, ht⟩ := unitIntervalRademacherLinearSup_attained ω
    rw [← ht]
    exact hc ⟨t, rfl⟩

/-- The supplied supremum is equal to the order supremum of the range of the
unit-interval Rademacher process. -/
theorem unitIntervalRademacherLinearSup_sSup_range (ω : Bool) :
    sSup
      (Set.range (fun t : UnitInterval =>
        unitIntervalRademacherLinearProcess.X ω t)) =
      unitIntervalRademacherLinearSup ω :=
  (unitIntervalRademacherLinearSup_isLUB_range ω).csSup_eq (Set.range_nonempty _)

private lemma rademacherLinear_value_le_one (ω : Bool) (t : UnitInterval) :
    signOfBool ω * (t : ℝ) ≤ 1 := by
  cases ω
  · have ht : 0 ≤ (t : ℝ) := unitInterval_value_nonneg t
    simp [signOfBool]
    linarith
  · simpa [signOfBool] using unitInterval_value_le_one t

private lemma rademacherLinear_value_ge_neg_one (ω : Bool) (t : UnitInterval) :
    -1 ≤ signOfBool ω * (t : ℝ) := by
  cases ω
  · have ht : (t : ℝ) ≤ 1 := unitInterval_value_le_one t
    simp [signOfBool]
    linarith
  · have ht : 0 ≤ (t : ℝ) := unitInterval_value_nonneg t
    simp [signOfBool]
    linarith

private lemma finiteSup_rademacherLinear_le_one
    {α : Type*} [Fintype α] [Nonempty α]
    (ω : Bool) (f : α → UnitInterval) :
    finiteSup (fun a : α => signOfBool ω * (f a : ℝ)) ≤ 1 := by
  unfold finiteSup
  exact Finset.sup'_le Finset.univ_nonempty _ fun a _ha =>
    rademacherLinear_value_le_one ω (f a)

private lemma finiteSup_rademacherLinear_ge_neg_one
    {α : Type*} [Fintype α] [Nonempty α]
    (ω : Bool) (f : α → UnitInterval) :
    -1 ≤ finiteSup (fun a : α => signOfBool ω * (f a : ℝ)) := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  unfold finiteSup
  exact (rademacherLinear_value_ge_neg_one ω (f a)).trans
    (Finset.le_sup' (fun a : α => signOfBool ω * (f a : ℝ)) (Finset.mem_univ a))

/-! ## Explicit half/quarter mesh sequence -/

/-- Index type for the first explicit unit-interval mesh sequence: the
three-point half mesh at scale `0`, and the five-point quarter mesh afterward.
-/
private abbrev unitIntervalExplicitMeshIndex : ℕ → Type
  | 0 => Fin 3
  | _ + 1 => Fin 5

private instance unitIntervalExplicitMeshIndex_fintype :
    (j : ℕ) → Fintype (unitIntervalExplicitMeshIndex j)
  | 0 => inferInstance
  | _ + 1 => inferInstance

/-- The first explicit unit-interval mesh sequence used by the projected
finite-net Dudley comparison. -/
private def unitIntervalExplicitMeshNet :
    ∀ j : ℕ, FiniteNet UnitInterval (unitIntervalExplicitMeshIndex j)
  | 0 => unitIntervalHalfMeshNet
  | _ + 1 => unitIntervalQuarterMeshNet

private theorem unitIntervalExplicitMeshNet_dist
    (j : ℕ) :
    (unitIntervalExplicitMeshNet j).dist =
      unitIntervalRademacherLinearProcess.dist := by
  by_cases hj : j = 0
  · subst j
    rfl
  · cases j with
    | zero => contradiction
    | succ j => rfl

private theorem unitIntervalExplicitMeshNet_radius_pos_m1 :
    ∀ j ∈ Finset.range 1,
      0 < (unitIntervalExplicitMeshNet j).radius +
        (unitIntervalExplicitMeshNet (j + 1)).radius := by
  intro j hj
  simp at hj
  subst j
  norm_num [unitIntervalExplicitMeshNet, unitIntervalExplicitMeshIndex,
    unitIntervalHalfMeshNet, unitIntervalQuarterMeshNet]

private theorem unitIntervalExplicitMeshNet_radius_geometric_m1 :
    ∀ j ∈ Finset.range 1,
      (unitIntervalExplicitMeshNet j).radius +
          (unitIntervalExplicitMeshNet (j + 1)).radius ≤
        (1 : ℝ) / (2 : ℝ) ^ j := by
  intro j hj
  simp at hj
  subst j
  norm_num [unitIntervalExplicitMeshNet, unitIntervalExplicitMeshIndex,
    unitIntervalHalfMeshNet, unitIntervalQuarterMeshNet]

private theorem unitIntervalExplicitMeshNet_pair_card_gt_one_m1 :
    ∀ j ∈ Finset.range 1,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (unitIntervalExplicitMeshNet j)
          (unitIntervalExplicitMeshNet (j + 1))) := by
  intro j hj
  simp at hj
  subst j
  simpa [unitIntervalExplicitMeshNet, unitIntervalExplicitMeshIndex]
    using unitIntervalHalfQuarterPair_card_gt_one

private theorem unitIntervalExplicitMeshNet_coverCount_le_15_m1 :
    ∀ j ∈ Finset.range 1,
      (unitIntervalExplicitMeshNet j).coveringNumber *
          (unitIntervalExplicitMeshNet (j + 1)).coveringNumber ≤
        (fun _ : ℕ => 15) j := by
  intro j hj
  simp at hj
  subst j
  change
    unitIntervalHalfMeshNet.coveringNumber *
        unitIntervalQuarterMeshNet.coveringNumber ≤
      15
  rw [unitIntervalHalfQuarter_coveringNumber_product]

private theorem unitIntervalRademacherLinear_explicitMesh_coarse_m1 :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (unitIntervalExplicitMeshNet 1) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalExplicitMeshNet 0).projection
              (FiniteNet.ProjectedIndex.source (unitIntervalExplicitMeshNet 1) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (unitIntervalExplicitMeshNet 1) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalExplicitMeshNet 0).projection
              (FiniteNet.ProjectedIndex.source (unitIntervalExplicitMeshNet 1) u))))
        ≤ finiteExpectation unitIntervalRademacherLinearProcess.weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono
            unitIntervalRademacherLinearProcess.weight_nonneg ?_
          intro ω
          simpa [unitIntervalRademacherLinearProcess] using
            finiteSup_rademacherLinear_le_one ω
              (fun u : FiniteNet.ProjectedIndex (unitIntervalExplicitMeshNet 1) =>
                (unitIntervalExplicitMeshNet 0).projection
                  (FiniteNet.ProjectedIndex.source
                    (unitIntervalExplicitMeshNet 1) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            unitIntervalRademacherLinearProcess.weight 1
            unitIntervalRademacherLinearProcess.weight_sum_one

/-- Explicit `m = 1` projected finite-net Dudley bound for the unit-interval
Rademacher process, paying the concrete half/quarter mesh product count `15`.
-/
theorem unitIntervalRademacherLinear_projectedQuarterMesh_dudley_log15_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
            unitIntervalRademacherLinearProcess.X ω
              (unitIntervalQuarterMeshNet.center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
      (P := unitIntervalRademacherLinearProcess)
      (A := unitIntervalExplicitMeshIndex)
      (N := unitIntervalExplicitMeshNet)
      (m := 1) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (coverCount := fun _ : ℕ => 15)
      unitIntervalExplicitMeshNet_dist
      (by intro s t; exact dist_comm s t)
      (by intro x y z; exact dist_triangle x y z)
      (by norm_num [unitIntervalRademacherLinearProcess])
      (by norm_num)
      unitIntervalExplicitMeshNet_radius_pos_m1
      unitIntervalExplicitMeshNet_radius_geometric_m1
      unitIntervalExplicitMeshNet_pair_card_gt_one_m1
      unitIntervalExplicitMeshNet_coverCount_le_15_m1
      unitIntervalRademacherLinear_explicitMesh_coarse_m1
  simpa [unitIntervalExplicitMeshNet, unitIntervalExplicitMeshIndex,
    unitIntervalRademacherLinearProcess] using hbase

/-! ## Rounded generic dyadic grid sequence -/

/-- The generic rounded dyadic grid sequence starts at level `1`, then moves to
level `2`, and so on. Thus its first two nets have `3` and `5` centers and
the same covering radii as the explicit half/quarter meshes. -/
abbrev unitIntervalRoundedDyadicGridIndex (j : ℕ) : Type :=
  unitIntervalDyadicGridIndex (j + 1)

/-- The shifted rounded dyadic net sequence used by the finite-scale Dudley
chain. Net `j` is the rounded dyadic grid at level `j + 1`. -/
def unitIntervalRoundedDyadicGridNet (j : ℕ) :
    FiniteNet UnitInterval (unitIntervalRoundedDyadicGridIndex j) :=
  unitIntervalDyadicRoundedGridNet (j + 1)

/-- Product-count envelope for adjacent shifted rounded dyadic grid levels. -/
def unitIntervalRoundedDyadicGridCoverCount (j : ℕ) : ℕ :=
  (2 ^ (j + 1) + 1) * (2 ^ (j + 2) + 1)

/-- The adjacent rounded-dyadic-grid product-count envelope is monotone in the
scale. -/
theorem monotone_unitIntervalRoundedDyadicGridCoverCount :
    Monotone unitIntervalRoundedDyadicGridCoverCount := by
  intro i j hij
  dsimp [unitIntervalRoundedDyadicGridCoverCount]
  have hpow_left : 2 ^ (i + 1) ≤ 2 ^ (j + 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (Nat.add_le_add_right hij 1)
  have hpow_right : 2 ^ (i + 2) ≤ 2 ^ (j + 2) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (Nat.add_le_add_right hij 2)
  exact Nat.mul_le_mul
    (Nat.add_le_add_right hpow_left 1)
    (Nat.add_le_add_right hpow_right 1)

/-- The rounded-dyadic-grid entropy-at-scale sequence is monotone, so the
finite prefix-sup envelope can be eliminated from arbitrary finite-horizon
bounds. -/
theorem monotone_unitIntervalRoundedDyadicGridEntropy :
    Monotone
      (fun j : ℕ =>
        Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) := by
  intro i j hij
  have hcount_pos_nat : 0 < unitIntervalRoundedDyadicGridCoverCount i := by
    dsimp [unitIntervalRoundedDyadicGridCoverCount]
    positivity
  have hcount_pos : 0 < (unitIntervalRoundedDyadicGridCoverCount i : ℝ) := by
    exact_mod_cast hcount_pos_nat
  exact Real.sqrt_le_sqrt
    (Real.log_le_log hcount_pos
      (by
        exact_mod_cast monotone_unitIntervalRoundedDyadicGridCoverCount hij))

/-- Prefix-sup simplification for the rounded-dyadic-grid entropy sequence. -/
theorem unitIntervalRoundedDyadicGridEntropy_prefixSup :
    FiniteSubGaussianProcess.finitePrefixSupEnvelope
        (fun j : ℕ =>
          Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) =
      (fun j : ℕ =>
          Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) :=
  FiniteSubGaussianProcess.finitePrefixSupEnvelope_eq_self_of_monotone
    monotone_unitIntervalRoundedDyadicGridEntropy

theorem unitIntervalRoundedDyadicGridNet_dist
    (j : ℕ) :
    (unitIntervalRoundedDyadicGridNet j).dist =
      unitIntervalRademacherLinearProcess.dist := by
  rfl

theorem unitIntervalRoundedDyadicGridNet_radius_pos (j : ℕ) :
    0 < (unitIntervalRoundedDyadicGridNet j).radius +
      (unitIntervalRoundedDyadicGridNet (j + 1)).radius := by
  have hleft : 0 < (unitIntervalRoundedDyadicGridNet j).radius := by
    simp [unitIntervalRoundedDyadicGridNet, unitIntervalDyadicRoundedGridNet]
  have hright : 0 ≤ (unitIntervalRoundedDyadicGridNet (j + 1)).radius :=
    (unitIntervalRoundedDyadicGridNet (j + 1)).radius_nonneg
  exact add_pos_of_pos_of_nonneg hleft hright

theorem unitIntervalRoundedDyadicGridNet_radius_geometric (j : ℕ) :
    (unitIntervalRoundedDyadicGridNet j).radius +
        (unitIntervalRoundedDyadicGridNet (j + 1)).radius ≤
      (1 : ℝ) / (2 : ℝ) ^ j := by
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  have hleft :
      (unitIntervalRoundedDyadicGridNet j).radius =
        (1 : ℝ) / ((2 : ℝ) ^ (j + 2)) := by
    simp [unitIntervalRoundedDyadicGridNet, unitIntervalDyadicRoundedGridNet,
      Nat.cast_pow]
  have hright :
      (unitIntervalRoundedDyadicGridNet (j + 1)).radius =
        (1 : ℝ) / ((2 : ℝ) ^ (j + 3)) := by
    simp [unitIntervalRoundedDyadicGridNet, unitIntervalDyadicRoundedGridNet,
      Nat.cast_pow]
  rw [hleft, hright]
  have hscaled :
      (1 : ℝ) / ((2 : ℝ) ^ (j + 2)) +
          (1 : ℝ) / ((2 : ℝ) ^ (j + 3)) =
        (3 : ℝ) / (8 * (2 : ℝ) ^ j) := by
    field_simp [hpow_pos.ne']
    ring
  rw [hscaled]
  have hmul : (3 : ℝ) ≤ 8 := by norm_num
  have hden_pos : 0 < (8 : ℝ) * (2 : ℝ) ^ j := by positivity
  calc
    (3 : ℝ) / (8 * (2 : ℝ) ^ j)
        ≤ 8 / (8 * (2 : ℝ) ^ j) :=
          div_le_div_of_nonneg_right hmul hden_pos.le
    _ = (1 : ℝ) / (2 : ℝ) ^ j := by
          field_simp [hpow_pos.ne']

theorem unitIntervalRoundedDyadicGridNet_coveringNumber_product (j : ℕ) :
    (unitIntervalRoundedDyadicGridNet j).coveringNumber *
        (unitIntervalRoundedDyadicGridNet (j + 1)).coveringNumber =
      unitIntervalRoundedDyadicGridCoverCount j := by
  rw [unitIntervalRoundedDyadicGridNet, unitIntervalRoundedDyadicGridNet,
    unitIntervalDyadicRoundedGridNet_coveringNumber,
    unitIntervalDyadicRoundedGridNet_coveringNumber]
  simp [unitIntervalRoundedDyadicGridCoverCount, add_comm, add_left_comm]

private theorem unitIntervalRoundedDyadicGridNet_radius_le_quarter (j : ℕ) :
    (unitIntervalRoundedDyadicGridNet j).radius ≤ (1 : ℝ) / 4 := by
  have hpow_nat : 4 ≤ (2 : ℕ) ^ (j + 2) := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 2 ≤ j + 2)
    norm_num at h
    exact h
  have hden_ge : (4 : ℝ) ≤ (((2 : ℕ) ^ (j + 2) : ℕ) : ℝ) := by
    exact_mod_cast hpow_nat
  have hden_pos : 0 < ((((2 : ℕ) ^ (j + 2) : ℕ) : ℝ)) := by
    positivity
  have hle :
      (1 : ℝ) / ((((2 : ℕ) ^ (j + 2) : ℕ) : ℝ)) ≤ (1 : ℝ) / 4 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hden_ge
  simpa [unitIntervalRoundedDyadicGridNet, unitIntervalDyadicRoundedGridNet,
    Nat.add_assoc] using hle

theorem unitIntervalRoundedDyadicGridNet_pair_card_gt_one (j : ℕ) :
    1 < Fintype.card
      (FiniteNet.ProjectionPair
        (unitIntervalRoundedDyadicGridNet j)
        (unitIntervalRoundedDyadicGridNet (j + 1))) := by
  classical
  let N0 := unitIntervalRoundedDyadicGridNet j
  let N1 := unitIntervalRoundedDyadicGridNet (j + 1)
  let p0 : FiniteNet.ProjectionPair N0 N1 :=
    FiniteNet.projectionPairOf N0 N1 unitIntervalZero
  let p1 : FiniteNet.ProjectionPair N0 N1 :=
    FiniteNet.projectionPairOf N0 N1 unitIntervalOne
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hproj :
      N0.project unitIntervalZero = N0.project unitIntervalOne := by
    exact congrArg (fun p : FiniteNet.ProjectionPair N0 N1 => p.1.1) hp
  have hcenter :
      N0.projection unitIntervalZero = N0.projection unitIntervalOne := by
    simp [FiniteNet.projection, hproj]
  have hzero :
      dist unitIntervalZero (N0.projection unitIntervalZero) ≤ N0.radius :=
    N0.projection_dist_le unitIntervalZero
  have hone :
      dist (N0.projection unitIntervalZero) unitIntervalOne ≤ N0.radius := by
    have h := N0.projection_dist_le unitIntervalOne
    rw [hcenter]
    simpa [dist_comm] using h
  have hdist_le :
      dist unitIntervalZero unitIntervalOne ≤ N0.radius + N0.radius := by
    calc
      dist unitIntervalZero unitIntervalOne
          ≤ dist unitIntervalZero (N0.projection unitIntervalZero) +
              dist (N0.projection unitIntervalZero) unitIntervalOne :=
            dist_triangle unitIntervalZero (N0.projection unitIntervalZero)
              unitIntervalOne
      _ ≤ N0.radius + N0.radius := add_le_add hzero hone
  have hradius_le :
      N0.radius + N0.radius ≤ (1 : ℝ) / 2 := by
    have h := unitIntervalRoundedDyadicGridNet_radius_le_quarter j
    nlinarith
  have hdist_half :
      dist unitIntervalZero unitIntervalOne ≤ (1 : ℝ) / 2 :=
    hdist_le.trans hradius_le
  norm_num [dist_unitIntervalZero_unitIntervalOne] at hdist_half

theorem unitIntervalRoundedDyadicGridNet_coverCount_le (j : ℕ) :
    (unitIntervalRoundedDyadicGridNet j).coveringNumber *
        (unitIntervalRoundedDyadicGridNet (j + 1)).coveringNumber ≤
      unitIntervalRoundedDyadicGridCoverCount j := by
  rw [unitIntervalRoundedDyadicGridNet_coveringNumber_product]

theorem unitIntervalRoundedDyadicGridNet_radius_pos_range (m : ℕ) :
    ∀ j ∈ Finset.range m,
      0 < (unitIntervalRoundedDyadicGridNet j).radius +
        (unitIntervalRoundedDyadicGridNet (j + 1)).radius := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_pos j

theorem unitIntervalRoundedDyadicGridNet_radius_geometric_range (m : ℕ) :
    ∀ j ∈ Finset.range m,
      (unitIntervalRoundedDyadicGridNet j).radius +
          (unitIntervalRoundedDyadicGridNet (j + 1)).radius ≤
        (1 : ℝ) / (2 : ℝ) ^ j := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_geometric j

theorem unitIntervalRoundedDyadicGridNet_pair_card_gt_one_range (m : ℕ) :
    ∀ j ∈ Finset.range m,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (unitIntervalRoundedDyadicGridNet j)
          (unitIntervalRoundedDyadicGridNet (j + 1))) := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_pair_card_gt_one j

theorem unitIntervalRoundedDyadicGridNet_coverCount_le_range (m : ℕ) :
    ∀ j ∈ Finset.range m,
      (unitIntervalRoundedDyadicGridNet j).coveringNumber *
          (unitIntervalRoundedDyadicGridNet (j + 1)).coveringNumber ≤
        unitIntervalRoundedDyadicGridCoverCount j := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_coverCount_le j

private theorem unitIntervalRoundedDyadicGridNet_radius_pos_m1 :
    ∀ j ∈ Finset.range 1,
      0 < (unitIntervalRoundedDyadicGridNet j).radius +
        (unitIntervalRoundedDyadicGridNet (j + 1)).radius := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_pos j

private theorem unitIntervalRoundedDyadicGridNet_radius_geometric_m1 :
    ∀ j ∈ Finset.range 1,
      (unitIntervalRoundedDyadicGridNet j).radius +
          (unitIntervalRoundedDyadicGridNet (j + 1)).radius ≤
        (1 : ℝ) / (2 : ℝ) ^ j := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_geometric j

private theorem unitIntervalRoundedDyadicGridNet_pair_card_gt_one_m1 :
    ∀ j ∈ Finset.range 1,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (unitIntervalRoundedDyadicGridNet j)
          (unitIntervalRoundedDyadicGridNet (j + 1))) := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_pair_card_gt_one j

private theorem unitIntervalRoundedDyadicGridNet_coverCount_le_15_m1 :
    ∀ j ∈ Finset.range 1,
      (unitIntervalRoundedDyadicGridNet j).coveringNumber *
          (unitIntervalRoundedDyadicGridNet (j + 1)).coveringNumber ≤
        (fun _ : ℕ => 15) j := by
  intro j hj
  simp at hj
  subst j
  change
    (unitIntervalDyadicRoundedGridNet 1).coveringNumber *
        (unitIntervalDyadicRoundedGridNet 2).coveringNumber ≤
      15
  rw [unitIntervalDyadicRoundedGridNet_coveringNumber_one,
    unitIntervalDyadicRoundedGridNet_coveringNumber_two]

private theorem unitIntervalRoundedDyadicGridNet_radius_pos_m2 :
    ∀ j ∈ Finset.range 2,
      0 < (unitIntervalRoundedDyadicGridNet j).radius +
        (unitIntervalRoundedDyadicGridNet (j + 1)).radius := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_pos j

private theorem unitIntervalRoundedDyadicGridNet_radius_geometric_m2 :
    ∀ j ∈ Finset.range 2,
      (unitIntervalRoundedDyadicGridNet j).radius +
          (unitIntervalRoundedDyadicGridNet (j + 1)).radius ≤
        (1 : ℝ) / (2 : ℝ) ^ j := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_radius_geometric j

private theorem unitIntervalRoundedDyadicGridNet_pair_card_gt_one_m2 :
    ∀ j ∈ Finset.range 2,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (unitIntervalRoundedDyadicGridNet j)
          (unitIntervalRoundedDyadicGridNet (j + 1))) := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_pair_card_gt_one j

private theorem unitIntervalRoundedDyadicGridNet_coverCount_le_m2 :
    ∀ j ∈ Finset.range 2,
      (unitIntervalRoundedDyadicGridNet j).coveringNumber *
          (unitIntervalRoundedDyadicGridNet (j + 1)).coveringNumber ≤
        unitIntervalRoundedDyadicGridCoverCount j := by
  intro j _hj
  exact unitIntervalRoundedDyadicGridNet_coverCount_le j

private theorem unitIntervalRademacherLinear_roundedDyadicGrid_coarse_m1 :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalRoundedDyadicGridNet 1) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalRoundedDyadicGridNet 0).projection
              (FiniteNet.ProjectedIndex.source
                (unitIntervalRoundedDyadicGridNet 1) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalRoundedDyadicGridNet 1) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalRoundedDyadicGridNet 0).projection
              (FiniteNet.ProjectedIndex.source
                (unitIntervalRoundedDyadicGridNet 1) u))))
        ≤ finiteExpectation unitIntervalRademacherLinearProcess.weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono
            unitIntervalRademacherLinearProcess.weight_nonneg ?_
          intro ω
          simpa [unitIntervalRademacherLinearProcess] using
            finiteSup_rademacherLinear_le_one ω
              (fun u : FiniteNet.ProjectedIndex
                  (unitIntervalRoundedDyadicGridNet 1) =>
                (unitIntervalRoundedDyadicGridNet 0).projection
                  (FiniteNet.ProjectedIndex.source
                    (unitIntervalRoundedDyadicGridNet 1) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            unitIntervalRademacherLinearProcess.weight 1
            unitIntervalRademacherLinearProcess.weight_sum_one

private theorem unitIntervalRademacherLinear_roundedDyadicGrid_coarse
    (m : ℕ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalRoundedDyadicGridNet m) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalRoundedDyadicGridNet 0).projection
              (FiniteNet.ProjectedIndex.source
                (unitIntervalRoundedDyadicGridNet m) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalRoundedDyadicGridNet m) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalRoundedDyadicGridNet 0).projection
              (FiniteNet.ProjectedIndex.source
                (unitIntervalRoundedDyadicGridNet m) u))))
        ≤ finiteExpectation unitIntervalRademacherLinearProcess.weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono
            unitIntervalRademacherLinearProcess.weight_nonneg ?_
          intro ω
          simpa [unitIntervalRademacherLinearProcess] using
            finiteSup_rademacherLinear_le_one ω
              (fun u : FiniteNet.ProjectedIndex
                  (unitIntervalRoundedDyadicGridNet m) =>
                (unitIntervalRoundedDyadicGridNet 0).projection
                  (FiniteNet.ProjectedIndex.source
                    (unitIntervalRoundedDyadicGridNet m) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            unitIntervalRademacherLinearProcess.weight 1
            unitIntervalRademacherLinearProcess.weight_sum_one

/-- Generic rounded-dyadic-grid `m = 1` projected finite-net Dudley bound for
the unit-interval Rademacher process. This replaces the bespoke half/quarter
mesh sequence with `unitIntervalDyadicRoundedGridNet 1` and
`unitIntervalDyadicRoundedGridNet 2`. -/
theorem unitIntervalRademacherLinear_roundedDyadicGrid_dudley_log15_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 2) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalDyadicRoundedGridNet 2).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
      (P := unitIntervalRademacherLinearProcess)
      (A := unitIntervalRoundedDyadicGridIndex)
      (N := unitIntervalRoundedDyadicGridNet)
      (m := 1) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (coverCount := fun _ : ℕ => 15)
      unitIntervalRoundedDyadicGridNet_dist
      (by intro s t; exact dist_comm s t)
      (by intro x y z; exact dist_triangle x y z)
      (by norm_num [unitIntervalRademacherLinearProcess])
      (by norm_num)
      unitIntervalRoundedDyadicGridNet_radius_pos_m1
      unitIntervalRoundedDyadicGridNet_radius_geometric_m1
      unitIntervalRoundedDyadicGridNet_pair_card_gt_one_m1
      unitIntervalRoundedDyadicGridNet_coverCount_le_15_m1
      unitIntervalRademacherLinear_roundedDyadicGrid_coarse_m1
  simpa [unitIntervalRoundedDyadicGridNet,
    unitIntervalRoundedDyadicGridIndex,
    unitIntervalRademacherLinearProcess] using hbase

/-- Generic rounded-dyadic-grid `m = 2` projected finite-net Dudley bound for
the unit-interval Rademacher process. This is the first finite-scale theorem
using three rounded dyadic levels, with adjacent product counts supplied by
`unitIntervalRoundedDyadicGridCoverCount`. -/
theorem unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m2_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 3) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalDyadicRoundedGridNet 3).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 2
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
      (P := unitIntervalRademacherLinearProcess)
      (A := unitIntervalRoundedDyadicGridIndex)
      (N := unitIntervalRoundedDyadicGridNet)
      (m := 2) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (coverCount := unitIntervalRoundedDyadicGridCoverCount)
      unitIntervalRoundedDyadicGridNet_dist
      (by intro s t; exact dist_comm s t)
      (by intro x y z; exact dist_triangle x y z)
      (by norm_num [unitIntervalRademacherLinearProcess])
      (by norm_num)
      unitIntervalRoundedDyadicGridNet_radius_pos_m2
      unitIntervalRoundedDyadicGridNet_radius_geometric_m2
      unitIntervalRoundedDyadicGridNet_pair_card_gt_one_m2
      unitIntervalRoundedDyadicGridNet_coverCount_le_m2
      (unitIntervalRademacherLinear_roundedDyadicGrid_coarse 2)
  simpa [unitIntervalRoundedDyadicGridNet,
    unitIntervalRoundedDyadicGridIndex,
    unitIntervalRademacherLinearProcess] using hbase

/-- Generic finite-horizon rounded-dyadic-grid projected Dudley bound for the
unit-interval Rademacher process. The terminal grid is the shifted rounded
dyadic net `unitIntervalRoundedDyadicGridNet m`, and the entropy envelope is
built from the adjacent rounded-grid covering products. -/
theorem unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound
    (m : ℕ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalRoundedDyadicGridNet m) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalRoundedDyadicGridNet m).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope
      (P := unitIntervalRademacherLinearProcess)
      (A := unitIntervalRoundedDyadicGridIndex)
      (N := unitIntervalRoundedDyadicGridNet)
      (m := m) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (coverCount := unitIntervalRoundedDyadicGridCoverCount)
      unitIntervalRoundedDyadicGridNet_dist
      (by intro s t; exact dist_comm s t)
      (by intro x y z; exact dist_triangle x y z)
      (by norm_num [unitIntervalRademacherLinearProcess])
      (by norm_num)
      (unitIntervalRoundedDyadicGridNet_radius_pos_range m)
      (unitIntervalRoundedDyadicGridNet_radius_geometric_range m)
      (unitIntervalRoundedDyadicGridNet_pair_card_gt_one_range m)
      (unitIntervalRoundedDyadicGridNet_coverCount_le_range m)
      (unitIntervalRademacherLinear_roundedDyadicGrid_coarse m)
  simpa [unitIntervalRademacherLinearProcess] using hbase

/-- Prefix-free finite-horizon rounded-dyadic-grid projected Dudley bound.

The rounded-grid product-count entropy is monotone, so the generic prefix-sup
envelope in the chaining theorem simplifies to the scale entropy itself. -/
theorem unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound_prefixFree
    (m : ℕ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalRoundedDyadicGridNet m) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalRoundedDyadicGridNet m).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (fun j : ℕ =>
            Real.sqrt
              (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) := by
  simpa [unitIntervalRoundedDyadicGridEntropy_prefixSup] using
    unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound m

/-- The `m = 3` projected rounded-dyadic-grid Dudley bound. This is a named
corollary of the arbitrary finite-horizon theorem, using terminal level `4`. -/
theorem unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m3_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 4) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalDyadicRoundedGridNet 4).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 3
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  simpa [unitIntervalRoundedDyadicGridNet,
    unitIntervalRoundedDyadicGridIndex,
    unitIntervalRademacherLinearProcess] using
    unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound 3

private lemma unitIntervalRademacherLinearSup_le_projectedQuarterMeshSup
    (ω : Bool) :
    unitIntervalRademacherLinearSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
          unitIntervalRademacherLinearProcess.X ω
            (unitIntervalQuarterMeshNet.center u.1)) := by
  classical
  cases ω
  · let u0 : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet :=
      ⟨unitIntervalQuarterMeshNet.project unitIntervalZero, ⟨unitIntervalZero, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
          unitIntervalRademacherLinearProcess.X false
            (unitIntervalQuarterMeshNet.center u.1))
        (Finset.mem_univ u0)
    have hval :
        unitIntervalRademacherLinearProcess.X false
            (unitIntervalQuarterMeshNet.center u0.1) = 0 := by
      norm_num [u0, unitIntervalRademacherLinearProcess,
        unitIntervalQuarterMeshNet, unitIntervalQuarterMeshProject,
        unitIntervalQuarterMeshCenter, unitIntervalZero, signOfBool]
    have hle0 :
        0 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
            unitIntervalRademacherLinearProcess.X false
              (unitIntervalQuarterMeshNet.center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle0
  · let u1 : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet :=
      ⟨unitIntervalQuarterMeshNet.project unitIntervalOne, ⟨unitIntervalOne, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
          unitIntervalRademacherLinearProcess.X true
            (unitIntervalQuarterMeshNet.center u.1))
        (Finset.mem_univ u1)
    have hval :
        unitIntervalRademacherLinearProcess.X true
            (unitIntervalQuarterMeshNet.center u1.1) = 1 := by
      norm_num [u1, unitIntervalRademacherLinearProcess,
        unitIntervalQuarterMeshNet, unitIntervalQuarterMeshProject,
        unitIntervalQuarterMeshCenter, unitIntervalOne, signOfBool]
    have hle1 :
        1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
            unitIntervalRademacherLinearProcess.X true
              (unitIntervalQuarterMeshNet.center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle1

/-- Explicit projected-quarter finite-net Dudley bound for the supplied
nonzero supremum of the unit-interval Rademacher process.

For this example the explicit quarter mesh contains both endpoints. Therefore
the supplied supremum is pointwise bounded by the projected quarter-mesh
supremum with no terminal-error slack. -/
theorem unitIntervalRademacherLinearSup_projectedQuarterMesh_dudley_log15_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet =>
            unitIntervalRademacherLinearProcess.X ω
              (unitIntervalQuarterMeshNet.center u.1))) := by
        exact finiteExpectation_mono
          unitIntervalRademacherLinearProcess.weight_nonneg
          unitIntervalRademacherLinearSup_le_projectedQuarterMeshSup
    _ ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) :=
        unitIntervalRademacherLinear_projectedQuarterMesh_dudley_log15_bound

/-- Any rounded dyadic grid contains both endpoints, so the supplied supremum
for the Rademacher linear process is pointwise bounded by the projected finite
supremum over that grid. -/
theorem unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup
    (level : ℕ) (ω : Bool) :
    unitIntervalRademacherLinearSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet level) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalDyadicRoundedGridNet level).center u.1)) := by
  classical
  cases ω
  · let u0 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet level) :=
      ⟨(unitIntervalDyadicRoundedGridNet level).project unitIntervalZero,
        ⟨unitIntervalZero, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet level) =>
          unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet level).center u.1))
        (Finset.mem_univ u0)
    have hval :
        unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet level).center u0.1) = 0 := by
      change unitIntervalRademacherLinearProcess.X false
          (unitIntervalDyadicGridCenter level
            (unitIntervalDyadicGridRoundProject level unitIntervalZero)) = 0
      rw [unitIntervalDyadicGridRoundProject_zero,
        unitIntervalDyadicGridCenter_leftEndpoint]
      norm_num [unitIntervalRademacherLinearProcess, unitIntervalZero,
        signOfBool]
    have hle0 :
        0 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet level) =>
            unitIntervalRademacherLinearProcess.X false
              ((unitIntervalDyadicRoundedGridNet level).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle0
  · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet level) :=
      ⟨(unitIntervalDyadicRoundedGridNet level).project unitIntervalOne,
        ⟨unitIntervalOne, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet level) =>
          unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet level).center u.1))
        (Finset.mem_univ u1)
    have hval :
        unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet level).center u1.1) = 1 := by
      change unitIntervalRademacherLinearProcess.X true
          (unitIntervalDyadicGridCenter level
            (unitIntervalDyadicGridRoundProject level unitIntervalOne)) = 1
      rw [unitIntervalDyadicGridRoundProject_one,
        unitIntervalDyadicGridCenter_rightEndpoint]
      norm_num [unitIntervalRademacherLinearProcess, unitIntervalOne,
        signOfBool]
    have hle1 :
        1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet level) =>
            unitIntervalRademacherLinearProcess.X true
              ((unitIntervalDyadicRoundedGridNet level).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle1

/-- Any rounded dyadic projected finite supremum is exactly the supplied
supremum for the unit-interval Rademacher linear process.

The reverse inequality uses the fact that rounded dyadic grids contain both
endpoints, while the forward inequality uses the range-level upper bound over
the full unit interval. -/
theorem unitIntervalRademacherLinear_projectedRoundedDyadicGridSup_eq
    (level : ℕ) (ω : Bool) :
    finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet level) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalDyadicRoundedGridNet level).center u.1)) =
      unitIntervalRademacherLinearSup ω := by
  classical
  apply le_antisymm
  · unfold finiteSup
    exact Finset.sup'_le Finset.univ_nonempty _ fun u _hu =>
      unitIntervalRademacherLinearSup_upper ω
        ((unitIntervalDyadicRoundedGridNet level).center u.1)
  · exact unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup level ω

/-- The rounded level-`2` generic dyadic grid contains the endpoints, so the
supplied supremum is pointwise bounded by its projected finite supremum. -/
private lemma unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridLevelTwoSup
    (ω : Bool) :
    unitIntervalRademacherLinearSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 2) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalDyadicRoundedGridNet 2).center u.1)) := by
  classical
  cases ω
  · let u0 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 2) :=
      ⟨(unitIntervalDyadicRoundedGridNet 2).project unitIntervalZero,
        ⟨unitIntervalZero, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet 2) =>
          unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet 2).center u.1))
        (Finset.mem_univ u0)
    have hval :
        unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet 2).center u0.1) = 0 := by
      norm_num [u0, unitIntervalRademacherLinearProcess,
        unitIntervalDyadicRoundedGridNet, unitIntervalDyadicGridRoundProject,
        unitIntervalDyadicGridCenter, unitIntervalZero, signOfBool]
    have hle0 :
        0 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 2) =>
            unitIntervalRademacherLinearProcess.X false
              ((unitIntervalDyadicRoundedGridNet 2).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle0
  · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 2) :=
      ⟨(unitIntervalDyadicRoundedGridNet 2).project unitIntervalOne,
        ⟨unitIntervalOne, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet 2) =>
          unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet 2).center u.1))
        (Finset.mem_univ u1)
    have hval :
        unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet 2).center u1.1) = 1 := by
      have hfloor : Nat.floor ((9 : ℝ) / 2) = 4 := by
        norm_num [Nat.floor_eq_iff]
      norm_num [u1, unitIntervalRademacherLinearProcess,
        unitIntervalDyadicRoundedGridNet, unitIntervalDyadicGridRoundProject,
        unitIntervalDyadicGridCenter, unitIntervalOne, signOfBool,
        hfloor]
    have hle1 :
        1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 2) =>
            unitIntervalRademacherLinearProcess.X true
              ((unitIntervalDyadicRoundedGridNet 2).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle1

/-- Rounded generic-dyadic-grid Dudley bound for the supplied nonzero supremum
of the unit-interval Rademacher process. This routes the supplied supremum
through the generic rounded grid at levels `1` and `2`, rather than through the
bespoke half/quarter mesh sequence. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_log15_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 2) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalDyadicRoundedGridNet 2).center u.1))) := by
        exact finiteExpectation_mono
          unitIntervalRademacherLinearProcess.weight_nonneg
          (unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup 2)
    _ ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 1
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun _ : ℕ => Real.sqrt (Real.log (15 : ℝ)))) :=
        unitIntervalRademacherLinear_roundedDyadicGrid_dudley_log15_bound

private lemma unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridLevelThreeSup
    (ω : Bool) :
    unitIntervalRademacherLinearSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 3) =>
          unitIntervalRademacherLinearProcess.X ω
            ((unitIntervalDyadicRoundedGridNet 3).center u.1)) := by
  classical
  cases ω
  · let u0 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 3) :=
      ⟨(unitIntervalDyadicRoundedGridNet 3).project unitIntervalZero,
        ⟨unitIntervalZero, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet 3) =>
          unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet 3).center u.1))
        (Finset.mem_univ u0)
    have hval :
        unitIntervalRademacherLinearProcess.X false
            ((unitIntervalDyadicRoundedGridNet 3).center u0.1) = 0 := by
      norm_num [u0, unitIntervalRademacherLinearProcess,
        unitIntervalDyadicRoundedGridNet, unitIntervalDyadicGridRoundProject,
        unitIntervalDyadicGridCenter, unitIntervalZero, signOfBool]
    have hle0 :
        0 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 3) =>
            unitIntervalRademacherLinearProcess.X false
              ((unitIntervalDyadicRoundedGridNet 3).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle0
  · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 3) :=
      ⟨(unitIntervalDyadicRoundedGridNet 3).project unitIntervalOne,
        ⟨unitIntervalOne, rfl⟩⟩
    have hle :=
      Finset.le_sup'
        (fun u : FiniteNet.ProjectedIndex
            (unitIntervalDyadicRoundedGridNet 3) =>
          unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet 3).center u.1))
        (Finset.mem_univ u1)
    have hval :
        unitIntervalRademacherLinearProcess.X true
            ((unitIntervalDyadicRoundedGridNet 3).center u1.1) = 1 := by
      have hfloor : Nat.floor ((17 : ℝ) / 2) = 8 := by
        norm_num [Nat.floor_eq_iff]
      norm_num [u1, unitIntervalRademacherLinearProcess,
        unitIntervalDyadicRoundedGridNet, unitIntervalDyadicGridRoundProject,
        unitIntervalDyadicGridCenter, unitIntervalOne, signOfBool,
        hfloor]
    have hle1 :
        1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 3) =>
            unitIntervalRademacherLinearProcess.X true
              ((unitIntervalDyadicRoundedGridNet 3).center u.1)) := by
      unfold finiteSup
      simpa [hval] using hle
    simpa [unitIntervalRademacherLinearSup] using hle1

/-- Rounded generic-dyadic-grid `m = 2` Dudley bound for the supplied nonzero
supremum of the unit-interval Rademacher process. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m2_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 2
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalDyadicRoundedGridNet 3) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalDyadicRoundedGridNet 3).center u.1))) := by
        exact finiteExpectation_mono
          unitIntervalRademacherLinearProcess.weight_nonneg
          unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridLevelThreeSup
    _ ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 2
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) :=
        unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m2_bound

/-- Generic finite-horizon rounded-dyadic-grid Dudley bound for the supplied
nonzero supremum of the unit-interval Rademacher process. This composes the
arbitrary projected-grid theorem with the endpoint supremum adapter for the
terminal rounded dyadic grid. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound
    (m : ℕ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  calc
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      finiteExpectation unitIntervalRademacherLinearProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (unitIntervalRoundedDyadicGridNet m) =>
            unitIntervalRademacherLinearProcess.X ω
              ((unitIntervalRoundedDyadicGridNet m).center u.1))) := by
        refine finiteExpectation_mono
          unitIntervalRademacherLinearProcess.weight_nonneg ?_
        intro ω
        simpa [unitIntervalRoundedDyadicGridNet] using
          unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup
            (m + 1) ω
    _ ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) :=
        unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound m

/-- Prefix-free arbitrary finite-horizon rounded-dyadic-grid Dudley bound for
the supplied nonzero supremum.

This is the same arbitrary-`m` theorem as
`unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound`, but with
the monotone rounded-grid entropy sequence replacing the generic prefix-sup
envelope. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree
    (m : ℕ) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (fun j : ℕ =>
            Real.sqrt
              (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ))) := by
  simpa [unitIntervalRoundedDyadicGridEntropy_prefixSup] using
    unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound m

/-- The `m = 3` rounded-dyadic-grid Dudley bound for the supplied nonzero
supremum. This is the first named supplied-supremum corollary beyond the
existing `m = 1` and `m = 2` examples. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m3_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 2 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) 3
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt
                (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)))) := by
  exact unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound 3

/-- The rounded generic-dyadic-grid Dudley bound for the supplied supremum,
with the one-step dyadic entropy budget evaluated. -/
theorem unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_log15_bound_eval :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + Real.sqrt 2 * Real.sqrt (Real.log (15 : ℝ)) := by
  have h :=
    unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_log15_bound
  convert h using 1
  · rw [FiniteSubGaussianProcess.finitePrefixSupEnvelope_const,
      FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget_one_const]
    simp [unitIntervalRademacherLinearProcess]
    ring_nf

/-- The projected-quarter finite-net Dudley bound for the supplied supremum,
with the one-step dyadic entropy budget evaluated. -/
theorem unitIntervalRademacherLinearSup_projectedQuarterMesh_dudley_log15_bound_eval :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + Real.sqrt 2 * Real.sqrt (Real.log (15 : ℝ)) := by
  have h :=
    unitIntervalRademacherLinearSup_projectedQuarterMesh_dudley_log15_bound
  convert h using 1
  · rw [FiniteSubGaussianProcess.finitePrefixSupEnvelope_const,
      FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget_one_const]
    simp [unitIntervalRademacherLinearProcess]
    ring_nf

private lemma unitIntervalRademacherLinearSup_le_one (ω : Bool) :
    unitIntervalRademacherLinearSup ω ≤ 1 := by
  cases ω <;> simp [unitIntervalRademacherLinearSup]

/-- A fixed finite-net Dudley instantiation for the nonzero supplied supremum
of the Rademacher linear process.

This theorem deliberately uses the finite-horizon `m = 0` boundary layer with a
coarse explicit budget. It is not the final continuous Dudley statement, but it
does route a nonzero supplied supremum for a non-finite index-space process
through the total-bounded finite-net bridge. -/
theorem unitIntervalRademacherLinearSup_dudley_m0_bound :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤ 3 := by
  classical
  let P := unitIntervalRademacherLinearProcess
  let N0 :=
    dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := UnitInterval) unitInterval_totallyBounded_univ
      (radiusScale := (1 : ℝ)) (by norm_num) 0
  have hdistP : P.dist = fun s t : UnitInterval => dist s t := rfl
  have hvariance : 0 < P.varianceProxy := by
    norm_num [P, unitIntervalRademacherLinearProcess]
  have hterminal :
      ∀ ω : Bool,
        unitIntervalRademacherLinearSup ω ≤
          finiteSup
            (fun u : FiniteNet.ProjectedIndex N0.net =>
              P.X ω (N0.net.center u.1)) +
            (2 : ℝ) := by
    intro ω
    have hsup_le : unitIntervalRademacherLinearSup ω ≤ 1 :=
      unitIntervalRademacherLinearSup_le_one ω
    have hfinite_ge :
        -1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex N0.net =>
            P.X ω (N0.net.center u.1)) := by
      simpa [P, unitIntervalRademacherLinearProcess] using
        finiteSup_rademacherLinear_ge_neg_one ω
          (fun u : FiniteNet.ProjectedIndex N0.net => N0.net.center u.1)
    linarith
  have hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex N0.net =>
            P.X ω (N0.net.projection
              (FiniteNet.ProjectedIndex.source N0.net u)))) ≤
      (1 : ℝ) := by
    calc
      finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex N0.net =>
              P.X ω (N0.net.projection
                (FiniteNet.ProjectedIndex.source N0.net u))))
          ≤ finiteExpectation P.weight (fun _ω : Bool => (1 : ℝ)) := by
            refine finiteExpectation_mono P.weight_nonneg ?_
            intro ω
            have hsup :
                finiteSup
                  (fun u : FiniteNet.ProjectedIndex N0.net =>
                    P.X ω (N0.net.projection
                      (FiniteNet.ProjectedIndex.source N0.net u))) ≤
                1 := by
              simpa [P, unitIntervalRademacherLinearProcess] using
                finiteSup_rademacherLinear_le_one ω
                  (fun u : FiniteNet.ProjectedIndex N0.net =>
                    N0.net.projection
                      (FiniteNet.ProjectedIndex.source N0.net u))
            exact hsup
      _ = (1 : ℝ) := by
            exact finiteExpectation_const_of_sum_one P.weight 1 P.weight_sum_one
  have hbase :=
    finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
      (P := P) (hT := unitInterval_totallyBounded_univ)
      (m := 0) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (entropyAtRadius := fun _ : ℝ => (0 : ℝ))
      (supFunctional := unitIntervalRademacherLinearSup)
      (terminalError := (2 : ℝ)) (by norm_num) hdistP hvariance
      (by intro j hj; simp at hj)
      (by intro j hj; simp at hj)
      (by intro a b hab; rfl)
      (by intro j hj; simp at hj)
      (by
        intro ω
        simpa [N0] using hterminal ω)
      (by
        simpa [N0] using hcoarse)
  have htail :
      (1 + 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in ((1 : ℝ) / (2 : ℝ) ^ (0 + 1))..((1 : ℝ) / 2),
            (fun _ : ℝ => (0 : ℝ)) ε) + 2) ≤
        (3 : ℝ) := by
    simp
    norm_num
  exact (by
    simpa [P] using hbase.trans htail)

/-- The first non-vacuous dyadic projection-pair type for the unit interval
with top scale `1`. -/
abbrev unitIntervalDyadicPair01 : Type :=
  FiniteNet.ProjectionPair
    (unitIntervalDyadicFiniteNet (radiusScale := (1 : ℝ)) (by norm_num) 0).net
    (unitIntervalDyadicFiniteNet (radiusScale := (1 : ℝ)) (by norm_num) 1).net

/-- The first adjacent dyadic projection-pair family over `[0,1]` is
nontrivial. The radius-`1/4` net cannot project both endpoints to the same
center. -/
theorem unitIntervalDyadicPair01_card_gt_one :
    1 < Fintype.card unitIntervalDyadicPair01 := by
  classical
  let N0 := unitIntervalDyadicFiniteNet (radiusScale := (1 : ℝ)) (by norm_num) 0
  let N1 := unitIntervalDyadicFiniteNet (radiusScale := (1 : ℝ)) (by norm_num) 1
  let p0 : FiniteNet.ProjectionPair N0.net N1.net :=
    FiniteNet.projectionPairOf N0.net N1.net unitIntervalZero
  let p1 : FiniteNet.ProjectionPair N0.net N1.net :=
    FiniteNet.projectionPairOf N0.net N1.net unitIntervalOne
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hproj :
      N0.net.project unitIntervalZero = N0.net.project unitIntervalOne := by
    exact congrArg (fun p : FiniteNet.ProjectionPair N0.net N1.net => p.1.1) hp
  have hcenter :
      N0.net.projection unitIntervalZero =
        N0.net.projection unitIntervalOne := by
    simp [FiniteNet.projection, hproj]
  have hzero :
      dist unitIntervalZero (N0.net.projection unitIntervalZero) ≤
        (1 : ℝ) / (2 : ℝ) ^ 2 := by
    have h := N0.net.projection_dist_le unitIntervalZero
    simpa [N0, unitIntervalDyadicFiniteNet, dyadicChainingNetRadius] using h
  have hone :
      dist (N0.net.projection unitIntervalZero) unitIntervalOne ≤
        (1 : ℝ) / (2 : ℝ) ^ 2 := by
    have h := N0.net.projection_dist_le unitIntervalOne
    rw [hcenter]
    simpa [N0, unitIntervalDyadicFiniteNet, dyadicChainingNetRadius, dist_comm] using h
  have hdist_le :
      dist unitIntervalZero unitIntervalOne ≤ (1 : ℝ) / 2 := by
    calc
      dist unitIntervalZero unitIntervalOne
          ≤ dist unitIntervalZero (N0.net.projection unitIntervalZero) +
              dist (N0.net.projection unitIntervalZero) unitIntervalOne :=
            dist_triangle unitIntervalZero (N0.net.projection unitIntervalZero)
              unitIntervalOne
      _ ≤ (1 : ℝ) / 2 := by
            linarith
  norm_num [dist_unitIntervalZero_unitIntervalOne] at hdist_le

/-- The entropy-envelope side condition needed at the first non-vacuous
unit-interval scale. -/
def unitIntervalDyadicEntropyM1Condition (entropyAtRadius : ℝ → ℝ) : Prop :=
  FiniteSubGaussianProcess.finitePrefixSupEnvelope
      (fun j => Real.sqrt (Real.log
        (dyadicChainingCoverCount
          (T := UnitInterval) unitInterval_totallyBounded_univ
          (radiusScale := (1 : ℝ)) (by norm_num) j : ℝ))) 0 ≤
    entropyAtRadius ((1 : ℝ) / (2 : ℝ))

/-- A constant entropy envelope large enough for the first non-vacuous
unit-interval dyadic scale. -/
def unitIntervalDyadicEntropyCapM1 : ℝ :=
  FiniteSubGaussianProcess.finitePrefixSupEnvelope
      (fun j => Real.sqrt (Real.log
        (dyadicChainingCoverCount
          (T := UnitInterval) unitInterval_totallyBounded_univ
          (radiusScale := (1 : ℝ)) (by norm_num) j : ℝ))) 0

/-- The constant first-scale entropy cap satisfies the `m = 1` entropy-envelope
side condition. -/
theorem unitIntervalDyadicEntropyM1Condition_constCap :
    unitIntervalDyadicEntropyM1Condition
      (fun _ : ℝ => unitIntervalDyadicEntropyCapM1) := by
  simp [unitIntervalDyadicEntropyM1Condition, unitIntervalDyadicEntropyCapM1]

/-- A fixed `m = 1` finite-net Dudley instantiation for the nonzero supplied
supremum of the Rademacher linear process.

Unlike the `m = 0` theorem, this exposes the first real finite-net side
conditions: the projection-pair cardinality, entropy envelope, antitonicity,
and interval-integrability obligations. Those are exactly the obligations that
must be discharged to make the unit-interval bridge non-vacuous at a positive
dyadic scale. -/
theorem unitIntervalRademacherLinearSup_dudley_m1_bound_of_entropy
    (entropyAtRadius : ℝ → ℝ)
    (hcard : 1 < Fintype.card unitIntervalDyadicPair01)
    (hentropyAtRadius : unitIntervalDyadicEntropyM1Condition entropyAtRadius)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        ((1 : ℝ) / (2 : ℝ) ^ (0 + 2))
        ((1 : ℝ) / (2 : ℝ) ^ (0 + 1))) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in ((1 : ℝ) / (2 : ℝ) ^ (1 + 1))..((1 : ℝ) / 2),
          entropyAtRadius ε) + 2 := by
  classical
  let P := unitIntervalRademacherLinearProcess
  let N0 :=
    dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := UnitInterval) unitInterval_totallyBounded_univ
      (radiusScale := (1 : ℝ)) (by norm_num) 0
  let N1 :=
    dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := UnitInterval) unitInterval_totallyBounded_univ
      (radiusScale := (1 : ℝ)) (by norm_num) 1
  have hdistP : P.dist = fun s t : UnitInterval => dist s t := rfl
  have hvariance : 0 < P.varianceProxy := by
    norm_num [P, unitIntervalRademacherLinearProcess]
  have hterminal :
      ∀ ω : Bool,
        unitIntervalRademacherLinearSup ω ≤
          finiteSup
            (fun u : FiniteNet.ProjectedIndex N1.net =>
              P.X ω (N1.net.center u.1)) +
            (2 : ℝ) := by
    intro ω
    have hsup_le : unitIntervalRademacherLinearSup ω ≤ 1 :=
      unitIntervalRademacherLinearSup_le_one ω
    have hfinite_ge :
        -1 ≤ finiteSup
          (fun u : FiniteNet.ProjectedIndex N1.net =>
            P.X ω (N1.net.center u.1)) := by
      simpa [P, unitIntervalRademacherLinearProcess] using
        finiteSup_rademacherLinear_ge_neg_one ω
          (fun u : FiniteNet.ProjectedIndex N1.net => N1.net.center u.1)
    linarith
  have hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex N1.net =>
            P.X ω (N0.net.projection
              (FiniteNet.ProjectedIndex.source N1.net u)))) ≤
      (1 : ℝ) := by
    calc
      finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex N1.net =>
              P.X ω (N0.net.projection
                (FiniteNet.ProjectedIndex.source N1.net u))))
          ≤ finiteExpectation P.weight (fun _ω : Bool => (1 : ℝ)) := by
            refine finiteExpectation_mono P.weight_nonneg ?_
            intro ω
            have hsup :
                finiteSup
                  (fun u : FiniteNet.ProjectedIndex N1.net =>
                    P.X ω (N0.net.projection
                      (FiniteNet.ProjectedIndex.source N1.net u))) ≤
                1 := by
              simpa [P, unitIntervalRademacherLinearProcess] using
                finiteSup_rademacherLinear_le_one ω
                  (fun u : FiniteNet.ProjectedIndex N1.net =>
                    N0.net.projection
                      (FiniteNet.ProjectedIndex.source N1.net u))
            exact hsup
      _ = (1 : ℝ) := by
            exact finiteExpectation_const_of_sum_one P.weight 1 P.weight_sum_one
  have hbase :=
    finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison
      (P := P) (hT := unitInterval_totallyBounded_univ)
      (m := 1) (coarseBudget := (1 : ℝ)) (radiusScale := (1 : ℝ))
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := unitIntervalRademacherLinearSup)
      (terminalError := (2 : ℝ)) (by norm_num) hdistP hvariance
      (by
        intro j hj
        simp at hj
        subst j
        simpa [unitIntervalDyadicPair01])
      (by
        intro j hj
        simp at hj
        subst j
        simpa [unitIntervalDyadicEntropyM1Condition] using hentropyAtRadius)
      hentropy_antitone
      (by
        intro j hj
        simp at hj
        subst j
        simpa using hintervalIntegrable)
      (by
        intro ω
        simpa [N1] using hterminal ω)
      (by
        simpa [N0, N1] using hcoarse)
  exact (by
    simpa [P, unitIntervalRademacherLinearProcess] using hbase)

/-- The `m = 1` unit-interval Dudley instantiation with the projection-pair
cardinality side condition discharged concretely. -/
theorem unitIntervalRademacherLinearSup_dudley_m1_bound
    (entropyAtRadius : ℝ → ℝ)
    (hentropyAtRadius : unitIntervalDyadicEntropyM1Condition entropyAtRadius)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        ((1 : ℝ) / (2 : ℝ) ^ (0 + 2))
        ((1 : ℝ) / (2 : ℝ) ^ (0 + 1))) :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in ((1 : ℝ) / (2 : ℝ) ^ (1 + 1))..((1 : ℝ) / 2),
          entropyAtRadius ε) + 2 :=
  unitIntervalRademacherLinearSup_dudley_m1_bound_of_entropy
    entropyAtRadius unitIntervalDyadicPair01_card_gt_one
    hentropyAtRadius hentropy_antitone hintervalIntegrable

/-- A closed `m = 1` unit-interval Dudley instantiation using the constant
first-scale entropy cap. -/
theorem unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in ((1 : ℝ) / (2 : ℝ) ^ (1 + 1))..((1 : ℝ) / 2),
          (fun _ : ℝ => unitIntervalDyadicEntropyCapM1) ε) + 2 := by
  refine
    unitIntervalRademacherLinearSup_dudley_m1_bound
      (fun _ : ℝ => unitIntervalDyadicEntropyCapM1)
      unitIntervalDyadicEntropyM1Condition_constCap ?_ ?_
  · intro a b hab
    rfl
  · exact
      (intervalIntegrable_const
        (μ := MeasureTheory.volume)
        (a := ((1 : ℝ) / (2 : ℝ) ^ (0 + 2)))
        (b := ((1 : ℝ) / (2 : ℝ) ^ (0 + 1)))
        (c := unitIntervalDyadicEntropyCapM1))

/-- The closed constant-envelope `m = 1` bound with the interval integral
evaluated. -/
theorem unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy_eval :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      3 + Real.sqrt 2 * unitIntervalDyadicEntropyCapM1 := by
  have h := unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy
  convert h using 1
  · simp [unitIntervalRademacherLinearProcess, intervalIntegral.integral_const]
    ring

end

end FormalSLT.Covering.UnitIntervalDudley
