import FormalSLT.Covering.FiniteSubGaussianChaining
import FormalSLT.Rademacher.Massart

/-!
# Two-point finite dyadic-net Dudley example

This module instantiates `FiniteDyadicNetSequence` on a second metric index
family, the two-point discrete space. Its purpose is API pressure: the
dyadic-net sequence abstraction is used outside the unit interval.

The result remains finite-scale. It does not assert a continuous Dudley
integral, total boundedness, separability, or a measurable supremum over an
arbitrary class.
-/

namespace FormalSLT.Covering.TwoPointDudley

open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess
open FormalSLT.Rademacher.FiniteSample
open scoped BigOperators

noncomputable section

/-- The second metric index family used to exercise the generic dyadic-net
sequence API. -/
abbrev TwoPoint : Type := Bool

/-- Discrete metric on the two-point index family. -/
def twoPointDist (s t : TwoPoint) : ℝ :=
  if s = t then 0 else 1

theorem twoPointDist_nonneg (s t : TwoPoint) : 0 ≤ twoPointDist s t := by
  by_cases h : s = t <;> simp [twoPointDist, h]

theorem twoPointDist_symm (s t : TwoPoint) :
    twoPointDist s t = twoPointDist t s := by
  cases s <;> cases t <;> norm_num [twoPointDist]

theorem twoPointDist_triangle (x y z : TwoPoint) :
    twoPointDist x z ≤ twoPointDist x y + twoPointDist y z := by
  cases x <;> cases y <;> cases z <;> norm_num [twoPointDist]

/-- A one-coordinate Rademacher process on the two-point index family. -/
def twoPointRademacherValue (ω : Bool) (t : TwoPoint) : ℝ :=
  if t then signOfBool ω else 0

private theorem twoPointRademacherValue_le_one (ω : Bool) (t : TwoPoint) :
    twoPointRademacherValue ω t ≤ 1 := by
  cases ω <;> cases t <;> norm_num [twoPointRademacherValue, signOfBool]

theorem twoPoint_rademacher_mgf_bound (s t : TwoPoint) (lam : ℝ) :
    finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
        (fun ω => Real.exp
          (lam * (twoPointRademacherValue ω t - twoPointRademacherValue ω s))) ≤
      Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist s t ^ 2 / 2) := by
  cases s <;> cases t
  · norm_num [finiteExpectation, twoPointRademacherValue, twoPointDist]
  · calc
      finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
          (fun ω => Real.exp
            (lam * (twoPointRademacherValue ω true -
              twoPointRademacherValue ω false)))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (1 : ℝ))) / 2 := by
              simp [finiteExpectation, twoPointRademacherValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam 1
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist false true ^ 2 / 2) := by
              norm_num [twoPointDist]
  · calc
      finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
          (fun ω => Real.exp
            (lam * (twoPointRademacherValue ω false -
              twoPointRademacherValue ω true)))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (-1 : ℝ))) / 2 := by
              simp [finiteExpectation, twoPointRademacherValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (-1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam (-1)
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist true false ^ 2 / 2) := by
              norm_num [twoPointDist]
  · norm_num [finiteExpectation, twoPointRademacherValue, twoPointDist]

/-- The two-point Rademacher process packaged as a finite sub-Gaussian
process. -/
def twoPointRademacherProcess : FiniteSubGaussianProcess Bool TwoPoint where
  weight := fun _ => (1 : ℝ) / 2
  weight_nonneg := by intro ω; norm_num
  weight_sum_one := by norm_num [Fintype.sum_bool]
  X := twoPointRademacherValue
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  varianceProxy := 1
  varianceProxy_nonneg := by norm_num
  mgf_increment := twoPoint_rademacher_mgf_bound

/-- Full two-point net at dyadic level `j`. The centers are both points; the
positive radius is chosen to fit the generic dyadic radius interface. -/
def twoPointDyadicNet (j : ℕ) : FiniteNet TwoPoint Bool where
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  center := id
  project := id
  radius := (1 : ℝ) / (2 : ℝ) ^ (j + 2)
  radius_nonneg := by positivity
  covers := by
    intro t
    cases t <;> simp [twoPointDist]

def twoPointDyadicCoverCount (_j : ℕ) : ℕ := 4

theorem twoPointDyadicNet_dist (j : ℕ) :
    (twoPointDyadicNet j).dist = twoPointRademacherProcess.dist := by
  rfl

theorem twoPointDyadicNet_radius_pos (j : ℕ) :
    0 < (twoPointDyadicNet j).radius + (twoPointDyadicNet (j + 1)).radius := by
  simp [twoPointDyadicNet]
  positivity

theorem twoPointDyadicNet_radius_geometric (j : ℕ) :
    (twoPointDyadicNet j).radius + (twoPointDyadicNet (j + 1)).radius ≤
      (1 : ℝ) / (2 : ℝ) ^ j := by
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  change
    (1 : ℝ) / (2 : ℝ) ^ (j + 2) +
        (1 : ℝ) / (2 : ℝ) ^ ((j + 1) + 2) ≤
      (1 : ℝ) / (2 : ℝ) ^ j
  rw [show (j + 1) + 2 = j + 3 by
    rw [Nat.add_assoc]]
  have hscaled :
      (1 : ℝ) / (2 : ℝ) ^ (j + 2) +
          (1 : ℝ) / (2 : ℝ) ^ (j + 3) =
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

theorem twoPointDyadicNet_pair_card_gt_one (j : ℕ) :
    1 < Fintype.card
      (FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1))) := by
  let p0 : FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) :=
    FiniteNet.projectionPairOf (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) false
  let p1 : FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) :=
    FiniteNet.projectionPairOf (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) true
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hfst : p0.1.1 = p1.1.1 := congrArg (fun p => p.1.1) hp
  norm_num [p0, p1, FiniteNet.projectionPairOf, twoPointDyadicNet] at hfst

theorem twoPointDyadicNet_coveringNumber (j : ℕ) :
    (twoPointDyadicNet j).coveringNumber = 2 := by
  simp [FiniteNet.coveringNumber]

theorem twoPointDyadicNet_coverCount_le (j : ℕ) :
    (twoPointDyadicNet j).coveringNumber *
        (twoPointDyadicNet (j + 1)).coveringNumber ≤
      twoPointDyadicCoverCount j := by
  simp [twoPointDyadicNet_coveringNumber, twoPointDyadicCoverCount]

/-- The second concrete `FiniteDyadicNetSequence` instantiation, independent of
the unit-interval rounded grid. -/
def twoPointDyadicNetSequence :
    FiniteSubGaussianProcess.FiniteDyadicNetSequence
      twoPointRademacherProcess (fun _j : ℕ => Bool) where
  N := twoPointDyadicNet
  coverCount := twoPointDyadicCoverCount
  radiusScale := 1
  dist_eq := twoPointDyadicNet_dist
  dist_symm := twoPointDist_symm
  dist_triangle := twoPointDist_triangle
  radiusScale_nonneg := by norm_num
  radius_pos := twoPointDyadicNet_radius_pos
  radius_geometric := twoPointDyadicNet_radius_geometric
  pair_card_gt_one := twoPointDyadicNet_pair_card_gt_one
  coverCount_le := twoPointDyadicNet_coverCount_le

private theorem twoPointRademacher_coarse (m : ℕ) :
    finiteExpectation twoPointRademacherProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω
            ((twoPointDyadicNet 0).projection
              (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation twoPointRademacherProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω
            ((twoPointDyadicNet 0).projection
              (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u))))
        ≤ finiteExpectation twoPointRademacherProcess.weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono twoPointRademacherProcess.weight_nonneg ?_
          intro ω
          unfold finiteSup
          exact Finset.sup'_le Finset.univ_nonempty _ fun u _hu =>
            twoPointRademacherValue_le_one ω
              ((twoPointDyadicNet 0).projection
                (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            twoPointRademacherProcess.weight 1
            twoPointRademacherProcess.weight_sum_one

/-- Packaged finite-dyadic Dudley instance for the two-point Rademacher
process. -/
def twoPointDudleyInstance :
    FiniteDyadicDudleyInstance twoPointRademacherProcess (fun _j : ℕ => Bool) where
  netSequence := twoPointDyadicNetSequence
  coarseBudget := 1
  variance_pos := by norm_num [twoPointRademacherProcess]
  coarse_bound := twoPointRademacher_coarse

/-- Projected finite-net Dudley bound for the two-point process through the
packaged finite-dyadic Dudley API. -/
theorem twoPointRademacher_projected_dudley_m_bound (m : ℕ) :
    finiteExpectation twoPointRademacherProcess.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
            twoPointRademacherProcess.X ω ((twoPointDyadicNet m).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * twoPointRademacherProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (twoPointDyadicCoverCount j : ℝ)))) := by
  have hbase :=
    FiniteDyadicDudleyInstance.projected_dudley_bound
      twoPointDudleyInstance m
  simpa [twoPointDudleyInstance, twoPointRademacherProcess] using hbase

/-- Supremum functional for the two-point Rademacher process. -/
def twoPointRademacherSup (ω : Bool) : ℝ :=
  finiteSup (fun t : TwoPoint => twoPointRademacherProcess.X ω t)

theorem twoPointRademacherSup_le_projectedSup (m : ℕ) (ω : Bool) :
    twoPointRademacherSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω ((twoPointDyadicNet m).center u.1)) := by
  unfold twoPointRademacherSup finiteSup
  apply Finset.sup'_le
  intro t _ht
  let u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) := ⟨t, ⟨t, rfl⟩⟩
  have hle :=
    Finset.le_sup'
      (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
        twoPointRademacherProcess.X ω ((twoPointDyadicNet m).center u.1))
      (Finset.mem_univ u)
  simpa [u, twoPointDyadicNet] using hle

/-- Supplied-supremum adapter for the two-point Rademacher process. -/
def twoPointRademacherSupAdapter :
    FiniteDyadicDudleyInstance.SupremumAdapter twoPointDudleyInstance where
  supFunctional := twoPointRademacherSup
  terminalError := 0
  terminal_bound := by
    intro m ω
    simpa using twoPointRademacherSup_le_projectedSup m ω

/-- Supplied-supremum Dudley bound for the two-point process through the
packaged finite-dyadic Dudley API. -/
theorem twoPointRademacherSup_dudley_m_bound (m : ℕ) :
    finiteExpectation twoPointRademacherProcess.weight twoPointRademacherSup ≤
      1 + 2 * Real.sqrt (2 * twoPointRademacherProcess.varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (twoPointDyadicCoverCount j : ℝ)))) := by
  have hbase :=
    FiniteDyadicDudleyInstance.suppliedSup_dudley_bound
      twoPointDudleyInstance twoPointRademacherSupAdapter m
  simpa [twoPointDudleyInstance, twoPointRademacherSupAdapter,
    twoPointRademacherProcess] using hbase

end

end FormalSLT.Covering.TwoPointDudley
