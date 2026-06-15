import FormalSLT.Covering.DudleySumToIntegral
import FormalSLT.Covering.TwoPointDudley

/-!
# Two-point centered Dudley entropy-integral example

This module instantiates the finite q087 entropy-integral theorem on the
two-point Rademacher process. The level-0 net is rooted at `false`, the
terminal net is the identity two-point net, and the covering profile is a
fixed finite envelope for the single adjacent net pair.

The statement remains finite-scale. It does not assert a continuous Dudley
theorem, measurable supremum theorem, or total-bounded limit passage.
-/

namespace FormalSLT.Covering.TwoPointDudleyIntegral

open Finset
open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.DudleySumToIntegral
open FormalSLT.Covering.TwoPointDudley
open FormalSLT.Rademacher.FiniteSample

noncomputable section

/-- Rooted two-point net. Both net indices realize the root `false`. -/
def twoPointRootNet : FiniteNet TwoPoint Bool where
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  center := fun _ => false
  project := fun _ => false
  radius := 1
  radius_nonneg := by norm_num
  covers := by
    intro t
    cases t <;> norm_num [twoPointDist]

/-- Terminal identity two-point net used at horizon `m = 1`. -/
def twoPointTerminalNet : FiniteNet TwoPoint Bool where
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  center := id
  project := id
  radius := (1 : ℝ) / 4
  radius_nonneg := by norm_num
  covers := by
    intro t
    cases t <;> norm_num [twoPointDist]

/-- Rooted two-level net family: root at level `0`, terminal identity after. -/
def twoPointRootedNet (j : ℕ) : FiniteNet TwoPoint Bool :=
  if j = 0 then twoPointRootNet else twoPointTerminalNet

theorem twoPointRootedNet_dist (j : ℕ) :
    (twoPointRootedNet j).dist = twoPointRademacherProcess.dist := by
  by_cases hj : j = 0 <;>
    simp [twoPointRootedNet, hj, twoPointRootNet, twoPointTerminalNet,
      twoPointRademacherProcess]

theorem twoPointRootedNet_root (t : TwoPoint) :
    (twoPointRootedNet 0).projection t = false := by
  simp [twoPointRootedNet, twoPointRootNet, FiniteNet.projection]

theorem twoPointRootedNet_terminal (t : TwoPoint) :
    (twoPointRootedNet 1).projection t = t := by
  cases t <;> simp [twoPointRootedNet, twoPointTerminalNet, FiniteNet.projection]

theorem twoPointRootedNet_radius_pos_m1 :
    ∀ j ∈ Finset.range 1,
      0 < (twoPointRootedNet j).radius + (twoPointRootedNet (j + 1)).radius := by
  intro j hj
  have hj0 : j = 0 := by
    have hjlt : j < 1 := by simpa using hj
    omega
  subst j
  norm_num [twoPointRootedNet, twoPointRootNet, twoPointTerminalNet]

theorem twoPointRootedNet_radius_geometric_m1 :
    ∀ j ∈ Finset.range 1,
      (twoPointRootedNet j).radius + (twoPointRootedNet (j + 1)).radius ≤
        (2 : ℝ) / (2 : ℝ) ^ j := by
  intro j hj
  have hj0 : j = 0 := by
    have hjlt : j < 1 := by simpa using hj
    omega
  subst j
  norm_num [twoPointRootedNet, twoPointRootNet, twoPointTerminalNet]

/-- Constant finite cover envelope for the single rooted/terminal pair. -/
def twoPointIntegralCoverProfile (_ε : ℝ) : ℕ := 4

theorem twoPointIntegralCoverProfile_antitone :
    Antitone twoPointIntegralCoverProfile := by
  intro ε δ hεδ
  rfl

theorem twoPointIntegralCoverProfile_pos (ε : ℝ) :
    0 < twoPointIntegralCoverProfile ε := by
  norm_num [twoPointIntegralCoverProfile]

theorem twoPointRootedNet_coverProduct_m1 :
    ∀ j ∈ Finset.range 1,
      (twoPointRootedNet j).coveringNumber *
          (twoPointRootedNet (j + 1)).coveringNumber ≤
        twoPointIntegralCoverProfile ((2 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  intro j hj
  have hj0 : j = 0 := by
    have hjlt : j < 1 := by simpa using hj
    omega
  subst j
  norm_num [twoPointRootedNet, twoPointRootNet, twoPointTerminalNet,
    FiniteNet.coveringNumber, twoPointIntegralCoverProfile]

theorem twoPointRootedNet_centered_increment_m1 :
    ∀ j ∈ Finset.range 1,
      ∀ pair : FiniteNet.ProjectionPair
          (twoPointRootedNet j) (twoPointRootedNet (j + 1)),
        finiteExpectation twoPointRademacherProcess.weight
          (fun ω => twoPointRademacherProcess.X ω
              ((twoPointRootedNet (j + 1)).center pair.1.2) -
            twoPointRademacherProcess.X ω
              ((twoPointRootedNet j).center pair.1.1)) = 0 := by
  intro j hj pair
  have hj0 : j = 0 := by
    have hjlt : j < 1 := by simpa using hj
    omega
  subst j
  cases pair.1.2 <;>
    norm_num [finiteExpectation, twoPointRootedNet, twoPointRootNet,
      twoPointTerminalNet, twoPointRademacherProcess,
      twoPointRademacherValue, signOfBool]

/--
Centered finite Dudley entropy-integral bound for the two-point Rademacher
process with a rooted initial net and one terminal identity level.
-/
theorem twoPointRademacher_centered_dudley_entropy_integral :
    finiteExpectation twoPointRademacherProcess.weight
        (fun ω => finiteSup
          (fun t : TwoPoint =>
            twoPointRademacherProcess.X ω t -
              twoPointRademacherProcess.X ω false)) ≤
      4 * Real.sqrt (2 * twoPointRademacherProcess.varianceProxy) *
        (∫ ε in ((2 : ℝ) / (2 : ℝ) ^ (1 + 1))..((2 : ℝ) / 2),
          Real.sqrt (Real.log (twoPointIntegralCoverProfile ε : ℝ))) := by
  exact
    dudley_entropy_integral_of_antitone_coveringNumber
      (P := twoPointRademacherProcess)
      (N := twoPointRootedNet)
      (m := 1)
      (t₀ := false)
      (radiusScale := 2)
      (coveringNumberAtRadius := twoPointIntegralCoverProfile)
      twoPointRootedNet_dist
      twoPointDist_symm
      twoPointDist_triangle
      twoPointRootedNet_root
      twoPointRootedNet_terminal
      (by norm_num [twoPointRademacherProcess])
      (by norm_num)
      twoPointRootedNet_radius_pos_m1
      twoPointRootedNet_radius_geometric_m1
      twoPointIntegralCoverProfile_antitone
      twoPointIntegralCoverProfile_pos
      twoPointRootedNet_coverProduct_m1
      twoPointRootedNet_centered_increment_m1

end

end FormalSLT.Covering.TwoPointDudleyIntegral
