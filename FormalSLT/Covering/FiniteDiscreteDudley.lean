import FormalSLT.Covering.FiniteSubGaussianChaining

/-!
# Finite discrete dyadic-net Dudley example

This module instantiates `FiniteDyadicNetSequence` for the finite discrete
metric family `Fin n`, assuming `2 ≤ n`. It is an API-usability example: the
cover-count envelope is `n * n`, so the generic dyadic-net wrapper is exercised
with a nonconstant finite family rather than only `[0,1]` or the two-point
space.

The process used here is the zero process. That keeps the stochastic part
deliberately trivial so the file tests the metric-net bookkeeping and the
generic Dudley wrappers directly.
-/

namespace FormalSLT.Covering.FiniteDiscreteDudley

open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess
open scoped BigOperators

noncomputable section

/-- Discrete metric on `Fin n`. -/
def finDiscreteDist {n : ℕ} (s t : Fin n) : ℝ :=
  if s = t then 0 else 1

theorem finDiscreteDist_nonneg {n : ℕ} (s t : Fin n) :
    0 ≤ finDiscreteDist s t := by
  by_cases h : s = t <;> simp [finDiscreteDist, h]

theorem finDiscreteDist_symm {n : ℕ} (s t : Fin n) :
    finDiscreteDist s t = finDiscreteDist t s := by
  by_cases h : s = t
  · subst h
    simp [finDiscreteDist]
  · have hts : t ≠ s := by
      intro hts
      exact h hts.symm
    simp [finDiscreteDist, h, hts]

theorem finDiscreteDist_triangle {n : ℕ} (x y z : Fin n) :
    finDiscreteDist x z ≤ finDiscreteDist x y + finDiscreteDist y z := by
  by_cases hxz : x = z
  · have hxy_nonneg : 0 ≤ finDiscreteDist x y := finDiscreteDist_nonneg x y
    have hyz_nonneg : 0 ≤ finDiscreteDist y z := finDiscreteDist_nonneg y z
    simpa [finDiscreteDist, hxz] using add_nonneg hxy_nonneg hyz_nonneg
  · by_cases hxy : x = y
    · subst hxy
      simp [finDiscreteDist, hxz]
    · by_cases hyz : y = z
      · subst hyz
        simp [finDiscreteDist, hxz]
      · simp [finDiscreteDist, hxz, hxy, hyz]

/-- The zero process on a finite discrete index family. -/
def finDiscreteZeroValue {n : ℕ} (_ω : PUnit) (_t : Fin n) : ℝ :=
  0

theorem finDiscreteZero_mgf_bound {n : ℕ} (s t : Fin n) (lam : ℝ) :
    finiteExpectation (fun _ : PUnit => (1 : ℝ))
        (fun ω => Real.exp
          (lam * (finDiscreteZeroValue ω t - finDiscreteZeroValue ω s))) ≤
      Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) := by
  have hnonneg :
      0 ≤ lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2 := by
    nlinarith [sq_nonneg lam, sq_nonneg (finDiscreteDist s t)]
  calc
    finiteExpectation (fun _ : PUnit => (1 : ℝ))
        (fun ω => Real.exp
          (lam * (finDiscreteZeroValue ω t - finDiscreteZeroValue ω s)))
        = 1 := by
          simp [finiteExpectation, finDiscreteZeroValue]
    _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) :=
          Real.one_le_exp hnonneg

/-- The zero process packaged as a finite sub-Gaussian process on `Fin n`. -/
def finDiscreteZeroProcess (n : ℕ) : FiniteSubGaussianProcess PUnit (Fin n) where
  weight := fun _ => (1 : ℝ)
  weight_nonneg := by intro ω; norm_num
  weight_sum_one := by simp
  X := finDiscreteZeroValue
  dist := finDiscreteDist
  dist_nonneg := finDiscreteDist_nonneg
  varianceProxy := 1
  varianceProxy_nonneg := by norm_num
  mgf_increment := finDiscreteZero_mgf_bound

/-- The full finite discrete net at dyadic level `j`. -/
def finDiscreteDyadicNet (n : ℕ) (j : ℕ) : FiniteNet (Fin n) (Fin n) where
  dist := finDiscreteDist
  dist_nonneg := finDiscreteDist_nonneg
  center := id
  project := id
  radius := (1 : ℝ) / (2 : ℝ) ^ (j + 2)
  radius_nonneg := by positivity
  covers := by
    intro t
    simp [finDiscreteDist]

/-- The projection-pair cover-count envelope for the full `Fin n` net family. -/
def finDiscreteDyadicCoverCount (n : ℕ) (_j : ℕ) : ℕ :=
  n * n

theorem finDiscreteDyadicNet_dist (n : ℕ) (j : ℕ) :
    (finDiscreteDyadicNet n j).dist = (finDiscreteZeroProcess n).dist := by
  rfl

theorem finDiscreteDyadicNet_radius_pos (n : ℕ) (j : ℕ) :
    0 < (finDiscreteDyadicNet n j).radius +
      (finDiscreteDyadicNet n (j + 1)).radius := by
  simp [finDiscreteDyadicNet]
  positivity

theorem finDiscreteDyadicNet_radius_geometric (n : ℕ) (j : ℕ) :
    (finDiscreteDyadicNet n j).radius +
        (finDiscreteDyadicNet n (j + 1)).radius ≤
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

instance finNonempty_of_fact_two_le (n : ℕ) [Fact (2 ≤ n)] : Nonempty (Fin n) :=
  ⟨⟨0, Nat.lt_of_lt_of_le (by norm_num) (Fact.out : 2 ≤ n)⟩⟩

private def finZero {n : ℕ} [Fact (2 ≤ n)] : Fin n :=
  ⟨0, Nat.lt_of_lt_of_le (by norm_num) (Fact.out : 2 ≤ n)⟩

private def finOne {n : ℕ} [Fact (2 ≤ n)] : Fin n :=
  ⟨1, Nat.lt_of_lt_of_le (by norm_num) (Fact.out : 2 ≤ n)⟩

private theorem finZero_ne_finOne {n : ℕ} [Fact (2 ≤ n)] :
    (finZero : Fin n) ≠ finOne := by
  intro h
  have hval := congrArg Fin.val h
  norm_num [finZero, finOne] at hval

theorem finDiscreteDyadicNet_pair_card_gt_one {n : ℕ} [Fact (2 ≤ n)] (j : ℕ) :
    1 < Fintype.card
      (FiniteNet.ProjectionPair
        (finDiscreteDyadicNet n j) (finDiscreteDyadicNet n (j + 1))) := by
  let p0 : FiniteNet.ProjectionPair
      (finDiscreteDyadicNet n j) (finDiscreteDyadicNet n (j + 1)) :=
    FiniteNet.projectionPairOf
      (finDiscreteDyadicNet n j) (finDiscreteDyadicNet n (j + 1)) (finZero : Fin n)
  let p1 : FiniteNet.ProjectionPair
      (finDiscreteDyadicNet n j) (finDiscreteDyadicNet n (j + 1)) :=
    FiniteNet.projectionPairOf
      (finDiscreteDyadicNet n j) (finDiscreteDyadicNet n (j + 1)) (finOne : Fin n)
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hfst : p0.1.1 = p1.1.1 := congrArg (fun p => p.1.1) hp
  exact finZero_ne_finOne (n := n) (by simpa [p0, p1, finDiscreteDyadicNet] using hfst)

theorem finDiscreteDyadicNet_coveringNumber (n : ℕ) (j : ℕ) :
    (finDiscreteDyadicNet n j).coveringNumber = n := by
  simp [FiniteNet.coveringNumber]

theorem finDiscreteDyadicNet_coverCount_le (n : ℕ) (j : ℕ) :
    (finDiscreteDyadicNet n j).coveringNumber *
        (finDiscreteDyadicNet n (j + 1)).coveringNumber ≤
      finDiscreteDyadicCoverCount n j := by
  simp [finDiscreteDyadicNet_coveringNumber, finDiscreteDyadicCoverCount]

/-- `Fin n` as a reusable finite dyadic-net sequence, for nondegenerate
finite discrete spaces. -/
def finDiscreteDyadicNetSequence (n : ℕ) [Fact (2 ≤ n)] :
    FiniteSubGaussianProcess.FiniteDyadicNetSequence
      (finDiscreteZeroProcess n) (fun _j : ℕ => Fin n) where
  N := finDiscreteDyadicNet n
  coverCount := finDiscreteDyadicCoverCount n
  radiusScale := 1
  dist_eq := finDiscreteDyadicNet_dist n
  dist_symm := finDiscreteDist_symm
  dist_triangle := finDiscreteDist_triangle
  radiusScale_nonneg := by norm_num
  radius_pos := finDiscreteDyadicNet_radius_pos n
  radius_geometric := finDiscreteDyadicNet_radius_geometric n
  pair_card_gt_one := finDiscreteDyadicNet_pair_card_gt_one
  coverCount_le := finDiscreteDyadicNet_coverCount_le n

/-- Supremum of a constant zero finite family. -/
private lemma finiteSup_zero {α : Type*} [Fintype α] [Nonempty α] :
    finiteSup (fun _ : α => (0 : ℝ)) = 0 := by
  unfold finiteSup
  simp

private theorem finDiscreteZero_coarse {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteZeroProcess n).weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
          (finDiscreteZeroProcess n).X ω
            ((finDiscreteDyadicNet n 0).projection
              (FiniteNet.ProjectedIndex.source (finDiscreteDyadicNet n m) u)))) ≤
      (0 : ℝ) := by
  simp [finDiscreteZeroProcess, finDiscreteZeroValue, finiteExpectation,
    finiteSup_zero]

/-- Projected finite-net Dudley bound for the zero process on `Fin n`, routed
through the generic dyadic-net sequence API. -/
theorem finDiscreteZero_projected_dudley_m_bound {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteZeroProcess n).weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
            (finDiscreteZeroProcess n).X ω ((finDiscreteDyadicNet n m).center u.1))) ≤
      2 * Real.sqrt (2 * (finDiscreteZeroProcess n).varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (finDiscreteDyadicCoverCount n j : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.FiniteDyadicNetSequence.projectedNet_dudley_bound
      (S := finDiscreteDyadicNetSequence n)
      (m := m) (coarseBudget := (0 : ℝ))
      (by norm_num [finDiscreteZeroProcess])
      (finDiscreteZero_coarse m)
  simpa [finDiscreteZeroProcess] using hbase

/-- Supremum functional for the zero process on `Fin n`. -/
def finDiscreteZeroSup (_n : ℕ) (_ω : PUnit) : ℝ :=
  0

theorem finDiscreteZeroSup_le_projectedSup {n : ℕ} [Fact (2 ≤ n)] (m : ℕ)
    (ω : PUnit) :
    finDiscreteZeroSup n ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
          (finDiscreteZeroProcess n).X ω ((finDiscreteDyadicNet n m).center u.1)) := by
  simp [finDiscreteZeroSup, finDiscreteZeroProcess, finDiscreteZeroValue,
    finiteSup_zero]

/-- Supplied-supremum Dudley bound for the zero process on `Fin n`, routed
through the generic dyadic-net sequence API. -/
theorem finDiscreteZeroSup_dudley_m_bound {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteZeroProcess n).weight (finDiscreteZeroSup n) ≤
      2 * Real.sqrt (2 * (finDiscreteZeroProcess n).varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (finDiscreteDyadicCoverCount n j : ℝ)))) := by
  have hbase :=
    FiniteSubGaussianProcess.FiniteDyadicNetSequence.supFunctional_dudley_bound
      (S := finDiscreteDyadicNetSequence n)
      (m := m) (coarseBudget := (0 : ℝ))
      (supFunctional := finDiscreteZeroSup n)
      (terminalError := (0 : ℝ))
      (by norm_num [finDiscreteZeroProcess])
      (by
        intro ω
        simpa [finDiscreteDyadicNetSequence] using
          finDiscreteZeroSup_le_projectedSup (n := n) m ω)
      (finDiscreteZero_coarse m)
  simpa [finDiscreteZeroProcess, finDiscreteZeroSup] using hbase

end

end FormalSLT.Covering.FiniteDiscreteDudley
