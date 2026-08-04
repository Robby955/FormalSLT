import FormalSLT.Covering.FiniteSubGaussianChaining
import FormalSLT.Rademacher.Massart

/-!
# Finite discrete dyadic-net Dudley example

This module instantiates `FiniteDyadicNetSequence` for the finite discrete
metric family `Fin n`, assuming `2 ≤ n`. It is an API-usability example: the
cover-count envelope is `n * n`, so the generic dyadic-net wrapper is exercised
with a nonconstant finite family rather than only `[0,1]` or the two-point
space.

The process is a nonzero one-coordinate Rademacher process embedded in `Fin n`.
It keeps the metric-net bookkeeping simple while making the supplied supremum
nontrivial.
-/

namespace FormalSLT.Covering.FiniteDiscreteDudley

open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess
open FormalSLT.Rademacher.FiniteSample
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

/-- A one-coordinate Rademacher process embedded in the finite discrete family. -/
def finDiscreteRademacherValue {n : ℕ} [Fact (2 ≤ n)] (ω : Bool) (t : Fin n) : ℝ :=
  if t = finOne then signOfBool ω else 0

private theorem finDiscreteRademacherValue_le_one {n : ℕ} [Fact (2 ≤ n)]
    (ω : Bool) (t : Fin n) :
    finDiscreteRademacherValue ω t ≤ 1 := by
  by_cases ht : t = finOne
  · cases ω <;> simp [finDiscreteRademacherValue, ht, signOfBool]
  · simp [finDiscreteRademacherValue, ht]

theorem finDiscrete_rademacher_mgf_bound {n : ℕ} [Fact (2 ≤ n)]
    (s t : Fin n) (lam : ℝ) :
    finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
        (fun ω => Real.exp
          (lam * (finDiscreteRademacherValue ω t - finDiscreteRademacherValue ω s))) ≤
      Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) := by
  by_cases hst : s = t
  · subst hst
    norm_num [finiteExpectation, finDiscreteRademacherValue, finDiscreteDist]
  · have hdist : finDiscreteDist s t = 1 := by
      simp [finDiscreteDist, hst]
    by_cases ht : t = finOne
    · by_cases hs : s = finOne
      · have hst' : s = t := by
          rw [hs, ht]
        exact (hst hst').elim
      · calc
          finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
              (fun ω => Real.exp
                (lam *
                  (finDiscreteRademacherValue ω t -
                    finDiscreteRademacherValue ω s)))
              = (∑ b : Bool, Real.exp (lam * signOfBool b * (1 : ℝ))) / 2 := by
                  simp [finiteExpectation, finDiscreteRademacherValue, ht, hs]
                  ring
          _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) ^ 2 / 2) := by
                  rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
                  exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam 1
          _ = Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) := by
                  norm_num [hdist]
    · by_cases hs : s = finOne
      · calc
          finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
              (fun ω => Real.exp
                (lam *
                  (finDiscreteRademacherValue ω t -
                    finDiscreteRademacherValue ω s)))
              = (∑ b : Bool, Real.exp (lam * signOfBool b * (-1 : ℝ))) / 2 := by
                  simp [finiteExpectation, finDiscreteRademacherValue, ht, hs]
                  ring
          _ ≤ Real.exp (lam ^ 2 * (-1 : ℝ) ^ 2 / 2) := by
                  rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
                  exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam (-1)
          _ = Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) := by
                  norm_num [hdist]
      · have hnonneg :
            0 ≤ lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2 := by
          nlinarith [sq_nonneg lam, sq_nonneg (finDiscreteDist s t)]
        calc
          finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
              (fun ω => Real.exp
                (lam *
                  (finDiscreteRademacherValue ω t -
                    finDiscreteRademacherValue ω s)))
              = 1 := by
                  simp [finiteExpectation, finDiscreteRademacherValue, ht, hs]
          _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) * finDiscreteDist s t ^ 2 / 2) :=
                  Real.one_le_exp hnonneg

/-- The embedded Rademacher process packaged as a finite sub-Gaussian process
on `Fin n`. -/
def finDiscreteRademacherProcess (n : ℕ) [Fact (2 ≤ n)] :
    FiniteSubGaussianProcess Bool (Fin n) where
  weight := fun _ => (1 : ℝ) / 2
  weight_nonneg := by intro ω; norm_num
  weight_sum_one := by norm_num [Fintype.sum_bool]
  X := finDiscreteRademacherValue
  dist := finDiscreteDist
  dist_nonneg := finDiscreteDist_nonneg
  varianceProxy := 1
  varianceProxy_nonneg := by norm_num
  mgf_increment := finDiscrete_rademacher_mgf_bound

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

theorem finDiscreteDyadicNet_dist (n : ℕ) [Fact (2 ≤ n)] (j : ℕ) :
    (finDiscreteDyadicNet n j).dist = (finDiscreteRademacherProcess n).dist := by
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
  change finZero = finOne at hfst
  exact finZero_ne_finOne (n := n) hfst

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
      (finDiscreteRademacherProcess n) (fun _j : ℕ => Fin n) where
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

private theorem finDiscreteRademacher_coarse {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteRademacherProcess n).weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
          (finDiscreteRademacherProcess n).X ω
            ((finDiscreteDyadicNet n 0).projection
              (FiniteNet.ProjectedIndex.source (finDiscreteDyadicNet n m) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation (finDiscreteRademacherProcess n).weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
          (finDiscreteRademacherProcess n).X ω
            ((finDiscreteDyadicNet n 0).projection
              (FiniteNet.ProjectedIndex.source (finDiscreteDyadicNet n m) u))))
        ≤ finiteExpectation (finDiscreteRademacherProcess n).weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono (finDiscreteRademacherProcess n).weight_nonneg ?_
          intro ω
          unfold finiteSup
          exact Finset.sup'_le Finset.univ_nonempty _ fun u _hu =>
            finDiscreteRademacherValue_le_one ω
              ((finDiscreteDyadicNet n 0).projection
                (FiniteNet.ProjectedIndex.source (finDiscreteDyadicNet n m) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            (finDiscreteRademacherProcess n).weight 1
            (finDiscreteRademacherProcess n).weight_sum_one

/-- Packaged finite-dyadic Dudley instance for the embedded Rademacher process
on `Fin n`. -/
def finDiscreteDudleyInstance (n : ℕ) [Fact (2 ≤ n)] :
    FiniteDyadicDudleyInstance (finDiscreteRademacherProcess n) (fun _j : ℕ => Fin n) where
  netSequence := finDiscreteDyadicNetSequence n
  coarseBudget := 1
  variance_pos := by norm_num [finDiscreteRademacherProcess]
  coarse_bound := finDiscreteRademacher_coarse

/-- Projected finite-net Dudley bound for the embedded Rademacher process on
`Fin n`, routed through the packaged finite-dyadic Dudley API. -/
theorem finDiscreteRademacher_projected_dudley_m_bound {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteRademacherProcess n).weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
            (finDiscreteRademacherProcess n).X ω ((finDiscreteDyadicNet n m).center u.1))) ≤
      1 + 2 * Real.sqrt (2 * (finDiscreteRademacherProcess n).varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (finDiscreteDyadicCoverCount n j : ℝ)))) := by
  have hbase :=
    FiniteDyadicDudleyInstance.projected_dudley_bound
      (finDiscreteDudleyInstance n) m
  convert hbase using 1 <;>
    simp [finDiscreteDudleyInstance, finDiscreteDyadicNetSequence,
      finDiscreteRademacherProcess]

/-- Supremum functional for the embedded Rademacher process on `Fin n`. -/
def finDiscreteRademacherSup {n : ℕ} [Fact (2 ≤ n)] (ω : Bool) : ℝ :=
  finiteSup (fun t : Fin n => (finDiscreteRademacherProcess n).X ω t)

theorem finDiscreteRademacherSup_true {n : ℕ} [Fact (2 ≤ n)] :
    finDiscreteRademacherSup (n := n) true = 1 := by
  unfold finDiscreteRademacherSup finiteSup
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ (by
      intro t _ht
      by_cases h : t = finOne
      · simp [finDiscreteRademacherProcess, finDiscreteRademacherValue, h, signOfBool]
      · simp [finDiscreteRademacherProcess, finDiscreteRademacherValue, h])
  · have hle :=
      Finset.le_sup'
        (fun t : Fin n => (finDiscreteRademacherProcess n).X true t)
        (Finset.mem_univ (finOne : Fin n))
    simpa [finDiscreteRademacherProcess, finDiscreteRademacherValue, signOfBool] using hle

theorem finDiscreteRademacherSup_le_projectedSup {n : ℕ} [Fact (2 ≤ n)] (m : ℕ)
    (ω : Bool) :
    finDiscreteRademacherSup (n := n) ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
          (finDiscreteRademacherProcess n).X ω ((finDiscreteDyadicNet n m).center u.1)) := by
  unfold finDiscreteRademacherSup finiteSup
  apply Finset.sup'_le
  intro t _ht
  let u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) := ⟨t, ⟨t, rfl⟩⟩
  have hle :=
    Finset.le_sup'
      (fun u : FiniteNet.ProjectedIndex (finDiscreteDyadicNet n m) =>
        (finDiscreteRademacherProcess n).X ω ((finDiscreteDyadicNet n m).center u.1))
      (Finset.mem_univ u)
  simpa [u, finDiscreteDyadicNet] using hle

/-- Supplied-supremum adapter for the embedded Rademacher process on `Fin n`. -/
def finDiscreteRademacherSupAdapter (n : ℕ) [Fact (2 ≤ n)] :
    FiniteDyadicDudleyInstance.SupremumAdapter (finDiscreteDudleyInstance n) where
  supFunctional := finDiscreteRademacherSup (n := n)
  terminalError := 0
  terminal_bound := by
    intro m ω
    convert finDiscreteRademacherSup_le_projectedSup (n := n) m ω using 1;
      simp [finDiscreteDudleyInstance, finDiscreteDyadicNetSequence]

/-- Supplied-supremum Dudley bound for the embedded Rademacher process on
`Fin n`, routed through the packaged finite-dyadic Dudley API. -/
theorem finDiscreteRademacherSup_dudley_m_bound {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    finiteExpectation (finDiscreteRademacherProcess n).weight
        (finDiscreteRademacherSup (n := n)) ≤
      1 + 2 * Real.sqrt (2 * (finDiscreteRademacherProcess n).varianceProxy) *
        FiniteSubGaussianProcess.finiteDyadicEntropyIntegralBudget (1 : ℝ) m
          (FiniteSubGaussianProcess.finitePrefixSupEnvelope
            (fun j : ℕ =>
              Real.sqrt (Real.log (finDiscreteDyadicCoverCount n j : ℝ)))) := by
  have hbase :=
    FiniteDyadicDudleyInstance.suppliedSup_dudley_bound
      (finDiscreteDudleyInstance n) (finDiscreteRademacherSupAdapter n) m
  convert hbase using 1 <;>
    simp [finDiscreteDudleyInstance, finDiscreteDyadicNetSequence,
      finDiscreteRademacherSupAdapter, finDiscreteRademacherProcess]

end

end FormalSLT.Covering.FiniteDiscreteDudley
