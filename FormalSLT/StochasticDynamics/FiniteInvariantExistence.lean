/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-!
# Existence of invariant laws for finite Markov kernels

Every Markov kernel on a nonempty finite state space has an invariant
probability mass function.  The construction is the classical Krylov--Bogolyubov
argument specialized to a finite simplex: take Cesaro averages of the iterated
laws, extract a convergent subsequence by compactness, and use the telescoping
identity to show that its limit is fixed by the kernel push-forward.

Combined with the finite Dobrushin uniqueness theorem, this supplies the
previously missing existence half of the stationary target.
-/

open Finset MeasureTheory ProbabilityTheory Set Filter Function Topology
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The ambient real-linear push-forward induced by a finite Markov kernel. -/
def finiteKernelPushLinear (P : Z → PMF Z) :
    (Z → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun μ y := ∑ x : Z, μ x * (P x y).toReal
  map_add' μ ν := by
    ext y
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c μ := by
    ext y
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
@[simp]
lemma finiteKernelPushLinear_apply (P : Z → PMF Z) (μ : Z → ℝ) (y : Z) :
    finiteKernelPushLinear P μ y = ∑ x : Z, μ x * (P x y).toReal :=
  rfl

/-- Kernel push-forward preserves the finite real probability simplex. -/
lemma finiteKernelPushLinear_mem_stdSimplex (P : Z → PMF Z)
    {μ : Z → ℝ} (hμ : μ ∈ stdSimplex ℝ Z) :
    finiteKernelPushLinear P μ ∈ stdSimplex ℝ Z := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _hx ↦
      mul_nonneg (hμ.1 x) ENNReal.toReal_nonneg
  · simp only [finiteKernelPushLinear_apply]
    rw [Finset.sum_comm]
    calc
      ∑ x : Z, ∑ y : Z, μ x * (P x y).toReal =
          ∑ x : Z, μ x * ∑ y : Z, (P x y).toReal := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Finset.mul_sum]
      _ = ∑ x : Z, μ x := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [finitePMF_real_mass_sum, mul_one]
      _ = 1 := hμ.2

/-- Kernel push-forward as a self-map of the finite probability simplex. -/
def finiteKernelPushSimplex (P : Z → PMF Z) :
    stdSimplex ℝ Z → stdSimplex ℝ Z := fun μ ↦
  ⟨finiteKernelPushLinear P μ, finiteKernelPushLinear_mem_stdSimplex P μ.2⟩

@[simp]
lemma finiteKernelPushSimplex_apply (P : Z → PMF Z)
    (μ : stdSimplex ℝ Z) (y : Z) :
    finiteKernelPushSimplex P μ y =
      ∑ x : Z, μ x * (P x y).toReal :=
  rfl

/-- The finite-simplex kernel push-forward is continuous. -/
lemma continuous_finiteKernelPushSimplex (P : Z → PMF Z) :
    Continuous (finiteKernelPushSimplex P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro y
  apply continuous_finsetSum
  intro x _hx
  exact ((continuous_apply x).comp continuous_subtype_val).mul continuous_const

/-- Orbit of a starting law under repeated kernel push-forward. -/
def finiteKernelOrbit (P : Z → PMF Z) (start : stdSimplex ℝ Z) (n : ℕ) :
    stdSimplex ℝ Z :=
  (finiteKernelPushSimplex P)^[n] start

@[simp]
lemma finiteKernelOrbit_zero (P : Z → PMF Z) (start : stdSimplex ℝ Z) :
    finiteKernelOrbit P start 0 = start := by
  simp [finiteKernelOrbit]

@[simp]
lemma finiteKernelOrbit_succ (P : Z → PMF Z) (start : stdSimplex ℝ Z)
    (n : ℕ) :
    finiteKernelOrbit P start (n + 1) =
      finiteKernelPushSimplex P (finiteKernelOrbit P start n) := by
  simp [finiteKernelOrbit, Function.iterate_succ_apply']

/-- The first `n+1` orbit laws averaged in the ambient real simplex. -/
def finiteKernelCesaroVector (P : Z → PMF Z) (start : stdSimplex ℝ Z)
    (n : ℕ) : Z → ℝ :=
  (1 / ((n : ℝ) + 1)) •
    ∑ k ∈ Finset.range (n + 1), (finiteKernelOrbit P start k : Z → ℝ)

/-- A finite Cesaro average of probability vectors is again a probability
vector. -/
lemma finiteKernelCesaroVector_mem_stdSimplex
    (P : Z → PMF Z) (start : stdSimplex ℝ Z) (n : ℕ) :
    finiteKernelCesaroVector P start n ∈ stdSimplex ℝ Z := by
  constructor
  · intro z
    simp only [finiteKernelCesaroVector, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    exact mul_nonneg (by positivity) <|
      Finset.sum_nonneg fun k _hk ↦ (finiteKernelOrbit P start k).2.1 z
  · simp only [finiteKernelCesaroVector, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have horbitSum :
        ∑ k ∈ Finset.range (n + 1),
            ∑ z : Z, finiteKernelOrbit P start k z = (n : ℝ) + 1 := by
      calc
        ∑ k ∈ Finset.range (n + 1),
            ∑ z : Z, finiteKernelOrbit P start k z =
            ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro k _hk
              exact (finiteKernelOrbit P start k).2.2
        _ = (n : ℝ) + 1 := by simp
    rw [horbitSum]
    field_simp

/-- Cesaro averages as points of the finite probability simplex. -/
def finiteKernelCesaro (P : Z → PMF Z) (start : stdSimplex ℝ Z) (n : ℕ) :
    stdSimplex ℝ Z :=
  ⟨finiteKernelCesaroVector P start n,
    finiteKernelCesaroVector_mem_stdSimplex P start n⟩

private lemma sum_range_shift_sub_sum_range {E : Type*} [AddCommGroup E]
    (f : ℕ → E) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (k + 1)) -
        ∑ k ∈ Finset.range N, f k =
      f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range N, f (k + 1)) + f (N + 1) -
              ((∑ k ∈ Finset.range N, f k) + f N) =
            ((∑ k ∈ Finset.range N, f (k + 1)) -
              ∑ k ∈ Finset.range N, f k) + (f (N + 1) - f N) := by
                abel
        _ = f (N + 1) - f 0 := by rw [ih]; abel

lemma finiteKernelPushLinear_orbit (P : Z → PMF Z)
    (start : stdSimplex ℝ Z) (n : ℕ) :
    finiteKernelPushLinear P (finiteKernelOrbit P start n : Z → ℝ) =
      (finiteKernelOrbit P start (n + 1) : Z → ℝ) := by
  apply funext
  intro z
  rw [finiteKernelOrbit_succ]
  rfl

/-- Applying the kernel to a Cesaro average differs from that average only by
the two endpoint laws divided by the averaging length. -/
lemma finiteKernelPushLinear_cesaroVector_sub
    (P : Z → PMF Z) (start : stdSimplex ℝ Z) (n : ℕ) :
    finiteKernelPushLinear P (finiteKernelCesaroVector P start n) -
        finiteKernelCesaroVector P start n =
      (1 / ((n : ℝ) + 1)) •
        ((finiteKernelOrbit P start (n + 1) : Z → ℝ) -
          (start : Z → ℝ)) := by
  unfold finiteKernelCesaroVector
  rw [map_smul, map_sum]
  simp_rw [finiteKernelPushLinear_orbit]
  rw [← smul_sub]
  congr 1
  simpa using sum_range_shift_sub_sum_range
    (fun k ↦ (finiteKernelOrbit P start k : Z → ℝ)) (n + 1)

/-- The endpoint term in the Cesaro telescoping identity vanishes. -/
lemma tendsto_finiteKernelCesaro_endpoint_zero
    (P : Z → PMF Z) (start : stdSimplex ℝ Z) :
    Tendsto
      (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) •
        ((finiteKernelOrbit P start (n + 1) : Z → ℝ) -
          (start : Z → ℝ)))
      atTop (nhds 0) := by
  rw [tendsto_pi_nhds]
  intro z
  simp only [Pi.zero_apply]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun n : ℕ ↦ abs_nonneg _) (fun n : ℕ ↦ ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdiff :
      |finiteKernelOrbit P start (n + 1) z - start z| ≤ 1 := by
    let a : ℝ := (finiteKernelOrbit P start (n + 1)).1 z
    let b : ℝ := start.1 z
    have ha := mem_Icc_of_mem_stdSimplex
      (finiteKernelOrbit P start (n + 1)).2 z
    have hb := mem_Icc_of_mem_stdSimplex start.2 z
    change |a - b| ≤ 1
    rw [abs_le]
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    constructor <;> linarith
  simp only [Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hdiff
      (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity)

/-- The kernel push-forward defect of the Cesaro averages converges to zero. -/
lemma tendsto_finiteKernelPushLinear_cesaroVector_sub_zero
    (P : Z → PMF Z) (start : stdSimplex ℝ Z) :
    Tendsto
      (fun n ↦ finiteKernelPushLinear P (finiteKernelCesaroVector P start n) -
        finiteKernelCesaroVector P start n)
      atTop (nhds 0) := by
  apply (tendsto_finiteKernelCesaro_endpoint_zero P start).congr'
  exact Filter.Eventually.of_forall fun n ↦
    (finiteKernelPushLinear_cesaroVector_sub P start n).symm

variable [Nonempty Z]

/-- Every finite Markov kernel has a fixed point in the real probability
simplex. -/
theorem exists_finiteKernelPushSimplex_fixedPoint (P : Z → PMF Z) :
    ∃ stationary : stdSimplex ℝ Z,
      finiteKernelPushSimplex P stationary = stationary := by
  let start : stdSimplex ℝ Z := stdSimplex.barycenter
  obtain ⟨stationary, φ, hφ, hlimit⟩ :=
    CompactSpace.tendsto_subseq (fun n ↦ finiteKernelCesaro P start n)
  have hlimitVal :
      Tendsto
        (fun n ↦ (finiteKernelCesaro P start (φ n) : Z → ℝ))
        atTop (nhds (stationary : Z → ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlimit
  have hpushLimit :
      Tendsto
        (fun n ↦
          (finiteKernelPushSimplex P
            (finiteKernelCesaro P start (φ n)) : Z → ℝ))
        atTop
        (nhds (finiteKernelPushSimplex P stationary : Z → ℝ)) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp <|
      (continuous_finiteKernelPushSimplex P).continuousAt.tendsto.comp hlimit
  have hdefectLimit :
      Tendsto
        (fun n ↦
          (finiteKernelPushSimplex P
              (finiteKernelCesaro P start (φ n)) : Z → ℝ) -
            (finiteKernelCesaro P start (φ n) : Z → ℝ))
        atTop
        (nhds
          ((finiteKernelPushSimplex P stationary : Z → ℝ) -
            (stationary : Z → ℝ))) :=
    hpushLimit.sub hlimitVal
  have hdefectZero :
      Tendsto
        (fun n ↦
          (finiteKernelPushSimplex P
              (finiteKernelCesaro P start (φ n)) : Z → ℝ) -
            (finiteKernelCesaro P start (φ n) : Z → ℝ))
        atTop (nhds 0) := by
    have hbase :=
      (tendsto_finiteKernelPushLinear_cesaroVector_sub_zero P start).comp
        hφ.tendsto_atTop
    apply hbase.congr'
    exact Filter.Eventually.of_forall fun n ↦ rfl
  have hzero :
      (finiteKernelPushSimplex P stationary : Z → ℝ) -
          (stationary : Z → ℝ) = 0 :=
    tendsto_nhds_unique hdefectLimit hdefectZero
  refine ⟨stationary, Subtype.ext ?_⟩
  exact sub_eq_zero.mp hzero

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The real-mass push-forward is the real mass of PMF bind. -/
lemma finiteKernelPushLinear_realMass_eq_bind
    (P : Z → PMF Z) (p : PMF Z) (y : Z) :
    finiteKernelPushLinear P (fun z ↦ (p z).toReal) y =
      ((p.bind P) y).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro z _hz
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p z)
      (PMF.apply_ne_top (P z) y))]
  simp only [ENNReal.toReal_mul]
  rfl

/-- Every Markov kernel on a nonempty finite state space has an invariant PMF. -/
theorem exists_invariantPMF (P : Z → PMF Z) :
    ∃ stationary : PMF Z, IsInvariantPMF P stationary := by
  obtain ⟨stationaryVec, hfixed⟩ :=
    exists_finiteKernelPushSimplex_fixedPoint P
  let hstationaryVec : IsPMF (stationaryVec : Z → ℝ) :=
    ⟨stationaryVec.2.1, stationaryVec.2.2⟩
  let stationary : PMF Z := hstationaryVec.toPMF
  refine ⟨stationary, ?_⟩
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (stationary.bind P) y)
    (PMF.apply_ne_top stationary y)).mp
  have hfixed_y := congrFun (congrArg Subtype.val hfixed) y
  calc
    ((stationary.bind P) y).toReal =
        finiteKernelPushLinear P (fun z ↦ (stationary z).toReal) y :=
      (finiteKernelPushLinear_realMass_eq_bind P stationary y).symm
    _ = finiteKernelPushLinear P (stationaryVec : Z → ℝ) y := by
      apply congrArg fun v : Z → ℝ ↦ finiteKernelPushLinear P v y
      funext z
      exact hstationaryVec.toPMF_apply_toReal z
    _ = stationaryVec y := hfixed_y
    _ = (stationary y).toReal := by
      exact (hstationaryVec.toPMF_apply_toReal y).symm

/-- A canonical invariant PMF chosen from finite-state existence. -/
noncomputable def finiteInvariantPMF (P : Z → PMF Z) : PMF Z :=
  Classical.choose (exists_invariantPMF P)

/-- The canonical finite invariant PMF is invariant. -/
theorem finiteInvariantPMF_isInvariant (P : Z → PMF Z) :
    IsInvariantPMF P (finiteInvariantPMF P) :=
  Classical.choose_spec (exists_invariantPMF P)

/-- Dobrushin contraction below one supplies a unique invariant PMF, not only
uniqueness conditional on a supplied invariant witness. -/
theorem existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one
    (P : Z → PMF Z)
    (hcoefficient : finiteDobrushinCoefficient P < 1) :
    ∃! stationary : PMF Z, IsInvariantPMF P stationary := by
  refine ⟨finiteInvariantPMF P, finiteInvariantPMF_isInvariant P, ?_⟩
  intro stationary hstationary
  exact invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one P
    hcoefficient stationary (finiteInvariantPMF P) hstationary
      (finiteInvariantPMF_isInvariant P)

/-- A candidate-kernel row-TV certificate supplies a unique invariant PMF for
the true finite kernel. -/
theorem existsUnique_invariantPMF_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1) :
    ∃! stationary : PMF Z, IsInvariantPMF P stationary := by
  refine ⟨finiteInvariantPMF P, finiteInvariantPMF_isInvariant P, ?_⟩
  intro stationary hstationary
  exact invariantPMF_unique_of_candidate_rowTV P Q hrowTV hcertificate
    stationary (finiteInvariantPMF P) hstationary
      (finiteInvariantPMF_isInvariant P)

end

end FormalSLT.StochasticDynamics
