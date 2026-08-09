/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.OptimizedLambdaCS
import Mathlib.Probability.CondVar
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Prequential risk along a finite Markov trajectory

This file connects a finite transition PMF to Mathlib's Ionescu--Tulcea trajectory
measure.  Its core result identifies the conditional expectation of a bounded
one-step squared loss under the generated path law.  The centered innovation is
therefore derived from the dynamics rather than assumed.  Its conditional
second moment uses the sharp universal `1/4` variance bound for `[0,1]` losses.

The path construction follows the Ionescu--Tulcea extension used by
`Mathlib.Probability.Kernel.IonescuTulcea.Traj`.  The time-uniform step uses the
finite-grid sub-Gamma confidence-sequence interface in
`FormalSLT.AnytimeValid.OptimizedLambdaCS`, in the tradition of Howard, Ramdas,
McAuliffe, and Sekhon (2021), *Time-uniform, nonparametric, nonasymptotic
confidence sequences*.

Scope is deliberately narrow: the state space is finite, the initial state is
deterministic, and the observable `f` and predictor `q` are fixed functions with
values in `[0,1]`.  The target is the pathwise average of one-step conditional
risks.  No stationarity, mixing, irreducibility, same-trajectory training,
continuous-state dynamics, or long-run stationary-risk conclusion is claimed.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The Markov kernel associated with a finite-state transition PMF. -/
def pmfKernel (P : Z → PMF Z) : Kernel Z Z :=
  Kernel.ofFunOfCountable fun z ↦ (P z).toMeasure

instance pmfKernel.instIsMarkovKernel (P : Z → PMF Z) : IsMarkovKernel (pmfKernel P) :=
  ⟨fun z ↦ by
    change IsProbabilityMeasure (P z).toMeasure
    infer_instance⟩

/-- The next-state kernel reads the current state from a finite trajectory prefix. -/
def prefixKernel (P : Z → PMF Z) (n : ℕ) : Kernel ((i : Finset.Iic n) → Z) Z :=
  (pmfKernel P).comap
    (fun x ↦ x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply (X := fun _ : Finset.Iic n ↦ Z)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

instance prefixKernel.instIsMarkovKernel (P : Z → PMF Z) (n : ℕ) :
    IsMarkovKernel (prefixKernel P n) := by
  unfold prefixKernel
  infer_instance

/-- An infinite Markov path with deterministic initial state `x0`. -/
def markovPathMeasure (P : Z → PMF Z) (x0 : Z) : Measure (ℕ → Z) :=
  Kernel.traj (X := fun _ : ℕ ↦ Z) (prefixKernel P) 0 (fun _ ↦ x0)

instance markovPathMeasure.instIsProbabilityMeasure (P : Z → PMF Z) (x0 : Z) :
    IsProbabilityMeasure (markovPathMeasure P x0) := by
  unfold markovPathMeasure
  infer_instance

/-- Squared one-step prediction loss. -/
def transitionSquaredLoss (f q : Z → ℝ) (x y : Z) : ℝ :=
  (f y - q x) ^ 2

/-- Observed one-step loss at time `n` along a trajectory. -/
def pathSquaredLoss (f q : Z → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  transitionSquaredLoss f q (x n) (x (n + 1))

/-- Conditional one-step risk under the transition row at the current state. -/
def conditionalSquaredRisk (P : Z → PMF Z) (f q : Z → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  ∫ y, transitionSquaredLoss f q (x n) y ∂(P (x n)).toMeasure

lemma measurable_pathSquaredLoss (f q : Z → ℝ) (n : ℕ) :
    Measurable (pathSquaredLoss f q n) := by
  unfold pathSquaredLoss transitionSquaredLoss
  fun_prop

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma transitionSquaredLoss_mem_Icc
    {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (x y : Z) :
    transitionSquaredLoss f q x y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · exact sq_nonneg _
  · unfold transitionSquaredLoss
    rcases hf y with ⟨hfy0, hfy1⟩
    rcases hq x with ⟨hqx0, hqx1⟩
    nlinarith [sq_nonneg (f y - q x), sq_nonneg (1 - (f y - q x)),
      sq_nonneg (1 + (f y - q x))]

lemma integrable_pathSquaredLoss
    {P : Z → PMF Z} {x0 : Z} {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (pathSquaredLoss f q n) (markovPathMeasure P x0) := by
  refine Integrable.of_bound (measurable_pathSquaredLoss f q n).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    change |transitionSquaredLoss f q (x n) (x (n + 1))| ≤ 1
    rw [abs_of_nonneg
      (transitionSquaredLoss_mem_Icc hf hq (x n) (x (n + 1))).1]
    exact (transitionSquaredLoss_mem_Icc hf hq (x n) (x (n + 1))).2

/-- Under the generated trajectory, the next coordinate has the transition PMF
at the last state of the supplied prefix. -/
lemma map_traj_next (P : Z → PMF Z) (n : ℕ) (u : (i : Finset.Iic n) → Z) :
    (Kernel.traj (X := fun _ : ℕ ↦ Z) (prefixKernel P) n u).map
        (fun x ↦ x (n + 1)) =
      (P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  rw [← Kernel.map_apply
    (Kernel.traj (X := fun _ : ℕ ↦ Z) (prefixKernel P) n)
    (measurable_pi_apply (n + 1)) u]
  rw [Kernel.map_traj_succ_self]
  rfl

/-- Integrating the observed next-step loss against a trajectory continuation is
the transition-row risk at the final state of the prefix. -/
lemma integral_pathSquaredLoss_traj
    (P : Z → PMF Z) (f q : Z → ℝ) (n : ℕ) (u : (i : Finset.Iic n) → Z) :
    ∫ x, pathSquaredLoss f q n x
        ∂Kernel.traj (X := fun _ : ℕ ↦ Z) (prefixKernel P) n u =
      ∫ y, transitionSquaredLoss f q
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
        ∂(P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  let μn : Measure (ℕ → Z) :=
    Kernel.traj (X := fun _ : ℕ ↦ Z) (prefixKernel P) n u
  calc
    ∫ x, pathSquaredLoss f q n x ∂μn =
        ∫ x, pathSquaredLoss f q n
          (Function.updateFinset x (Finset.Iic n) u) ∂μn := by
      exact Kernel.integral_traj (X := fun _ : ℕ ↦ Z) u
        (measurable_pathSquaredLoss f q n).aestronglyMeasurable
    _ = ∫ x, transitionSquaredLoss f q
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (x (n + 1)) ∂μn := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simp [pathSquaredLoss, Function.updateFinset, Finset.mem_Iic]
    _ = ∫ y, transitionSquaredLoss f q
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
          ∂Measure.map (fun x : ℕ → Z ↦ x (n + 1)) μn := by
      symm
      exact integral_map
        (measurable_pi_apply (n + 1)).aemeasurable
        (measurable_of_countable
          (transitionSquaredLoss f q
            (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩))).aestronglyMeasurable
    _ = ∫ y, transitionSquaredLoss f q
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
        ∂(P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
      rw [show Measure.map (fun x : ℕ → Z ↦ x (n + 1)) μn =
          (P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure by
        exact map_traj_next P n u]

/-- The generated Markov trajectory determines the conditional expectation of
the next-step squared loss.  In particular, the right-hand side is not carried
as a martingale-difference assumption. -/
theorem pathSquaredLoss_condExp
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (markovPathMeasure P x0)[pathSquaredLoss f q n |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[markovPathMeasure P x0]
      conditionalSquaredRisk P f q n := by
  have hcond := Kernel.condExp_traj
    (X := fun _ : ℕ ↦ Z) (κ := prefixKernel P)
    (a := 0) (b := n) (Nat.zero_le n)
    (integrable_pathSquaredLoss (P := P) (x0 := x0) hf hq n)
  unfold markovPathMeasure
  filter_upwards [hcond] with x hx
  rw [hx, integral_pathSquaredLoss_traj P f q n]
  rfl

omit [Fintype Z] [MeasurableSingletonClass Z] in
private lemma stronglyMeasurable_piLE_of_prefix
    (n : ℕ) (g : ((i : Finset.Iic n) → Z) → ℝ) (hg : StronglyMeasurable g) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
      (fun x ↦ g (Preorder.frestrictLe n x)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact hg.comp_measurable (comap_measurable _)

lemma stronglyMeasurable_conditionalSquaredRisk
    (P : Z → PMF Z) (f q : Z → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
      (conditionalSquaredRisk P f q n) := by
  let g : ((i : Finset.Iic n) → Z) → ℝ := fun u ↦
    ∫ y, transitionSquaredLoss f q
      (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
      ∂(P (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  have hg : StronglyMeasurable g := (measurable_of_countable g).stronglyMeasurable
  change StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
    (fun x ↦ ∫ y, transitionSquaredLoss f q (x n) y ∂(P (x n)).toMeasure)
  simpa [g, Preorder.frestrictLe_apply] using
    stronglyMeasurable_piLE_of_prefix n g hg

lemma conditionalSquaredRisk_mem_Icc
    (P : Z → PMF Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : ℕ → Z) :
    conditionalSquaredRisk P f q n x ∈ Set.Icc (0 : ℝ) 1 := by
  let rowLoss : Z → ℝ := fun y ↦ transitionSquaredLoss f q (x n) y
  have hrow_int : Integrable rowLoss (P (x n)).toMeasure := Integrable.of_finite
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y ↦ (transitionSquaredLoss_mem_Icc hf hq (x n) y).1)
  · have hle := integral_mono_ae hrow_int (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun y ↦
          (transitionSquaredLoss_mem_Icc hf hq (x n) y).2)
    simpa [conditionalSquaredRisk, rowLoss] using hle

lemma integrable_conditionalSquaredRisk
    {P : Z → PMF Z} {x0 : Z} {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (conditionalSquaredRisk P f q n) (markovPathMeasure P x0) := by
  have hrisk_meas : StronglyMeasurable (conditionalSquaredRisk P f q n) :=
    (stronglyMeasurable_conditionalSquaredRisk P f q n).mono
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le n)
  refine Integrable.of_bound hrisk_meas.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (conditionalSquaredRisk_mem_Icc P hf hq n x).1]
    exact (conditionalSquaredRisk_mem_Icc P hf hq n x).2

/-- Observed loss minus its transition-row conditional risk. -/
def markovRiskInnovation (P : Z → PMF Z) (f q : Z → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  pathSquaredLoss f q n x - conditionalSquaredRisk P f q n x

private lemma stronglyMeasurable_pathSquaredLoss_succ
    (f q : Z → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) (n + 1)]
      (pathSquaredLoss f q n) := by
  let g : ((i : Finset.Iic (n + 1)) → Z) → ℝ := fun u ↦
    transitionSquaredLoss f q
      (u ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩)
      (u ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  have hg : StronglyMeasurable g := (measurable_of_countable g).stronglyMeasurable
  change StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) (n + 1)]
    (fun x ↦ transitionSquaredLoss f q (x n) (x (n + 1)))
  simpa [g, Preorder.frestrictLe_apply] using
    stronglyMeasurable_piLE_of_prefix (n + 1) g hg

lemma markovRiskInnovation_incrementAdapted
    (P : Z → PMF Z) (f q : Z → ℝ) :
    AnytimeValid.IncrementAdapted
      (Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (markovRiskInnovation P f q) := by
  intro n
  exact (stronglyMeasurable_pathSquaredLoss_succ f q n).sub
    ((stronglyMeasurable_conditionalSquaredRisk P f q n).mono
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).mono (Nat.le_succ n)))

lemma measurable_markovRiskInnovation
    (P : Z → PMF Z) (f q : Z → ℝ) (n : ℕ) :
    Measurable (markovRiskInnovation P f q n) :=
  ((markovRiskInnovation_incrementAdapted P f q) n).mono
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le (n + 1)) |>.measurable

lemma abs_markovRiskInnovation_le_one
    (P : Z → PMF Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : ℕ → Z) :
    |markovRiskInnovation P f q n x| ≤ 1 := by
  have hloss := transitionSquaredLoss_mem_Icc hf hq (x n) (x (n + 1))
  have hrisk := conditionalSquaredRisk_mem_Icc P hf hq n x
  rcases hloss with ⟨hloss0, hloss1⟩
  rcases hrisk with ⟨hrisk0, hrisk1⟩
  rw [abs_le]
  unfold markovRiskInnovation pathSquaredLoss
  constructor <;> linarith

lemma integrable_markovRiskInnovation
    {P : Z → PMF Z} {x0 : Z} {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (markovRiskInnovation P f q n) (markovPathMeasure P x0) := by
  exact (integrable_pathSquaredLoss (P := P) (x0 := x0) hf hq n).sub
    (integrable_conditionalSquaredRisk (P := P) (x0 := x0) hf hq n)

/-- The prequential innovation is conditionally centered because its risk term
is the transition-row conditional expectation of the observed loss. -/
theorem markovRiskInnovation_condExp_eq_zero
    (P : Z → PMF Z) (x0 : Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (markovPathMeasure P x0)[markovRiskInnovation P f q n |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[markovPathMeasure P x0] 0 := by
  have hloss_int := integrable_pathSquaredLoss (P := P) (x0 := x0) hf hq n
  have hrisk_int := integrable_conditionalSquaredRisk (P := P) (x0 := x0) hf hq n
  have hsub := condExp_sub hloss_int hrisk_int
    (Filtration.piLE (X := fun _ : ℕ ↦ Z) n)
  have hsub' :
      (markovPathMeasure P x0)[markovRiskInnovation P f q n |
          Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[markovPathMeasure P x0]
        (markovPathMeasure P x0)[pathSquaredLoss f q n |
            Filtration.piLE (X := fun _ : ℕ ↦ Z) n] -
          (markovPathMeasure P x0)[conditionalSquaredRisk P f q n |
            Filtration.piLE (X := fun _ : ℕ ↦ Z) n] := by
    rw [show markovRiskInnovation P f q n =
        pathSquaredLoss f q n - conditionalSquaredRisk P f q n by rfl]
    exact hsub
  have hloss := pathSquaredLoss_condExp P x0 f q hf hq n
  have hrisk :
      (markovPathMeasure P x0)[conditionalSquaredRisk P f q n |
          Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =
      conditionalSquaredRisk P f q n :=
    condExp_of_stronglyMeasurable
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le n)
      (stronglyMeasurable_conditionalSquaredRisk P f q n) hrisk_int
  filter_upwards [hsub', hloss] with x hsubx hlossx
  rw [hsubx]
  change (markovPathMeasure P x0)[pathSquaredLoss f q n |
      Filtration.piLE (X := fun _ : ℕ ↦ Z) n] x -
    (markovPathMeasure P x0)[conditionalSquaredRisk P f q n |
      Filtration.piLE (X := fun _ : ℕ ↦ Z) n] x = 0
  rw [hlossx, hrisk]
  simp

/-- The conditional second moment of the centered one-step loss has the sharp
`1/4` bound for a random variable taking values in `[0,1]`.  The proof uses the
actual transition-law conditional expectation, then applies
`E[L² | ℱ] ≤ E[L | ℱ]` and `m(1-m) ≤ 1/4`. -/
theorem markovRiskInnovation_condSecondMoment_le_one_fourth
    (P : Z → PMF Z) (x0 : Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (markovPathMeasure P x0)[fun x ↦ (markovRiskInnovation P f q n x) ^ 2 |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] ≤ᵐ[markovPathMeasure P x0]
      fun _ ↦ (1 / 4 : ℝ) := by
  let μ := markovPathMeasure P x0
  let ℱ := Filtration.piLE (X := fun _ : ℕ ↦ Z)
  let L := pathSquaredLoss f q n
  have hL_Icc : ∀ᵐ x ∂μ, L x ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun x ↦ by
      exact transitionSquaredLoss_mem_Icc hf hq (x n) (x (n + 1))
  have hL_memLp : MemLp L 2 μ :=
    memLp_of_bounded hL_Icc
      (measurable_pathSquaredLoss f q n).aestronglyMeasurable 2
  have hL_cond :
      μ[L | ℱ n] =ᵐ[μ] conditionalSquaredRisk P f q n := by
    simpa [μ, ℱ, L] using pathSquaredLoss_condExp P x0 f q hf hq n
  have hinnovation_eq_condVar :
      μ[fun x ↦ (markovRiskInnovation P f q n x) ^ 2 | ℱ n] =ᵐ[μ]
        Var[L; μ | ℱ n] := by
    unfold ProbabilityTheory.condVar
    refine condExp_congr_ae ?_
    filter_upwards [hL_cond] with x hx
    change (L x - conditionalSquaredRisk P f q n x) ^ 2 =
      (L x - μ[L | ℱ n] x) ^ 2
    rw [hx]
  have hcondVar_formula :=
    condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le n) hL_memLp
  have hL_sq_le : ∀ᵐ x ∂μ, L x ^ 2 ≤ L x :=
    hL_Icc.mono fun x hx ↦ by
      rcases hx with ⟨hx0, hx1⟩
      nlinarith [sq_nonneg (L x)]
  have hcond_sq_le := condExp_mono (m := ℱ n) (μ := μ)
    hL_memLp.integrable_sq (integrable_pathSquaredLoss
      (P := P) (x0 := x0) hf hq n) hL_sq_le
  filter_upwards [hinnovation_eq_condVar, hcondVar_formula,
    hcond_sq_le, hL_cond] with x hinnovation hformula hsq hmean
  rw [hinnovation, hformula]
  change μ[fun x ↦ L x ^ 2 | ℱ n] x - (μ[L | ℱ n] x) ^ 2 ≤ 1 / 4
  have hrisk := conditionalSquaredRisk_mem_Icc P hf hq n x
  rw [hmean] at hsq ⊢
  nlinarith [sq_nonneg (conditionalSquaredRisk P f q n x - 1 / 2)]

/-- Conservative unit bound, retained as a compatibility corollary of the
sharp `1/4` conditional-second-moment theorem. -/
lemma markovRiskInnovation_condSecondMoment_le_one
    (P : Z → PMF Z) (x0 : Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (markovPathMeasure P x0)[fun x ↦ (markovRiskInnovation P f q n x) ^ 2 |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] ≤ᵐ[markovPathMeasure P x0]
      fun _ ↦ (1 : ℝ) := by
  filter_upwards [markovRiskInnovation_condSecondMoment_le_one_fourth
    P x0 hf hq n] with x hx
  exact hx.trans (by norm_num)

/-- Running empirical one-step squared loss along the observed trajectory. -/
def empiricalPrequentialRisk (f q : Z → ℝ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  AnytimeValid.runningMean (pathSquaredLoss f q) n x

/-- Running average of the transition-row conditional risks encountered along
the trajectory.  This is the pathwise target; no stationary law is assumed. -/
def averageConditionalRisk (P : Z → PMF Z) (f q : Z → ℝ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  AnytimeValid.runningMean (conditionalSquaredRisk P f q) n x

omit [Fintype Z] [MeasurableSingletonClass Z] in
/-- The innovation running mean is exactly observed prequential risk minus the
average conditional transition risk. -/
theorem runningMean_markovRiskInnovation
    (P : Z → PMF Z) (f q : Z → ℝ) (n : ℕ) (x : ℕ → Z) :
    AnytimeValid.runningMean (markovRiskInnovation P f q) n x =
      empiricalPrequentialRisk f q n x - averageConditionalRisk P f q n x := by
  unfold markovRiskInnovation empiricalPrequentialRisk averageConditionalRisk
  unfold AnytimeValid.runningMean AnytimeValid.runningSum
  rw [Finset.sum_sub_distrib]
  ring

private theorem integrable_subGammaExponentialProcess_of_bounded
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : ℕ → Omega → ℝ} {sigma2 b lam : ℝ} (n : ℕ)
    (hb : 0 < b) (hsigma : 0 ≤ sigma2) (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k))
    (hbound : ∀ k, ∀ᵐ omega ∂mu, |X k omega| ≤ b) :
    Integrable (AnytimeValid.subGammaExponentialProcess X sigma2 b lam n) mu := by
  refine Integrable.of_bound ?_ (Real.exp (lam * (n : ℝ) * b)) ?_
  · have hpair : Measurable (fun omega : Omega ↦ (lam, omega)) :=
      measurable_const.prodMk measurable_id
    exact ((AnytimeValid.measurable_subGammaExponentialProcess_prod
      X sigma2 b n hX_meas).comp hpair).aestronglyMeasurable
  · have hall : ∀ᵐ omega ∂mu, ∀ k, |X k omega| ≤ b := ae_all_iff.2 hbound
    filter_upwards [hall] with omega homega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold AnytimeValid.subGammaExponentialProcess; positivity)]
    exact AnytimeValid.subGammaExponentialProcess_le_of_bound
      X sigma2 b lam lam n omega hb hsigma hlam le_rfl hblam
      (fun i _hi ↦ homega i)

/-- Raw two-sided failure set for single-trajectory Markov risk validation,
using the sharp universal `1/4` conditional-variance proxy. -/
def markovPrequentialRiskRawFailure
    (P : Z → PMF Z) (f q : Z → ℝ) (Lam : Finset ℝ) (delta : ℝ) :
    Set (ℕ → Z) :=
  {x | ∃ n : ℕ, 0 < n ∧
    ∃ lam ∈ Lam,
      AnytimeValid.subGammaCgf (1 / 4) 1 lam / lam +
          Real.log ((Lam.card : ℝ) / (delta / 2)) / ((n : ℝ) * lam) ≤
        |empiricalPrequentialRisk f q n x - averageConditionalRisk P f q n x|}

/-- The raw all-time/all-grid failure set has outer mass at most `delta` under
the actual Ionescu--Tulcea Markov path law. -/
theorem markovPrequentialRiskRawFailure_mass_le_delta
    (P : Z → PMF Z) (x0 : Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    {Lam : Finset ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hLam : Lam.Nonempty)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo (0 : ℝ) 3) :
    (markovPathMeasure P x0).real
      (markovPrequentialRiskRawFailure P f q Lam delta) ≤ delta := by
  let mu := markovPathMeasure P x0
  let filtration := Filtration.piLE (X := fun _ : ℕ ↦ Z)
  let X := markovRiskInnovation P f q
  have hcs := AnytimeValid.optimized_lambda_two_sided_confidence_sequence
    (μ := mu) (ℱ := filtration) (X := X)
    (sigma2 := (1 / 4 : ℝ)) (b := (1 : ℝ)) (delta := delta) (Lam := Lam)
    hdelta (by norm_num) (by norm_num) hLam (by simpa using hLam_mem)
    (measurable_markovRiskInnovation P f q)
    (integrable_markovRiskInnovation (P := P) (x0 := x0) hf hq)
    (markovRiskInnovation_incrementAdapted P f q)
    (fun lam hlam n ↦ integrable_subGammaExponentialProcess_of_bounded n
      (by norm_num) (by norm_num) (hLam_mem lam hlam).1.le
      (by simpa using (hLam_mem lam hlam).2)
      (measurable_markovRiskInnovation P f q)
      (fun k ↦ Filter.Eventually.of_forall fun x ↦
        abs_markovRiskInnovation_le_one P hf hq k x))
    (fun lam hlam n ↦ integrable_subGammaExponentialProcess_of_bounded n
      (by norm_num) (by norm_num) (hLam_mem lam hlam).1.le
      (by simpa using (hLam_mem lam hlam).2)
      (fun k ↦ (measurable_markovRiskInnovation P f q k).neg)
      (fun k ↦ Filter.Eventually.of_forall fun x ↦ by
        simpa only [abs_neg] using abs_markovRiskInnovation_le_one P hf hq k x))
    (fun k ↦ Filter.Eventually.of_forall fun x ↦
      abs_markovRiskInnovation_le_one P hf hq k x)
    (markovRiskInnovation_condExp_eq_zero P x0 hf hq)
    (markovRiskInnovation_condSecondMoment_le_one_fourth P x0 hf hq)
  simpa [mu, filtration, X, markovPrequentialRiskRawFailure,
    runningMean_markovRiskInnovation] using hcs

/-- A measurable hull of the raw Markov-risk failure set.  It contains every
failure path and has the same outer mass, yielding an ordinary measurable
exceptional event. -/
def markovPrequentialRiskExceptionalEvent
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    (Lam : Finset ℝ) (delta : ℝ) : Set (ℕ → Z) :=
  toMeasurable (markovPathMeasure P x0)
    (markovPrequentialRiskRawFailure P f q Lam delta)

theorem markovPrequentialRiskExceptionalEvent_measurable
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    (Lam : Finset ℝ) (delta : ℝ) :
    MeasurableSet (markovPrequentialRiskExceptionalEvent P x0 f q Lam delta) :=
  measurableSet_toMeasurable _ _

theorem markovPrequentialRiskRawFailure_subset_exceptionalEvent
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    (Lam : Finset ℝ) (delta : ℝ) :
    markovPrequentialRiskRawFailure P f q Lam delta ⊆
      markovPrequentialRiskExceptionalEvent P x0 f q Lam delta :=
  subset_toMeasurable _ _

/-- Publication-facing ordinary-probability statement: one measurable event of
probability at most `delta` contains every time/grid failure. -/
theorem markovPrequentialRiskExceptionalEvent_mass_le_delta
    (P : Z → PMF Z) (x0 : Z) {f q : Z → ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1)
    {Lam : Finset ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hLam : Lam.Nonempty)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo (0 : ℝ) 3) :
    (markovPathMeasure P x0).real
      (markovPrequentialRiskExceptionalEvent P x0 f q Lam delta) ≤ delta := by
  rw [markovPrequentialRiskExceptionalEvent, Measure.real, measure_toMeasurable]
  exact markovPrequentialRiskRawFailure_mass_le_delta
    P x0 hf hq hdelta hLam hLam_mem

/-- Outside the measurable exceptional event, the observed and conditional
trajectory-average risks differ by less than every declared grid boundary. -/
theorem abs_prequentialRisk_sub_averageConditionalRisk_lt_of_not_mem
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    {Lam : Finset ℝ} {delta lam : ℝ} {n : ℕ} {x : ℕ → Z}
    (hx : x ∉ markovPrequentialRiskExceptionalEvent P x0 f q Lam delta)
    (hn : 0 < n) (hlam : lam ∈ Lam) :
    |empiricalPrequentialRisk f q n x - averageConditionalRisk P f q n x| <
      AnytimeValid.subGammaCgf (1 / 4) 1 lam / lam +
        Real.log ((Lam.card : ℝ) / (delta / 2)) / ((n : ℝ) * lam) := by
  have hxraw : x ∉ markovPrequentialRiskRawFailure P f q Lam delta := fun hraw ↦
    hx (markovPrequentialRiskRawFailure_subset_exceptionalEvent
      P x0 f q Lam delta hraw)
  exact lt_of_not_ge fun hfail ↦ hxraw ⟨n, hn, lam, hlam, hfail⟩

/-- Human-readable upper certificate for the latent average conditional risk.
The right-hand side uses only the observed prequential loss and declared
confidence parameters. -/
theorem averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem
    (P : Z → PMF Z) (x0 : Z) (f q : Z → ℝ)
    {Lam : Finset ℝ} {delta lam : ℝ} {n : ℕ} {x : ℕ → Z}
    (hx : x ∉ markovPrequentialRiskExceptionalEvent P x0 f q Lam delta)
    (hn : 0 < n) (hlam : lam ∈ Lam) :
    averageConditionalRisk P f q n x < empiricalPrequentialRisk f q n x +
      (AnytimeValid.subGammaCgf (1 / 4) 1 lam / lam +
        Real.log ((Lam.card : ℝ) / (delta / 2)) / ((n : ℝ) * lam)) := by
  have habs := abs_prequentialRisk_sub_averageConditionalRisk_lt_of_not_mem
    P x0 f q hx hn hlam
  have hdiff : averageConditionalRisk P f q n x - empiricalPrequentialRisk f q n x ≤
      |empiricalPrequentialRisk f q n x - averageConditionalRisk P f q n x| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

end

end FormalSLT.StochasticDynamics
