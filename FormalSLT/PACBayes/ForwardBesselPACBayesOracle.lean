/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.ForwardBesselPACBayesCountable

/-!
# Observable finite-prefix oracle for forward PAC-Bayes boundaries

The countable geometric tilt catalog is fixed before the data.  On its one
master event, this module minimizes the exact observable hybrid-Bessel
boundary over the growing prefix available at a reporting time.  The selected
atom may depend on the path, time, and posterior because every catalog atom is
already controlled on the same event.

This is an exact finite-prefix selector, not a global minimum over `Nat`, an
all-real optimizer, or a selected e-process.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable

namespace FormalSLT.PACBayes.ForwardBesselPACBayesOracle

noncomputable section

variable {ι Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

omit [DecidableEq ι] [Nonempty ι] in
private theorem countableForwardBesselPACBayesFinitePrefix_exists_argmin
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) :
    ∃ j ∈ Finset.range (maxIndex + 1),
      ∀ j' ∈ Finset.range (maxIndex + 1),
        countableForwardBesselPACBayesBoundary
            prior weight lam X posterior delta j n ω ≤
          countableForwardBesselPACBayesBoundary
            prior weight lam X posterior delta j' n ω := by
  exact (Finset.range (maxIndex + 1)).exists_min_image
    (fun j ↦ countableForwardBesselPACBayesBoundary
      prior weight lam X posterior delta j n ω)
    (by simp)

/-- An exact minimizer of the observable boundary over atoms
`0, ..., maxIndex`. -/
def countableForwardBesselPACBayesFinitePrefixArgmin
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) : ℕ :=
  Classical.choose
    (countableForwardBesselPACBayesFinitePrefix_exists_argmin
      prior weight lam X posterior delta maxIndex n ω)

omit [DecidableEq ι] [Nonempty ι] in
/-- The finite-prefix minimizer is one of the declared candidate atoms. -/
theorem countableForwardBesselPACBayesFinitePrefixArgmin_mem
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) :
    countableForwardBesselPACBayesFinitePrefixArgmin
        prior weight lam X posterior delta maxIndex n ω ∈
      Finset.range (maxIndex + 1) := by
  exact
    (Classical.choose_spec
      (countableForwardBesselPACBayesFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n ω)).1

omit [DecidableEq ι] [Nonempty ι] in
/-- The selected boundary is no larger than any candidate boundary in the
declared prefix. -/
theorem countableForwardBesselPACBayesFinitePrefixArgmin_le
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) {j : ℕ}
    (hj : j ∈ Finset.range (maxIndex + 1)) :
    countableForwardBesselPACBayesBoundary
        prior weight lam X posterior delta
          (countableForwardBesselPACBayesFinitePrefixArgmin
            prior weight lam X posterior delta maxIndex n ω)
          n ω ≤
      countableForwardBesselPACBayesBoundary
        prior weight lam X posterior delta j n ω := by
  exact
    (Classical.choose_spec
      (countableForwardBesselPACBayesFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n ω)).2 j hj

/-- The growing prefix extends two atoms past the standard all-time index.
Those finer tilts are needed for a variance-adaptive square-root oracle while
the standard atom remains available as a worst-case-rate benchmark. -/
def growingPrefixForwardBesselPACBayesMaxIndex (n : ℕ) : ℕ :=
  geometricForwardTiltIndex n + 2

/-- Reciprocal scale of geometric atom `j`. -/
def geometricForwardEffectiveScale (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (j + 1)

theorem geometricForwardEffectiveScale_pos (j : ℕ) :
    0 < geometricForwardEffectiveScale j := by
  unfold geometricForwardEffectiveScale
  positivity

theorem geometricForwardEffectiveScale_zero :
    geometricForwardEffectiveScale 0 = 2 := by
  norm_num [geometricForwardEffectiveScale]

theorem geometricForwardEffectiveScale_succ (j : ℕ) :
    geometricForwardEffectiveScale (j + 1) =
      2 * geometricForwardEffectiveScale j := by
  unfold geometricForwardEffectiveScale
  rw [show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
  ring

theorem geometricForwardEffectiveScale_sq (j : ℕ) :
    geometricForwardEffectiveScale j ^ 2 =
      (geometricForwardTiltTime j : ℝ) := by
  unfold geometricForwardEffectiveScale geometricForwardTiltTime
  push_cast
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

/-- A real number below the largest scale of a finite dyadic prefix has a
factor-two upper dyadic bracket inside that prefix. -/
private theorem exists_dyadic_effectiveScale_mem_range
    {u : ℝ} {maxIndex : ℕ} (hu : 1 ≤ u)
    (hupper : u < geometricForwardEffectiveScale maxIndex) :
    ∃ j ∈ Finset.range (maxIndex + 1),
      (2 : ℝ) ^ j ≤ u ∧
        u < geometricForwardEffectiveScale j ∧
        geometricForwardEffectiveScale j ≤ 2 * u := by
  obtain ⟨j, hjlower, hjupper⟩ :=
    exists_nat_pow_near hu (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_, hjlower, ?_, ?_⟩
  · simp only [Finset.mem_range]
    by_contra hj
    have hindex : maxIndex + 1 ≤ j := by omega
    have hpow : geometricForwardEffectiveScale maxIndex ≤
        (2 : ℝ) ^ j := by
      unfold geometricForwardEffectiveScale
      exact pow_le_pow_right₀ (by norm_num) hindex
    linarith
  · simpa [geometricForwardEffectiveScale] using hjupper
  · unfold geometricForwardEffectiveScale
    rw [pow_succ]
    nlinarith

/-- KL plus the confidence and polynomial atom-selection charge at geometric
atom `j`. -/
def geometricForwardBesselPACBayesComplexity
    (prior posterior : ι → ℝ) (delta : ℝ) (j : ℕ) : ℝ :=
  klDiv posterior prior +
    Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)

omit [DecidableEq ι] [Nonempty ι] in
/-- Polynomial atom-selection complexity is monotone along the geometric
catalog. -/
theorem geometricForwardBesselPACBayesComplexity_mono
    (prior posterior : ι → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    {j maxIndex : ℕ} (hj : j ≤ maxIndex) :
    geometricForwardBesselPACBayesComplexity
        prior posterior delta j ≤
      geometricForwardBesselPACBayesComplexity
        prior posterior delta maxIndex := by
  have hjR : (j : ℝ) ≤ (maxIndex : ℝ) := by exact_mod_cast hj
  have hprod :
      ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤
        ((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2) := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hratioPos : 0 <
      (((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta := by
    positivity
  have hratio :
      (((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta ≤
        (((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2)) / delta :=
    div_le_div_of_nonneg_right hprod hdelta.le
  unfold geometricForwardBesselPACBayesComplexity
  linarith [Real.log_le_log hratioPos hratio]

/-- Complexity at the largest atom in the reporting-time prefix. -/
def growingPrefixForwardBesselPACBayesComplexity
    (prior posterior : ι → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  geometricForwardBesselPACBayesComplexity prior posterior delta
    (growingPrefixForwardBesselPACBayesMaxIndex n)

omit [DecidableEq ι] [Nonempty ι] in
/-- Full prior support and `delta ≤ 1` put the largest-prefix complexity
above `1/2`, uniformly over the reporting time. -/
theorem growingPrefixForwardBesselPACBayesComplexity_half_le
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (n : ℕ) :
    1 / 2 ≤ growingPrefixForwardBesselPACBayesComplexity
      prior posterior delta n := by
  let maxIndex := growingPrefixForwardBesselPACBayesMaxIndex n
  have hratio : (2 : ℝ) ≤
      (((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2)) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hindex0 : (0 : ℝ) ≤ maxIndex := Nat.cast_nonneg maxIndex
    nlinarith
  have hloghalf : (1 : ℝ) / 2 ≤
      Real.log
        ((((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2)) / delta) := by
    calc
      (1 : ℝ) / 2 = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
      _ ≤ Real.log
          ((((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2)) / delta) :=
        Real.log_le_log (by norm_num) hratio
  unfold growingPrefixForwardBesselPACBayesComplexity
    geometricForwardBesselPACBayesComplexity
  change 1 / 2 ≤ klDiv posterior prior +
    Real.log
      ((((maxIndex : ℝ) + 1) * ((maxIndex : ℝ) + 2)) / delta)
  nlinarith [klDiv_nonneg hposterior hprior]

omit [DecidableEq ι] [Nonempty ι] in
/-- Exact iterated-logarithm form of the growing-prefix complexity.  The
polynomial atom cost is evaluated at `Nat.log 4 n`, so its logarithm is the
explicit `log log n` overhead. -/
theorem growingPrefixForwardBesselPACBayesComplexity_eq_logLog
    (prior posterior : ι → ℝ) (delta : ℝ) {n : ℕ} (hn : 4 ≤ n) :
    growingPrefixForwardBesselPACBayesComplexity
        prior posterior delta n =
      klDiv posterior prior +
        Real.log
          ((((Nat.log 4 n : ℝ) + 2) *
            ((Nat.log 4 n : ℝ) + 3)) / delta) := by
  have hbase := geometricForwardTiltIndex_add_one hn
  have hfirstNat :
      geometricForwardTiltIndex n + 2 + 1 = Nat.log 4 n + 2 := by
    omega
  have hsecondNat :
      geometricForwardTiltIndex n + 2 + 2 = Nat.log 4 n + 3 := by
    omega
  have hfirst :
      ((geometricForwardTiltIndex n + 2 : ℕ) : ℝ) + 1 =
        (Nat.log 4 n : ℝ) + 2 := by
    exact_mod_cast hfirstNat
  have hsecond :
      ((geometricForwardTiltIndex n + 2 : ℕ) : ℝ) + 2 =
        (Nat.log 4 n : ℝ) + 3 := by
    exact_mod_cast hsecondNat
  unfold growingPrefixForwardBesselPACBayesComplexity
    geometricForwardBesselPACBayesComplexity
    growingPrefixForwardBesselPACBayesMaxIndex
  rw [hfirst, hsecond]

/-- Explicit observable square-root envelope.  Its complexity is evaluated at
the largest atom of the growing prefix, while its variance term is the
path-observed posterior hybrid-Bessel penalty. -/
def growingPrefixForwardBesselPACBayesLILEnvelope
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let A := growingPrefixForwardBesselPACBayesComplexity
    prior posterior delta n
  let Q := forwardPosteriorHybridBesselPenalty posterior X n ω
  (2 * A + (5 / 2 : ℝ) * A * Real.sqrt (2 * Q / A)) / (n : ℝ)

/-- A finite dyadic prefix competes, up to an explicit factor, with the
continuous optimizer of `A * s + 2 * Q / s`. -/
theorem exists_dyadic_quadratic_oracle
    {A Q : ℝ} {maxIndex : ℕ} (hA : 1 / 2 ≤ A) (hQ : 0 ≤ Q)
    (hcover :
      2 * Q < A * geometricForwardEffectiveScale maxIndex ^ 2) :
    ∃ j ∈ Finset.range (maxIndex + 1),
      A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j ≤
        2 * A + (5 / 2 : ℝ) * A * Real.sqrt (2 * Q / A) := by
  let u := Real.sqrt (2 * Q / A)
  have hApos : 0 < A := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hA
  have harg : 0 ≤ 2 * Q / A := by positivity
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Real.sqrt_nonneg _
  have husq : u ^ 2 = 2 * Q / A := by
    dsimp [u]
    exact Real.sq_sqrt harg
  have hAusq : A * u ^ 2 = 2 * Q := by
    rw [husq]
    field_simp [hApos.ne']
  by_cases hsmall : Q ≤ 2 * A
  · refine ⟨0, by simp, ?_⟩
    have hu_le_two : u ≤ 2 := by
      apply (sq_le_sq₀ hu0 (by norm_num)).mp
      rw [husq]
      apply (div_le_iff₀ hApos).2
      nlinarith
    have hu_mul : u ^ 2 ≤ 2 * u := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu_le_two)]
    have hQ_le : Q ≤ A * u := by
      have hmul := mul_le_mul_of_nonneg_left hu_mul hApos.le
      nlinarith
    rw [geometricForwardEffectiveScale_zero]
    norm_num
    nlinarith [mul_nonneg hApos.le hu0]
  · have hlarge : 2 * A < Q := lt_of_not_ge hsmall
    have hfrac : 4 < 2 * Q / A := by
      apply (lt_div_iff₀ hApos).2
      nlinarith
    have hu_two : 2 < u := by
      have hsquare : 4 < u ^ 2 := by simpa [husq] using hfrac
      nlinarith
    have hfracUpper :
        2 * Q / A < geometricForwardEffectiveScale maxIndex ^ 2 := by
      apply (div_lt_iff₀ hApos).2
      simpa [mul_comm] using hcover
    have huUpper : u < geometricForwardEffectiveScale maxIndex := by
      dsimp [u]
      exact (Real.sqrt_lt harg
        (geometricForwardEffectiveScale_pos maxIndex).le).2 hfracUpper
    obtain ⟨j, hj, _hjlower, hujs, hjs⟩ :=
      exists_dyadic_effectiveScale_mem_range
        (u := u) (maxIndex := maxIndex) (by linarith) huUpper
    refine ⟨j, hj, ?_⟩
    let s := geometricForwardEffectiveScale j
    have hspos : 0 < s := geometricForwardEffectiveScale_pos j
    have hust : u < s := by simpa [s] using hujs
    have hst : s ≤ 2 * u := by simpa [s] using hjs
    have hfactor : 0 ≤ (s - u / 2) * (2 * u - s) := by
      apply mul_nonneg
      · nlinarith
      · linarith
    have hquadratic :
        s ^ 2 + u ^ 2 ≤ (5 / 2 : ℝ) * s * u := by
      nlinarith
    have hrate :
        A * s + 2 * Q / s ≤ (5 / 2 : ℝ) * A * u := by
      rw [← hAusq]
      calc
        A * s + A * u ^ 2 / s = A * (s ^ 2 + u ^ 2) / s := by
          field_simp [hspos.ne']
        _ ≤ A * ((5 / 2 : ℝ) * s * u) / s :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hquadratic hApos.le) hspos.le
        _ = (5 / 2 : ℝ) * A * u := by
          field_simp [hspos.ne']
    dsimp [s] at hrate ⊢
    nlinarith

/-- The reporting-time prefix reaches a squared effective scale strictly
beyond `4 * n`.  This is the deterministic coverage fact that lets the
observable oracle balance every hybrid penalty `Q ≤ n`. -/
theorem growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul
    {n : ℕ} (hn : 4 ≤ n) :
    4 * (n : ℝ) <
      geometricForwardEffectiveScale
        (growingPrefixForwardBesselPACBayesMaxIndex n) ^ 2 := by
  let r := Nat.log 4 n
  have hupper : n < 4 ^ (r + 1) := by
    dsimp [r]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hindex :
      growingPrefixForwardBesselPACBayesMaxIndex n + 1 = r + 2 := by
    unfold growingPrefixForwardBesselPACBayesMaxIndex
    have hbase : geometricForwardTiltIndex n + 1 = r := by
      simpa [r] using geometricForwardTiltIndex_add_one hn
    omega
  have hNat :
      4 * n <
        geometricForwardTiltTime
          (growingPrefixForwardBesselPACBayesMaxIndex n) := by
    unfold geometricForwardTiltTime
    rw [hindex]
    calc
      4 * n < 4 * 4 ^ (r + 1) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hupper
      _ = 4 ^ (r + 2) := by
        rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
        omega
  rw [geometricForwardEffectiveScale_sq]
  exact_mod_cast hNat

/-- The observable selector over the growing geometric prefix at time `n`. -/
def growingPrefixForwardBesselPACBayesArgmin
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  countableForwardBesselPACBayesFinitePrefixArgmin
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The growing-prefix selector belongs to its declared candidate prefix. -/
theorem growingPrefixForwardBesselPACBayesArgmin_mem
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) :
    growingPrefixForwardBesselPACBayesArgmin
        prior X posterior delta n ω ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
  exact countableForwardBesselPACBayesFinitePrefixArgmin_mem
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The observable selector improves on every geometric atom in the growing
prefix. -/
theorem growingPrefixForwardBesselPACBayesArgmin_le
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) {j : ℕ}
    (hj : j ∈ Finset.range
      (growingPrefixForwardBesselPACBayesMaxIndex n + 1)) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta j n ω := by
  exact countableForwardBesselPACBayesFinitePrefixArgmin_le
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω hj

omit [DecidableEq ι] [Nonempty ι] in
/-- Observable quadratic envelope for one geometric catalog atom.  Unlike the
worst-case all-time rate, this bound retains the path-observed posterior hybrid
Bessel penalty instead of replacing it by the sample size. -/
theorem countableForwardBesselPACBayesBoundary_le_observableRate
    {prior posterior : ι → ℝ} (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (j n : ℕ) (hn : 2 ≤ n) (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt
          X posterior delta j n ω ≤
      ((klDiv posterior prior +
            Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) *
          (2 : ℝ) ^ (j + 1) +
        2 * forwardPosteriorHybridBesselPenalty posterior X n ω /
          (2 : ℝ) ^ (j + 1)) /
        (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hpenalty :=
    forwardPosteriorHybridBesselPenalty_mem_Icc hposterior hn hX ω
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (geometricForwardTilt_le_half j)
  have hvar :
      forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          forwardPosteriorHybridBesselPenalty posterior X n ω ≤
        2 * (geometricForwardTilt j) ^ 2 *
          forwardPosteriorHybridBesselPenalty posterior X n ω := by
    exact mul_le_mul_of_nonneg_right hpsi hpenalty.1
  have hdenpos : 0 < (n : ℝ) * geometricForwardTilt j :=
    mul_pos (Nat.cast_pos.mpr hnpos) (geometricForwardTilt_pos j)
  unfold countableForwardBesselPACBayesBoundary
  rw [polynomialForwardTiltWeight_log_cost hdelta.ne' j]
  calc
    (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) +
        forwardEmpiricalBernsteinPsi (geometricForwardTilt j) *
          forwardPosteriorHybridBesselPenalty posterior X n ω) /
        ((n : ℝ) * geometricForwardTilt j) ≤
      (klDiv posterior prior +
          Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta) +
        2 * (geometricForwardTilt j) ^ 2 *
          forwardPosteriorHybridBesselPenalty posterior X n ω) /
        ((n : ℝ) * geometricForwardTilt j) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      linarith
    _ = ((klDiv posterior prior +
            Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) *
          (2 : ℝ) ^ (j + 1) +
        2 * forwardPosteriorHybridBesselPenalty posterior X n ω /
          (2 : ℝ) ^ (j + 1)) /
        (n : ℝ) := by
      unfold geometricForwardTilt
      field_simp [show (n : ℝ) ≠ 0 by positivity]

omit [DecidableEq ι] [Nonempty ι] in
/-- The post-data growing-prefix selector automatically competes with the
observable quadratic rate of every declared atom in its current prefix. -/
theorem growingPrefixForwardBesselPACBayesBoundary_le_observableRate
    {prior posterior : ι → ℝ} (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {j n : ℕ} (hn : 2 ≤ n) (ω : Ω)
    (hj : j ∈ Finset.range
      (growingPrefixForwardBesselPACBayesMaxIndex n + 1)) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      ((klDiv posterior prior +
            Real.log ((((j : ℝ) + 1) * ((j : ℝ) + 2)) / delta)) *
          (2 : ℝ) ^ (j + 1) +
        2 * forwardPosteriorHybridBesselPenalty posterior X n ω /
          (2 : ℝ) ^ (j + 1)) /
        (n : ℝ) := by
  exact (growingPrefixForwardBesselPACBayesArgmin_le
    prior X posterior delta n ω hj).trans
      (countableForwardBesselPACBayesBoundary_le_observableRate
        hposterior hdelta hX j n hn ω)

omit [DecidableEq ι] [Nonempty ι] in
/-- Explicit observable variance-adaptive envelope for the exact post-data
selector.  The complexity is the KL plus the polynomial atom cost at the
largest atom of the reporting-time prefix. -/
theorem growingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      growingPrefixForwardBesselPACBayesLILEnvelope
        prior X posterior delta n ω := by
  let maxIndex := growingPrefixForwardBesselPACBayesMaxIndex n
  let A := growingPrefixForwardBesselPACBayesComplexity
    prior posterior delta n
  let Q := forwardPosteriorHybridBesselPenalty posterior X n ω
  have hnpos : 0 < n := by omega
  have hAhalf : (1 : ℝ) / 2 ≤ A := by
    simpa [A] using growingPrefixForwardBesselPACBayesComplexity_half_le
      hprior hposterior hdelta hdelta1 n
  have hQmem : Q ∈ Set.Icc 0 (n : ℝ) := by
    simpa [Q] using forwardPosteriorHybridBesselPenalty_mem_Icc
      hposterior (by omega) hX ω
  have hscale :
      4 * (n : ℝ) < geometricForwardEffectiveScale maxIndex ^ 2 := by
    simpa [maxIndex] using
      growingPrefixForwardBesselPACBayes_scale_sq_gt_four_mul hn
  have hcover :
      2 * Q < A * geometricForwardEffectiveScale maxIndex ^ 2 := by
    calc
      2 * Q ≤ 2 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hQmem.2 (by norm_num)
      _ < (1 / 2 : ℝ) *
          geometricForwardEffectiveScale maxIndex ^ 2 := by
        nlinarith
      _ ≤ A * geometricForwardEffectiveScale maxIndex ^ 2 :=
        mul_le_mul_of_nonneg_right hAhalf
          (sq_nonneg (geometricForwardEffectiveScale maxIndex))
  obtain ⟨j, hj, horacle⟩ :=
    exists_dyadic_quadratic_oracle hAhalf hQmem.1 hcover
  have hjle : j ≤ maxIndex := by
    have hjlt : j < maxIndex + 1 := by
      simpa only [Finset.mem_range] using hj
    omega
  have hAjA :
      geometricForwardBesselPACBayesComplexity prior posterior delta j ≤ A := by
    simpa [A, maxIndex, growingPrefixForwardBesselPACBayesComplexity] using
      (geometricForwardBesselPACBayesComplexity_mono
        prior posterior hdelta hjle)
  have hselected :
      countableForwardBesselPACBayesBoundary
          prior polynomialForwardTiltWeight geometricForwardTilt X posterior
            delta (growingPrefixForwardBesselPACBayesArgmin
              prior X posterior delta n ω) n ω ≤
        (geometricForwardBesselPACBayesComplexity
              prior posterior delta j * geometricForwardEffectiveScale j +
            2 * Q / geometricForwardEffectiveScale j) /
          (n : ℝ) := by
    simpa [geometricForwardBesselPACBayesComplexity,
      geometricForwardEffectiveScale, Q] using
        (growingPrefixForwardBesselPACBayesBoundary_le_observableRate
          hposterior hdelta hX (n := n) (j := j) (by omega) ω (by
            simpa [maxIndex] using hj))
  have hscale0 : 0 ≤ geometricForwardEffectiveScale j :=
    (geometricForwardEffectiveScale_pos j).le
  have hcomplexityRate :
      (geometricForwardBesselPACBayesComplexity
            prior posterior delta j * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : ℝ) ≤
      (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hmul := mul_le_mul_of_nonneg_right hAjA hscale0
    linarith
  have horacleRate :
      (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : ℝ) ≤
      (2 * A + (5 / 2 : ℝ) * A * Real.sqrt (2 * Q / A)) /
        (n : ℝ) :=
    div_le_div_of_nonneg_right horacle (Nat.cast_nonneg n)
  calc
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      (geometricForwardBesselPACBayesComplexity
            prior posterior delta j * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : ℝ) := hselected
    _ ≤ (A * geometricForwardEffectiveScale j +
          2 * Q / geometricForwardEffectiveScale j) /
        (n : ℝ) := hcomplexityRate
    _ ≤ (2 * A + (5 / 2 : ℝ) * A * Real.sqrt (2 * Q / A)) /
        (n : ℝ) := horacleRate
    _ = growingPrefixForwardBesselPACBayesLILEnvelope
        prior X posterior delta n ω := by
      simp [growingPrefixForwardBesselPACBayesLILEnvelope, A, Q]

omit [DecidableEq ι] [Nonempty ι] in
/-- The observable selector is bounded by the existing all-time deterministic
rate because the standard geometric atom remains in its candidate prefix. -/
theorem growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      allTimeGeometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta n := by
  have hcandidate : geometricForwardTiltIndex n ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
    simp [growingPrefixForwardBesselPACBayesMaxIndex]
  exact (growingPrefixForwardBesselPACBayesArgmin_le
    prior X posterior delta n ω hcandidate).trans
      (countableForwardBesselPACBayesBoundary_selected_le_allTimeRate
        hprior hposterior hdelta hdelta1 hX hn ω)

omit [DecidableEq ι] [Nonempty ι] in
/-- The exact observable oracle width vanishes for arbitrary time-varying
finite posteriors. -/
theorem growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (ω : Ω) :
    Filter.Tendsto
      (fun n ↦ countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X
          (posterior n) delta
          (growingPrefixForwardBesselPACBayesArgmin
            prior X (posterior n) delta n ω) n ω)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact countableForwardBesselPACBayesBoundary_nonneg
      hprior (hposterior n) hdelta hdelta1 hX
      (growingPrefixForwardBesselPACBayesArgmin
        prior X (posterior n) delta n ω) n hn ω
  · exact Filter.Eventually.of_forall fun n ↦
      growingPrefixForwardBesselPACBayesArgmin_le
        prior X (posterior n) delta n ω
          (j := geometricForwardTiltIndex n) (by
            simp only [Finset.mem_range]
            unfold growingPrefixForwardBesselPACBayesMaxIndex
            omega)
  · exact countableForwardBesselPACBayesBoundary_selected_tendsto_zero
      hprior posterior hposterior hdelta hdelta1 hX ω

/-- One countable-master event supports post-data minimization of the exact
observable boundary over every growing geometric prefix.  On the same event,
the selected boundary has the explicit observable LIL-order envelope and the
existing worst-case all-time rate, and it vanishes along all integer times. -/
theorem exists_growingPrefixForwardBesselPACBayesOracle_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ}
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n)) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        (∀ ω ∈ goodEvent, ∀ n : ℕ, 4 ≤ n →
          let selected := growingPrefixForwardBesselPACBayesArgmin
            prior X (posterior ω n) delta n ω
          selected ∈ Finset.range
              (growingPrefixForwardBesselPACBayesMaxIndex n + 1) ∧
            posteriorAverage (posterior ω n) mean <
              posteriorAverage (posterior ω n)
                  (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                countableForwardBesselPACBayesBoundary
                  prior polynomialForwardTiltWeight geometricForwardTilt X
                    (posterior ω n) delta selected n ω ∧
            countableForwardBesselPACBayesBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt X
                  (posterior ω n) delta selected n ω ≤
              growingPrefixForwardBesselPACBayesLILEnvelope
                prior X (posterior ω n) delta n ω ∧
            countableForwardBesselPACBayesBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt X
                  (posterior ω n) delta selected n ω ≤
              allTimeGeometricPolynomialForwardRate
                (fun _ ↦ klDiv (posterior ω n) prior) delta n) ∧
        (∀ ω ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ countableForwardBesselPACBayesBoundary
              prior polynomialForwardTiltWeight geometricForwardTilt X
                (posterior ω n) delta
                (growingPrefixForwardBesselPACBayesArgmin
                  prior X (posterior ω n) delta n ω) n ω)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_geometricForwardBesselPACBayes_event
      hprior hdelta hX_adapted hX_unit hmean
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro ω hω n hn
    let selected := growingPrefixForwardBesselPACBayesArgmin
      prior X (posterior ω n) delta n ω
    have hselected_mem : selected ∈
        Finset.range
          (growingPrefixForwardBesselPACBayesMaxIndex n + 1) :=
      growingPrefixForwardBesselPACBayesArgmin_mem
        prior X (posterior ω n) delta n ω
    have hrisk := hgood ω hω selected (posterior ω n)
      (hposterior ω n) n (by omega)
    have hLIL := growingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
      hprior (hposterior ω n) hdelta hdelta1 hX_unit hn ω
    have hrate := growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
      hprior (hposterior ω n) hdelta hdelta1 hX_unit hn ω
    exact ⟨hselected_mem, hrisk, hLIL, hrate⟩
  · intro ω _hω
    exact growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
      hprior (posterior ω) (hposterior ω) hdelta hdelta1 hX_unit ω

end

end FormalSLT.PACBayes.ForwardBesselPACBayesOracle
