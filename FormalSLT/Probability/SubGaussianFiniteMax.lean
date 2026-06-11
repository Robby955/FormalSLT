import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fintype.EquivFin
import FormalSLT.Covering.FiniteSubGaussianChaining

/-!
# Finite sub-Gaussian maximal inequality

Finite maximal inequalities for weighted finite probability spaces. The module
exposes the probability-facing wrapper around the finite MGF-to-supremum
primitive used by the Dudley chaining layer.
-/

namespace FormalSLT.Probability.SubGaussianFiniteMax

open Finset
open FormalSLT.Covering.FiniteSubGaussianChaining
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*}

/-- Finite Jensen for the exponential function in weighted-expectation form. -/
theorem exp_finiteExpectation_le_of_jensen [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω : Ω, 0 ≤ w ω)
    (hsum : ∑ ω : Ω, w ω = 1)
    (Z : Ω → ℝ) (lam : ℝ) :
    Real.exp (lam * finiteExpectation w Z) ≤
      finiteExpectation w (fun ω => Real.exp (lam * Z ω)) := by
  have hjensen :
      Real.exp (∑ ω ∈ (Finset.univ : Finset Ω), w ω • (lam * Z ω)) ≤
        ∑ ω ∈ (Finset.univ : Finset Ω), w ω • Real.exp (lam * Z ω) :=
    convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset Ω))
      (w := w)
      (p := fun ω => lam * Z ω)
      (fun ω _hω => hw ω)
      (by simpa using hsum)
      (fun _ω _hω => Set.mem_univ _)
  have hcenter :
      (∑ ω ∈ (Finset.univ : Finset Ω), w ω • (lam * Z ω)) =
        lam * finiteExpectation w Z := by
    unfold finiteExpectation
    calc
      (∑ ω ∈ (Finset.univ : Finset Ω), w ω • (lam * Z ω))
          = ∑ ω : Ω, lam * (w ω * Z ω) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            simp [smul_eq_mul]
            ring
      _ = lam * ∑ ω : Ω, w ω * Z ω := by
            rw [Finset.mul_sum]
  rw [hcenter] at hjensen
  simpa [finiteExpectation, smul_eq_mul] using hjensen

private lemma finiteExpectation_neg [Fintype Ω]
    (w : Ω → ℝ) (Z : Ω → ℝ) :
    finiteExpectation w (fun ω => -Z ω) = -finiteExpectation w Z := by
  unfold finiteExpectation
  calc
    (∑ ω : Ω, w ω * (fun ω => -Z ω) ω)
        = ∑ ω : Ω, -(w ω * Z ω) := by
          apply Finset.sum_congr rfl
          intro ω _hω
          ring
    _ = -∑ ω : Ω, w ω * Z ω := by
          rw [Finset.sum_neg_distrib]

private lemma finiteSup_eq_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Y : ι → ℝ) (i₀ : ι) :
    finiteSup Y = Y i₀ := by
  unfold finiteSup
  apply Finset.sup'_eq_of_forall
  intro i _hi
  congr
  exact Subsingleton.elim i i₀

private lemma sqrt_two_sq_mul_eq (sigma L : ℝ) (hsigma : 0 ≤ sigma) :
    Real.sqrt (2 * sigma ^ 2 * L) =
      sigma * Real.sqrt (2 * L) := by
  calc
    Real.sqrt (2 * sigma ^ 2 * L)
        = Real.sqrt (sigma ^ 2 * (2 * L)) := by ring_nf
    _ = Real.sqrt (sigma ^ 2) * Real.sqrt (2 * L) := by
          rw [Real.sqrt_mul (sq_nonneg sigma)]
    _ = sigma * Real.sqrt (2 * L) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsigma]

/--
Finite maximal inequality for a one-sided sub-Gaussian family over a finite
weighted probability space.
-/
theorem subgaussian_finite_max
    [Fintype Ω] [Fintype ι] [Nonempty ι]
    (w : Ω → ℝ) (hw : ∀ ω : Ω, 0 ≤ w ω)
    (hsum : ∑ ω : Ω, w ω = 1)
    (Y : ι → Ω → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (hmean : ∀ i : ι, finiteExpectation w (fun ω => Y i ω) = 0)
    (hmgf : ∀ i : ι, ∀ lam : ℝ, 0 ≤ lam →
      finiteExpectation w (fun ω => Real.exp (lam * Y i ω)) ≤
        Real.exp (lam ^ 2 * sigma ^ 2 / 2)) :
    finiteExpectation w (fun ω => finiteSup (fun i : ι => Y i ω)) ≤
      sigma * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ)) := by
  classical
  by_cases hcard : 1 < Fintype.card ι
  · let L : ℝ := Real.log (Fintype.card ι : ℝ)
    let variance : ℝ := sigma ^ 2
    let lam : ℝ := Real.sqrt (2 * L / variance)
    have hL : 0 < L := by
      have hcard_real : (1 : ℝ) < (Fintype.card ι : ℝ) := by
        exact_mod_cast hcard
      simpa [L] using Real.log_pos hcard_real
    have hvariance : 0 < variance := by
      dsimp [variance]
      exact sq_pos_of_pos hsigma
    have hlam : 0 < lam := by
      dsimp [lam]
      exact Real.sqrt_pos_of_pos (by positivity)
    have hbase :
        finiteExpectation w (fun ω => finiteSup (fun i : ι => Y i ω)) ≤
          (Real.log (Fintype.card ι : ℝ) + lam ^ 2 * sigma ^ 2 / 2) / lam :=
      finite_expectedSup_le_of_mgf_log
        w hw hsum (fun ω i => Y i ω)
        lam (lam ^ 2 * sigma ^ 2 / 2) hlam
        (fun i => hmgf i lam hlam.le)
    calc
      finiteExpectation w (fun ω => finiteSup (fun i : ι => Y i ω))
          ≤ (Real.log (Fintype.card ι : ℝ) + lam ^ 2 * sigma ^ 2 / 2) / lam := hbase
      _ = Real.sqrt (2 * sigma ^ 2 * Real.log (Fintype.card ι : ℝ)) := by
            have hopt := sqrt_entropy_optimizer_identity
              (L := L) (q := variance) hL hvariance
            dsimp [L, variance, lam] at hopt ⊢
            simpa [mul_assoc, mul_left_comm, mul_comm] using hopt
      _ = sigma * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ)) :=
            sqrt_two_sq_mul_eq sigma (Real.log (Fintype.card ι : ℝ)) hsigma.le
  · have hle_one : Fintype.card ι ≤ 1 := Nat.le_of_not_gt hcard
    haveI : Subsingleton ι :=
      Fintype.card_le_one_iff_subsingleton.mp hle_one
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    have hsup : ∀ ω : Ω, finiteSup (fun i : ι => Y i ω) = Y i₀ ω := by
      intro ω
      exact finiteSup_eq_of_subsingleton (fun i : ι => Y i ω) i₀
    calc
      finiteExpectation w (fun ω => finiteSup (fun i : ι => Y i ω))
          = finiteExpectation w (fun ω => Y i₀ ω) := by
            unfold finiteExpectation
            apply Finset.sum_congr rfl
            intro ω _hω
            change w ω * finiteSup (fun i : ι => Y i ω) = w ω * Y i₀ ω
            rw [hsup ω]
      _ = 0 := hmean i₀
      _ ≤ sigma * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ)) :=
            mul_nonneg hsigma.le (Real.sqrt_nonneg _)

private lemma finiteSup_abs_le_signedSup
    [Fintype ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) (ω : Ω) :
    finiteSup (fun i : ι => |Y i ω|) ≤
      finiteSup (fun bi : Bool × ι =>
        match bi.1 with
        | true => Y bi.2 ω
        | false => -Y bi.2 ω) := by
  unfold finiteSup
  apply Finset.sup'_le
  intro i _hi
  by_cases hnonneg : 0 ≤ Y i ω
  · rw [abs_of_nonneg hnonneg]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (Bool × ι)))
      (f := fun bi : Bool × ι =>
        match bi.1 with
        | true => Y bi.2 ω
        | false => -Y bi.2 ω)
      (Finset.mem_univ (true, i))
  · rw [abs_of_neg (lt_of_not_ge hnonneg)]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (Bool × ι)))
      (f := fun bi : Bool × ι =>
        match bi.1 with
        | true => Y bi.2 ω
        | false => -Y bi.2 ω)
      (Finset.mem_univ (false, i))

/--
Two-sided finite maximal inequality, proved by applying
`subgaussian_finite_max` to the signed family indexed by `Bool × ι`.
-/
theorem subgaussian_finite_max_abs
    [Fintype Ω] [Fintype ι] [Nonempty ι]
    (w : Ω → ℝ) (hw : ∀ ω : Ω, 0 ≤ w ω)
    (hsum : ∑ ω : Ω, w ω = 1)
    (Y : ι → Ω → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (hmean : ∀ i : ι, finiteExpectation w (fun ω => Y i ω) = 0)
    (hmgf_pos : ∀ i : ι, ∀ lam : ℝ, 0 ≤ lam →
      finiteExpectation w (fun ω => Real.exp (lam * Y i ω)) ≤
        Real.exp (lam ^ 2 * sigma ^ 2 / 2))
    (hmgf_neg : ∀ i : ι, ∀ lam : ℝ, 0 ≤ lam →
      finiteExpectation w (fun ω => Real.exp (lam * (-Y i ω))) ≤
        Real.exp (lam ^ 2 * sigma ^ 2 / 2)) :
    finiteExpectation w (fun ω => finiteSup (fun i : ι => |Y i ω|)) ≤
      sigma * Real.sqrt (2 * Real.log (2 * (Fintype.card ι : ℝ))) := by
  classical
  let signedY : Bool × ι → Ω → ℝ := fun bi ω =>
    match bi.1 with
    | true => Y bi.2 ω
    | false => -Y bi.2 ω
  have hmean_signed :
      ∀ bi : Bool × ι, finiteExpectation w (fun ω => signedY bi ω) = 0 := by
    rintro ⟨b, i⟩
    cases b <;> simp [signedY, finiteExpectation_neg, hmean i]
  have hmgf_signed :
      ∀ bi : Bool × ι, ∀ lam : ℝ, 0 ≤ lam →
        finiteExpectation w (fun ω => Real.exp (lam * signedY bi ω)) ≤
          Real.exp (lam ^ 2 * sigma ^ 2 / 2) := by
    rintro ⟨b, i⟩ lam hlam
    cases b
    · simpa [signedY] using hmgf_neg i lam hlam
    · simpa [signedY] using hmgf_pos i lam hlam
  have hmono :
      finiteExpectation w (fun ω => finiteSup (fun i : ι => |Y i ω|)) ≤
        finiteExpectation w (fun ω => finiteSup (fun bi : Bool × ι => signedY bi ω)) :=
    finiteExpectation_mono hw (fun ω => by
      simpa [signedY] using finiteSup_abs_le_signedSup (Y := Y) ω)
  have hmax :
      finiteExpectation w (fun ω => finiteSup (fun bi : Bool × ι => signedY bi ω)) ≤
        sigma * Real.sqrt (2 * Real.log (Fintype.card (Bool × ι) : ℝ)) :=
    subgaussian_finite_max
      w hw hsum signedY sigma hsigma hmean_signed hmgf_signed
  have hcard :
      (Fintype.card (Bool × ι) : ℝ) = 2 * (Fintype.card ι : ℝ) := by
    simp [Fintype.card_prod]
  calc
    finiteExpectation w (fun ω => finiteSup (fun i : ι => |Y i ω|))
        ≤ finiteExpectation w (fun ω => finiteSup (fun bi : Bool × ι => signedY bi ω)) := hmono
    _ ≤ sigma * Real.sqrt (2 * Real.log (Fintype.card (Bool × ι) : ℝ)) := hmax
    _ = sigma * Real.sqrt (2 * Real.log (2 * (Fintype.card ι : ℝ))) := by
          rw [hcard]

end

end FormalSLT.Probability.SubGaussianFiniteMax
