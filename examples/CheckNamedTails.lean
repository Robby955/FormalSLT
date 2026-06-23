import FormalSLT.Concentration.NamedTails
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Named two-sided tail corollaries: concrete Rademacher witness

This file does two things:

1. Type-checks and axiom-audits the named two-sided tail-probability corollaries
   (`chernoff_tail`, `subGaussianMGF_tail_twoSided`, `hoeffding_mean_tail_twoSided`,
   `bernstein_tail`, `bennett_tail`). Each `#print axioms` should report only
   `[propext, Classical.choice, Quot.sound]`.

2. Builds a GENUINE concrete non-vacuity witness: the symmetric Rademacher
   distribution `X = ±1` with probability `1/2` each, on `Fin 2`. This is a real
   bounded, centered, unit-variance distribution. We instantiate the finite
   two-sided `bernstein_tail` on it at threshold `ε = 1`, discharge every
   hypothesis on explicit numeric data, and obtain the explicit tail bound

       P(|X| ≥ 1) ≤ 2 · exp(-3/8).

   The witness is NON-VACUOUS: both atoms satisfy `|X z| = 1 ≥ 1`, so the left-hand
   mass is exactly `1` (the whole probability), not `0`; the inequality
   `1 ≤ 2 · exp(-3/8)` is a real constraint on a genuinely non-empty event, and we
   verify numerically that `2 · exp(-3/8) ≈ 1.374`, so the bound is satisfied with
   room. This is not a `#check`-only certificate: the theorem `rademacher_tail`
   below applies the audited corollary to concrete data.
-/

open scoped BigOperators
open FormalSLT.Concentration.NamedTails

/-! ## Axiom audit of the named corollaries -/

#check @chernoff_tail
#print axioms chernoff_tail

#check @subGaussianMGF_tail_twoSided
#print axioms subGaussianMGF_tail_twoSided

#check @hoeffding_mean_tail_twoSided
#print axioms hoeffding_mean_tail_twoSided

#check @bernstein_tail
#print axioms bernstein_tail

#check @bennett_tail
#print axioms bennett_tail

/-! ## Concrete Rademacher witness -/

namespace FormalSLT.CheckNamedTails

noncomputable section

/-- The two atoms of the Rademacher distribution. -/
abbrev R := Fin 2

/-- Uniform probability mass: each atom has mass `1/2`. -/
def pRad : R → ℝ := fun _ => 1 / 2

/-- The Rademacher observable: `X 0 = 1`, `X 1 = -1`. -/
def XRad : R → ℝ := fun z => if z = 0 then 1 else -1

/-- `pRad` is nonnegative. -/
theorem pRad_nonneg : ∀ z, 0 ≤ pRad z := by
  intro z; norm_num [pRad]

/-- `pRad` sums to one. -/
theorem pRad_sum : ∑ z, pRad z = 1 := by
  rw [Fin.sum_univ_two]; norm_num [pRad]

/-- The Rademacher observable is centered: `∑ p z · X z = 0`. -/
theorem XRad_centered : ∑ z, pRad z * XRad z = 0 := by
  rw [Fin.sum_univ_two]; norm_num [pRad, XRad]

/-- The observable is two-sidedly bounded by `b = 1`: `|X z| ≤ 1`. -/
theorem XRad_bound : ∀ z, |XRad z| ≤ 1 := by
  intro z; fin_cases z <;> norm_num [XRad]

/-- Unit variance proxy: `∑ p z · X z² = 1 ≤ 1`. -/
theorem XRad_var : ∑ z, pRad z * XRad z ^ 2 ≤ 1 := by
  rw [Fin.sum_univ_two]; norm_num [pRad, XRad]

/-- **The witness.** The audited two-sided Bernstein tail corollary applied to the
Rademacher distribution at threshold `ε = 1`, with `b = 1`, `v = 1`. Every
hypothesis is discharged on explicit data; the conclusion is the concrete tail
bound `P(|X| ≥ 1) ≤ 2 · exp(-3/8)`. -/
theorem rademacher_tail :
    ∑ z ∈ Finset.univ.filter (fun z => (1 : ℝ) ≤ |XRad z|), pRad z
      ≤ 2 * Real.exp (-(1 ^ 2) / (2 * (1 + 1 * 1 / 3))) :=
  bernstein_tail pRad XRad (b := 1) (v := 1) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num)
    pRad_nonneg pRad_sum XRad_centered XRad_bound XRad_var

/-- **Non-vacuity, part 1.** Both atoms lie in the deviation event `{1 ≤ |X|}`, so
the left-hand mass of `rademacher_tail` is exactly the full probability `1`, not
the trivial `0`. The bound therefore constrains a genuinely non-empty event. -/
theorem rademacher_mass_eq_one :
    ∑ z ∈ Finset.univ.filter (fun z => (1 : ℝ) ≤ |XRad z|), pRad z = 1 := by
  have hfilter : (Finset.univ.filter (fun z => (1 : ℝ) ≤ |XRad z|)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro z _
    fin_cases z <;> norm_num [XRad]
  rw [hfilter, pRad_sum]

/-- **Non-vacuity, part 2.** The right-hand bound is numerically `> 1` (≈ 1.374),
so the witnessed inequality `1 ≤ 2 · exp(-3/8)` holds with a genuine margin — the
bound is neither failing nor vacuously trivial. Proved via the convexity bound
`1 + x ≤ exp x` at `x = -3/8`, giving `exp(-3/8) ≥ 5/8` and `2 · (5/8) > 1`. -/
theorem rademacher_bound_gt_one :
    (1 : ℝ) < 2 * Real.exp (-(1 ^ 2) / (2 * (1 + 1 * 1 / 3))) := by
  have hsimp : -(1 ^ 2 : ℝ) / (2 * (1 + 1 * 1 / 3)) = -(3 / 8) := by norm_num
  rw [hsimp]
  have hlb : (5 : ℝ) / 8 ≤ Real.exp (-(3 / 8)) := by
    have := Real.add_one_le_exp (-(3 / 8 : ℝ))
    linarith
  calc (1 : ℝ) < 2 * (5 / 8) := by norm_num
    _ ≤ 2 * Real.exp (-(3 / 8)) := by linarith [hlb]

/-- The witnessed bound is genuinely satisfied: the actual mass `1` is below the
bound, which is the whole point — a real, non-vacuous instance of the corollary. -/
theorem rademacher_witness_sound :
    (∑ z ∈ Finset.univ.filter (fun z => (1 : ℝ) ≤ |XRad z|), pRad z)
      ≤ 2 * Real.exp (-(1 ^ 2) / (2 * (1 + 1 * 1 / 3))) :=
  rademacher_tail

/-! ## Informative witness: a tails instance with bound `< 1`

The Rademacher witness above fires at the maximal threshold `ε = b`, where the
right-hand bound is `≈ 1.374 > 1` and so certifies firing and non-emptiness but
not informativeness. This second witness exercises the analytic content: a
three-atom observable `X ∈ {4, 0, -4}` with a small deviation mass, at threshold
`ε = 3 < b = 4`, where the Bernstein bound evaluates to `2·exp(-9/10) ≈ 0.813 < 1`
— an informative tail bound on a genuinely non-empty deviation event. -/

/-- Three-atom support. -/
abbrev T := Fin 3

/-- Mass: `1/32` on each extreme atom, `30/32` on the centre. -/
def pInf : T → ℝ := fun z => if z = 1 then 30 / 32 else 1 / 32

/-- Observable: `X 0 = 4`, `X 1 = 0`, `X 2 = -4`. Bounded by `b = 4`. -/
def XInf : T → ℝ := fun z => if z = 0 then 4 else if z = 2 then -4 else 0

/-- Pointwise evaluation of the mass on each atom. -/
theorem pInf_vals : pInf 0 = 1 / 32 ∧ pInf 1 = 30 / 32 ∧ pInf 2 = 1 / 32 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pInf]
/-- Pointwise evaluation of the observable on each atom. -/
theorem XInf_vals : XInf 0 = 4 ∧ XInf 1 = 0 ∧ XInf 2 = -4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [XInf]

theorem pInf_nonneg : ∀ z, 0 ≤ pInf z := by
  intro z; fin_cases z <;> norm_num [pInf]
theorem pInf_sum : ∑ z, pInf z = 1 := by
  rw [Fin.sum_univ_three, pInf_vals.1, pInf_vals.2.1, pInf_vals.2.2]; norm_num
theorem XInf_centered : ∑ z, pInf z * XInf z = 0 := by
  rw [Fin.sum_univ_three, pInf_vals.1, pInf_vals.2.1, pInf_vals.2.2,
      XInf_vals.1, XInf_vals.2.1, XInf_vals.2.2]; norm_num
theorem XInf_bound : ∀ z, |XInf z| ≤ 4 := by
  intro z
  fin_cases z
  · rw [show (⟨0, by norm_num⟩ : T) = 0 from rfl, XInf_vals.1]; norm_num
  · rw [show (⟨1, by norm_num⟩ : T) = 1 from rfl, XInf_vals.2.1]; norm_num
  · rw [show (⟨2, by norm_num⟩ : T) = 2 from rfl, XInf_vals.2.2]; norm_num
/-- Variance proxy `v = 1`: `∑ p z · X z² = 2·(1/32)·16 = 1`. -/
theorem XInf_var : ∑ z, pInf z * XInf z ^ 2 ≤ 1 := by
  rw [Fin.sum_univ_three, pInf_vals.1, pInf_vals.2.1, pInf_vals.2.2,
      XInf_vals.1, XInf_vals.2.1, XInf_vals.2.2]; norm_num

/-- **The informative witness.** The two-sided Bernstein corollary at `b = 4`,
`v = 1`, `ε = 3`, with bound `2·exp(-3²/(2(1 + 4·3/3)))`. Every hypothesis is
discharged on explicit data. -/
theorem informative_tail :
    ∑ z ∈ Finset.univ.filter (fun z => (3 : ℝ) ≤ |XInf z|), pInf z
      ≤ 2 * Real.exp (-(3 ^ 2) / (2 * (1 + 4 * 3 / 3))) :=
  bernstein_tail pInf XInf (b := 4) (v := 1) (eps := 3)
    (by norm_num) (by norm_num) (by norm_num)
    pInf_nonneg pInf_sum XInf_centered XInf_bound XInf_var

/-- **Non-vacuity.** The deviation event `{3 ≤ |X|}` is the two extreme atoms,
mass exactly `1/16 > 0`, so the bound constrains a genuinely non-empty event. -/
theorem informative_mass_pos :
    ∑ z ∈ Finset.univ.filter (fun z => (3 : ℝ) ≤ |XInf z|), pInf z = 1 / 16 := by
  have hfilter :
      (Finset.univ.filter (fun z => (3 : ℝ) ≤ |XInf z|)) = {0, 2} := by
    ext z; fin_cases z <;> simp [XInf] <;> norm_num
  rw [hfilter, Finset.sum_pair (by decide), pInf_vals.1, pInf_vals.2.2]; norm_num

/-- **Informativeness.** The right-hand bound is `< 1` (`≈ 0.813`), so unlike the
maximal-threshold Rademacher witness this instance is a genuinely informative tail
bound, not merely a firing one. Proved via `exp` monotonicity and `exp(-0.9) < 1/2`
from `exp(0.9) > 2` (since `exp(0.6931...) = 2` and `0.9 > log 2`). -/
theorem informative_bound_lt_one :
    2 * Real.exp (-(3 ^ 2) / (2 * (1 + 4 * 3 / 3))) < 1 := by
  have hsimp : -(3 ^ 2 : ℝ) / (2 * (1 + 4 * 3 / 3)) = -(9 / 10) := by norm_num
  rw [hsimp]
  have hlog2 : Real.log 2 < 9 / 10 := by
    have := Real.log_two_lt_d9
    linarith
  have hexp : Real.exp (-(9 / 10)) < 1 / 2 := by
    rw [show -(9 / 10 : ℝ) = -(9 / 10) from rfl]
    have h : Real.exp (-(9 / 10)) = (Real.exp (9 / 10))⁻¹ := by
      rw [Real.exp_neg]
    rw [h]
    have hgt : (2 : ℝ) < Real.exp (9 / 10) := by
      have : Real.exp (Real.log 2) < Real.exp (9 / 10) :=
        Real.exp_lt_exp.mpr hlog2
      rwa [Real.exp_log (by norm_num)] at this
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)] at *
    · nlinarith [hgt]
  linarith [hexp]

end

end FormalSLT.CheckNamedTails

-- AXIOM AUDIT of the concrete witness (sorry-free? no custom axioms?)
namespace FormalSLT.CheckNamedTails
#print axioms rademacher_tail
#print axioms rademacher_mass_eq_one
#print axioms rademacher_bound_gt_one
#print axioms rademacher_witness_sound
#print axioms informative_tail
#print axioms informative_mass_pos
#print axioms informative_bound_lt_one
end FormalSLT.CheckNamedTails
