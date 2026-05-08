import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import FormalSLT.Rademacher.FiniteSample

/-!
# Rademacher probability bridge

Connects the finite combinatorial sign-vector machinery of
`FormalSLT.Rademacher.FiniteSample` to the standard
probability/expectation interpretation: a uniform distribution on
`Fin n → Bool` and the empirical Rademacher complexity expressed as the
expectation of the (1/n)-scaled supremum.

What this module provides (all closed, no `sorry`, no `admit`):

* `uniformSignPMF n : PMF (Fin n → Bool)` — the uniform probability mass
  function on the `2^n` sign vectors. Each sign vector has mass
  `(2^n : ℝ≥0∞)⁻¹`.
* `uniformSignPMF_apply` — the explicit pointwise mass.
* `uniform_average_eq_finset_sum` — for any real-valued function on sign
  vectors, the discrete uniform average `(2^n : ℝ)⁻¹ · ∑_σ f σ` equals
  the Bochner integral of `f` against the measure derived from
  `uniformSignPMF`.
* `signedEmpiricalMean ℓ z σ i` — the `(1/n)`-scaled signed empirical
  mean for a single hypothesis index `i`, sample `z`, sign vector `σ`.
* `supSignedEmpiricalMean ℓ z σ` — the supremum over the finite
  hypothesis class of the signed empirical mean. The value being
  averaged in the empirical Rademacher complexity.
* `empiricalRademacherComplexity_eq_integral` — restates the
  combinatorial definition `empiricalRademacherComplexity` from
  `FiniteSampleRademacher` as the expectation of `supSignedEmpiricalMean`
  under `uniformSignPMF`.

Out of scope for this module (deferred to later PRs):

- The expected symmetrization theorem
  `E_S sup_h (risk h - empiricalRisk_S h) ≤ 2 · E_S empiricalRademacherComplexity_S(H)`.
  This is `feat/lean-finite-sample-rademacher-symmetrization`.
- High-probability uniform-deviation bound via McDiarmid.
  This is `feat/lean-rademacher-generalization-bound`.
- Any contraction lemma, scaling lemma, or hypothesis-class composition
  result for Rademacher complexity.
- Connection to the existing `FormalSLT.Rademacher`
  measure-theoretic scaffolding (separate cleanup task).
-/

namespace FormalSLT.Rademacher.ProbabilityBridge

open Finset Function MeasureTheory PMF
open FormalSLT.Rademacher.FiniteSample (signOfBool empiricalRademacherComplexity)
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### Uniform PMF on sign vectors -/

/-- Uniform probability mass function on the `2^n` sign vectors. Each
sign vector receives mass `(2^n : ℝ≥0∞)⁻¹`. -/
noncomputable def uniformSignPMF (n : ℕ) : PMF (Fin n → Bool) :=
  PMF.ofFintype
    (fun _ : Fin n → Bool => ((2 : ℝ≥0∞) ^ n)⁻¹)
    (by
      have h_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have h_two_pow_ne_top : ((2 : ℝ≥0∞) ^ n) ≠ ⊤ :=
        ENNReal.pow_ne_top (by simp)
      have h_two_pow_ne_zero : ((2 : ℝ≥0∞) ^ n) ≠ 0 := by
        exact pow_ne_zero _ (by simp)
      calc ∑ _σ : Fin n → Bool, ((2 : ℝ≥0∞) ^ n)⁻¹
          = (Finset.univ : Finset (Fin n → Bool)).card • ((2 : ℝ≥0∞) ^ n)⁻¹ := by
            rw [Finset.sum_const]
        _ = (2 ^ n : ℕ) • ((2 : ℝ≥0∞) ^ n)⁻¹ := by rw [h_card]
        _ = ((2 ^ n : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
            rw [nsmul_eq_mul]
        _ = ((2 : ℝ≥0∞) ^ n) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
            congr 1
            push_cast
            rfl
        _ = 1 := ENNReal.mul_inv_cancel h_two_pow_ne_zero h_two_pow_ne_top)

@[simp] lemma uniformSignPMF_apply (σ : Fin n → Bool) :
    uniformSignPMF n σ = ((2 : ℝ≥0∞) ^ n)⁻¹ := rfl

/-- The mass of every sign vector in `uniformSignPMF` converts cleanly to
the real-valued reciprocal `(2^n : ℝ)⁻¹`. -/
lemma uniformSignPMF_apply_toReal (σ : Fin n → Bool) :
    (uniformSignPMF n σ).toReal = ((2 : ℝ) ^ n)⁻¹ := by
  rw [uniformSignPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

/-! ### Discrete uniform average ↔ Bochner integral -/

/-- The discrete uniform average over the sign vectors equals the
expectation of `f` under `uniformSignPMF`. The averaging factor
`(2^n : ℝ)⁻¹` is the real-valued mass of each sign vector. -/
theorem uniform_average_eq_finset_sum (f : (Fin n → Bool) → ℝ) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, f σ
      = ∫ σ, f σ ∂(uniformSignPMF n).toMeasure := by
  rw [PMF.integral_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [uniformSignPMF_apply_toReal, smul_eq_mul]

/-! ### Signed empirical mean and its supremum -/

variable {ι Z : Type*}

/-- The `(1/n)`-scaled signed empirical mean for a single hypothesis
index. This is the inner quantity whose supremum over `i` is averaged
in the empirical Rademacher complexity. -/
noncomputable def signedEmpiricalMean
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) (σ : Fin n → Bool) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)

/-- The supremum over a finite hypothesis class of the signed empirical
mean. This is the integrand for the empirical Rademacher complexity. -/
noncomputable def supSignedEmpiricalMean
    [Fintype ι] [Nonempty ι]
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) (σ : Fin n → Bool) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => signedEmpiricalMean ℓ z σ i)

/-! ### The bridge theorem -/

/-- **Empirical Rademacher complexity as an expectation.**

The combinatorial definition of `empiricalRademacherComplexity` from
`FormalSLT.Rademacher.FiniteSample` equals the Bochner
expectation of the supremum-of-signed-empirical-means functional under
the uniform distribution on sign vectors. This is the recognizable
"expectation form" used throughout statistical learning theory. -/
theorem empiricalRademacherComplexity_eq_integral
    [Fintype ι] [Nonempty ι]
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    empiricalRademacherComplexity ℓ z
      = ∫ σ, supSignedEmpiricalMean ℓ z σ ∂(uniformSignPMF n).toMeasure := by
  rw [← uniform_average_eq_finset_sum]
  rfl

end FormalSLT.Rademacher.ProbabilityBridge
