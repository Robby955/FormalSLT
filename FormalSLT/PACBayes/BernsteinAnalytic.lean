import FormalSLT.Probability.BernsteinMGF

/-!
# Analytic finite-iid Bernstein concentration

This module exposes the finite iid Bernstein concentration theorem in the
PAC-Bayes namespace. It reuses the already-proved variance-aware finite product
MGF theorem `FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail` and
specializes it to a scalar observable `X : Z → ℝ` with `0 ≤ X ≤ b`.

For finite iid samples `S : Fin n → Z`, the public theorem controls
`P(empiricalMean X S - mean X ≥ ε)` by

`exp (-(n : ℝ) * ε^2 / (2 * (σ² + b * ε / 3)))`.

This is a finite-distribution theorem. It does not assert an arbitrary
standard-Borel or real-valued product-measure concentration theorem.

Reference: S. N. Bernstein (1924), "On a modification of Chebyshev's
inequality and of the error formula of Laplace"; the original citation has no
DOI/arXiv in the checked bibliography, so `scripts/citation_audit.py` reports
`WARN_UNVERIFIABLE` rather than a machine-checked PASS.
-/

namespace FormalSLT.PACBayes.BernsteinAnalytic

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF

noncomputable section

variable {Z : Type*}

/-- Finite mean of a scalar observable under a finite PMF. -/
def finiteMean [Fintype Z] (p : Z → ℝ) (X : Z → ℝ) : ℝ :=
  ∑ z : Z, p z * X z

/-- Finite empirical mean of a scalar observable on an iid sample. -/
def finiteEmpiricalMean {n : ℕ} (X : Z → ℝ) (S : Fin n → Z) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, X (S k)

/-- Finite centered second moment around the finite mean. -/
def finiteCenteredSecondMoment [Fintype Z] (p : Z → ℝ) (X : Z → ℝ) : ℝ :=
  ∑ z : Z, p z * (X z - finiteMean p X) ^ (2 : Nat)

/-- Finite iid upper-tail mass for the empirical mean. -/
def bernsteinIIDUpperTailMass [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (X : Z → ℝ) (eps : ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.filter
      (fun S : Fin n → Z => finiteMean p X + eps ≤ finiteEmpiricalMean X S),
    finiteProductSampleWeight p S

private lemma finitePopulationRisk_neg_eq [Fintype Z]
    (p : Z → ℝ) (X : Z → ℝ) :
    finitePopulationRisk p (fun _ : Unit => fun z => -X z) () = -finiteMean p X := by
  unfold finitePopulationRisk finiteMean
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

private lemma finiteEmpiricalRisk_neg_eq {n : ℕ}
    (X : Z → ℝ) (S : Fin n → Z) :
    finiteEmpiricalRisk (fun _ : Unit => fun z => -X z) () S =
      -finiteEmpiricalMean X S := by
  unfold finiteEmpiricalRisk finiteEmpiricalMean
  rw [Finset.sum_neg_distrib]
  ring

/-- Finite iid Bernstein upper-tail inequality for bounded scalar observables.

If `X ∈ [0,b]`, the centered second moment equals `σ²`, and `σ² > 0`, then the
upper tail of the empirical mean satisfies the standard Bernstein bound with
explicit variance dependence. -/
theorem bernstein_iid_bounded_upper_tail [Fintype Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p) (X : Z → ℝ)
    {b sigma2 eps : ℝ}
    (hb : 0 < b) (hsigma2 : 0 < sigma2) (heps : 0 ≤ eps)
    (hX_nonneg : ∀ z, 0 ≤ X z)
    (hX_bound : ∀ z, X z ≤ b)
    (hvariance : finiteCenteredSecondMoment p X = sigma2) :
    bernsteinIIDUpperTailMass (n := n) p X eps ≤
      Real.exp (-(n : ℝ) * eps ^ (2 : Nat) / (2 * (sigma2 + b * eps / 3))) := by
  classical
  let loss : Unit → Z → ℝ := fun _ z => -X z
  have hmean_nonneg : 0 ≤ finiteMean p X := by
    unfold finiteMean
    exact Finset.sum_nonneg
      (fun z _ => mul_nonneg (hp.nonneg z) (hX_nonneg z))
  have hbound_loss :
      ∀ z, finitePopulationRisk p loss () - loss () z ≤ b := by
    intro z
    have hpop := finitePopulationRisk_neg_eq p X
    have hx := hX_bound z
    dsimp [loss]
    rw [hpop]
    linarith
  have hvar_loss :
      ∑ z : Z, p z * (finitePopulationRisk p loss () - loss () z) ^ (2 : Nat) ≤
        sigma2 := by
    have hpop := finitePopulationRisk_neg_eq p X
    calc
      (∑ z : Z, p z * (finitePopulationRisk p loss () - loss () z) ^ (2 : Nat))
          =
        ∑ z : Z, p z * (X z - finiteMean p X) ^ (2 : Nat) := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          dsimp [loss]
          rw [hpop]
          ring
      _ = sigma2 := hvariance
      _ ≤ sigma2 := le_rfl
  have htail :=
    FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail
      (ι := Unit) (Z := Z) (n := n) hn p hp loss () hb hsigma2 heps
      hbound_loss hvar_loss
  simpa [bernsteinIIDUpperTailMass, finitePopulationRisk_neg_eq,
    finiteEmpiricalRisk_neg_eq, loss] using htail

end

end FormalSLT.PACBayes.BernsteinAnalytic
