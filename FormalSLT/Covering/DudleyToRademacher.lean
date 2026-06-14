import FormalSLT.Covering.DudleySumToIntegral
import FormalSLT.Covering.ContinuousDudleyCovering
import FormalSLT.Rademacher.Massart

/-!
# Finite Dudley entropy integral to empirical Rademacher complexity

This module bridges the Dudley entropy-integral lane to the empirical
Rademacher complexity. It packages the canonical sign-vector Rademacher process
as a `FiniteSubGaussianProcess` over the discrete sign-vector space
`Fin n → Bool`, identifies its centered weighted-supremum expectation with the
empirical Rademacher complexity, and forwards the supplied net/covering data to
the Dudley entropy integral on both endpoints:
* the finite endpoint
  `dudley_entropy_integral_of_antitone_coveringNumber`
  (`dudley_rademacher_complexity_bound`), and
* the continuous endpoint
  `ContinuousDudleyCovering.continuous_dudley_entropy_integral_of_coveringNumber`
  (`continuous_dudley_rademacher_complexity_bound`).

The sub-Gaussian increment bound is discharged from the discrete sign-vector
factorization (`Massart.cosh_le_exp_sq_half`), not assumed. The process metric
is the empirical L2 distance over the sample, and the variance proxy is `1/n`,
so the increment MGF matches the structure field exactly.

## Continuous endpoint

`continuous_dudley_rademacher_complexity_bound` instantiates the continuous
Dudley entropy integral on the canonical Rademacher process. The index class
`ι` carries a pseudometric certified to be the empirical L2 distance
(`hmetric`, exposed in closed form by `canonicalRademacherProcess_dist`), the
variance-proxy rewrite `1/n` turns the `4 · √(2 · varianceProxy)` constant into
`4 · √(2/n)`, and the integral runs from `0` to `radiusScale/2` over the genuine
metric-entropy integrand `√(log N(F, ε))`. The separability/terminal boundary
certificate and the dyadic cover-count domination are the same caller interface
the continuous theorem consumes (realizable from finite-cover/pathwise-modulus
data via the `TotalBoundedDudley` boundary-choice adapters); they are not the
conclusion, which is the proven chaining inequality.
-/

namespace FormalSLT.Covering.DudleyToRademacher

open Finset
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.DudleySumToIntegral
open FormalSLT.Rademacher.FiniteSample
open FormalSLT.Rademacher.Massart

noncomputable section

universe u

variable {n : ℕ} {ι : Type u} {Z : Type*} [Fintype ι] [Nonempty ι]

/-- The centered increment of the canonical sign-vector empirical mean. For a
sample `z` and loss `ℓ`, the difference of two coordinates `s, t` is the
sign-weighted empirical mean of the per-sample loss gap. -/
private def lossGap (ℓ : ι → Z → ℝ) (z : Fin n → Z) (s t : ι) (k : Fin n) : ℝ :=
  ℓ t (z k) - ℓ s (z k)

/-- Empirical L2 distance between two hypotheses on the sample. -/
private def empiricalDist (ℓ : ι → Z → ℝ) (z : Fin n → Z) (s t : ι) : ℝ :=
  Real.sqrt ((∑ k : Fin n, lossGap ℓ z s t k ^ 2) / (n : ℝ))

omit [Fintype ι] [Nonempty ι] in
private theorem empiricalDist_nonneg (ℓ : ι → Z → ℝ) (z : Fin n → Z) (s t : ι) :
    0 ≤ empiricalDist ℓ z s t := by
  unfold empiricalDist
  exact Real.sqrt_nonneg _

omit [Fintype ι] [Nonempty ι] in
private theorem empiricalDist_sq (ℓ : ι → Z → ℝ) (z : Fin n → Z) (s t : ι)
    (hn : 0 < n) :
    empiricalDist ℓ z s t ^ 2 = (∑ k : Fin n, lossGap ℓ z s t k ^ 2) / (n : ℝ) := by
  unfold empiricalDist
  rw [Real.sq_sqrt]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · exact_mod_cast hn.le

/-- The sign-vector average MGF of a centered empirical-mean increment is
bounded by the discrete sub-Gaussian factor with the empirical squared sum.
Mirrors the coordinate factorization of `Massart.sign_avg_exp_le`, but keeps the
exact `∑ k, g_k ^ 2` term so the bound matches the empirical L2 metric. -/
private theorem signedIncrement_mgf_le
    (g : Fin n → ℝ) (lam : ℝ) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        Real.exp (lam *
          ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * g k))
      ≤ Real.exp (lam ^ 2 * (∑ k : Fin n, g k ^ 2) / (2 * (n : ℝ) ^ 2)) := by
  have h_exp_sum : ∀ σ : Fin n → Bool,
      Real.exp (lam * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * g k))
        = ∏ k : Fin n, Real.exp (lam * (n : ℝ)⁻¹ * signOfBool (σ k) * g k) := by
    intro σ
    have hrw : lam * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * g k)
          = ∑ k : Fin n, lam * (n : ℝ)⁻¹ * signOfBool (σ k) * g k := by
      have h1 : lam * ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * g k)
            = (lam * (n : ℝ)⁻¹) * ∑ k : Fin n, signOfBool (σ k) * g k := by ring
      rw [h1, Finset.mul_sum Finset.univ _ (lam * (n : ℝ)⁻¹)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hrw, Real.exp_sum]
  simp_rw [h_exp_sum]
  rw [show ∑ σ : Fin n → Bool, ∏ k : Fin n,
        Real.exp (lam * (n : ℝ)⁻¹ * signOfBool (σ k) * g k)
      = ∏ k : Fin n, ∑ b : Bool,
        Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k) from by
    rw [← Fintype.prod_sum (fun k (b : Bool) =>
        Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k))]]
  have h_coord_bound : ∀ k : Fin n,
      ∑ b : Bool, Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k)
        ≤ 2 * Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) := by
    intro k
    have hcosh := cosh_le_exp_sq_half (lam * (n : ℝ)⁻¹) (g k)
    have hsum : ∑ b : Bool, Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k)
        = Real.exp (lam * (n : ℝ)⁻¹ * g k)
          + Real.exp (-(lam * (n : ℝ)⁻¹ * g k)) := by
      simp only [Fintype.sum_bool, signOfBool_true, signOfBool_false]
      ring_nf
    rw [hsum]
    have hrw2 : (lam * (↑n)⁻¹) ^ 2 * g k ^ 2 / 2
        = lam ^ 2 * (↑n)⁻¹ ^ 2 * g k ^ 2 / 2 := by ring
    linarith [hcosh, hrw2 ▸ hcosh]
  have h_prod_bound :
      ∏ k : Fin n, ∑ b : Bool, Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k)
        ≤ ∏ k : Fin n, (2 * Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)) :=
    Finset.prod_le_prod
      (fun k _ => Finset.sum_nonneg (fun b _ => le_of_lt (Real.exp_pos _)))
      (fun k _ => h_coord_bound k)
  have h_factor_two :
      ∏ k : Fin n, (2 * Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2))
        = (2 : ℝ) ^ n * ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) := by
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_const]
  have h_cancel : ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n *
      ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2))
    = ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
  have h_prod_exp :
      ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)
        = Real.exp (∑ k : Fin n, lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) :=
    (Real.exp_sum Finset.univ _).symm
  have h_sum_eq :
      (∑ k : Fin n, lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)
        = lam ^ 2 * (∑ k : Fin n, g k ^ 2) / (2 * (n : ℝ) ^ 2) := by
    have hstep :
        (∑ k : Fin n, lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)
          = (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 / 2) * ∑ k : Fin n, g k ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hstep, inv_pow]
    ring
  calc ((2 : ℝ) ^ n)⁻¹ * ∏ k : Fin n, ∑ b : Bool,
        Real.exp (lam * (n : ℝ)⁻¹ * signOfBool b * g k)
      ≤ ((2 : ℝ) ^ n)⁻¹ * ∏ k : Fin n,
          (2 * Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)) := by gcongr
    _ = ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n *
          ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2)) := by
        rw [h_factor_two]
    _ = ∏ k : Fin n, Real.exp (lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) := h_cancel
    _ = Real.exp (∑ k : Fin n, lam ^ 2 * (n : ℝ)⁻¹ ^ 2 * g k ^ 2 / 2) := h_prod_exp
    _ = Real.exp (lam ^ 2 * (∑ k : Fin n, g k ^ 2) / (2 * (n : ℝ) ^ 2)) := by
        rw [h_sum_eq]

/-- The canonical sign-vector Rademacher process packaged as a finite
sub-Gaussian process over the discrete sign-vector space `Fin n → Bool`.

`X σ i` is the sign-weighted empirical mean `(1/n) ∑_k σ_k · ℓ_i(z_k)`, the
weight is uniform `(2^n)⁻¹`, the metric is the empirical L2 distance, and the
variance proxy is `1/n`. The increment MGF is discharged from the discrete
sign-vector factorization in `signedIncrement_mgf_le`. -/
def canonicalRademacherProcess (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    FiniteSubGaussianProcess (Fin n → Bool) ι where
  weight := fun _ => ((2 : ℝ) ^ n)⁻¹
  weight_nonneg := by intro σ; positivity
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, card_signVectors, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat,
      mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))]
  X := fun σ i => (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k)
  dist := empiricalDist ℓ z
  dist_nonneg := empiricalDist_nonneg ℓ z
  varianceProxy := (n : ℝ)⁻¹
  varianceProxy_nonneg := by positivity
  mgf_increment := by
    intro s t lam
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, inv_zero, zero_mul]
      simp [finiteExpectation, empiricalDist, lossGap]
    · have hkey := signedIncrement_mgf_le (fun k => lossGap ℓ z s t k) lam
      have hgap : ∀ σ : Fin n → Bool,
          ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ t (z k))
            - ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ s (z k))
          = (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * lossGap ℓ z s t k := by
        intro σ
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [lossGap]
        ring
      have hlhs :
          finiteExpectation (fun _ : Fin n → Bool => ((2 : ℝ) ^ n)⁻¹)
              (fun σ => Real.exp (lam *
                (((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ t (z k))
                  - ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ s (z k)))))
            = ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
                Real.exp (lam *
                  ((n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * lossGap ℓ z s t k)) := by
        unfold finiteExpectation
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        simp only []
        rw [hgap σ]
      rw [hlhs]
      refine hkey.trans ?_
      apply Real.exp_le_exp.mpr
      rw [empiricalDist_sq ℓ z s t hn]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hexp_eq :
          lam ^ 2 * (∑ k : Fin n, lossGap ℓ z s t k ^ 2) / (2 * (n : ℝ) ^ 2)
            = lam ^ 2 * (n : ℝ)⁻¹ *
                ((∑ k : Fin n, lossGap ℓ z s t k ^ 2) / (n : ℝ)) / 2 := by
        field_simp
      exact hexp_eq.le

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem canonicalRademacherProcess_weight (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    (σ : Fin n → Bool) :
    (canonicalRademacherProcess ℓ z).weight σ = ((2 : ℝ) ^ n)⁻¹ := rfl

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem canonicalRademacherProcess_X (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    (σ : Fin n → Bool) (i : ι) :
    (canonicalRademacherProcess ℓ z).X σ i
      = (n : ℝ)⁻¹ * ∑ k : Fin n, signOfBool (σ k) * ℓ i (z k) := rfl

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem canonicalRademacherProcess_varianceProxy (ℓ : ι → Z → ℝ)
    (z : Fin n → Z) :
    (canonicalRademacherProcess ℓ z).varianceProxy = (n : ℝ)⁻¹ := rfl

omit [Fintype ι] [Nonempty ι] in
/-- The canonical Rademacher process metric is the empirical L2 distance on the
sample: `√((1/n) ∑_k (ℓ t (z k) - ℓ s (z k))²)`. This exposes the (private)
process metric in closed form so the continuous-instantiation bridge can state
the index-metric compatibility certificate without referencing `empiricalDist`. -/
@[simp] theorem canonicalRademacherProcess_dist (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    (s t : ι) :
    (canonicalRademacherProcess ℓ z).dist s t
      = Real.sqrt ((∑ k : Fin n, (ℓ t (z k) - ℓ s (z k)) ^ 2) / (n : ℝ)) := rfl

/-- The empirical Rademacher complexity equals the weighted expectation of the
finite supremum of the canonical process coordinates. Pure definitional
unfolding of `empiricalRademacherComplexity`, `finiteExpectation`, and
`finiteSup` against the canonical process. -/
theorem empiricalRademacherComplexity_eq_finiteExpectation_finiteSup
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) :
    empiricalRademacherComplexity ℓ z
      = finiteExpectation (canonicalRademacherProcess ℓ z).weight
          (fun σ => finiteSup (fun i : ι => (canonicalRademacherProcess ℓ z).X σ i)) := by
  unfold empiricalRademacherComplexity finiteExpectation finiteSup
  simp only [canonicalRademacherProcess_weight, canonicalRademacherProcess_X]
  rw [Finset.mul_sum]

/-- Centering: if the base hypothesis `t₀` has identically zero canonical
process coordinate, the centered supremum agrees with the plain supremum, so the
weighted expectation of the centered supremum equals the empirical Rademacher
complexity. -/
theorem empiricalRademacherComplexity_eq_centered
    (ℓ : ι → Z → ℝ) (z : Fin n → Z) (t₀ : ι)
    (hbase : ∀ σ : Fin n → Bool, (canonicalRademacherProcess ℓ z).X σ t₀ = 0) :
    empiricalRademacherComplexity ℓ z
      = finiteExpectation (canonicalRademacherProcess ℓ z).weight
          (fun σ => finiteSup
            (fun i : ι => (canonicalRademacherProcess ℓ z).X σ i
              - (canonicalRademacherProcess ℓ z).X σ t₀)) := by
  rw [empiricalRademacherComplexity_eq_finiteExpectation_finiteSup ℓ z]
  unfold finiteExpectation
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  unfold finiteSup
  refine Finset.sup'_congr _ rfl (fun i _ => ?_)
  rw [hbase σ, sub_zero]

/-- **Finite Dudley entropy integral to empirical Rademacher complexity.**

For a finite loss class admitting an antitone positive covering profile `N` and a
base hypothesis `t₀` with identically zero canonical coordinate, the empirical
Rademacher complexity is bounded by the finite-Dudley entropy integral. The
sub-Gaussian increment control is discharged from the discrete sign-vector
factorization (it is not assumed); the metric/symmetry/triangle and net data are
supplied through the same interface that the finite Dudley spine consumes.

This is the finite endpoint. The continuous-instantiation endpoint
(instantiating the continuous Dudley integral's entropy profile from covering
numbers) is `continuous_dudley_rademacher_complexity_bound` below. -/
theorem dudley_rademacher_complexity_bound
    (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (t₀ : ι) (radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hbase : ∀ σ : Fin n → Bool, (canonicalRademacherProcess ℓ z).X σ t₀ = 0)
    (hdist : ∀ j : ℕ, (N j).dist = (canonicalRademacherProcess ℓ z).dist)
    (hsymm : ∀ s t : ι,
      (canonicalRademacherProcess ℓ z).dist s t
        = (canonicalRademacherProcess ℓ z).dist t s)
    (htri : ∀ x y w : ι,
      (canonicalRademacherProcess ℓ z).dist x w
        ≤ (canonicalRademacherProcess ℓ z).dist x y
          + (canonicalRademacherProcess ℓ z).dist y w)
    (hroot : ∀ t : ι, (N 0).projection t = t₀)
    (hlast : ∀ t : ι, (N m).projection t = t)
    (hvariance : 0 < (canonicalRademacherProcess ℓ z).varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_product : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hcenter : ∀ j ∈ Finset.range m,
      ∀ pair : FiniteNet.ProjectionPair (N j) (N (j + 1)),
        finiteExpectation (canonicalRademacherProcess ℓ z).weight
          (fun σ => (canonicalRademacherProcess ℓ z).X σ ((N (j + 1)).center pair.1.2) -
            (canonicalRademacherProcess ℓ z).X σ ((N j).center pair.1.1)) = 0) :
    empiricalRademacherComplexity ℓ z ≤
      4 * Real.sqrt (2 / (n : ℝ)) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  rw [empiricalRademacherComplexity_eq_centered ℓ z t₀ hbase,
      show (2 : ℝ) / (n : ℝ) = 2 * (canonicalRademacherProcess ℓ z).varianceProxy by
        rw [canonicalRademacherProcess_varianceProxy, div_eq_mul_inv]]
  exact dudley_entropy_integral_of_antitone_coveringNumber
    (P := canonicalRademacherProcess ℓ z) (N := N) (m := m) (t₀ := t₀)
    (radiusScale := radiusScale)
    (coveringNumberAtRadius := coveringNumberAtRadius)
    hdist hsymm htri hroot hlast hvariance hradiusScale_nonneg
    hradius_pos hradius_geometric hcover_antitone hcover_pos
    hcover_product hcenter

/-- **Continuous Dudley entropy integral to empirical Rademacher complexity.**

This closes the continuous-instantiation gap left open by
`dudley_rademacher_complexity_bound`. The index class `ι` carries a pseudometric
that the caller certifies to be the empirical L2 distance on the sample
(`hmetric`, discharging the continuous theorem's `hdistP`). Under total
boundedness of `ι`, an antitone positive covering-number profile dominating the
dyadic chaining cover counts, and the separability/terminal boundary certificate
`hchoose'` for the Rademacher process, the empirical Rademacher complexity is
bounded by the continuous Dudley entropy integral
`∫₀^{radiusScale/2} √(log N(F, ε)) dε`, with the `C/√n` constant
`4 · √(2/n)` produced by rewriting the process variance proxy `1/n`.

Unlike the finite endpoint, the integral runs from `0` (not from a positive
terminal floor), and the entropy profile is the genuine metric-entropy integrand
`√(log N(F, ε))` for the covering-number profile `N(F, ε) = coveringNumberAtRadius ε`.

The analytic content of the bound is the continuous Dudley entropy integral
`ContinuousDudleyCovering.continuous_dudley_entropy_integral_of_coveringNumber`;
this theorem is the instantiation on `canonicalRademacherProcess ℓ z` together
with the `varianceProxy = 1/n` rewrite that turns `4 · √(2 · varianceProxy)`
into `4 · √(2/n)`. -/
theorem continuous_dudley_rademacher_complexity_bound
    [PseudoMetricSpace ι]
    (ℓ : ι → Z → ℝ) (z : Fin n → Z)
    (coarseBudget radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hT : TotallyBounded (Set.univ : Set ι))
    (hradiusScale : 0 < radiusScale)
    (hmetric : (canonicalRademacherProcess ℓ z).dist = fun s t => dist s t)
    (hvariance : 0 < (canonicalRademacherProcess ℓ z).varianceProxy)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_dominates : ∀ j : ℕ,
      FormalSLT.Covering.TotalBoundedDudley.dyadicChainingCoverCount
          (T := ι) hT hradiusScale j ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hchoose' : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
      ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
      ∃ (embed : K → ι), ∃ (separabilityError : ℝ), ∃ (terminalError : ℝ),
        separabilityError + terminalError ≤ eta ∧
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := ι) hT hradiusScale j).net
            (FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := ι) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable
            (fun ε : ℝ =>
              Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
            MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ σ : Fin n → Bool,
          finiteSup (fun i : ι => (canonicalRademacherProcess ℓ z).X σ i) ≤
            finiteSup (fun k : K => (canonicalRademacherProcess ℓ z).X σ (embed k))
              + separabilityError) ∧
        (∀ σ : Fin n → Bool, ∀ k : K,
          (canonicalRademacherProcess ℓ z).X σ (embed k) ≤
            (canonicalRademacherProcess ℓ z).X σ
              ((FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := ι) hT hradiusScale m).net.projection (embed k)) +
              terminalError) ∧
        (finiteExpectation (canonicalRademacherProcess ℓ z).weight
          (fun σ => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := ι) hT hradiusScale m).net =>
              (canonicalRademacherProcess ℓ z).X σ
                ((FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := ι) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (FormalSLT.Covering.TotalBoundedDudley.dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := ι) hT hradiusScale m).net u)))) ≤
          coarseBudget)) :
    empiricalRademacherComplexity ℓ z ≤
      coarseBudget + 4 * Real.sqrt (2 / (n : ℝ)) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  rw [empiricalRademacherComplexity_eq_finiteExpectation_finiteSup ℓ z,
      show (2 : ℝ) / (n : ℝ)
          = 2 * (canonicalRademacherProcess ℓ z).varianceProxy by
        rw [canonicalRademacherProcess_varianceProxy, div_eq_mul_inv]]
  exact FormalSLT.Covering.ContinuousDudleyCovering.continuous_dudley_entropy_integral_of_coveringNumber
    (P := canonicalRademacherProcess ℓ z) (hT := hT)
    (coarseBudget := coarseBudget) (radiusScale := radiusScale)
    (coveringNumberAtRadius := coveringNumberAtRadius)
    (supFunctional := fun σ =>
      finiteSup (fun i : ι => (canonicalRademacherProcess ℓ z).X σ i))
    hradiusScale hmetric hvariance hcover_antitone hcover_pos
    hcover_dominates hchoose'

/-- Instantiation of the bridge on the two-point hypothesis class `Bool`. -/
example {Z : Type*} (ℓ : Bool → Z → ℝ) {n : ℕ} (z : Fin n → Z)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet Bool (A j))
    (m : ℕ) (t₀ : Bool) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ) :=
  dudley_rademacher_complexity_bound (ι := Bool) ℓ z N m t₀ radiusScale
    coveringNumberAtRadius

end

#check @dudley_rademacher_complexity_bound

#check @continuous_dudley_rademacher_complexity_bound

#print axioms dudley_rademacher_complexity_bound

#print axioms continuous_dudley_rademacher_complexity_bound

end FormalSLT.Covering.DudleyToRademacher
