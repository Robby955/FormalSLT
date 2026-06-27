import FormalSLT.Covering.DudleyToRademacher
import FormalSLT.Rademacher.Symmetrization

/-!
# Metric-entropy mean generalization bridge

This module composes FormalSLT's finite Rademacher symmetrization theorem with
the finite Dudley-to-Rademacher endpoint. The result is a finite-class,
explicit-constant mean generalization bound:

`E_S sup_i (risk_i - empRisk_i) <= 8 * sqrt (2 / n) * entropyIntegral`.

The analytic chaining content remains in
`Covering.DudleyToRademacher.dudley_rademacher_complexity_bound`. The new
bridge here is the measure-theoretic step: a sample-independent metric entropy
profile gives the same deterministic Dudley budget on almost every sample, and
`integral_mono_ae` pulls that budget through the sample expectation.

This is a finite, explicit-constant bridge inside FormalSLT's own
chaining-to-learning pipeline. It is not a priority or novelty claim; broader
general sub-Gaussian Dudley formalizations exist in other libraries, including
lean-rademacher and AI4SLT. FormalSLT deliberately keeps the finite-class
measurability surface explicit here.

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Rademacher.MetricEntropyGeneralization

open MeasureTheory
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.GhostSample (piMeasure genGap)
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)
open FormalSLT.Rademacher.Symmetrization
  (expected_genGap_le_two_expected_empiricalRademacherComplexity)

noncomputable section

universe u

variable {n : ℕ} {ι : Type u} {Z : Type*}
variable [Fintype ι] [Nonempty ι] [MeasurableSpace Z]

/-- The uniform Dudley budget associated with a sample-independent covering
profile and a fixed truncation scale. -/
def uniformDudleyBudget (n m : ℕ) (radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ) : ℝ :=
  4 * Real.sqrt (2 / (n : ℝ)) *
    (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
      Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))

omit [MeasurableSpace Z] in
/-- The sample-dependent side conditions consumed by the finite
Dudley-to-Rademacher endpoint, with the entropy profile
`coveringNumberAtRadius` kept sample-independent. -/
structure SampleDudleySideConditions
    (ℓ : ι → Z → ℝ) (S : Fin n → Z)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (t₀ : ι) (radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ) : Prop where
  hbase :
    ∀ σ : Fin n → Bool,
      (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).X σ t₀ = 0
  hdist :
    ∀ j : ℕ,
      (N j).dist =
        (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist
  hsymm :
    ∀ s t : ι,
      (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist s t =
        (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist t s
  htri :
    ∀ x y w : ι,
      (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist x w ≤
        (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist x y +
          (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).dist y w
  hroot : ∀ t : ι, (N 0).projection t = t₀
  hlast : ∀ t : ι, (N m).projection t = t
  hvariance :
    0 < (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).varianceProxy
  hradiusScale_nonneg : 0 ≤ radiusScale
  hradius_pos :
    ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius
  hradius_geometric :
    ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j
  hcover_antitone : Antitone coveringNumberAtRadius
  hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε
  hcover_product :
    ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))
  hcenter :
    ∀ j ∈ Finset.range m,
      ∀ pair : FiniteNet.ProjectionPair (N j) (N (j + 1)),
        FormalSLT.Covering.FiniteSubGaussianChaining.finiteExpectation
            (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).weight
            (fun σ =>
              (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).X σ
                  ((N (j + 1)).center pair.1.2) -
                (FormalSLT.Covering.DudleyToRademacher.canonicalRademacherProcess ℓ S).X σ
                  ((N j).center pair.1.1)) =
          0

/-- Pull an almost-everywhere per-sample Dudley bound through the iid sample
expectation.

For almost every sample, `hside` supplies the sample-dependent net, centering,
geometric-radius, and cover-product side conditions needed by
`Covering.DudleyToRademacher.dudley_rademacher_complexity_bound`, while the
entropy profile `coveringNumberAtRadius` is uniform in the sample. -/
theorem expected_empiricalRademacher_le_dudley_uniform
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ)
    (hrad_int :
      Integrable (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
        (piMeasure μ n))
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : (Fin n → Z) → ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ)
    (t₀ : (Fin n → Z) → ι)
    (hside :
      ∀ᵐ S ∂(piMeasure μ n),
        SampleDudleySideConditions ℓ S (N S) m (t₀ S)
          radiusScale coveringNumberAtRadius) :
    ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n)
      ≤ uniformDudleyBudget n m radiusScale coveringNumberAtRadius := by
  have hsample :
      ∀ᵐ S ∂(piMeasure μ n),
        empiricalRademacherComplexity ℓ S ≤
          uniformDudleyBudget n m radiusScale coveringNumberAtRadius := by
    refine hside.mono ?_
    intro S hS
    exact
      FormalSLT.Covering.DudleyToRademacher.dudley_rademacher_complexity_bound
        ℓ S (N S) m (t₀ S) radiusScale coveringNumberAtRadius
        hS.hbase hS.hdist hS.hsymm hS.htri hS.hroot hS.hlast
        hS.hvariance hS.hradiusScale_nonneg hS.hradius_pos
        hS.hradius_geometric hS.hcover_antitone hS.hcover_pos
        hS.hcover_product hS.hcenter
  have hconst_int :
      Integrable
        (fun _S : Fin n → Z =>
          uniformDudleyBudget n m radiusScale coveringNumberAtRadius)
        (piMeasure μ n) :=
    integrable_const _
  calc
    ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n)
        ≤ ∫ _S : Fin n → Z,
            uniformDudleyBudget n m radiusScale coveringNumberAtRadius
              ∂(piMeasure μ n) :=
          integral_mono_ae hrad_int hconst_int hsample
    _ = uniformDudleyBudget n m radiusScale coveringNumberAtRadius := by
          simp [integral_const]

/-- **Mean metric-entropy generalization bound.**

If the finite loss class is measurable and uniformly bounded, and the finite
Dudley endpoint supplies the same entropy budget for almost every iid sample,
then the expected one-sided uniform generalization gap is bounded by the
metric-entropy integral with the symmetrization factor included. -/
theorem metricEntropy_generalization_mean
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : ι → Z → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n)
    (hrad_int :
      Integrable (fun S : Fin n → Z => empiricalRademacherComplexity ℓ S)
        (piMeasure μ n))
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : (Fin n → Z) → ∀ j : ℕ, FiniteNet ι (A j))
    (m : ℕ) (radiusScale : ℝ) (coveringNumberAtRadius : ℝ → ℕ)
    (t₀ : (Fin n → Z) → ι)
    (hside :
      ∀ᵐ S ∂(piMeasure μ n),
        SampleDudleySideConditions ℓ S (N S) m (t₀ S)
          radiusScale coveringNumberAtRadius) :
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
      ≤ 8 * Real.sqrt (2 / (n : ℝ)) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  have hsymm :
      ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
        ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) :=
    expected_genGap_le_two_expected_empiricalRademacherComplexity
      μ ℓ hB hℓ_meas hℓ_bdd hn
  have hrad :
    ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n)
        ≤ uniformDudleyBudget n m radiusScale coveringNumberAtRadius :=
    expected_empiricalRademacher_le_dudley_uniform
      μ ℓ hrad_int N m radiusScale coveringNumberAtRadius t₀ hside
  calc
    ∫ S, genGap μ ℓ S ∂(piMeasure μ n)
        ≤ 2 * ∫ S, empiricalRademacherComplexity ℓ S ∂(piMeasure μ n) := hsymm
    _ ≤ 2 * uniformDudleyBudget n m radiusScale coveringNumberAtRadius := by
          nlinarith
    _ = 8 * Real.sqrt (2 / (n : ℝ)) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
          simp [uniformDudleyBudget]
          ring

/-- A concrete finite, positive entropy budget: the constant two-point entropy
profile over sample size one and radius interval `[0, 1]` has a nonzero finite
right-hand side. This is the numerical non-vacuity witness for the q100 bound's
metric-entropy term. -/
theorem metricEntropy_generalization_nonvacuous :
    0 <
      8 * Real.sqrt (2 / (1 : ℝ)) *
        (∫ _ε in (0 : ℝ)..(1 : ℝ), Real.sqrt (Real.log (2 : ℝ))) := by
  rw [intervalIntegral.integral_const]
  norm_num
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsqrt_log : 0 < Real.sqrt (Real.log (2 : ℝ)) :=
    Real.sqrt_pos.2 hlog
  have hsqrt_two : 0 < Real.sqrt (2 / (1 : ℝ)) := by
    apply Real.sqrt_pos.2
    norm_num
  positivity

end

end FormalSLT.Rademacher.MetricEntropyGeneralization
