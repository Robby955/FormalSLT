import Mathlib.Probability.CDF
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.Basic
import FormalSLT.UniformConvergence
import FormalSLT.Rademacher.ERMGeneralization
import FormalSLT.PACBayes.VCHybrid

/-!
# Glivenko-Cantelli bridge

This module adds the named Glivenko-Cantelli surface missing from the current
FormalSLT library and connects it to the existing finite-class
uniform-convergence, Rademacher, VC, and PAC-Bayes theorem surfaces.

The imported mathlib snapshot has `ProbabilityTheory.cdf` and strong-law
infrastructure, but no theorem named Glivenko-Cantelli and no empirical-CDF API.
Accordingly, this file makes the bridge explicit: the classical empirical-CDF
uniform-deviation process is the lower-ray indicator-class empirical process.
-/

open scoped BigOperators Function Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory
open FormalSLT.ERM
open FormalSLT.GhostSample (piMeasure)
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayes.VCHybrid
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)
open FormalSLT.Risk
open FormalSLT.VC.Rademacher (effectiveClass)

namespace FormalSLT.GlivenkoCantelli

noncomputable section

/-- Lower-ray indicator `1{z <= x}`, as a real-valued loss/function class member. -/
def lowerRayIndicator (x z : ℝ) : ℝ :=
  if z ≤ x then 1 else 0

/-- Lower-ray indicators are `[0,1]`-valued. -/
theorem lowerRayIndicator_mem_Icc (x z : ℝ) :
    lowerRayIndicator x z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold lowerRayIndicator
  split_ifs <;> norm_num

/-- Finite empirical average over a supplied sample-index finset. -/
def empiricalAverage {ι Ω : Type*} (s : Finset ι) (f : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ s, f i ω) / (s.card : ℝ)

/-- Empirical average of a function class member along a sample map. -/
def classEmpiricalAverage {ι Ω Z : Type*}
    (X : ι → Ω → Z) (s : Finset ι) (f : Z → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ s, f (X i ω)) / (s.card : ℝ)

/-- Empirical CDF for a finite sample indexed by `s`. -/
def empiricalCDF {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) : ℝ :=
  classEmpiricalAverage X s (lowerRayIndicator x) ω

/-- The empirical CDF is exactly the empirical average of lower-ray indicators. -/
theorem empiricalCDF_eq_lowerRayEmpiricalAverage {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) :
    empiricalCDF X s ω x =
      classEmpiricalAverage X s (lowerRayIndicator x) ω := rfl

/--
Uniform deviation of an abstract empirical process over a class `F`, using an
explicit population functional. This avoids baking integrability into the
definition and matches the way the existing finite-class probability wrappers
accept externally supplied risks.
-/
def gcClassUniformDeviation {ι Ω Z H : Type*}
    (F : H → Z → ℝ) (population : H → ℝ)
    (X : ι → Ω → Z) (s : Finset ι) (ω : Ω) : ℝ :=
  sSup {r : ℝ | ∃ h : H, r = |classEmpiricalAverage X s (F h) ω - population h|}

/-- Uniform empirical-CDF deviation, written as a lower-ray class deviation. -/
def empiricalCDFUniformDeviation {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ) : ℝ :=
  gcClassUniformDeviation lowerRayIndicator (fun x : ℝ => ProbabilityTheory.cdf μ x) X s ω

/-- Empirical-CDF uniform deviation is the lower-ray GC-class deviation. -/
theorem empiricalCDFUniformDeviation_eq_gcClassUniformDeviation {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ) :
    empiricalCDFUniformDeviation X s ω μ =
      gcClassUniformDeviation lowerRayIndicator
        (fun x : ℝ => ProbabilityTheory.cdf μ x) X s ω := rfl

/--
An indexed class is Glivenko-Cantelli along `X` when the uniform empirical
process over `Finset.range n` converges almost surely to zero.
-/
def IsGCClass {Ω Z H : Type*} [MeasurableSpace Ω]
    (F : H → Z → ℝ) (population : H → ℝ)
    (X : ℕ → Ω → Z) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P,
    Tendsto
      (fun n : ℕ => gcClassUniformDeviation F population X (Finset.range n) ω)
      atTop (𝓝 0)

/-- Classical empirical-CDF Glivenko-Cantelli statement in this module's notation. -/
def ClassicalGlivenkoCantelli {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (μ : Measure ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    Tendsto
      (fun n : ℕ => empiricalCDFUniformDeviation X (Finset.range n) ω μ)
      atTop (𝓝 0)

/--
The classical empirical-CDF GC statement is exactly the GC-class statement for
the lower-ray indicator class. This is the measure-theory/statistics-to-SLT
bridge: the index `x : ℝ` in the CDF is the hypothesis/class index in uniform
convergence.
-/
theorem lowerRayGC_iff_classicalGlivenkoCantelli {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (μ : Measure ℝ) :
    IsGCClass lowerRayIndicator (fun x : ℝ => ProbabilityTheory.cdf μ x) X P ↔
      ClassicalGlivenkoCantelli X P μ := by
  rfl

/--
Pointwise empirical-CDF strong law for a fixed lower ray.

This is the classical-statistics input available directly from mathlib's
strong law: for each fixed threshold `x`, the empirical CDF at `x` converges
almost surely to the population mass of that lower ray. The uncountable
uniformization over all `x` is the remaining full Glivenko-Cantelli step.
-/
theorem lowerRayPointwiseStrongLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Ω → ℝ) (x : ℝ)
    (hIntegrable : Integrable (fun ω => lowerRayIndicator x (X 0 ω)) P)
    (hIndep :
      Pairwise
        ((· ⟂ᵢ[P] ·) on
          (fun n : ℕ => fun ω : Ω => lowerRayIndicator x (X n ω))))
    (hIdent :
      ∀ i,
        IdentDistrib
          (fun ω : Ω => lowerRayIndicator x (X i ω))
          (fun ω : Ω => lowerRayIndicator x (X 0 ω)) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => empiricalCDF X (Finset.range n) ω x)
        atTop (𝓝 (∫ ω, lowerRayIndicator x (X 0 ω) ∂P)) := by
  simpa [empiricalCDF, classEmpiricalAverage, Finset.card_range] using
    ProbabilityTheory.strong_law_ae_real
      (μ := P)
      (X := fun n : ℕ => fun ω : Ω => lowerRayIndicator x (X n ω))
      hIntegrable hIndep hIdent

/--
Finite-class uniform-convergence bridge: pointwise two-sided deviation tails
imply a simultaneous finite-class empirical-process bad-event bound.
-/
theorem finiteClassUniformConvergenceBridge
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (deviation : H → Ω → ℝ) {ε : ℝ} {pointwiseTail : ℝ≥0∞}
    (hPointwiseTail : ∀ h, μ {ω | ε ≤ |deviation h ω|} ≤ pointwiseTail) :
    μ (⋃ h, {ω | ε ≤ |deviation h ω|}) ≤ Fintype.card H • pointwiseTail :=
  FormalSLT.UniformConvergence.finiteClassTwoSidedUniformDeviationUnionBound
    deviation hPointwiseTail

/-- VC/Hoeffding finite-class zero-one bridge already proved in `UniformConvergence`. -/
theorem vcHoeffdingBridge_for_gcClass
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real)
    (hδ_real_lt :
      δ_real < (2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) :
    μ (⋃ p : Fin T × H,
        {ω |
          √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real :=
  FormalSLT.UniformConvergence.finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius
    hIndep hMeas hBound01 hRisk hNonemptySample hδ_real_pos hδ_real_lt

/-- Rademacher ERM learnability bridge already proved in the finite-class Rademacher lane. -/
theorem rademacherERMBridge_for_gcClass
    {ι Z : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Z] {μ : Measure Z}
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    (hOracle : ∀ i : ι, risk μ ℓ i_star ≤ risk μ ℓ i)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 4 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + 2 * ε
            ≤ risk μ ℓ (hhat S) - risk μ ℓ i_star}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) :=
  FormalSLT.Rademacher.ERMGeneralization.rademacher_erm_excessRisk_tail
    hB hℓ_meas hℓ_bdd hn hCard hhat hERM i_star hOracle hε

/-- VC/PAC-Bayes hybrid learnability bridge already proved in the PAC-Bayes lane. -/
theorem vcPacBayesHybridBridge_for_gcClass
    {Ω ι Z : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ)
    (vcBad : Finset Ω)
    {lambda scale delta B : ℝ} {n d : ℕ}
    {ℓ : ι → Z → ℝ} (sample : Ω → Fin n → Z)
    (hB : 0 < B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth : ∀ ω', (effectiveClass ℓ (sample ω')).card ≤
      ∑ k ∈ Finset.range (d + 1), n.choose k)
    (empiricalAnchor : Ω → ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hRadGood : ∀ ω', ω' ∉ vcBad →
      posteriorEmpiricalRisk ρ (empiricalRiskFn ω') ≤ empiricalAnchor ω' +
        2 * empiricalRademacherComplexity ℓ (sample ω'))
    (hω :
      ω ∉ vcPacBayesHybridBadSamples vcBad π lambda scale delta
        riskFn empiricalRiskFn varianceProxy) :
    posteriorRisk ρ riskFn ≤
      empiricalAnchor ω +
        vcCapacityTerm B n d +
        (klDiv ρ π + Real.log (1 / delta)) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) :=
  FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound_from_vcRademacher
    hρ vcBad sample hB hℓ_bdd hn hd hdn hGrowth empiricalAnchor
    riskFn empiricalRiskFn varianceProxy ω hRadGood hω

/-! ## Concrete Bernoulli witness -/

/-- CDF of the Bernoulli distribution with mass `1/2` at `0` and `1/2` at `1`. -/
def bernoulliHalfCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then (1 / 2 : ℝ) else 1

/-- Empirical CDF of the concrete four-point sample `[0, 0, 0, 1]`. -/
def bernoulliThreeZerosOneOneSampleCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then (3 / 4 : ℝ) else 1

/--
The concrete Bernoulli sample `[0, 0, 0, 1]` has uniform CDF deviation at most
`1/4` from the Bernoulli-`1/2` CDF.
-/
theorem bernoulliThreeZerosOneOne_uniformDeviation_le_quarter :
    ∀ x : ℝ,
      |bernoulliThreeZerosOneOneSampleCDF x - bernoulliHalfCDF x| ≤ (1 / 4 : ℝ) := by
  intro x
  unfold bernoulliThreeZerosOneOneSampleCDF bernoulliHalfCDF
  by_cases hx0 : x < 0
  · simp [hx0]
  · by_cases hx1 : x < 1
    · simp [hx0, hx1]
      norm_num
    · simp [hx0, hx1]

end

end FormalSLT.GlivenkoCantelli
