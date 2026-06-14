/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# Non-vacuous McAllester discharge of the flagship population-risk decomposition

`FlagshipComposition` previously exposed the McAllester compiler contribution only as a
nonnegative scalar.  This module derives the pointwise McAllester risk inequality for a
sample outside the compiled bad set, then uses it to discharge the flagship scalar
`populationDecomposition` field with a real population risk and a nonzero McAllester gap.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBoundedLoss
open FormalSLT.PACBayesFiniteProductMGF

namespace FormalSLT.TestTimeMeta

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The general-width compiler theorem gives the McAllester bad-event mass bound. -/
theorem mcAllesterGeneralWidth_badEventMass_from_compile
    {ι Z : Type*}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (spec : PACBayesCertificateSpec ι Z)
    (lossBound : ℝ)
    (hn : 0 < spec.sampleSize)
    (hdataLaw : IsPMF spec.dataLaw)
    (hprior : IsFullSupportPMF spec.prior)
    (hcomplexityBound : 0 < spec.complexityBound)
    (hdelta : 0 < spec.delta)
    (hlossBound : 0 ≤ lossBound)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ spec.loss i z ∧ spec.loss i z ≤ lossBound) :
    (∑ S ∈ compiledMcAllesterGeneralBadSamples lossBound spec,
        finiteProductSampleWeight spec.dataLaw S) ≤ spec.delta := by
  exact PACBayesCertificateCompiler.compileGeneralWidth_sound
    spec lossBound hn hdataLaw hprior hcomplexityBound hdelta hlossBound hloss

/--
Pointwise McAllester risk bound for a fixed posterior/sample outside the compiled
bad set.  The conclusion is derived from membership in the good complement; no
`R ≤ Rhat + penalty` hypothesis is threaded through the statement.
-/
theorem mcAllesterPointwiseRiskBound_of_not_mem_compiledBad
    {ι Z : Type*} [Fintype Z] [Fintype ι]
    (spec : PACBayesCertificateSpec ι Z)
    (lossBound : ℝ)
    (S : Fin spec.sampleSize → Z)
    (hposterior : IsPMF spec.posterior)
    (hcomplexity :
      klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤
        spec.complexityBound)
    (hnotBad : S ∉ compiledMcAllesterGeneralBadSamples lossBound spec) :
    PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior ≤
      PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior S +
        mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound lossBound := by
  classical
  by_contra hle
  have hbad :
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior >
        PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior S +
          mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound lossBound :=
    lt_of_not_ge hle
  apply hnotBad
  simp only [compiledMcAllesterGeneralBadSamples, Finset.mem_filter]
  exact ⟨Finset.mem_univ S, hposterior, hcomplexity, hbad⟩

namespace McAllesterDecompWorkedExample

/-- Dirac data law on a two-point domain. -/
def dataLaw : Fin 2 → ℝ := fun z => if z = 0 then 1 else 0

/-- One-hypothesis full-support prior. -/
def prior : Fin 1 → ℝ := fun _ => 1

/-- Deterministic posterior on the unique hypothesis. -/
def posterior : Fin 1 → ℝ := fun _ => 1

/-- Bounded loss table. -/
def loss : Fin 1 → Fin 2 → ℝ := fun _ z =>
  if z = 0 then (1 : ℝ) / 4 else (3 : ℝ) / 4

/-- One-sample McAllester certificate spec. -/
def spec : PACBayesCertificateSpec (Fin 1) (Fin 2) where
  lossBound := 1
  sampleSize := 1
  hypothesisCardinality := 1
  dataLaw := dataLaw
  prior := prior
  posterior := posterior
  loss := loss
  delta := 1
  complexityBound := 1

/-- The observed sample hits the support point of the Dirac data law. -/
def sample : Fin spec.sampleSize → Fin 2 := fun _ => 0

/-- A genuine probability measure used to define the population risk. -/
def populationMeasure : Measure (Fin 2) := Measure.dirac 0

instance : IsProbabilityMeasure populationMeasure := by
  dsimp [populationMeasure]
  infer_instance

/-- The population risk is an integral average, not the McAllester bound side. -/
def populationRisk : ℝ :=
  ∫ z, PACBayesBoundedLoss.posteriorAverage spec.posterior (fun i => spec.loss i z) ∂populationMeasure

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    fin_cases z <;> norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    norm_num [prior]
  · simp [prior]
  · intro i
    fin_cases i
    norm_num [prior]

theorem posterior_isPMF : IsPMF posterior := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    norm_num [posterior]
  · simp [posterior]

theorem loss_mem_unitInterval :
    ∀ i : Fin 1, ∀ z : Fin 2, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro i z
  fin_cases i
  fin_cases z <;> norm_num [loss]

theorem complexity_le :
    klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤
      spec.complexityBound := by
  norm_num [spec, klDiv, prior, posterior]

theorem populationRisk_eq_posteriorPopulationRisk :
    populationRisk =
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior := by
  norm_num [populationRisk, populationMeasure, spec, dataLaw, loss, posterior,
    PACBayesBoundedLoss.posteriorPopulationRisk, finitePopulationRisk, PACBayesBoundedLoss.posteriorAverage, integral_dirac]

theorem sample_not_mem_bad :
    sample ∉ compiledMcAllesterGeneralBadSamples spec.lossBound spec := by
  classical
  intro hmem
  simp only [compiledMcAllesterGeneralBadSamples, Finset.mem_filter] at hmem
  have hbad := hmem.2.2.2
  have hpen_nonneg :
      0 ≤ mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound spec.lossBound := by
    simp [spec, mcAllesterGeneralPenalty, mcAllesterPenalty]
  have hpop :
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior = (1 : ℝ) / 4 := by
    norm_num [spec, dataLaw, loss, posterior, PACBayesBoundedLoss.posteriorPopulationRisk,
      finitePopulationRisk, PACBayesBoundedLoss.posteriorAverage]
  have hemp :
      PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior sample = (1 : ℝ) / 4 := by
    norm_num [spec, sample, loss, posterior, PACBayesBoundedLoss.posteriorEmpiricalRisk,
      finiteEmpiricalRisk, PACBayesBoundedLoss.posteriorAverage]
  rw [hpop, hemp] at hbad
  linarith

/-- Concrete pointwise McAllester risk inequality with the penalty derived from the bad set. -/
theorem pointwiseRiskBound :
    PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior ≤
      PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior sample +
        mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound spec.lossBound := by
  exact mcAllesterPointwiseRiskBound_of_not_mem_compiledBad
    spec spec.lossBound sample posterior_isPMF complexity_le sample_not_mem_bad

theorem mcAllesterContributionNonnegative :
    0 ≤ flagshipMcAllesterContribution spec := by
  exact flagshipMcAllesterContribution_from_compileGeneralWidth
    spec
    spec.lossBound
    (by norm_num [spec])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    (by norm_num [spec])
    (by norm_num [spec])
    (by
      intro i z
      simpa [spec] using loss_mem_unitInterval i z)

/-- Only the McAllester contribution is nonzero in this worked decomposition. -/
def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution := flagshipMcAllesterContribution spec
  onlineIidContribution := 0
  bernsteinOrGaussianContribution := 0
  anytimeVilleContribution := 0
  prefixKernelContribution := 0
  mcAllesterGeneralWidthContributionNonnegative := mcAllesterContributionNonnegative
  onlineIidContributionNonnegative := le_rfl
  bernsteinOrGaussianContributionNonnegative := le_rfl
  anytimeVilleContributionNonnegative := le_rfl
  prefixKernelContributionNonnegative := le_rfl

/-- User inputs whose population risk is the integral average above. -/
def user : FlagshipUserSupplied where
  sampleSize := spec.sampleSize
  targetConfidence := 1
  delta := spec.delta
  lossWidth := spec.lossBound
  empiricalRisk := PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior sample
  populationRisk := populationRisk
  positiveSampleSize := by norm_num [spec]
  deltaPositive := by norm_num [spec]
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num [spec]
  empiricalRiskNonnegative := by
    norm_num [spec, sample, loss, posterior, PACBayesBoundedLoss.posteriorEmpiricalRisk,
      finiteEmpiricalRisk, PACBayesBoundedLoss.posteriorAverage]
  populationRiskNonnegative := by
    norm_num [populationRisk, populationMeasure, spec, loss, posterior,
      PACBayesBoundedLoss.posteriorAverage, integral_dirac]

/-- The McAllester gap is the actual general-width penalty; the other gaps are zero. -/
theorem populationDecomposition_holds :
    user.populationRisk ≤
      user.empiricalRisk +
        mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound spec.lossBound +
        0 + 0 + 0 + 0 := by
  have h := pointwiseRiskBound
  rw [show user.populationRisk =
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior by
        exact populationRisk_eq_posteriorPopulationRisk]
  simpa [user, add_assoc] using h

theorem scalarBounds :
    FlagshipScalarComponentBounds user derived
      (mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound spec.lossBound)
      0 0 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact populationDecomposition_holds
  · simp [user, derived, flagshipMcAllesterContribution, mcAllesterGeneralPenalty]
  · simp [derived]
  · simp [derived]
  · simp [derived]
  · simp [derived]

/--
Non-vacuous flagship McAllester worked example: the population risk is a real
integral average, and the only nonzero gap is the derived McAllester penalty.
-/
theorem flagship_population_le_bound :
    user.populationRisk ≤ flagshipBound user derived := by
  exact flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

/--
The assembled flagship certificate.  Its `user.populationRisk` is the genuine Dirac
integral `populationRisk`, and the only nonzero derived gap is the real
`flagshipMcAllesterContribution spec` (the general-width penalty obtained from
`sample_not_mem_bad`); the bound is the proved `flagship_population_le_bound`, not a
definitional copy of the right-hand side.
-/
def certificate : FlagshipCertificate where
  user := user
  derived := derived
  assembledBound := flagship_population_le_bound

/-- The flagship theorem certifies the assembled non-vacuous McAllester certificate. -/
theorem flagship_conclusion_holds : flagshipConclusion certificate :=
  pacBayesTestTimeFlagship_theorem certificate

end McAllesterDecompWorkedExample

end

end FormalSLT.TestTimeMeta
