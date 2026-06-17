/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.McAllesterCompilerHighProbability
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# High-probability McAllester population-decomposition slot

This module wires the McAllester compiler good-event mass theorem into the
flagship scalar interface.  The finite worked instance uses two samples, two
data values, two hypotheses, and `delta = 1/2`, so the confidence statement is
the genuine good-event mass bound rather than a vacuous `delta = 1` case.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBoundedLoss
open FormalSLT.PACBayesFiniteProductMGF

namespace FormalSLT.TestTimeMeta

noncomputable section

local instance mcAllesterRealDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

namespace McAllesterRealDecompWorkedExample

/-- Uniform data law on a two-point domain. -/
def dataLaw : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform full-support prior on two hypotheses. -/
def prior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform posterior on the same two hypotheses. -/
def posterior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Bounded loss table with two distinct hypothesis losses. -/
def loss : Fin 2 → Fin 2 → ℝ := fun i _ =>
  if i = 0 then (1 : ℝ) / 4 else (1 : ℝ) / 2

/-- Non-degenerate McAllester certificate spec. -/
def spec : PACBayesCertificateSpec (Fin 2) (Fin 2) where
  lossBound := 1
  sampleSize := 2
  hypothesisCardinality := 2
  dataLaw := dataLaw
  prior := prior
  posterior := posterior
  loss := loss
  delta := (1 : ℝ) / 2
  complexityBound := 2

/-- A concrete sample used to instantiate the pointwise flagship scalar slot. -/
def sample : Fin spec.sampleSize → Fin 2 := fun _ => 0

def mcAllesterGap : ℝ :=
  mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound spec.lossBound

/-- The population risk used by the scalar flagship interface. -/
def populationRisk : ℝ :=
  PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    fin_cases z <;> norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [prior]
  · simp [prior]
  · intro i
    fin_cases i <;> norm_num [prior]

theorem posterior_isPMF : IsPMF posterior := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [posterior]
  · simp [posterior]

theorem loss_mem_unitInterval :
    ∀ i : Fin 2, ∀ z : Fin 2, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro i z
  fin_cases i <;> fin_cases z <;> norm_num [loss]

theorem delta_pos : 0 < spec.delta := by
  norm_num [spec]

theorem delta_lt_one : spec.delta < 1 := by
  norm_num [spec]

theorem klDiv_posterior_prior : klDiv spec.posterior spec.prior = 0 := by
  unfold spec klDiv posterior prior
  norm_num

theorem complexity_le :
    klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤
      spec.complexityBound := by
  have hlog_le_one : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    norm_num at h
    exact h
  have hlog_le_two : Real.log (2 : ℝ) ≤ 2 := by
    linarith
  rw [klDiv_posterior_prior]
  simpa [spec] using hlog_le_two

theorem posteriorPopulationRisk_eq_three_eighths :
    PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior =
      (3 : ℝ) / 8 := by
  norm_num [spec, dataLaw, loss, posterior,
    PACBayesBoundedLoss.posteriorPopulationRisk, finitePopulationRisk,
    PACBayesBoundedLoss.posteriorAverage]

theorem posteriorEmpiricalRisk_eq_three_eighths
    (S : Fin spec.sampleSize → Fin 2) :
    PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior S =
      (3 : ℝ) / 8 := by
  norm_num [spec, loss, posterior,
    PACBayesBoundedLoss.posteriorEmpiricalRisk, finiteEmpiricalRisk,
    PACBayesBoundedLoss.posteriorAverage]

theorem populationRisk_eq_posteriorPopulationRisk :
    populationRisk =
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior := by
  rfl

theorem mcAllesterPenalty_nonnegative :
    0 ≤ mcAllesterGap := by
  unfold mcAllesterGap mcAllesterGeneralPenalty
  exact mul_nonneg (by norm_num [spec]) (Real.sqrt_nonneg _)

theorem sample_mem_good :
    sample ∈ compiledMcAllesterGeneralGoodSamples spec.lossBound spec := by
  classical
  simp only [compiledMcAllesterGeneralGoodSamples, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro _hposterior _hcomplexity
  rw [posteriorPopulationRisk_eq_three_eighths,
    posteriorEmpiricalRisk_eq_three_eighths sample]
  exact le_add_of_nonneg_right mcAllesterPenalty_nonnegative

theorem mcAllesterContributionNonnegative :
    0 ≤ flagshipMcAllesterContribution spec := by
  exact flagshipMcAllesterContribution_from_compileGeneralWidth
    spec
    spec.lossBound
    (by norm_num [spec])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    delta_pos
    (by norm_num [spec])
    (by
      intro i z
      simpa [spec] using loss_mem_unitInterval i z)

theorem mcAllesterContribution_pos :
    0 < flagshipMcAllesterContribution spec := by
  unfold flagshipMcAllesterContribution mcAllesterPenalty
  apply Real.sqrt_pos.2
  norm_num [spec]

/-- The McAllester contribution is the only nonzero slot in this sidecar. -/
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

/-- User inputs for the real McAllester sidecar. -/
def user : FlagshipUserSupplied where
  sampleSize := spec.sampleSize
  targetConfidence := 1 - spec.delta
  delta := spec.delta
  lossWidth := spec.lossBound
  empiricalRisk := PACBayesBoundedLoss.posteriorEmpiricalRisk spec.loss spec.posterior sample
  populationRisk := populationRisk
  positiveSampleSize := by norm_num [spec]
  deltaPositive := delta_pos
  confidenceNonnegative := by norm_num [spec]
  lossWidthNonnegative := by norm_num [spec]
  empiricalRiskNonnegative := by
    rw [posteriorEmpiricalRisk_eq_three_eighths sample]
    norm_num
  populationRiskNonnegative := by
    rw [populationRisk_eq_posteriorPopulationRisk, posteriorPopulationRisk_eq_three_eighths]
    norm_num

theorem populationDecomposition_holds :
    user.populationRisk ≤
      user.empiricalRisk + mcAllesterGap + 0 + 0 + 0 + 0 := by
  have h :=
    FormalSLT.PACBayes.mcAllesterPointwiseRiskBound_of_mem_good
      spec spec.lossBound sample sample_mem_good posterior_isPMF complexity_le
  rw [show user.populationRisk =
      PACBayesBoundedLoss.posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior by
        rfl]
  simpa [user, mcAllesterGap, add_assoc] using h

theorem scalarBounds :
    FlagshipScalarComponentBounds user derived mcAllesterGap 0 0 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact populationDecomposition_holds
  · simp [user, derived, mcAllesterGap, flagshipMcAllesterContribution,
      mcAllesterGeneralPenalty, spec]
  · simp [derived]
  · simp [derived]
  · simp [derived]
  · simp [derived]

theorem flagship_population_le_bound :
    user.populationRisk ≤ flagshipBound user derived := by
  exact flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

def certificate : FlagshipCertificate where
  user := user
  derived := derived
  assembledBound := flagship_population_le_bound

theorem flagship_conclusion_holds : flagshipConclusion certificate :=
  pacBayesTestTimeFlagship_theorem certificate

end McAllesterRealDecompWorkedExample

/--
The concrete two-sample, two-hypothesis McAllester good event has mass at least
`1 - delta`, with `delta = 1/2`.
-/
theorem mcAllesterReal_goodEventMass_ge_one_sub_delta :
    1 - McAllesterRealDecompWorkedExample.spec.delta ≤
      ∑ S ∈ compiledMcAllesterGeneralGoodSamples
          McAllesterRealDecompWorkedExample.spec.lossBound
          McAllesterRealDecompWorkedExample.spec,
        finiteProductSampleWeight
          McAllesterRealDecompWorkedExample.spec.dataLaw S := by
  exact mcAllesterGeneralWidth_goodEventMass_ge_one_sub_delta
    McAllesterRealDecompWorkedExample.spec
    McAllesterRealDecompWorkedExample.spec.lossBound
    (by norm_num [McAllesterRealDecompWorkedExample.spec])
    McAllesterRealDecompWorkedExample.dataLaw_isPMF
    McAllesterRealDecompWorkedExample.prior_isFullSupportPMF
    (by norm_num [McAllesterRealDecompWorkedExample.spec])
    McAllesterRealDecompWorkedExample.delta_pos
    (by norm_num [McAllesterRealDecompWorkedExample.spec])
    (by
      intro i z
      simpa [McAllesterRealDecompWorkedExample.spec] using
        McAllesterRealDecompWorkedExample.loss_mem_unitInterval i z)

/--
Pointwise McAllester population-risk bound on every sample in the good event of
the concrete non-degenerate spec.
-/
theorem mcAllesterReal_pointwiseRiskBound_of_mem_good
    (S : Fin McAllesterRealDecompWorkedExample.spec.sampleSize → Fin 2)
    (hS : S ∈ compiledMcAllesterGeneralGoodSamples
      McAllesterRealDecompWorkedExample.spec.lossBound
      McAllesterRealDecompWorkedExample.spec) :
    PACBayesBoundedLoss.posteriorPopulationRisk
        McAllesterRealDecompWorkedExample.spec.dataLaw
        McAllesterRealDecompWorkedExample.spec.loss
        McAllesterRealDecompWorkedExample.spec.posterior ≤
      PACBayesBoundedLoss.posteriorEmpiricalRisk
          McAllesterRealDecompWorkedExample.spec.loss
          McAllesterRealDecompWorkedExample.spec.posterior S +
        mcAllesterGeneralPenalty
          McAllesterRealDecompWorkedExample.spec.sampleSize
          McAllesterRealDecompWorkedExample.spec.complexityBound
          McAllesterRealDecompWorkedExample.spec.lossBound := by
  exact FormalSLT.PACBayes.mcAllesterPointwiseRiskBound_of_mem_good
    McAllesterRealDecompWorkedExample.spec
    McAllesterRealDecompWorkedExample.spec.lossBound
    S
    hS
    McAllesterRealDecompWorkedExample.posterior_isPMF
    McAllesterRealDecompWorkedExample.complexity_le

/--
Flagship-facing McAllester slot: the same concrete spec supplies both the
non-vacuous good-event mass and the scalar component bound consumed by the
flagship assembly.
-/
theorem mcAllesterReal_flagshipContribution :
    (1 - McAllesterRealDecompWorkedExample.spec.delta ≤
      ∑ S ∈ compiledMcAllesterGeneralGoodSamples
          McAllesterRealDecompWorkedExample.spec.lossBound
          McAllesterRealDecompWorkedExample.spec,
        finiteProductSampleWeight
          McAllesterRealDecompWorkedExample.spec.dataLaw S) ∧
      FlagshipScalarComponentBounds
        McAllesterRealDecompWorkedExample.user
        McAllesterRealDecompWorkedExample.derived
        McAllesterRealDecompWorkedExample.mcAllesterGap
        0 0 0 0 := by
  exact ⟨mcAllesterReal_goodEventMass_ge_one_sub_delta,
    McAllesterRealDecompWorkedExample.scalarBounds⟩

end

end FormalSLT.TestTimeMeta
