import FormalSLT.PACBayes.McAllesterBoundGeneral

/-!
# PAC-Bayes certificate compiler

This module defines a small Lean-side certificate specification and a compiler
soundness theorem. A practitioner supplies a finite hypothesis index, finite
data domain, data law, prior, loss table, sample size, confidence target, and
complexity budget. The compiler proposition is the McAllester bad-event bound
for that specification, and `compile_sound` emits the proof term from the
finite McAllester theorem.

The q061 general-width surface keeps the original `[0,1]` compiler theorem
as the `lossBound = 1` corollary while exposing `compileGeneralWidth` for
losses in `[0, b]`.

Reference: McAllester, D.A. (1999). "PAC-Bayesian model averaging."
-/

namespace FormalSLT.PACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBoundedLoss

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite practitioner specification for the McAllester certificate compiler. -/
structure PACBayesCertificateSpec (ι Z : Type*) where
  lossBound : ℝ
  sampleSize : ℕ
  hypothesisCardinality : ℕ
  dataLaw : Z → ℝ
  prior : ι → ℝ
  posterior : ι → ℝ
  loss : ι → Z → ℝ
  delta : ℝ
  complexityBound : ℝ

/-- Samples on which the target posterior from the spec violates McAllester. -/
def compiledMcAllesterBadSamples {ι Z : Type*} [Fintype Z] [Fintype ι]
    (spec : PACBayesCertificateSpec ι Z) : Finset (Fin spec.sampleSize → Z) :=
  Finset.univ.filter fun S : Fin spec.sampleSize → Z =>
    IsPMF spec.posterior ∧
      klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤ spec.complexityBound ∧
      posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior >
        posteriorEmpiricalRisk spec.loss spec.posterior S +
          mcAllesterPenalty spec.sampleSize spec.complexityBound

/-- The proposition emitted by the certificate compiler for a finite spec. -/
def compiledMcAllesterCertificate {ι Z : Type*} [Fintype Z] [Fintype ι]
    (spec : PACBayesCertificateSpec ι Z) : Prop :=
  (∑ S ∈ compiledMcAllesterBadSamples spec,
      finiteProductSampleWeight spec.dataLaw S) ≤ spec.delta

/-- Samples on which the target posterior violates the general-width McAllester bound. -/
def compiledMcAllesterGeneralBadSamples {ι Z : Type*} [Fintype Z] [Fintype ι]
    (lossBound : ℝ) (spec : PACBayesCertificateSpec ι Z) :
    Finset (Fin spec.sampleSize → Z) :=
  Finset.univ.filter fun S : Fin spec.sampleSize → Z =>
    IsPMF spec.posterior ∧
      klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤ spec.complexityBound ∧
      posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior >
        posteriorEmpiricalRisk spec.loss spec.posterior S +
          mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound lossBound

/-- The proposition emitted by the compiler for a general-width finite spec. -/
def compiledMcAllesterGeneralCertificate {ι Z : Type*} [Fintype Z] [Fintype ι]
    (lossBound : ℝ) (spec : PACBayesCertificateSpec ι Z) : Prop :=
  (∑ S ∈ compiledMcAllesterGeneralBadSamples lossBound spec,
      finiteProductSampleWeight spec.dataLaw S) ≤ spec.delta

/- Namespace for the Lean-side certificate compiler. -/
namespace PACBayesCertificateCompiler

/-- Compile a finite practitioner spec to its McAllester certificate proposition. -/
def compile {ι Z : Type*} [Fintype Z] [Fintype ι]
    (spec : PACBayesCertificateSpec ι Z) : Prop :=
  compiledMcAllesterCertificate spec

/-- Compile a finite practitioner spec to its general-width McAllester certificate. -/
def compileGeneralWidth {ι Z : Type*} [Fintype Z] [Fintype ι]
    (lossBound : ℝ) (spec : PACBayesCertificateSpec ι Z) : Prop :=
  compiledMcAllesterGeneralCertificate lossBound spec

/--
General-width compiler soundness for losses in `[0, b]`.

This is the widened q061 compiler theorem. It routes through
`mcAllesterBoundGeneral_badEventMass_le_delta`; no normalization hypothesis is
hidden in the theorem statement.
-/
theorem compileGeneralWidth_sound {ι Z : Type*}
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
    compileGeneralWidth lossBound spec := by
  have hstrong :
      (∑ S ∈ mcAllesterGeneralBadSamples (n := spec.sampleSize)
          spec.dataLaw spec.prior spec.loss spec.complexityBound spec.delta lossBound,
          finiteProductSampleWeight spec.dataLaw S) ≤ spec.delta :=
    mcAllesterBoundGeneral_badEventMass_le_delta
      (n := spec.sampleSize)
      hn
      spec.dataLaw hdataLaw
      spec.prior hprior
      spec.loss
      (hcomplexityBound := hcomplexityBound)
      (hdelta := hdelta)
      (hlossBound := hlossBound)
      hloss
  have hsubset :
      compiledMcAllesterGeneralBadSamples lossBound spec ⊆
        mcAllesterGeneralBadSamples (n := spec.sampleSize)
          spec.dataLaw spec.prior spec.loss spec.complexityBound spec.delta lossBound := by
    intro S hS
    simp only [compiledMcAllesterGeneralBadSamples, mcAllesterGeneralBadSamples,
      Finset.mem_filter] at hS ⊢
    rcases hS.2 with ⟨hposterior, hcomplexity, hbad⟩
    exact ⟨hS.1, ⟨spec.posterior, hposterior, hcomplexity, hbad⟩⟩
  have hmass_le :
      (∑ S ∈ compiledMcAllesterGeneralBadSamples lossBound spec,
          finiteProductSampleWeight spec.dataLaw S) ≤
        ∑ S ∈ mcAllesterGeneralBadSamples (n := spec.sampleSize)
          spec.dataLaw spec.prior spec.loss spec.complexityBound spec.delta lossBound,
          finiteProductSampleWeight spec.dataLaw S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro S _hS _hnot
      unfold finiteProductSampleWeight
      exact Finset.prod_nonneg (fun k _hk => hdataLaw.nonneg (S k)))
  exact hmass_le.trans hstrong

/--
Unit-width compiler soundness. This is the original q053 surface, now retained
as the `lossBound = 1` corollary of `compileGeneralWidth_sound`.
-/
theorem compile_sound {ι Z : Type*}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι]
    (spec : PACBayesCertificateSpec ι Z)
    (hn : 0 < spec.sampleSize)
    (hdataLaw : IsPMF spec.dataLaw)
    (hprior : IsFullSupportPMF spec.prior)
    (hcomplexityBound : 0 < spec.complexityBound)
    (hdelta : 0 < spec.delta)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ spec.loss i z ∧ spec.loss i z ≤ 1) :
    compile spec := by
  have hgeneral : compileGeneralWidth 1 spec :=
    compileGeneralWidth_sound
      spec
      1
      hn
      hdataLaw
      hprior
      hcomplexityBound
      hdelta
      (by norm_num)
      hloss
  simpa [compile, compiledMcAllesterCertificate, compiledMcAllesterBadSamples,
    compileGeneralWidth, compiledMcAllesterGeneralCertificate,
    compiledMcAllesterGeneralBadSamples, mcAllesterGeneralPenalty] using hgeneral

end PACBayesCertificateCompiler

namespace BinaryClassifierExample

/-- Data law on a two-point domain. -/
def dataLaw : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform full-support prior on sixteen hypotheses. -/
def prior : Fin 16 → ℝ := fun _ => (1 : ℝ) / 16

/-- A bounded zero-one loss table. -/
def loss : Fin 16 → Fin 2 → ℝ := fun _ z =>
  if z = 0 then 0 else 1

/-- Compiler-facing binary-classification spec. -/
def spec : PACBayesCertificateSpec (Fin 16) (Fin 2) where
  lossBound := 1
  sampleSize := 4000
  hypothesisCardinality := 16
  dataLaw := dataLaw
  prior := prior
  posterior := fun i => if i = 0 then 1 else 0
  loss := loss
  delta := (1 : ℝ) / 20
  complexityBound := (2884160497897 : ℝ) / 500000000000

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro _; norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro _; norm_num [prior]
  · simp [prior]
  · intro _; norm_num [prior]

theorem loss_mem_unitInterval :
    ∀ i : Fin 16, ∀ z : Fin 2, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro _ z
  fin_cases z <;> norm_num [loss, Fin.ext_iff]

/-- Compiled binary-classification PAC-Bayes certificate. -/
theorem certificate : PACBayesCertificateCompiler.compile spec := by
  exact PACBayesCertificateCompiler.compile_sound
    spec
    (by norm_num [spec])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    (by norm_num [spec])
    loss_mem_unitInterval

end BinaryClassifierExample

namespace BoundedRegressionStub

/-- Uniform data law on a three-point finite regression stub. -/
def dataLaw : Fin 3 → ℝ := fun _ => (1 : ℝ) / 3

/-- Uniform full-support prior over eight finite predictors. -/
def prior : Fin 8 → ℝ := fun _ => (1 : ℝ) / 8

/-- Bounded regression-style loss levels in `[0, 1]`. -/
def loss : Fin 8 → Fin 3 → ℝ := fun _ z =>
  if z = 0 then 0 else if z = 1 then (1 : ℝ) / 2 else 1

/-- Compiler-facing bounded-regression stub spec. -/
def spec : PACBayesCertificateSpec (Fin 8) (Fin 3) where
  lossBound := 1
  sampleSize := 2500
  hypothesisCardinality := 8
  dataLaw := dataLaw
  prior := prior
  posterior := fun i => if i = 0 then 1 else 0
  loss := loss
  delta := (1 : ℝ) / 25
  complexityBound := (5 : ℝ)

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro _; norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro _; norm_num [prior]
  · simp [prior]
  · intro _; norm_num [prior]

theorem loss_mem_unitInterval :
    ∀ i : Fin 8, ∀ z : Fin 3, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro _ z
  fin_cases z <;> norm_num [loss, Fin.ext_iff]

/-- Compiled bounded-regression stub PAC-Bayes certificate. -/
theorem certificate : PACBayesCertificateCompiler.compile spec := by
  exact PACBayesCertificateCompiler.compile_sound
    spec
    (by norm_num [spec])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    (by norm_num [spec])
    loss_mem_unitInterval

end BoundedRegressionStub

namespace DecisionStumpExample

/-- Uniform data law on four ordered points. -/
def dataLaw : Fin 4 → ℝ := fun _ => (1 : ℝ) / 4

/-- Uniform full-support prior over four threshold stumps. -/
def prior : Fin 4 → ℝ := fun _ => (1 : ℝ) / 4

/-- Threshold-stump zero-one loss table over the finite ordered domain. -/
def loss : Fin 4 → Fin 4 → ℝ := fun stump z =>
  if (z : ℕ) ≤ (stump : ℕ) then 0 else 1

/-- Compiler-facing decision-stump spec. -/
def spec : PACBayesCertificateSpec (Fin 4) (Fin 4) where
  lossBound := 1
  sampleSize := 6000
  hypothesisCardinality := 4
  dataLaw := dataLaw
  prior := prior
  posterior := fun i => if i = 0 then 1 else 0
  loss := loss
  delta := (1 : ℝ) / 20
  complexityBound := (6 : ℝ)

theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro _; norm_num [dataLaw]
  · simp [dataLaw]

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro _; norm_num [prior]
  · simp [prior]
  · intro _; norm_num [prior]

theorem loss_mem_unitInterval :
    ∀ i : Fin 4, ∀ z : Fin 4, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro i z
  fin_cases i <;> fin_cases z <;> norm_num [loss]

/-- Compiled decision-stump PAC-Bayes certificate. -/
theorem certificate : PACBayesCertificateCompiler.compile spec := by
  exact PACBayesCertificateCompiler.compile_sound
    spec
    (by norm_num [spec])
    dataLaw_isPMF
    prior_isFullSupportPMF
    (by norm_num [spec])
    (by norm_num [spec])
    loss_mem_unitInterval

end DecisionStumpExample

end

end FormalSLT.PACBayes
