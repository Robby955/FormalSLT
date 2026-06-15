import FormalSLT.PACBayes.Compiler
import FormalSLT.AlgorithmicStability

/-!
# McAllester compiler high-probability good-event mass

This module is the McAllester general-width analogue of the Catoni-form
`pac_bayes_generalization`. The compiler already bounds the bad sample mass.
Here the good samples are the explicit implication form of the complement. We
prove that this set is the complement of the compiled bad samples and that its
product mass is at least `1 - delta`.

The final bridge lets downstream code use membership in the good set instead of
the pointwise `hnotBad` hypothesis in
`FormalSLT.TestTimeMeta.mcAllesterPointwiseRiskBound_of_not_mem_compiledBad`.

Sources:
* McAllester, D.A. (1999). "PAC-Bayesian model averaging." Proceedings of the
  Twelfth Annual Conference on Computational Learning Theory (COLT 1999),
  164-170. DOI: 10.1145/307400.307435.
* McAllester, D.A. (2003). "PAC-Bayesian stochastic model selection." Machine
  Learning 51(1), 5-21. DOI: 10.1023/A:1021840411064.
* Catoni, O. (2007). "PAC-Bayesian Supervised Classification: The
  Thermodynamics of Statistical Learning." IMS Lecture Notes Monograph Series,
  Vol. 56. arXiv:0712.0248.
-/

namespace FormalSLT.PACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBoundedLoss

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Samples on which the compiled general-width McAllester inequality holds. -/
def compiledMcAllesterGeneralGoodSamples {ι Z : Type*} [Fintype Z] [Fintype ι]
    (lossBound : ℝ) (spec : PACBayesCertificateSpec ι Z) :
    Finset (Fin spec.sampleSize → Z) :=
  Finset.univ.filter fun S : Fin spec.sampleSize → Z =>
    IsPMF spec.posterior →
      klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤ spec.complexityBound →
        posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior ≤
          posteriorEmpiricalRisk spec.loss spec.posterior S +
            mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound lossBound

/--
The good samples are exactly the complement of the compiled general-width
McAllester bad samples.
-/
theorem compiledMcAllesterGeneralGoodSamples_eq_compl {ι Z : Type*}
    [Fintype Z] [Fintype ι]
    (lossBound : ℝ) (spec : PACBayesCertificateSpec ι Z)
    (S : Fin spec.sampleSize → Z) :
    S ∈ compiledMcAllesterGeneralGoodSamples lossBound spec ↔
      S ∉ compiledMcAllesterGeneralBadSamples lossBound spec := by
  classical
  simp only [compiledMcAllesterGeneralGoodSamples, compiledMcAllesterGeneralBadSamples,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hgood hbad
    rcases hbad with ⟨hposterior, hcomplexity, hgt⟩
    exact (not_lt.mpr (hgood hposterior hcomplexity)) hgt
  · intro hnotBad hposterior hcomplexity
    by_contra hle
    exact hnotBad ⟨hposterior, hcomplexity, lt_of_not_ge hle⟩

/--
The general-width McAllester compiler good-event mass is at least `1 - delta`.
-/
theorem mcAllesterGeneralWidth_goodEventMass_ge_one_sub_delta {ι Z : Type*}
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
    1 - spec.delta ≤
      ∑ S ∈ compiledMcAllesterGeneralGoodSamples lossBound spec,
        finiteProductSampleWeight spec.dataLaw S := by
  classical
  set badSet : Finset (Fin spec.sampleSize → Z) :=
    compiledMcAllesterGeneralBadSamples lossBound spec with hbadSet
  set goodSet : Finset (Fin spec.sampleSize → Z) :=
    compiledMcAllesterGeneralGoodSamples lossBound spec with hgoodSet
  have hcompl : ∀ S : Fin spec.sampleSize → Z, S ∈ goodSet ↔ S ∉ badSet := by
    intro S
    rw [hgoodSet, hbadSet]
    exact compiledMcAllesterGeneralGoodSamples_eq_compl lossBound spec S
  have hdisj : Disjoint badSet goodSet := by
    rw [Finset.disjoint_left]
    intro S hbad hgood
    exact ((hcompl S).mp hgood) hbad
  have hcover :
      (Finset.univ : Finset (Fin spec.sampleSize → Z)) = badSet ∪ goodSet := by
    ext S
    refine ⟨fun _ => ?_, fun _ => Finset.mem_univ S⟩
    rw [Finset.mem_union]
    by_cases hbad : S ∈ badSet
    · exact Or.inl hbad
    · exact Or.inr ((hcompl S).mpr hbad)
  have htotal :
      (∑ S : Fin spec.sampleSize → Z, finiteProductSampleWeight spec.dataLaw S) = 1 := by
    simpa [FormalSLT.AlgorithmicStability.finiteProductSampleWeight,
      FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight] using
      (FormalSLT.AlgorithmicStability.finiteProductSampleWeight_sum_eq_one
        (n := spec.sampleSize) (Z := Z) (p := spec.dataLaw) hdataLaw.sum_one)
  have hsum_split :
      (∑ S : Fin spec.sampleSize → Z, finiteProductSampleWeight spec.dataLaw S) =
        (∑ S ∈ badSet, finiteProductSampleWeight spec.dataLaw S) +
          (∑ S ∈ goodSet, finiteProductSampleWeight spec.dataLaw S) := by
    have hunion :=
      Finset.sum_union (s₁ := badSet) (s₂ := goodSet)
        (f := fun S => finiteProductSampleWeight spec.dataLaw S) hdisj
    calc
      (∑ S : Fin spec.sampleSize → Z, finiteProductSampleWeight spec.dataLaw S)
          = ∑ S ∈ (Finset.univ : Finset (Fin spec.sampleSize → Z)),
              finiteProductSampleWeight spec.dataLaw S := rfl
      _ = ∑ S ∈ badSet ∪ goodSet, finiteProductSampleWeight spec.dataLaw S := by
            rw [← hcover]
      _ = (∑ S ∈ badSet, finiteProductSampleWeight spec.dataLaw S) +
            (∑ S ∈ goodSet, finiteProductSampleWeight spec.dataLaw S) :=
          hunion
  have hbad :
      (∑ S ∈ badSet, finiteProductSampleWeight spec.dataLaw S) ≤ spec.delta := by
    rw [hbadSet]
    exact PACBayesCertificateCompiler.compileGeneralWidth_sound
      spec lossBound hn hdataLaw hprior hcomplexityBound hdelta hlossBound hloss
  rw [hgoodSet]
  linarith

/--
Membership in the compiler good set discharges the pointwise McAllester risk
inequality for the fixed posterior in the specification.
-/
theorem mcAllesterPointwiseRiskBound_of_mem_good {ι Z : Type*}
    [Fintype Z] [Fintype ι]
    (spec : PACBayesCertificateSpec ι Z)
    (lossBound : ℝ)
    (S : Fin spec.sampleSize → Z)
    (hS : S ∈ compiledMcAllesterGeneralGoodSamples lossBound spec)
    (hposterior : IsPMF spec.posterior)
    (hcomplexity :
      klDiv spec.posterior spec.prior + Real.log (1 / spec.delta) ≤
        spec.complexityBound) :
    posteriorPopulationRisk spec.dataLaw spec.loss spec.posterior ≤
      posteriorEmpiricalRisk spec.loss spec.posterior S +
        mcAllesterGeneralPenalty spec.sampleSize spec.complexityBound lossBound := by
  exact (Finset.mem_filter.mp hS).2 hposterior hcomplexity

end

end FormalSLT.PACBayes
