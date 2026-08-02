/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformIID

/-!
# Time-uniform i.i.d. PAC-Bayes with a finite tilt grid

This module removes the need to choose the sub-Gamma tilt before seeing the
sample.  Starting from the fixed-tilt i.i.d. PAC-Bayes theorem, it takes a finite
union over a nonempty grid `Lam` of admissible tilts.  Outside one exceptional
event of probability at most `delta`, the generalization bound therefore holds
simultaneously for every positive time, every posterior PMF, and every tilt in
the grid.

The price of selecting the tilt from the data is the explicit finite-grid
penalty `log (Lam.card / delta)`.  This is a finite-grid result, not a continuous
or countable tilt-mixture theorem.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open Finset Real BigOperators

namespace FormalSLT.PACBayes.TimeUniformIIDGrid

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open FormalSLT.PACBayes.TimeUniformIID

variable {ι Z Ω : Type*} [Fintype ι] [Nonempty ι]

/-- Failure of the i.i.d. PAC-Bayes bound for some posterior, positive time, and
tilt in a finite grid.  Both the posterior and the tilt may depend on the sample
path. -/
def timeUniformIIDPACBayesGridAnyPosteriorUpperFailure [MeasurableSpace Z]
    (dataLaw : Measure Z) (prior : ι → ℝ) (loss : ι → Z → ℝ)
    (sample : ℕ → Ω → Z) (Lam : Finset ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ lam ∈ Lam, ∃ posterior : ι → ℝ,
    IsPMF posterior ∧
      ∃ n : ℕ, 0 < n ∧
        subGammaCgf 1 1 lam / lam
            + (klDiv posterior prior + Real.log ((Lam.card : ℝ) / delta)) /
                ((n : ℝ) * lam)
          ≤ iidPosteriorPopulationRisk dataLaw loss posterior -
              iidPosteriorEmpiricalRisk loss sample posterior n ω}

omit [Nonempty ι] in
/-- The finite-grid failure event is contained in the union of fixed-tilt
failure events, each receiving confidence budget `delta / Lam.card`. -/
theorem timeUniformIIDPACBayesGridAnyPosteriorUpperFailure_subset_iUnion
    [MeasurableSpace Z]
    {dataLaw : Measure Z} {prior : ι → ℝ} {loss : ι → Z → ℝ}
    {sample : ℕ → Ω → Z} {Lam : Finset ℝ} {delta : ℝ}
    (hdelta : delta ≠ 0) (hLam : Lam.Nonempty) :
    timeUniformIIDPACBayesGridAnyPosteriorUpperFailure
        dataLaw prior loss sample Lam delta
      ⊆
    ⋃ lam ∈ Lam,
      timeUniformIIDPACBayesAnyPosteriorUpperFailure
        dataLaw prior loss sample lam (delta / (Lam.card : ℝ)) := by
  intro ω hω
  rcases hω with ⟨lam, hlam, posterior, hposterior, n, hn, hfail⟩
  refine Set.mem_iUnion.2 ⟨lam, Set.mem_iUnion.2 ⟨hlam, ?_⟩⟩
  refine ⟨posterior, hposterior, n, hn, ?_⟩
  have hcard : (Lam.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hLam).ne'
  have hbudget : 1 / (delta / (Lam.card : ℝ)) = (Lam.card : ℝ) / delta := by
    field_simp
  rw [hbudget]
  exact hfail

/-- Time-uniform PAC-Bayes generalization bound with data-dependent selection
from a finite grid of sub-Gamma tilts.

With probability at least `1 - delta`, simultaneously for every positive time,
every posterior PMF, and every `lam ∈ Lam`, the posterior population risk minus
its running empirical risk is at most

`subGammaCgf 1 1 lam / lam + (KL + log (Lam.card / delta)) / (n * lam)`.

The posterior and the grid tilt may both depend on the observed sample path. -/
theorem timeUniformIIDPACBayes_grid_allPosteriors_bound
    [mZ : MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [TopologicalSpace.MetrizableSpace Z]
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {dataLaw : Measure Z} [IsProbabilityMeasure dataLaw]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {loss : ι → Z → ℝ} {sample : ℕ → Ω → Z}
    {Lam : Finset ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hLam : Lam.Nonempty)
    (hLam_mem : ∀ lam ∈ Lam, lam ∈ Set.Ioo (0 : ℝ) 3)
    (hloss : ∀ i, StronglyMeasurable (loss i))
    (hloss_range : ∀ i z, 0 ≤ loss i z ∧ loss i z ≤ 1)
    (hsample : ∀ k, StronglyMeasurable (sample k))
    (hsample_indep : iIndepFun sample μ)
    (hsample_law : ∀ k, HasLaw (sample k) dataLaw μ) :
    μ.real (timeUniformIIDPACBayesGridAnyPosteriorUpperFailure
      dataLaw prior loss sample Lam delta) ≤ delta := by
  classical
  have hcard_pos : (0 : ℝ) < (Lam.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hLam
  let fixedFailure : ℝ → Set Ω := fun lam =>
    timeUniformIIDPACBayesAnyPosteriorUpperFailure
      dataLaw prior loss sample lam (delta / (Lam.card : ℝ))
  calc
    μ.real (timeUniformIIDPACBayesGridAnyPosteriorUpperFailure
        dataLaw prior loss sample Lam delta)
        ≤ μ.real (⋃ lam ∈ Lam, fixedFailure lam) :=
      measureReal_mono
        (timeUniformIIDPACBayesGridAnyPosteriorUpperFailure_subset_iUnion
          (dataLaw := dataLaw) (prior := prior) (loss := loss)
          (sample := sample) (Lam := Lam) (delta := delta)
          hdelta.ne' hLam) (measure_ne_top μ _)
    _ ≤ ∑ lam ∈ Lam, μ.real (fixedFailure lam) :=
      measureReal_biUnion_finset_le Lam fixedFailure
    _ ≤ ∑ _lam ∈ Lam, delta / (Lam.card : ℝ) := by
      apply Finset.sum_le_sum
      intro lam hlam
      exact timeUniformIIDPACBayes_allPosteriors_bound
        (μ := μ) (dataLaw := dataLaw) hprior
        (div_pos hdelta hcard_pos) (hLam_mem lam hlam).1 (hLam_mem lam hlam).2
        hloss hloss_range hsample hsample_indep hsample_law
    _ = delta := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

end

end FormalSLT.PACBayes.TimeUniformIIDGrid
