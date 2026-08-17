/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousJointMeanVarianceReversePACBayes

/-!
# Finite tilt catalogs for continuous-posterior reverse PAC-Bayes

This module combines finitely many fixed-tilt continuous-posterior reverse
epochs by allocating confidence `delta * w c` to catalog atom `c`.  The master
event is a posterior-independent finite union.  Outside it, a catalog atom may
be selected after observing both the horizon sample and the posterior, while
the displayed bound retains one measure-theoretic hypothesis KL term.

The construction reuses the fully discharged fixed-tilt theorem.  It exposes
no MGF, adaptedness, submartingale, or Fubini interface.  The catalog is finite,
full-support, and fixed before the data; this is not all-real optimization,
epoch stitching, a forward e-process, or a continuous observation-space
result.
-/

namespace FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse

open Finset BigOperators MeasureTheory
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF

noncomputable section

variable {κ Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]

/-- One posterior-independent bad event for every atom of a finite weighted
continuous-posterior tilt catalog. -/
def continuousReverseJointMeanVarianceEpochCatalogBadPaths
    [Fintype κ] [Fintype Z]
    (w : κ → ℝ) (prior : Measure Θ)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ)
    (t eta : κ → ℝ) (delta : ℝ) : Set (Fin N → Z) :=
  ⋃ c : κ, continuousReverseJointMeanVarianceEpochBadPaths
    prior N hN m p ell (t c) (eta c) (delta * w c)

/-- The weighted catalog master event has mass at most `delta`.

Each atom invokes the fully discharged fixed-tilt continuous theorem at
confidence `delta * w c`; finite subadditivity and `sum w = 1` close the
catalog. -/
theorem continuousReverseJointMeanVarianceEpochCatalogBadPaths_mass_le_delta
    [Fintype κ] [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (w : κ → ℝ) (hw : IsFullSupportPMF w)
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : κ → ℝ)
    (ht : ∀ c, 0 ≤ t c) (heta : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochCatalogBadPaths
          w prior N hN m p ell t eta delta) ≤ ENNReal.ofReal delta := by
  classical
  let muN : Measure (Fin N → Z) :=
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  have hentry (c : κ) :
      muN (continuousReverseJointMeanVarianceEpochBadPaths
        prior N hN m p ell (t c) (eta c) (delta * w c)) ≤
        ENNReal.ofReal (delta * w c) := by
    exact
      continuousReverseJointMeanVarianceEpochBadPaths_mass_le_delta_of_measurable_bounded
        prior N m hN hm p hp ell hell_meas hell
        (ht c) (heta c) (hkappa c) (mul_pos hdelta (hw.pos c))
  unfold continuousReverseJointMeanVarianceEpochCatalogBadPaths
  change muN (⋃ c : κ, continuousReverseJointMeanVarianceEpochBadPaths
    prior N hN m p ell (t c) (eta c) (delta * w c)) ≤
      ENNReal.ofReal delta
  calc
    muN (⋃ c : κ, continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell (t c) (eta c) (delta * w c)) ≤
        ∑' c : κ, muN (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell (t c) (eta c) (delta * w c)) :=
      measure_iUnion_le _
    _ ≤ ∑' c : κ, ENNReal.ofReal (delta * w c) :=
      ENNReal.tsum_le_tsum hentry
    _ = ∑ c : κ, ENNReal.ofReal (delta * w c) := by rw [tsum_fintype]
    _ = ENNReal.ofReal (∑ c : κ, delta * w c) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg
        (fun c _ ↦ mul_nonneg hdelta.le (hw.nonneg c))
    _ = ENNReal.ofReal delta := by
      congr 1
      rw [← Finset.mul_sum, hw.sum_one, mul_one]

omit [MeasurableSpace Z] in
/-- Outside the catalog event, one declared atom inherits the fixed-tilt
continuous-posterior risk theorem and pays `log (1 / (delta * w c))`.
There is still exactly one measure-theoretic hypothesis KL term. -/
theorem continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
    [Fintype κ] [Fintype Z]
    (w : κ → ℝ) (hw : IsFullSupportPMF w)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : κ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (x : Fin N → Z)
    (hx : x ∉ continuousReverseJointMeanVarianceEpochCatalogBadPaths
      w prior N hN m p ell t eta delta)
    (c : κ) (htc : 0 < t c) (heta_c : 0 ≤ eta c)
    (hkappa_c : 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    (hbalance :
      (m : ℝ) * (Real.exp (t c) - 1 - t c) ≤
        Real.exp (-t c) * finiteJointMeanVarianceKappa m (eta c))
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / (delta * w c))) / (t c * (m : ℝ)) +
        (eta c / t c) *
          (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) := by
  have hfixed : x ∉ continuousReverseJointMeanVarianceEpochBadPaths
      prior N hN m p ell (t c) (eta c) (delta * w c) := by
    intro hbad
    exact hx (Set.mem_iUnion.mpr ⟨c, hbad⟩)
  exact
    continuousReverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem_of_measurable_bounded
      prior posterior hposteriorPrior N m s hN hm hms hsN p hp ell
      hell_meas hell htc heta_c hkappa_c hbalance
      (mul_pos hdelta (hw.pos c)) x hfixed hllr

omit [MeasurableSpace Z] in
/-- A catalog atom may be selected from the observed horizon path and the
posterior because the common event already controls every atom.  Selection
adds only the declared weight penalty, not a second hypothesis KL term. -/
theorem continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_selected_of_not_mem
    [Fintype κ] [Fintype Z]
    (w : κ → ℝ) (hw : IsFullSupportPMF w)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : κ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (select : (Fin N → Z) → Measure Θ → κ)
    (ht : ∀ c, 0 < t c) (heta_nonneg : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    (hbalance : ∀ c,
      (m : ℝ) * (Real.exp (t c) - 1 - t c) ≤
        Real.exp (-t c) * finiteJointMeanVarianceKappa m (eta c))
    (x : Fin N → Z)
    (hx : x ∉ continuousReverseJointMeanVarianceEpochCatalogBadPaths
      w prior N hN m p ell t eta delta)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / (delta * w (select x posterior)))) /
            (t (select x posterior) * (m : ℝ)) +
        (eta (select x posterior) / t (select x posterior)) *
          (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) := by
  exact
    continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_of_not_mem
      w hw prior posterior hposteriorPrior N m s hN hm hms hsN p hp ell
      hell_meas hell t eta hdelta x hx (select x posterior)
      (ht _) (heta_nonneg _) (hkappa _) (hbalance _) hllr

/-- Existential good-event form of the selected continuous-posterior catalog
bound for a fixed posterior and selector.  The exhibited bad event itself is
posterior-independent. -/
theorem exists_continuousReverseJointMeanVarianceEpochCatalog_goodEvent
    [Fintype κ] [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (w : κ → ℝ) (hw : IsFullSupportPMF w)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : κ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (select : (Fin N → Z) → Measure Θ → κ)
    (ht : ∀ c, 0 < t c) (heta_nonneg : ∀ c, 0 ≤ eta c)
    (hkappa : ∀ c, 0 ≤ finiteJointMeanVarianceKappa m (eta c))
    (hbalance : ∀ c,
      (m : ℝ) * (Real.exp (t c) - 1 - t c) ≤
        Real.exp (-t c) * finiteJointMeanVarianceKappa m (eta c))
    (hllr : Integrable (llr posterior prior) posterior) :
    ∃ bad : Set (Fin N → Z),
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure) bad ≤
        ENNReal.ofReal delta ∧
      ∀ x ∉ bad,
        (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
          (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
            ((InformationTheory.klDiv posterior prior).toReal +
              Real.log (1 / (delta * w (select x posterior)))) /
                (t (select x posterior) * (m : ℝ)) +
            (eta (select x posterior) / t (select x posterior)) *
              (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
                ∂posterior) := by
  let bad := continuousReverseJointMeanVarianceEpochCatalogBadPaths
    w prior N hN m p ell t eta delta
  refine ⟨bad, ?_, ?_⟩
  · exact continuousReverseJointMeanVarianceEpochCatalogBadPaths_mass_le_delta
      w hw prior N m hN ⟨hm, hms.trans hsN⟩ p hp ell hell_meas hell
      t eta (fun c ↦ (ht c).le) heta_nonneg hkappa hdelta
  · intro x hx
    exact
      continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_selected_of_not_mem
        w hw prior posterior hposteriorPrior N m s hN hm hms hsN p hp ell
        hell_meas hell t eta hdelta select ht heta_nonneg hkappa hbalance
        x hx hllr

end

end FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse
