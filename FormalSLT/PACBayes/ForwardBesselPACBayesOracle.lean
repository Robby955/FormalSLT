/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.ForwardBesselPACBayesCountable

/-!
# Observable finite-prefix oracle for forward PAC-Bayes boundaries

The countable geometric tilt catalog is fixed before the data.  On its one
master event, this module minimizes the exact observable hybrid-Bessel
boundary over the growing prefix available at a reporting time.  The selected
atom may depend on the path, time, and posterior because every catalog atom is
already controlled on the same event.

This is an exact finite-prefix selector, not a global minimum over `Nat`, an
all-real optimizer, or a selected e-process.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable

namespace FormalSLT.PACBayes.ForwardBesselPACBayesOracle

noncomputable section

variable {ι Ω : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}

omit [DecidableEq ι] [Nonempty ι] in
private theorem countableForwardBesselPACBayesFinitePrefix_exists_argmin
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) :
    ∃ j ∈ Finset.range (maxIndex + 1),
      ∀ j' ∈ Finset.range (maxIndex + 1),
        countableForwardBesselPACBayesBoundary
            prior weight lam X posterior delta j n ω ≤
          countableForwardBesselPACBayesBoundary
            prior weight lam X posterior delta j' n ω := by
  exact (Finset.range (maxIndex + 1)).exists_min_image
    (fun j ↦ countableForwardBesselPACBayesBoundary
      prior weight lam X posterior delta j n ω)
    (by simp)

/-- An exact minimizer of the observable boundary over atoms
`0, ..., maxIndex`. -/
def countableForwardBesselPACBayesFinitePrefixArgmin
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) : ℕ :=
  Classical.choose
    (countableForwardBesselPACBayesFinitePrefix_exists_argmin
      prior weight lam X posterior delta maxIndex n ω)

omit [DecidableEq ι] [Nonempty ι] in
/-- The finite-prefix minimizer is one of the declared candidate atoms. -/
theorem countableForwardBesselPACBayesFinitePrefixArgmin_mem
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) :
    countableForwardBesselPACBayesFinitePrefixArgmin
        prior weight lam X posterior delta maxIndex n ω ∈
      Finset.range (maxIndex + 1) := by
  exact
    (Classical.choose_spec
      (countableForwardBesselPACBayesFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n ω)).1

omit [DecidableEq ι] [Nonempty ι] in
/-- The selected boundary is no larger than any candidate boundary in the
declared prefix. -/
theorem countableForwardBesselPACBayesFinitePrefixArgmin_le
    (prior : ι → ℝ) (weight lam : ℕ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ) (delta : ℝ)
    (maxIndex n : ℕ) (ω : Ω) {j : ℕ}
    (hj : j ∈ Finset.range (maxIndex + 1)) :
    countableForwardBesselPACBayesBoundary
        prior weight lam X posterior delta
          (countableForwardBesselPACBayesFinitePrefixArgmin
            prior weight lam X posterior delta maxIndex n ω)
          n ω ≤
      countableForwardBesselPACBayesBoundary
        prior weight lam X posterior delta j n ω := by
  exact
    (Classical.choose_spec
      (countableForwardBesselPACBayesFinitePrefix_exists_argmin
        prior weight lam X posterior delta maxIndex n ω)).2 j hj

/-- The growing prefix extends two atoms past the standard all-time index.
Those finer tilts are needed for a variance-adaptive square-root oracle while
the standard atom remains available as a worst-case-rate benchmark. -/
def growingPrefixForwardBesselPACBayesMaxIndex (n : ℕ) : ℕ :=
  geometricForwardTiltIndex n + 2

/-- The observable selector over the growing geometric prefix at time `n`. -/
def growingPrefixForwardBesselPACBayesArgmin
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  countableForwardBesselPACBayesFinitePrefixArgmin
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The growing-prefix selector belongs to its declared candidate prefix. -/
theorem growingPrefixForwardBesselPACBayesArgmin_mem
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) :
    growingPrefixForwardBesselPACBayesArgmin
        prior X posterior delta n ω ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
  exact countableForwardBesselPACBayesFinitePrefixArgmin_mem
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω

omit [DecidableEq ι] [Nonempty ι] in
/-- The observable selector improves on every geometric atom in the growing
prefix. -/
theorem growingPrefixForwardBesselPACBayesArgmin_le
    (prior : ι → ℝ) (X : ι → ℕ → Ω → ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (n : ℕ) (ω : Ω) {j : ℕ}
    (hj : j ∈ Finset.range
      (growingPrefixForwardBesselPACBayesMaxIndex n + 1)) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta j n ω := by
  exact countableForwardBesselPACBayesFinitePrefixArgmin_le
    prior polynomialForwardTiltWeight geometricForwardTilt X posterior delta
      (growingPrefixForwardBesselPACBayesMaxIndex n) n ω hj

omit [DecidableEq ι] [Nonempty ι] in
/-- The observable selector is bounded by the existing all-time deterministic
rate because the standard geometric atom remains in its candidate prefix. -/
theorem growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
    {prior posterior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (hposterior : IsPMF posterior)
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) (ω : Ω) :
    countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X posterior
          delta (growingPrefixForwardBesselPACBayesArgmin
            prior X posterior delta n ω) n ω ≤
      allTimeGeometricPolynomialForwardRate
        (fun _ ↦ klDiv posterior prior) delta n := by
  have hcandidate : geometricForwardTiltIndex n ∈
      Finset.range (growingPrefixForwardBesselPACBayesMaxIndex n + 1) := by
    simp [growingPrefixForwardBesselPACBayesMaxIndex]
  exact (growingPrefixForwardBesselPACBayesArgmin_le
    prior X posterior delta n ω hcandidate).trans
      (countableForwardBesselPACBayesBoundary_selected_le_allTimeRate
        hprior hposterior hdelta hdelta1 hX hn ω)

omit [DecidableEq ι] [Nonempty ι] in
/-- The exact observable oracle width vanishes for arbitrary time-varying
finite posteriors. -/
theorem growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    (posterior : ℕ → ι → ℝ) (hposterior : ∀ n, IsPMF (posterior n))
    {X : ι → ℕ → Ω → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (ω : Ω) :
    Filter.Tendsto
      (fun n ↦ countableForwardBesselPACBayesBoundary
        prior polynomialForwardTiltWeight geometricForwardTilt X
          (posterior n) delta
          (growingPrefixForwardBesselPACBayesArgmin
            prior X (posterior n) delta n ω) n ω)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact countableForwardBesselPACBayesBoundary_nonneg
      hprior (hposterior n) hdelta hdelta1 hX
      (growingPrefixForwardBesselPACBayesArgmin
        prior X (posterior n) delta n ω) n hn ω
  · exact Filter.Eventually.of_forall fun n ↦
      growingPrefixForwardBesselPACBayesArgmin_le
        prior X (posterior n) delta n ω
          (j := geometricForwardTiltIndex n) (by
            simp only [Finset.mem_range]
            unfold growingPrefixForwardBesselPACBayesMaxIndex
            omega)
  · exact countableForwardBesselPACBayesBoundary_selected_tendsto_zero
      hprior posterior hposterior hdelta hdelta1 hX ω

/-- One countable-master event supports post-data minimization of the exact
observable boundary over every growing geometric prefix.  The selected width
also vanishes along all integer times. -/
theorem exists_growingPrefixForwardBesselPACBayesOracle_event
    [IsProbabilityMeasure μ]
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ}
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i)
    (posterior : Ω → ℕ → ι → ℝ)
    (hposterior : ∀ ω n, IsPMF (posterior ω n)) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        (∀ ω ∈ goodEvent, ∀ n : ℕ, 4 ≤ n →
          let selected := growingPrefixForwardBesselPACBayesArgmin
            prior X (posterior ω n) delta n ω
          selected ∈ Finset.range
              (growingPrefixForwardBesselPACBayesMaxIndex n + 1) ∧
            posteriorAverage (posterior ω n) mean <
              posteriorAverage (posterior ω n)
                  (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                countableForwardBesselPACBayesBoundary
                  prior polynomialForwardTiltWeight geometricForwardTilt X
                    (posterior ω n) delta selected n ω ∧
            countableForwardBesselPACBayesBoundary
                prior polynomialForwardTiltWeight geometricForwardTilt X
                  (posterior ω n) delta selected n ω ≤
              allTimeGeometricPolynomialForwardRate
                (fun _ ↦ klDiv (posterior ω n) prior) delta n) ∧
        (∀ ω ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ countableForwardBesselPACBayesBoundary
              prior polynomialForwardTiltWeight geometricForwardTilt X
                (posterior ω n) delta
                (growingPrefixForwardBesselPACBayesArgmin
                  prior X (posterior ω n) delta n ω) n ω)
            Filter.atTop (nhds 0)) := by
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_geometricForwardBesselPACBayes_event
      hprior hdelta hX_adapted hX_unit hmean
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro ω hω n hn
    let selected := growingPrefixForwardBesselPACBayesArgmin
      prior X (posterior ω n) delta n ω
    have hselected_mem : selected ∈
        Finset.range
          (growingPrefixForwardBesselPACBayesMaxIndex n + 1) :=
      growingPrefixForwardBesselPACBayesArgmin_mem
        prior X (posterior ω n) delta n ω
    have hrisk := hgood ω hω selected (posterior ω n)
      (hposterior ω n) n (by omega)
    have hrate := growingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
      hprior (hposterior ω n) hdelta hdelta1 hX_unit hn ω
    exact ⟨hselected_mem, hrisk, hrate⟩
  · intro ω _hω
    exact growingPrefixForwardBesselPACBayesBoundary_tendsto_zero
      hprior (posterior ω) (hposterior ω) hdelta hdelta1 hX_unit ω

end

end FormalSLT.PACBayes.ForwardBesselPACBayesOracle
