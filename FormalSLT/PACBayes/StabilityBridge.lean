/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesBoundedLoss

/-!
# Stability-to-PAC-Bayes point-mass bridge

This module records the finite point-mass specialization of the existing
PAC-Bayes bounded-loss capstone.  A deterministic/stable learning rule outputs
a single hypothesis `h`; viewing that output as the degenerate posterior
`delta_h` turns the PAC-Bayes complexity term `KL(delta_h || pi)` into the
Occam-style code-length term `-log (pi h)`.

The composition route is deliberately narrow:

* finite hypothesis classes;
* finite data domains and iid product sample weights;
* bounded losses in `[0,1]`;
* point-mass posteriors only;
* no new concentration inequality.

The proof uses the existing `FormalSLT.PACBayesBoundedLoss.pac_bayes_generalization`
capstone, which itself is the bounded-loss confidence layer over the finite
change-of-measure machinery.  The only extra ingredients here are finite-sum
Dirac algebra and a monotone-event argument: the all-posteriors PAC-Bayes event
implies the point-mass event for the hypothesis selected by a deterministic
learner.

Sources checked for the surrounding mathematical framing:
McAllester (PAC-Bayes, 1999), Catoni (2007), and Bousquet-Elisseeff
(Stability and Generalization, JMLR 2002).  The formal contribution here is
composition and specialization of existing FormalSLT theorems, not new
mathematics.
-/

namespace FormalSLT.PACBayes.StabilityBridge

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBoundedLoss

noncomputable section

variable {ι Z : Type*}

/-- The point-mass posterior at a finite hypothesis. -/
def diracPosterior [DecidableEq ι] (h : ι) : ι → ℝ :=
  fun i => if i = h then 1 else 0

/-- A point-mass posterior is a finite PMF. -/
theorem diracPosterior_isPMF [Fintype ι] [DecidableEq ι] (h : ι) :
    IsPMF (diracPosterior h) := by
  classical
  constructor
  · intro i
    by_cases hi : i = h
    · simp [diracPosterior, hi]
    · simp [diracPosterior, hi]
  · unfold diracPosterior
    rw [Finset.sum_eq_single h]
    · simp
    · intro i _hi hih
      simp [hih]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ h))

/-- Finite Dirac-posteriors reduce posterior averages to point evaluation. -/
theorem posteriorAverage_dirac [Fintype ι] [DecidableEq ι]
    (h : ι) (g : ι → ℝ) :
    FormalSLT.PACBayesBoundedLoss.posteriorAverage (diracPosterior h) g = g h := by
  classical
  unfold FormalSLT.PACBayesBoundedLoss.posteriorAverage diracPosterior
  rw [Finset.sum_eq_single h]
  · simp
  · intro i _hi hih
    simp [hih]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ h))

/-- Posterior population risk at a point-mass posterior is the selected risk. -/
theorem posteriorPopulationRisk_dirac [Fintype Z] [Fintype ι] [DecidableEq ι]
    (p : Z → ℝ) (loss : ι → Z → ℝ) (h : ι) :
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss (diracPosterior h) =
      finitePopulationRisk p loss h := by
  unfold FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk
  exact posteriorAverage_dirac h (fun i => finitePopulationRisk p loss i)

/-- Posterior empirical risk at a point-mass posterior is the selected empirical risk. -/
theorem posteriorEmpiricalRisk_dirac {n : ℕ} [Fintype ι] [DecidableEq ι]
    (loss : ι → Z → ℝ) (S : Fin n → Z) (h : ι) :
    FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss (diracPosterior h) S =
      finiteEmpiricalRisk loss h S := by
  unfold FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk
  exact posteriorAverage_dirac h (fun i => finiteEmpiricalRisk loss i S)

private lemma finiteProductSampleWeight_nonneg {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S := by
  intro S
  unfold finiteProductSampleWeight
  exact Finset.prod_nonneg (fun k _hk => hp.nonneg (S k))

/--
Dirac-posterior KL identity:
`KL(delta_h || pi) = -log (pi h)` for a finite full-support prior mass at `h`.
-/
theorem diracPosterior_klDiv_eq_neg_log_prior
    [Fintype ι] [DecidableEq ι]
    (prior : ι → ℝ) (h : ι) (hprior_h : 0 < prior h) :
    klDiv (diracPosterior h) prior = - Real.log (prior h) := by
  classical
  have _hprior_ne : prior h ≠ 0 := ne_of_gt hprior_h
  unfold klDiv diracPosterior
  rw [Finset.sum_eq_single h]
  · simp [Real.log_inv, one_div]
  · intro i _hi hih
    simp [hih]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ h))

/--
Point-mass PAC-Bayes generalization: with probability at least `1 - delta`,
the deterministic learner output `A S` satisfies the PAC-Bayes bounded-loss
bound with the Dirac-posterior complexity term rewritten as `-log (prior (A S))`.
-/
theorem pointMass_pacBayes_generalization
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (loss : ι → Z → ℝ) (A : (Fin n → Z) → ι)
    (lam delta : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < delta)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ loss i z ∧ loss i z ≤ 1) :
    1 - delta ≤
      ∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        finitePopulationRisk p loss (A S) ≤
          finiteEmpiricalRisk loss (A S) S +
            (- Real.log (prior (A S)) + Real.log (1 / delta)) / lam +
            lam / (8 * (n : ℝ))),
        finiteProductSampleWeight p S := by
  classical
  let allPosteriorGood : (Fin n → Z) → Prop := fun S =>
    ∀ ρ : ι → ℝ, IsPMF ρ →
      FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss ρ ≤
        FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss ρ S +
          (klDiv ρ prior + Real.log (1 / delta)) / lam +
          lam / (8 * (n : ℝ))
  let pointGood : (Fin n → Z) → Prop := fun S =>
    finitePopulationRisk p loss (A S) ≤
      finiteEmpiricalRisk loss (A S) S +
        (- Real.log (prior (A S)) + Real.log (1 / delta)) / lam +
        lam / (8 * (n : ℝ))
  have hcap :
      1 - delta ≤
        ∑ S ∈ (Finset.univ.filter allPosteriorGood),
          finiteProductSampleWeight p S := by
    simpa [allPosteriorGood] using
      FormalSLT.PACBayesBoundedLoss.pac_bayes_generalization
        (Z := Z) (ι := ι) (n := n) hn p hp prior hprior loss lam delta
        hlam hdelta hloss
  have hsubset :
      Finset.univ.filter allPosteriorGood ⊆ Finset.univ.filter pointGood := by
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    rcases hS with ⟨hmem, hgood⟩
    refine ⟨hmem, ?_⟩
    have hdirac :=
      hgood (diracPosterior (A S)) (diracPosterior_isPMF (A S))
    have hkl :
        klDiv (diracPosterior (A S)) prior =
          - Real.log (prior (A S)) :=
      diracPosterior_klDiv_eq_neg_log_prior prior (A S) (hprior.pos (A S))
    have hpop :
        FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss
            (diracPosterior (A S)) =
          finitePopulationRisk p loss (A S) :=
      posteriorPopulationRisk_dirac p loss (A S)
    have hemp :
        FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss
            (diracPosterior (A S)) S =
          finiteEmpiricalRisk loss (A S) S :=
      posteriorEmpiricalRisk_dirac loss S (A S)
    simpa [pointGood, hpop, hemp, hkl] using hdirac
  have hmass :
      (∑ S ∈ (Finset.univ.filter allPosteriorGood),
          finiteProductSampleWeight p S) ≤
        ∑ S ∈ (Finset.univ.filter pointGood),
          finiteProductSampleWeight p S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun S _hpoint _hnot =>
        finiteProductSampleWeight_nonneg (Z := Z) (p := p) hp S)
  exact hcap.trans (by simpa [pointGood] using hmass)

/--
Fixed-hypothesis corollary of the point-mass PAC-Bayes bridge.  This is the
same event with the deterministic learner specialized to the constant rule
`S ↦ h`.
-/
theorem deterministicHypothesis_pacBayes_generalization
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (loss : ι → Z → ℝ) (h : ι)
    (lam delta : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < delta)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ loss i z ∧ loss i z ≤ 1) :
    1 - delta ≤
      ∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        finitePopulationRisk p loss h ≤
          finiteEmpiricalRisk loss h S +
            (- Real.log (prior h) + Real.log (1 / delta)) / lam +
            lam / (8 * (n : ℝ))),
        finiteProductSampleWeight p S := by
  simpa using
    pointMass_pacBayes_generalization
      (Z := Z) (ι := ι) (n := n) hn p hp prior hprior loss (fun _S => h)
      lam delta hlam hdelta hloss

end

end FormalSLT.PACBayes.StabilityBridge
