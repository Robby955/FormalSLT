import FormalSLT.PACBayes.McAllesterBound

/-!
# General-width McAllester PAC-Bayes finite certificate surface

This module widens the q053 `[0, 1]` McAllester compiler surface to losses in
`[0, b]` for an explicit loss bound `b ≥ 0`. The proof is a scaling argument:
for `b > 0`, normalize the loss by `b`, apply the existing unit-width theorem,
and scale the square-root penalty back to `b * sqrt(C / (2n))`. The `b = 0`
case is handled separately: the bounded-loss hypotheses force every loss value
to be zero, so the bad event is empty.

Reference: McAllester, D.A. (1999). "PAC-Bayesian model averaging."
-/

namespace FormalSLT.PACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBoundedLoss

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The square-root McAllester penalty scaled by an explicit loss bound. -/
def mcAllesterGeneralPenalty (n : ℕ) (complexityBound lossBound : ℝ) : ℝ :=
  lossBound * mcAllesterPenalty n complexityBound

/-- Samples on which some posterior violates the fixed-budget general-width bound. -/
def mcAllesterGeneralBadSamples {ι Z : Type*} {n : ℕ} [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (loss : ι → Z → ℝ)
    (complexityBound delta lossBound : ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S : Fin n → Z =>
    ∃ posterior : ι → ℝ,
      IsPMF posterior ∧
        klDiv posterior prior + Real.log (1 / delta) ≤ complexityBound ∧
        posteriorPopulationRisk p loss posterior >
          posteriorEmpiricalRisk loss posterior S +
            mcAllesterGeneralPenalty n complexityBound lossBound

private lemma posteriorPopulationRisk_div_const {ι Z : Type*}
    [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (loss : ι → Z → ℝ) (posterior : ι → ℝ) (b : ℝ) :
    posteriorPopulationRisk p (fun i z => loss i z / b) posterior =
      posteriorPopulationRisk p loss posterior / b := by
  unfold posteriorPopulationRisk PACBayesBoundedLoss.posteriorAverage finitePopulationRisk
  calc
    (∑ i, posterior i * (∑ z, p z * (loss i z / b))) =
        ∑ i, (posterior i * (∑ z, p z * loss i z)) / b := by
          refine Finset.sum_congr rfl (fun i _hi => ?_)
          have hinner :
              (∑ z, p z * (loss i z / b)) =
                (∑ z, p z * loss i z) / b := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun z _hz => ?_)
            ring
          rw [hinner]
          ring
      _ = (∑ i, posterior i * (∑ z, p z * loss i z)) / b := by
          rw [Finset.sum_div]

private lemma finiteEmpiricalRisk_div_const {ι Z : Type*}
    {n : ℕ} (loss : ι → Z → ℝ) (i : ι) (S : Fin n → Z) (b : ℝ) :
    finiteEmpiricalRisk (fun i z => loss i z / b) i S =
      finiteEmpiricalRisk loss i S / b := by
  unfold finiteEmpiricalRisk
  rw [← Finset.sum_div]
  ring

private lemma posteriorEmpiricalRisk_div_const {ι Z : Type*}
    {n : ℕ} [Fintype ι]
    (loss : ι → Z → ℝ) (posterior : ι → ℝ) (S : Fin n → Z) (b : ℝ) :
    PACBayesBoundedLoss.posteriorEmpiricalRisk (fun i z => loss i z / b) posterior S =
      PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S / b := by
  unfold PACBayesBoundedLoss.posteriorEmpiricalRisk PACBayesBoundedLoss.posteriorAverage
  calc
    (∑ i, posterior i * finiteEmpiricalRisk (fun i z => loss i z / b) i S) =
        ∑ i, (posterior i * finiteEmpiricalRisk loss i S) / b := by
          refine Finset.sum_congr rfl (fun i _hi => ?_)
          rw [finiteEmpiricalRisk_div_const]
          ring
      _ = (∑ i, posterior i * finiteEmpiricalRisk loss i S) / b := by
          rw [Finset.sum_div]

/--
Finite McAllester PAC-Bayes bad-event theorem for losses bounded in `[0, b]`.

For a finite product sample with data law `p`, the total sample mass of samples
admitting a posterior inside the stated complexity budget but violating

`R(ρ) ≤ Rhat_S(ρ) + b * sqrt(C / (2n))`

is at most `delta`.
-/
theorem mcAllesterBoundGeneral_badEventMass_le_delta
    {ι Z : Type*} {n : ℕ}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (loss : ι → Z → ℝ) {complexityBound delta lossBound : ℝ}
    (hcomplexityBound : 0 < complexityBound) (hdelta : 0 < delta)
    (hlossBound : 0 ≤ lossBound)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ loss i z ∧ loss i z ≤ lossBound) :
    (∑ S ∈ mcAllesterGeneralBadSamples (n := n) p prior loss
        complexityBound delta lossBound,
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  by_cases hb_zero : lossBound = 0
  · have hloss_zero : ∀ i : ι, ∀ z : Z, loss i z = 0 := by
      intro i z
      exact le_antisymm (by simpa [hb_zero] using (hloss i z).2) (hloss i z).1
    have hempty :
        mcAllesterGeneralBadSamples (n := n) p prior loss
          complexityBound delta lossBound = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      simp only [mcAllesterGeneralBadSamples, Finset.mem_filter] at hS
      rcases hS.2 with ⟨posterior, _hposterior, _hcomplexity, hbad⟩
      have hpop : posteriorPopulationRisk p loss posterior = 0 := by
        unfold posteriorPopulationRisk PACBayesBoundedLoss.posteriorAverage finitePopulationRisk
        simp [hloss_zero]
      have hemp : PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S = 0 := by
        unfold PACBayesBoundedLoss.posteriorEmpiricalRisk
          PACBayesBoundedLoss.posteriorAverage finiteEmpiricalRisk
        simp [hloss_zero]
      have hpen : mcAllesterGeneralPenalty n complexityBound lossBound = 0 := by
        simp [mcAllesterGeneralPenalty, hb_zero]
      linarith
    rw [hempty]
    simp [hdelta.le]
  · have hb_pos : 0 < lossBound := lt_of_le_of_ne hlossBound (Ne.symm hb_zero)
    let normalizedLoss : ι → Z → ℝ := fun i z => loss i z / lossBound
    have hnormalized :
        ∀ i : ι, ∀ z : Z, 0 ≤ normalizedLoss i z ∧ normalizedLoss i z ≤ 1 := by
      intro i z
      constructor
      · exact div_nonneg (hloss i z).1 hb_pos.le
      · exact (div_le_one hb_pos).2 (hloss i z).2
    have hstrong :
        (∑ S ∈ mcAllesterBadSamples (n := n) p prior normalizedLoss
            complexityBound delta,
            finiteProductSampleWeight p S) ≤ delta :=
      mcAllesterBoundedLoss_badEventMass_le_delta
        (n := n) hn p hp prior hprior normalizedLoss
        hcomplexityBound hdelta hnormalized
    have hsubset :
        mcAllesterGeneralBadSamples (n := n) p prior loss
            complexityBound delta lossBound ⊆
          mcAllesterBadSamples (n := n) p prior normalizedLoss
            complexityBound delta := by
      intro S hS
      simp only [mcAllesterGeneralBadSamples, mcAllesterBadSamples,
        Finset.mem_filter] at hS ⊢
      rcases hS.2 with ⟨posterior, hposterior, hcomplexity, hbad⟩
      refine ⟨hS.1, posterior, hposterior, hcomplexity, ?_⟩
      have hdiv :=
        div_lt_div_of_pos_right hbad hb_pos
      have hpop :=
        posteriorPopulationRisk_div_const p loss posterior lossBound
      have hemp :=
        posteriorEmpiricalRisk_div_const loss posterior S lossBound
      have hpen :
          (PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S +
              mcAllesterGeneralPenalty n complexityBound lossBound) / lossBound =
            PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S / lossBound +
              mcAllesterPenalty n complexityBound := by
        unfold mcAllesterGeneralPenalty
        field_simp [hb_zero]
      rw [hpen] at hdiv
      rw [← hpop, ← hemp] at hdiv
      exact hdiv
    have hmass_le :
        (∑ S ∈ mcAllesterGeneralBadSamples (n := n) p prior loss
            complexityBound delta lossBound,
            finiteProductSampleWeight p S) ≤
          ∑ S ∈ mcAllesterBadSamples (n := n) p prior normalizedLoss
            complexityBound delta,
            finiteProductSampleWeight p S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro S _hS _hnot
        unfold finiteProductSampleWeight
        exact Finset.prod_nonneg (fun k _hk => hp.nonneg (S k)))
    exact hmass_le.trans hstrong

end

end FormalSLT.PACBayes
