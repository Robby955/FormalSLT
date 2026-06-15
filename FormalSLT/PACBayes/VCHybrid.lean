import FormalSLT.PACBayes.BernsteinBound
import FormalSLT.Probability.FiniteUnionBound
import FormalSLT.VC.SampleComplexity

/-!
# VC / PAC-Bayes hybrid bound

This module combines two existing finite-sample spines:

* the Sauer-Shelah/VC capacity scale from `FormalSLT.VC.SampleComplexity`;
* the finite PAC-Bayes Bernstein change-of-measure penalty from
  `FormalSLT.PACBayes.BernsteinBound`.

The high-probability glue is the finite weighted union bound: a VC bad event
and a PAC-Bayes Bernstein bad event are joined into one hybrid bad event.
-/

open scoped BigOperators

namespace FormalSLT.PACBayes.VCHybrid

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.Probability.FiniteUnionBound

noncomputable section

variable {Ω ι : Type*}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The Sauer-Shelah/VC capacity scale appearing in the VC sample-complexity bound. -/
def vcCapacityTerm (B : ℝ) (n d : ℕ) : ℝ :=
  2 * B * Real.sqrt (2 * (d : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (d : ℝ)) / (n : ℝ))

/-- The VC capacity term is nonnegative for a nonnegative loss envelope. -/
theorem vcCapacityTerm_nonneg {B : ℝ} {n d : ℕ} (hB : 0 ≤ B) :
    0 ≤ vcCapacityTerm B n d := by
  unfold vcCapacityTerm
  positivity

private lemma finiteEventMass_univ_eq_sum [Fintype Ω] [DecidableEq Ω]
    (ν : Ω → ℝ) (event : Finset Ω) :
    finiteEventMass (Finset.univ : Finset Ω) ν event = ∑ ω ∈ event, ν ω := by
  classical
  unfold finiteEventMass
  rw [← Finset.sum_filter]
  simp

/--
The hybrid bad samples are a finite union of the supplied VC bad event and the
finite PAC-Bayes Bernstein fixed-`lambda` bad event.
-/
def vcPacBayesHybridBadSamples [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    (vcBad : Finset Ω) (π : ι → ℝ) (lambda scale delta : ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) : Finset Ω :=
  (Finset.univ : Finset Bool).biUnion fun usePAC =>
    if usePAC then
      finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
        riskFn empiricalRiskFn varianceProxy
    else
      vcBad

/--
Finite hybrid bad-event mass bound.

The proof uses the finite weighted union bound to combine an externally
supplied VC bad-event budget with the finite PAC-Bayes Bernstein bad-event
budget. The PAC-Bayes budget is derived from the existing Bernstein prior
moment theorem, not assumed as a free bad-event mass.
-/
theorem vcPacBayesHybridBadEventMass_le
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ν : Ω → ℝ} (hν : IsPMF ν)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (vcBad : Finset Ω)
    (lambda scale deltaVC deltaPAC : ℝ)
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdeltaPAC : 0 < deltaPAC)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ)
    (hVC :
      (∑ ω ∈ vcBad, ν ω) ≤ deltaVC)
    (hExpected :
      expectedPriorBernsteinExpMoment ν π lambda scale riskFn empiricalRiskFn
        varianceProxy ≤ 1) :
    (∑ ω ∈
        vcPacBayesHybridBadSamples vcBad π lambda scale deltaPAC
          riskFn empiricalRiskFn varianceProxy,
        ν ω) ≤ deltaVC + deltaPAC := by
  classical
  let pacBad : Finset Ω :=
    finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale deltaPAC
      riskFn empiricalRiskFn varianceProxy
  let events : Bool → Finset Ω := fun usePAC => if usePAC then pacBad else vcBad
  have hUnion :
      finiteUnionEventMass (Finset.univ : Finset Ω) ν events (Finset.univ : Finset Bool)
        ≤ finiteEventMassSum (Finset.univ : Finset Ω) ν events (Finset.univ : Finset Bool) :=
    finiteProbabilityUnionBound_proof (support := (Finset.univ : Finset Ω)) (w := ν)
      (events := events) (s := (Finset.univ : Finset Bool)) hν.nonneg
  have hPAC_sum :
      (∑ ω ∈ pacBad, ν ω) ≤ deltaPAC := by
    dsimp [pacBad]
    exact finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
      hν hπ lambda scale deltaPAC hlambda hscale hdeltaPAC
      riskFn empiricalRiskFn varianceProxy hExpected
  have hPAC :
      finiteEventMass (Finset.univ : Finset Ω) ν pacBad ≤ deltaPAC := by
    simpa [finiteEventMass_univ_eq_sum ν pacBad] using hPAC_sum
  have hVCmass :
      finiteEventMass (Finset.univ : Finset Ω) ν vcBad ≤ deltaVC := by
    simpa [finiteEventMass_univ_eq_sum ν vcBad] using hVC
  have hsum :
      finiteEventMassSum (Finset.univ : Finset Ω) ν events (Finset.univ : Finset Bool)
        ≤ deltaVC + deltaPAC := by
    dsimp [finiteEventMassSum, events]
    simpa [Bool.forall_bool, add_comm] using add_le_add hPAC hVCmass
  have hmass :
      finiteEventMass (Finset.univ : Finset Ω) ν
          (vcPacBayesHybridBadSamples vcBad π lambda scale deltaPAC
            riskFn empiricalRiskFn varianceProxy)
        ≤ deltaVC + deltaPAC := by
    simpa [finiteUnionEventMass, vcPacBayesHybridBadSamples, pacBad, events] using
      hUnion.trans hsum
  simpa [finiteEventMass_univ_eq_sum ν
    (vcPacBayesHybridBadSamples vcBad π lambda scale deltaPAC
      riskFn empiricalRiskFn varianceProxy)] using hmass

/--
Pointwise hybrid posterior-risk bound on the complement of the hybrid bad
event.

The right-hand side carries both spines: the Sauer-Shelah/VC capacity term
`vcCapacityTerm B n d`, and the PAC-Bayes KL change-of-measure term
`(klDiv ρ π + log (1 / delta)) / lambda`, plus the Bernstein variance term.
-/
theorem vcPacBayesBernsteinPosteriorRisk_bound
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ)
    (vcBad : Finset Ω)
    {lambda scale delta B : ℝ} {n d : ℕ}
    (empiricalAnchor : Ω → ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hVCGood :
      ∀ ω', ω' ∉ vcBad →
        posteriorEmpiricalRisk ρ (empiricalRiskFn ω') ≤
          empiricalAnchor ω' + vcCapacityTerm B n d)
    (hω :
      ω ∉ vcPacBayesHybridBadSamples vcBad π lambda scale delta
        riskFn empiricalRiskFn varianceProxy) :
    posteriorRisk ρ riskFn ≤
      empiricalAnchor ω +
        vcCapacityTerm B n d +
        (klDiv ρ π + Real.log (1 / delta)) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) := by
  classical
  let pacBad : Finset Ω :=
    finitePACBayesBernsteinFixedLambdaBadSamples π lambda scale delta
      riskFn empiricalRiskFn varianceProxy
  have hω_not_pac : ω ∉ pacBad := by
    intro hbad
    apply hω
    dsimp [vcPacBayesHybridBadSamples, pacBad]
    simpa [pacBad] using (Or.inl hbad : ω ∈ pacBad ∨ ω ∈ vcBad)
  have hω_not_vc : ω ∉ vcBad := by
    intro hbad
    apply hω
    dsimp [vcPacBayesHybridBadSamples, pacBad]
    simpa [pacBad] using (Or.inr hbad : ω ∈ pacBad ∨ ω ∈ vcBad)
  have hgap :
      posteriorGeneralizationGap ρ riskFn (empiricalRiskFn ω)
        ≤ (klDiv ρ π + Real.log (1 / delta)) / lambda +
          lambda * posteriorMarginVarianceProxy ρ varianceProxy /
            (2 * (1 - scale * lambda)) := by
    by_contra hnot
    have hbad : ω ∈ pacBad := by
      dsimp [pacBad, finitePACBayesBernsteinFixedLambdaBadSamples]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ ω, ρ, hρ, lt_of_not_ge hnot⟩
    exact hω_not_pac hbad
  have hbase :
      posteriorRisk ρ riskFn ≤
        posteriorEmpiricalRisk ρ (empiricalRiskFn ω) +
          (klDiv ρ π + Real.log (1 / delta)) / lambda +
          lambda * posteriorMarginVarianceProxy ρ varianceProxy /
            (2 * (1 - scale * lambda)) := by
    unfold posteriorGeneralizationGap at hgap
    linarith
  have hvc := hVCGood ω hω_not_vc
  linarith

end

end FormalSLT.PACBayes.VCHybrid
