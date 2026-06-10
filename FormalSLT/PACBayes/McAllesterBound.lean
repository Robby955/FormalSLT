import FormalSLT.PACBayesBoundedLoss

/-!
# McAllester PAC-Bayes finite certificate surface

This module packages the finite bounded-loss McAllester statement in the
shape used by the certificate compiler. The proof is delegated to the existing
finite bounded-loss shell: finite data domain, finite hypothesis index,
full-support prior, finite posterior, `[0, 1]` loss, and fixed positive
posterior-complexity budget.

Reference: McAllester, D.A. (1999). "PAC-Bayesian model averaging."
-/

namespace FormalSLT.PACBayes

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBoundedLoss

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The square-root McAllester penalty for a fixed complexity budget. -/
def mcAllesterPenalty (n : ℕ) (complexityBound : ℝ) : ℝ :=
  Real.sqrt (complexityBound / (2 * (n : ℝ)))

/-- Samples on which some posterior violates the fixed-budget McAllester bound. -/
def mcAllesterBadSamples {ι Z : Type*} {n : ℕ} [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (loss : ι → Z → ℝ)
    (complexityBound delta : ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S : Fin n → Z =>
    ∃ posterior : ι → ℝ,
      IsPMF posterior ∧
        klDiv posterior prior + Real.log (1 / delta) ≤ complexityBound ∧
        posteriorPopulationRisk p loss posterior >
          posteriorEmpiricalRisk loss posterior S +
            mcAllesterPenalty n complexityBound

/--
Finite McAllester PAC-Bayes bad-event theorem for `[0, 1]` losses.

For a finite product sample with data law `p`, the total sample mass of
samples admitting a posterior inside the stated complexity budget but violating
the McAllester square-root posterior-risk bound is at most `delta`.
-/
theorem mcAllesterBoundedLoss_badEventMass_le_delta
    {ι Z : Type*} {n : ℕ}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (loss : ι → Z → ℝ) {complexityBound delta : ℝ}
    (hcomplexityBound : 0 < complexityBound) (hdelta : 0 < delta)
    (hloss : ∀ i : ι, ∀ z : Z, 0 ≤ loss i z ∧ loss i z ≤ 1) :
    (∑ S ∈ mcAllesterBadSamples (n := n) p prior loss complexityBound delta,
        finiteProductSampleWeight p S) ≤ delta := by
  simpa [mcAllesterBadSamples, mcAllesterPenalty] using
    finiteMcAllesterBoundedComplexity_badEventMass_le_delta
      (n := n) hn p hp prior hprior loss
      (hcomplexityBound := hcomplexityBound)
      (hdelta := hdelta)
      hloss

end

end FormalSLT.PACBayes
