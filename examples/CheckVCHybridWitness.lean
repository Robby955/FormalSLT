import FormalSLT.PACBayes.VCHybrid

/-!
# VC / PAC-Bayes hybrid: GENUINE concrete witness (adversarial non-vacuity check)

This file does NOT just `#check` the theorem. It instantiates
`vcPacBayesBernsteinPosteriorRisk_bound` on an explicit finite instance and
PROVES every hypothesis constructively, then reads off a concrete numeric
conclusion. This demonstrates joint satisfiability of all hypotheses with a
non-trivial conclusion.

Instance:
* `Ω = ι = Unit` (one sample outcome, one hypothesis).
* posterior `ρ = 1` (the only PMF on `Unit`).
* prior `π = 1`.
* `riskFn () = 3/10`, `empiricalRiskFn () () = 1/2`, `varianceProxy () = 1/10`.
* `vcBad = ∅`, `lambda = 1`, `scale = 0`, `delta = 1`, `B = 0`, `n = d = 0`.
* `empiricalAnchor () = 1/2`.

Because `riskFn ≤ empiricalRiskFn` pointwise here, the posterior gap is `≤ 0`
while the Bernstein RHS is `≥ 0`, so no posterior violates and the hybrid bad
set is genuinely empty. Hence `() ∉ hybridBad` is provable, and `hVCGood` holds
over the real element `()` (which is in the complement of `vcBad = ∅`).
-/

namespace FormalSLT.PACBayes.VCHybrid.Witness

open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayes.VCHybrid

noncomputable section

/-- The only PMF on `Unit`: the constant `1`. -/
def rhoU : Unit → ℝ := fun _ => 1
def piU : Unit → ℝ := fun _ => 1
def riskU : Unit → ℝ := fun _ => 3 / 10
def empRiskU : Unit → Unit → ℝ := fun _ _ => 1 / 2
def varU : Unit → ℝ := fun _ => 1 / 10
def anchorU : Unit → ℝ := fun _ => 1 / 2

theorem rhoU_isPMF : IsPMF rhoU where
  nonneg := by intro i; simp [rhoU]
  sum_one := by simp [rhoU]

/-- The hybrid bad set is genuinely EMPTY on this instance: no posterior can
violate the Bernstein bound because the gap is `≤ 0` and the RHS is `≥ 0`. -/
theorem hybridBad_empty :
    vcPacBayesHybridBadSamples (Ω := Unit) (ι := Unit)
        (∅ : Finset Unit) piU (1 : ℝ) (0 : ℝ) (1 : ℝ) riskU empRiskU varU = ∅ := by
  classical
  ext ω
  simp only [Finset.notMem_empty, iff_false]
  intro hmem
  -- unfold hybrid bad membership
  rw [vcPacBayesHybridBadSamples, Finset.mem_biUnion] at hmem
  obtain ⟨usePAC, _, hev⟩ := hmem
  rcases usePAC with _ | _
  · -- usePAC = false branch is `vcBad = ∅`
    simp at hev
  · -- usePAC = true branch: PAC bad event. Show it is empty.
    rw [if_pos rfl, finitePACBayesBernsteinFixedLambdaBadSamples,
      Finset.mem_filter] at hev
    obtain ⟨_, ρ, hρ, hbad⟩ := hev
    -- gap ≤ 0, RHS ≥ 0, contradiction with strict >
    have hsum : ∑ i : Unit, ρ i = 1 := hρ.sum_one
    have hρu : ρ () = 1 := by simpa using hsum
    -- posteriorGeneralizationGap = posteriorRisk - posteriorEmpiricalRisk
    --                            = ρ()*risk - ρ()*emprisk = 1*(3/10 - 1/2) = -1/5
    have hgapval :
        posteriorGeneralizationGap ρ riskU (empRiskU ω) = -(1 / 5) := by
      rw [posteriorGeneralizationGap_eq_sum]
      simp [riskU, empRiskU, hρu]
      norm_num
    -- klDiv ρ π = ρ()*log(ρ()/π()) = 1*log(1/1) = 0
    have hkl : klDiv ρ piU = 0 := by
      unfold klDiv
      simp [piU, hρu]
    -- posteriorMarginVarianceProxy ρ varU = ρ()*varU() = 1/10 ≥ 0
    have hvarval : posteriorMarginVarianceProxy ρ varU = 1 / 10 := by
      unfold posteriorMarginVarianceProxy
      simp [varU, hρu]
    -- The Bernstein RHS at lambda=1, scale=0, delta=1:
    -- (klDiv + log(1/1))/1 + 1*(1/10)/(2*(1-0)) = 0 + (1/10)/2 = 1/20 ≥ 0
    rw [hgapval, hkl, hvarval] at hbad
    rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.log_one] at hbad
    norm_num at hbad

/-- `hVCGood` holds non-vacuously: it must hold for the REAL element `()` which
is in the complement of `vcBad = ∅`. We pick `B = 0, n = d = 0` so the VC
capacity term is `0`, and `posteriorEmpiricalRisk ρ (empRisk ()) = 1/2 ≤
anchor () + 0 = 1/2`. -/
theorem hVCGood_holds :
    ∀ ω' : Unit, ω' ∉ (∅ : Finset Unit) →
      posteriorEmpiricalRisk rhoU (empRiskU ω') ≤
        anchorU ω' + vcCapacityTerm 0 0 0 := by
  intro ω' _
  have hcap : vcCapacityTerm 0 0 0 = 0 := by
    unfold vcCapacityTerm; norm_num
  rw [hcap]
  unfold posteriorEmpiricalRisk posteriorAverage
  simp [rhoU, empRiskU, anchorU]

/-- The MAIN theorem applied to the concrete instance. All hypotheses are
discharged by the constructive proofs above; `hω` uses the proven emptiness of
the hybrid bad set so it holds for the genuine element `()`. -/
theorem concrete_bound :
    posteriorRisk rhoU riskU ≤
      anchorU () +
        vcCapacityTerm 0 0 0 +
        (klDiv rhoU piU + Real.log (1 / (1 : ℝ))) / 1 +
        (1 : ℝ) * posteriorMarginVarianceProxy rhoU varU /
          (2 * (1 - (0 : ℝ) * 1)) := by
  have hω : () ∉
      vcPacBayesHybridBadSamples (∅ : Finset Unit) piU (1 : ℝ) (0 : ℝ) (1 : ℝ)
        riskU empRiskU varU := by
    rw [hybridBad_empty]; exact Finset.notMem_empty ()
  exact vcPacBayesBernsteinPosteriorRisk_bound
    (ρ := rhoU) (π := piU) rhoU_isPMF (∅ : Finset Unit)
    (lambda := 1) (scale := 0) (delta := 1) (B := 0) (n := 0) (d := 0)
    anchorU riskU empRiskU varU ()
    hVCGood_holds hω

/-- Read off the concrete numbers: LHS `= 3/10`, RHS `= 1/2 + 0 + 0 + 1/20 = 11/20`.
The inequality `3/10 ≤ 11/20` is TRUE and STRICT (not an equality, not a
trivial `x ≤ x`), so the conclusion is genuinely non-trivial. -/
theorem concrete_numbers :
    posteriorRisk rhoU riskU = 3 / 10 ∧
    anchorU () +
        vcCapacityTerm 0 0 0 +
        (klDiv rhoU piU + Real.log (1 / (1 : ℝ))) / 1 +
        (1 : ℝ) * posteriorMarginVarianceProxy rhoU varU /
          (2 * (1 - (0 : ℝ) * 1)) = 11 / 20 := by
  refine ⟨?_, ?_⟩
  · unfold posteriorRisk posteriorAverage
    simp [rhoU, riskU]
  · have hcap : vcCapacityTerm 0 0 0 = 0 := by unfold vcCapacityTerm; norm_num
    have hkl : klDiv rhoU piU = 0 := by unfold klDiv; simp [rhoU, piU]
    have hvar : posteriorMarginVarianceProxy rhoU varU = 1 / 10 := by
      unfold posteriorMarginVarianceProxy; simp [rhoU, varU]
    rw [hcap, hkl, hvar]
    simp only [anchorU]
    norm_num

end

#print axioms concrete_bound
#print axioms concrete_numbers
#print axioms hybridBad_empty

end FormalSLT.PACBayes.VCHybrid.Witness
