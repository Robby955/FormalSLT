import FormalSLT.PACBayesBernstein
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Adversarial witness for `finitePACBayesBernsteinMargin_badEventMass_le_delta`.

Goal: instantiate the audited theorem with CONCRETE finite data, discharge ALL
hypotheses (hν, hπ, hlambda, hscale, hdelta, hcomplexity, hpenalty, hExpected),
and obtain a NON-trivial conclusion where the bad-sample set is genuinely
NON-EMPTY (so the bound `∑ bad ν ω ≤ delta` is constraining, not `0 ≤ delta`).

Concrete data:
* ι = Fin 1 (single hypothesis), Ω = Fin 2 (two samples).
* π = 1 (full-support PMF on Fin 1).  So klDiv ρ π = 0 for the unique PMF ρ = 1.
* riskFn = 5, empiricalRiskFn ω = (if ω = 0 then 1 else 5).
    gap at ω=0 is 5-1 = 4; gap at ω=1 is 5-5 = 0.
* varianceProxy = 1, lambda = 1, scale = 1/2, delta = 1/2.
* complexityOf = 2  (≥ klDiv + log(1/δ) = 0 + log 2 ≈ 0.693).
* margin penalty = sqrt(2·V·C) + scale·C = sqrt(4) + 1 = 2 + 1 = 3.
    gap(ω=0) = 4 > 3  ⇒  ω=0 is in the BAD set (non-empty!).
    gap(ω=1) = 0 < 3  ⇒  ω=1 is good.
* ν = (1/64, 63/64): bad-set ν-mass = 1/64, conclusion is `1/64 ≤ 1/2` (non-trivial).
* hpenalty holds at AM-GM tangency (equality):
    (1/λ - s)C = λV/(2(1-sλ))  ⇒  (1 - 1/2)·2 = 1·1/(2·1/2)  ⇒  1 = 1. ✓
* hExpected: (1/64)·e^3 + (63/64)·e^(-1) ≤ (1/64)·27 + (63/64)·(1/2)
            = 27/64 + 63/128 = 117/128 < 1. ✓
-/

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein

namespace FormalSLT.AdversarialWitnessBernstein

noncomputable section

abbrev I := Fin 1
abbrev O := Fin 2

def piPrior : I → ℝ := fun _ => 1
def nu : O → ℝ := fun ω => if ω = 0 then (1 : ℝ) / 64 else 63 / 64
def riskFn : I → ℝ := fun _ => 5
def empRiskFn : O → I → ℝ := fun ω _ => if ω = 0 then 1 else 5
def varProxy : I → ℝ := fun _ => 1
def complexityOf : (I → ℝ) → ℝ := fun _ => 2

def lam : ℝ := 1
def sc : ℝ := 1 / 2
def del : ℝ := 1 / 2

/-- ν is a PMF. -/
theorem hnu : IsPMF nu where
  nonneg := by intro i; fin_cases i <;> norm_num [nu]
  sum_one := by simp [nu, Fin.sum_univ_two]; norm_num

/-- π is a full-support PMF on Fin 1. -/
theorem hpi : IsFullSupportPMF piPrior where
  nonneg := by intro i; norm_num [piPrior]
  sum_one := by simp [piPrior]
  pos := by intro i; norm_num [piPrior]

/-- On Fin 1 every PMF equals the point mass: ρ 0 = 1. -/
theorem pmf_fin1 {ρ : I → ℝ} (hρ : IsPMF ρ) : ρ 0 = 1 := by
  have := hρ.sum_one
  simpa using this

/-- klDiv ρ π = 0 for any PMF ρ on Fin 1. -/
theorem kl_zero {ρ : I → ℝ} (hρ : IsPMF ρ) : klDiv ρ piPrior = 0 := by
  unfold klDiv
  rw [Fin.sum_univ_one, pmf_fin1 hρ]
  simp [piPrior]

/-- posteriorMarginVarianceProxy ρ varProxy = 1 for any PMF ρ on Fin 1. -/
theorem var_one {ρ : I → ℝ} (hρ : IsPMF ρ) :
    posteriorMarginVarianceProxy ρ varProxy = 1 := by
  unfold posteriorMarginVarianceProxy
  rw [Fin.sum_univ_one, pmf_fin1 hρ]
  simp [varProxy]

/-- complexity certificate. -/
theorem hcomplexity :
    ∀ ρ : I → ℝ, IsPMF ρ → klDiv ρ piPrior + Real.log (1 / del) ≤ complexityOf ρ := by
  intro ρ hρ
  rw [kl_zero hρ]
  simp only [complexityOf, del, zero_add]
  have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  rw [h2]
  have hlog : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  linarith

/-- penalty certificate (AM-GM tangency: holds with equality). -/
theorem hpenalty :
    ∀ ρ : I → ℝ, IsPMF ρ →
      complexityOf ρ / lam +
          lam * posteriorMarginVarianceProxy ρ varProxy / (2 * (1 - sc * lam))
        ≤
      Real.sqrt (2 * posteriorMarginVarianceProxy ρ varProxy * complexityOf ρ) +
        sc * complexityOf ρ := by
  intro ρ hρ
  rw [var_one hρ]
  simp only [complexityOf, lam, sc]
  have hsqrt : Real.sqrt (2 * 1 * 2) = 2 := by
    rw [show (2 * 1 * 2 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

/-- The prior moment at outcome ω. -/
theorem moment_eq (ω : O) :
    priorBernsteinExpMoment piPrior lam sc riskFn empRiskFn varProxy ω
      = Real.exp ((5 - empRiskFn ω 0) - 1) := by
  unfold priorBernsteinExpMoment
  rw [Fin.sum_univ_one]
  simp only [piPrior, riskFn, varProxy, lam, sc, one_mul]
  congr 1
  norm_num

/-- e^3 < 27 via e < 3. -/
theorem exp3_lt : Real.exp 3 < 27 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith [he, hpos, sq_nonneg (Real.exp 1)]

/-- e^(-1) ≤ 1/2 via 2 < e. -/
theorem expNeg1_le : Real.exp (-1) ≤ 1 / 2 := by
  have he : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_neg]
  rw [hinv]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
  linarith

/-- THE expected-moment certificate, proved with explicit exp bounds. -/
theorem hExpected :
    expectedPriorBernsteinExpMoment nu piPrior lam sc riskFn empRiskFn varProxy ≤ 1 := by
  unfold expectedPriorBernsteinExpMoment
  rw [Fin.sum_univ_two, moment_eq, moment_eq]
  -- ω = 0: empRiskFn 0 0 = 1, exponent (5-1)-1 = 3
  -- ω = 1: empRiskFn 1 0 = 5, exponent (5-5)-1 = -1
  simp only [nu, empRiskFn]
  norm_num
  -- goal now: (1/64)·e^3 + (63/64)·e^(-1) ≤ 1
  nlinarith [exp3_lt, expNeg1_le, Real.exp_pos 3, Real.exp_pos (-1)]

/-- The bad-sample Finset for our concrete data. -/
def badSet : Finset O :=
  finitePACBayesBernsteinPenaltyBadSamples riskFn empRiskFn
    (fun ρ =>
      Real.sqrt (2 * posteriorMarginVarianceProxy ρ varProxy * complexityOf ρ) +
        sc * complexityOf ρ)

/-- THE WITNESS: the audited theorem applied to concrete data, ALL hypotheses
discharged. Conclusion: the ν-mass of the bad set is ≤ delta. -/
theorem witness_conclusion :
    (∑ ω ∈ badSet, nu ω) ≤ del :=
  finitePACBayesBernsteinMargin_badEventMass_le_delta
    hnu hpi lam sc del (by norm_num [lam]) (by norm_num [sc, lam]) (by norm_num [del])
    riskFn empRiskFn varProxy complexityOf hcomplexity hpenalty hExpected

/-- NON-VACUITY: outcome 0 is genuinely in the bad set (gap 4 > penalty 3). -/
theorem zero_mem_badSet : (0 : O) ∈ badSet := by
  classical
  unfold badSet finitePACBayesBernsteinPenaltyBadSamples
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  -- use ρ = the point mass (the constant 1 on Fin 1, the unique PMF)
  refine ⟨fun _ => 1, ⟨?_, ?_⟩, ?_⟩
  · intro i; norm_num
  · simp
  · -- posteriorGeneralizationGap = 4 > penalty = 3
    simp only
    have hgap : posteriorGeneralizationGap (fun _ => (1:ℝ)) riskFn (empRiskFn 0) = 4 := by
      rw [posteriorGeneralizationGap_eq_sum, Fin.sum_univ_one]
      simp [riskFn, empRiskFn]
      norm_num
    have hpen :
        Real.sqrt (2 * posteriorMarginVarianceProxy (fun _ => (1:ℝ)) varProxy * complexityOf (fun _ => 1)) +
          sc * complexityOf (fun _ => 1) = 3 := by
      have hv : posteriorMarginVarianceProxy (fun _ => (1:ℝ)) varProxy = 1 := by
        unfold posteriorMarginVarianceProxy
        rw [Fin.sum_univ_one]; simp [varProxy]
      rw [hv]
      simp only [complexityOf, sc]
      have hsqrt : Real.sqrt (2 * 1 * 2) = 2 := by
        rw [show (2 * 1 * 2 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hsqrt]; norm_num
    rw [hgap, hpen]
    norm_num

/-- The bad set is non-empty: the conclusion is NOT the trivial empty-sum `0 ≤ del`. -/
theorem badSet_nonempty : badSet.Nonempty :=
  ⟨0, zero_mem_badSet⟩

/-- The bad-set mass is exactly 1/64 (genuinely positive), so the conclusion
`1/64 ≤ 1/2` is a real numeric bound on a real non-empty event. -/
theorem badSet_mass_eq : (∑ ω ∈ badSet, nu ω) = 1 / 64 := by
  classical
  have hsub : badSet ⊆ {(0 : O)} := by
    intro ω hω
    unfold badSet finitePACBayesBernsteinPenaltyBadSamples at hω
    rw [Finset.mem_filter] at hω
    obtain ⟨_, ρ, hρ, hbad⟩ := hω
    simp only at hbad
    -- if ω ≠ 0, gap = 0 which is NOT > penalty ≥ 0, contradiction
    by_cases hω0 : ω = 0
    · simp [hω0]
    · exfalso
      have hgap : posteriorGeneralizationGap ρ riskFn (empRiskFn ω) = 0 := by
        rw [posteriorGeneralizationGap_eq_sum, Fin.sum_univ_one, pmf_fin1 hρ]
        simp [riskFn, empRiskFn, hω0]
      have hpen_nonneg :
          (0:ℝ) ≤ Real.sqrt (2 * posteriorMarginVarianceProxy ρ varProxy * complexityOf ρ) +
            sc * complexityOf ρ := by
        rw [var_one hρ]
        simp only [complexityOf, sc]
        positivity
      rw [hgap] at hbad
      linarith
  have hmem : (0 : O) ∈ badSet := zero_mem_badSet
  have : badSet = {(0 : O)} :=
    Finset.Subset.antisymm hsub (by simpa using hmem)
  rw [this]
  simp [nu]

end

end FormalSLT.AdversarialWitnessBernstein

-- AXIOM AUDIT (sorry-free? no custom axioms?)
namespace FormalSLT.AdversarialWitnessBernstein
#print axioms witness_conclusion
#print axioms zero_mem_badSet
#print axioms badSet_nonempty
#print axioms badSet_mass_eq
#print axioms hExpected
#print axioms hpenalty
#print axioms hcomplexity
end FormalSLT.AdversarialWitnessBernstein
