import FormalSLT.PACBayes.McAllesterBound

/-!
# Tight finite PAC-Bayes change of measure

This module packages the finite PAC-Bayes chain in one place:

* Donsker-Varadhan gives the finite variational change-of-measure step.
* The exact log-prior-moment form gives the tight deterministic posterior-risk
  bound for a fixed sample.
* The bounded-loss MGF certificate yields the fixed-`lambda` Catoni bound.
* Optimizing that Catoni penalty at a fixed complexity budget yields the
  McAllester square-root bound.

The scope is finite data domains, finite hypothesis classes, full-support
finite priors, finite posteriors, and bounded scalar losses.
-/

namespace FormalSLT.PACBayes.ChangeOfMeasure

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/--
Donsker-Varadhan variational change-of-measure step for finite posteriors.

This is the finite PAC-Bayes bridge from a posterior expectation to a prior
log-moment plus `KL(posterior‖prior)`.
-/
theorem dv_variational_step
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {posterior prior : ι → ℝ}
    (hposterior : IsPMF posterior)
    (hprior : IsFullSupportPMF prior)
    (f : ι → ℝ) :
    (∑ i : ι, posterior i * f i)
      ≤ klDiv posterior prior +
        Real.log (∑ i : ι, prior i * Real.exp (f i)) := by
  exact donsker_varadhan hposterior hprior f

/--
Tight deterministic finite PAC-Bayes change-of-measure bound.

For a fixed sample and positive `lambda`, the posterior population risk is
bounded by empirical risk plus the exact finite prior log-moment
`log E_prior exp(lambda * (risk - empiricalRisk))`, with no Markov or
bounded-loss slack.
-/
theorem tight_changeOfMeasure_bound
    {ι Z : Type*} {n : ℕ} [Fintype ι] [Fintype Z] [Nonempty ι]
    (p : Z → ℝ)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (loss : ι → Z → ℝ) (S : Fin n → Z)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss posterior
      ≤ FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S +
        (klDiv posterior prior +
          Real.log
            (FormalSLT.PACBayesBoundedLoss.priorDeviationMGF
              p prior loss lambda S)) / lambda := by
  let riskFn : ι → ℝ := fun i => finitePopulationRisk p loss i
  let empiricalRiskFn : ι → ℝ := fun i => finiteEmpiricalRisk loss i S
  have h :=
    posterior_risk_le_empiricalRisk_plus_complexity_div_lambda
      hposterior hprior hlambda riskFn empiricalRiskFn
  simpa [riskFn, empiricalRiskFn,
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk,
    FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk,
    FormalSLT.PACBayesBoundedLoss.posteriorAverage,
    posteriorRisk, posteriorEmpiricalRisk, posteriorAverage,
    FormalSLT.PACBayesBoundedLoss.priorDeviationMGF] using h

/--
Finite Catoni fixed-`lambda` posterior-risk bound from the bounded-loss MGF
certificate at a fixed sample.
-/
theorem catoni_changeOfMeasure_bound
    {ι Z : Type*} {n : ℕ} [Fintype ι] [Fintype Z] [Nonempty ι]
    (hn : 0 < n)
    (p : Z → ℝ)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (loss : ι → Z → ℝ) (S : Fin n → Z)
    {lambda delta : ℝ} (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hconf :
      FormalSLT.PACBayesBoundedLoss.priorDeviationMGF
          p prior loss lambda S ≤
        Real.exp (lambda ^ 2 / (8 * (n : ℝ))) / delta) :
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss posterior
      ≤ FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S +
        (klDiv posterior prior + Real.log (1 / delta)) / lambda +
        lambda / (8 * (n : ℝ)) := by
  exact
    FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le
      hn p prior hprior posterior hposterior loss S hlambda hdelta hconf

/--
Finite McAllester square-root bound obtained by optimizing the fixed-`lambda`
Catoni penalty at a fixed posterior-complexity budget.
-/
theorem mcallester_tight_bound
    {ι Z : Type*} {n : ℕ} [Fintype ι] [Fintype Z] [Nonempty ι]
    (hn : 0 < n)
    (p : Z → ℝ)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (loss : ι → Z → ℝ) (S : Fin n → Z)
    {complexityBound delta : ℝ}
    (hcomplexityBound : 0 < complexityBound) (hdelta : 0 < delta)
    (hcomplexity :
      klDiv posterior prior + Real.log (1 / delta) ≤ complexityBound)
    (hconf :
      FormalSLT.PACBayesBoundedLoss.priorDeviationMGF
          p prior loss (Real.sqrt (8 * (n : ℝ) * complexityBound)) S ≤
        Real.exp
          ((Real.sqrt (8 * (n : ℝ) * complexityBound)) ^ 2 /
            (8 * (n : ℝ))) / delta) :
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk p loss posterior
      ≤ FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk loss posterior S +
        Real.sqrt (complexityBound / (2 * (n : ℝ))) := by
  exact
    FormalSLT.PACBayesBoundedLoss.posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt
      hn p prior hprior posterior hposterior loss S
      hcomplexityBound hdelta hcomplexity hconf

/-! ### Concrete two-point witness -/

/-- Uniform prior over two hypotheses. -/
def twoPointPrior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform posterior over two hypotheses. -/
def twoPointPosterior : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Uniform data law over two data points. -/
def twoPointDataLaw : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Nontrivial zero-one loss over the two-point data domain. -/
def twoPointLoss : Fin 2 → Fin 2 → ℝ := fun _ z => if z = 0 then 0 else 1

/-- A nonempty two-sample dataset. -/
def twoPointSample : Fin 2 → Fin 2 := fun k => k

theorem twoPointPrior_isFullSupportPMF :
    IsFullSupportPMF twoPointPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [twoPointPrior]
  · simp [twoPointPrior]
  · intro i
    fin_cases i <;> norm_num [twoPointPrior]

theorem twoPointPosterior_isPMF :
    IsPMF twoPointPosterior := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [twoPointPosterior]
  · simp [twoPointPosterior]

theorem twoPointDataLaw_isPMF :
    IsPMF twoPointDataLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    fin_cases z <;> norm_num [twoPointDataLaw]
  · simp [twoPointDataLaw]

theorem twoPointLoss_mem_unitInterval :
    ∀ i : Fin 2, ∀ z : Fin 2, 0 ≤ twoPointLoss i z ∧ twoPointLoss i z ≤ 1 := by
  intro i z
  fin_cases i <;> fin_cases z <;> norm_num [twoPointLoss, Fin.ext_iff]

theorem twoPointLoss_nontrivial :
    twoPointLoss 0 1 = 1 := by
  norm_num [twoPointLoss, Fin.ext_iff]

theorem twoPoint_zero_kl :
    klDiv twoPointPosterior twoPointPrior = 0 := by
  simp [klDiv, twoPointPosterior, twoPointPrior]

theorem twoPoint_priorDeviationMGF_le :
    FormalSLT.PACBayesBoundedLoss.priorDeviationMGF
        twoPointDataLaw twoPointPrior twoPointLoss
        (Real.sqrt (8 * (2 : ℝ) * 1)) twoPointSample
      ≤
        Real.exp
          ((Real.sqrt (8 * (2 : ℝ) * 1)) ^ 2 / (8 * (2 : ℝ))) / 1 := by
  have hmoment :
      FormalSLT.PACBayesBoundedLoss.priorDeviationMGF
          twoPointDataLaw twoPointPrior twoPointLoss
          (Real.sqrt (8 * (2 : ℝ) * 1)) twoPointSample = 1 := by
    norm_num [FormalSLT.PACBayesBoundedLoss.priorDeviationMGF,
      finitePopulationRisk, finiteEmpiricalRisk, twoPointDataLaw,
      twoPointPrior, twoPointLoss, twoPointSample]
  rw [hmoment]
  have hsqrt_sq :
      (Real.sqrt (8 * (2 : ℝ) * 1)) ^ 2 = 16 := by
    rw [Real.sq_sqrt (by norm_num : 0 ≤ 8 * (2 : ℝ) * 1)]
    norm_num
  rw [hsqrt_sq]
  norm_num

/--
Concrete non-vacuity witness: a two-point prior, two-point posterior, two-point
sample, and explicit McAllester penalty. The bound is strictly below one.
-/
theorem twoPoint_mcallester_nonvacuous :
    FormalSLT.PACBayesBoundedLoss.posteriorPopulationRisk
        twoPointDataLaw twoPointLoss twoPointPosterior
      ≤ FormalSLT.PACBayesBoundedLoss.posteriorEmpiricalRisk
          twoPointLoss twoPointPosterior twoPointSample +
        Real.sqrt ((1 : ℝ) / (2 * (2 : ℝ))) ∧
    Real.sqrt ((1 : ℝ) / (2 * (2 : ℝ))) < 1 := by
  constructor
  · have hcomplexity :
        klDiv twoPointPosterior twoPointPrior + Real.log (1 / (1 : ℝ)) ≤
          (1 : ℝ) := by
      rw [twoPoint_zero_kl]
      norm_num
    exact
      mcallester_tight_bound
        (n := 2)
        (hn := by norm_num)
        twoPointDataLaw
        twoPointPrior twoPointPrior_isFullSupportPMF
        twoPointPosterior twoPointPosterior_isPMF
        twoPointLoss twoPointSample
        (hcomplexityBound := by norm_num)
        (hdelta := by norm_num)
        hcomplexity
        twoPoint_priorDeviationMGF_le
  · rw [Real.sqrt_lt' zero_lt_one]
    norm_num

end

end FormalSLT.PACBayes.ChangeOfMeasure
