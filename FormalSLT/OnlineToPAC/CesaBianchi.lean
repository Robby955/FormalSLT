import FormalSLT.OnlineToPAC.RegretConversion

/-!
# Cesa-Bianchi-Conconi-Gentile online-to-PAC corollary

This module exposes a finite-time corollary of
`onlineToPAC_boundedLoss_iid_of_regret_and_deviation`. It keeps the regret-rate
and high-probability deviation assumptions explicit in the original theorem,
and also exposes the q059 iid-derived variant `cesaBianchi_iid`.  Neither theorem
formalizes asymptotic `o(sqrt(T))` facts for a particular online algorithm.

Reference: Cesa-Bianchi, Conconi, Gentile (2004), "On the Generalization
Ability of On-Line Learning Algorithms," IEEE Transactions on Information
Theory 50(9), DOI 10.1109/TIT.2004.833339.
-/

namespace FormalSLT.OnlineToPAC

noncomputable section

/--
Finite-time Cesa-Bianchi-Conconi-Gentile style bounded-loss iid
high-probability conversion.

This theorem is explicitly conditional on a per-round regret-rate certificate
`input.regretBound / T ≤ regretRate` and on the deviation gate supplied to
`onlineToPAC_boundedLoss_iid_of_regret_and_deviation`. It is therefore the
finite-time certificate form of the 2004 result, not a proof of the asymptotic
regret theorem for a particular online algorithm.
-/
theorem cesaBianchiConconiGentile2004_boundedLoss_iid_highProbability
    {T : ℕ} (hT : 0 < T)
    (input : BoundedLossRegretConversionInput T)
    (regretRate : ℝ)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hdeviation :
      averagePopulationLoss input ≤ averageEmpiricalLoss input + input.deviationBound)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ))
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate) :
    averagePopulationLoss input ≤
      input.comparatorEmpiricalLoss + regretRate + input.deviationBound := by
  have hbase :=
    onlineToPAC_boundedLoss_iid_of_regret_and_deviation
      hT input hlossBound hpopulationBounded hempiricalBounded hdeviation hregret
  unfold onlineToPACBound at hbase
  linarith

/--
Finite-time Cesa-Bianchi-Conconi-Gentile style conversion with the iid
deviation gate derived from the q059 bad-event complement.

The probabilistic statement is split cleanly: this theorem is the pointwise
sample conversion outside the bad event, while
`FormalSLT.Probability.IIDConcentration.iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid`
bounds that bad event under independent bounded losses.
-/
theorem cesaBianchi_iid
    {T : ℕ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (input : BoundedLossRegretConversionInput T)
    (X : Fin T → Ω → ℝ) (ω : Ω) {eps : ℝ}
    (regretRate : ℝ)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hpopulationEq :
      ∀ t : Fin T, input.populationLoss t = ∫ x, X t x ∂μ)
    (hempiricalEq :
      ∀ t : Fin T, input.empiricalLoss t = X t ω)
    (hdeviationRadius : eps ≤ input.deviationBound)
    (hnotBad :
      ω ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent μ X eps)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ))
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate) :
    averagePopulationLoss input ≤
      input.comparatorEmpiricalLoss + regretRate + input.deviationBound := by
  have hbase :=
    regretConversion_iid
      hT μ input X ω hlossBound hpopulationBounded hempiricalBounded
      hpopulationEq hempiricalEq hdeviationRadius hnotBad hregret
  unfold onlineToPACBound at hbase
  linarith

end

end FormalSLT.OnlineToPAC
