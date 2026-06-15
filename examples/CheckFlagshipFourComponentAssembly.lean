import FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly

/-!
# Axiom audit for the four-component flagship assembly
-/

open FormalSLT.TestTimeMeta
open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

#print axioms flagshipFourComponent_four_slots_positive
#print axioms flagshipFourComponent_scalarBounds_from_incrementModel
#print axioms flagshipFourComponent_population_le_bound_from_incrementModel
#print axioms flagshipFourComponent_conclusion_from_incrementModel

#check @flagshipFourComponent_four_slots_positive
#check @FlagshipFourComponentConclusion
#check @flagshipFourComponent_scalarBounds_from_incrementModel
#check @flagshipFourComponent_population_le_bound_from_incrementModel
#check @flagshipFourComponent_conclusion_from_incrementModel

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t n)
      ≤ anytimeVilleTailContribution lam n t :=
  (flagshipFourComponent_conclusion_from_incrementModel
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
    (lam := lam) (t := t) (n := n)
    hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter
    hvar).anytimeUniform
