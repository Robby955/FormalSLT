import FormalSLT.TestTimeMeta.FlagshipFiveComponentAssembly

/-!
# Axiom audit for the five-component flagship assembly
-/

open FormalSLT.TestTimeMeta
open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

#print axioms flagshipFiveComponent_five_slots_positive
#print axioms flagshipFiveComponent_scalarBounds_from_incrementModel
#print axioms flagshipFiveComponent_population_le_bound_from_incrementModel
#print axioms flagshipFiveComponent_conclusion_from_incrementModel

#check @flagshipFiveComponent_five_slots_positive
#check @FlagshipFiveComponentConclusion
#check @flagshipFiveComponent_scalarBounds_from_incrementModel
#check @flagshipFiveComponent_population_le_bound_from_incrementModel
#check @flagshipFiveComponent_conclusion_from_incrementModel

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
    0 < (flagshipFiveComponent_certificate_from_incrementModel
          (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
          (lam := lam) (t := t) (n := n)
          hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter
          hvar).derived.prefixKernelContribution :=
  (flagshipFiveComponent_conclusion_from_incrementModel
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
    (lam := lam) (t := t) (n := n)
    hn hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable hbound hcenter
    hvar).fiveSlotsPositive.2.2.2.2
