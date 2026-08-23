import FormalSLT.Sequential

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ]
    {E : ℕ → Ω → ℝ} (hE : EProcess μ 𝒢 E) :
    μ.real {ω | (2 : ℝ) ≤ finiteRunningMax E 10 ω} ≤ (1 : ℝ) / 2 := by
  simpa using
    (eProcess_typeI_control hE (α := (1 : ℝ) / 2) (by norm_num) 10)
