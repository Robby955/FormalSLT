import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter MeasureTheory
open scoped ENNReal Topology

namespace FormalSLT.Probability.MeasureConvergence

noncomputable section

/--
Monotone convergence theorem for nonnegative functions, stated with
Lebesgue `lintegral`.

This is the exact nonnegative measure-theoretic scope of the governed MCT
claim: almost-everywhere measurable functions increase almost everywhere and
converge almost everywhere to `F`, so their integrals converge to the integral
of `F`.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::monotone-convergence-theorem`.
-/
theorem monotoneConvergenceLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ≥0∞} {F : Ω → ℝ≥0∞}
    (hMeas : ∀ n, AEMeasurable (f n) μ)
    (hMono : ∀ᵐ ω ∂μ, Monotone fun n => f n ω)
    (hTendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω))) :
    Tendsto (fun n => ∫⁻ ω, f n ω ∂μ) atTop (𝓝 (∫⁻ ω, F ω ∂μ)) :=
  MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hMeas hMono hTendsto

/--
Fatou's lemma for nonnegative measurable functions, stated with `lintegral`.

The `liminf` form is the canonical statement behind the page's expectation
notation for nonnegative random variables.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::fatou-lemma`.
-/
theorem fatouLemmaLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ≥0∞} (hMeas : ∀ n, Measurable (f n)) :
    ∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ
      ≤ liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop :=
  MeasureTheory.lintegral_liminf_le hMeas

/--
Dominated convergence theorem for Bochner integrals.

This wraps mathlib's theorem with the exact assumptions the governed claim
needs to expose: a measurable sequence, an integrable real-valued dominating
bound, domination almost everywhere, and almost-everywhere convergence.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::dominated-convergence-theorem`.
-/
theorem dominatedConvergenceIntegral
    {Ω G : Type*} [MeasurableSpace Ω] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure Ω} {F : ℕ → Ω → G} {f : Ω → G} (bound : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hBoundIntegrable : Integrable bound μ)
    (hBound : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ bound ω)
    (hTendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hMeas hBoundIntegrable hBound hTendsto

end

end FormalSLT.Probability.MeasureConvergence
