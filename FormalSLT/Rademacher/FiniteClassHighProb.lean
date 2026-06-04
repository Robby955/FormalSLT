import FormalSLT.Rademacher.HighProbability
import FormalSLT.Rademacher.Massart

/-!
# High-probability generalization bound for finite hypothesis classes

Combines:
- **Massart's lemma** (deterministic):
    `empiricalRademacherComplexity ℓ z ≤ B · √(2 · log|H| / n)`
- **High-probability Rademacher** (probabilistic):
    `P(genGap S ≥ 2 · E[R̂ad] + ε) ≤ exp(-ε²n/(2B²))`

to obtain the explicit textbook-style bound:

    P(genGap S ≥ 2B · √(2 · log|H| / n) + ε) ≤ exp(-ε²n/(2B²))

## Interpretation

With probability at least `1 - exp(-ε²n/(2B²))` over an iid sample `S ~ μⁿ`,
the generalization gap of any hypothesis in a finite class of size `|H|` with
`B`-bounded loss satisfies:

    sup_h (risk(h) - R̂_S(h)) < 2B · √(2 · log|H| / n) + ε

This is the "plug-in Massart" form; the Rademacher complexity term becomes a
closed-form function of `B`, `|H|`, and `n` alone.

No `sorry`, no `admit`, no custom `axiom`.
-/

open scoped ENNReal NNReal Topology
open MeasureTheory Filter ProbabilityTheory Real
open FormalSLT.GhostSample
  (genGap piMeasure measurable_genGap)
open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity)
open FormalSLT.Rademacher.HighProbability
  (genGap_highProb_rademacher)
open FormalSLT.Rademacher.Massart
  (massart_finite_class)

noncomputable section

namespace FormalSLT.Rademacher.FiniteClassHighProb

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z}

/-- The expected empirical Rademacher complexity is bounded by the Massart
deterministic bound. Since `empiricalRademacherComplexity ℓ z ≤ C` for ALL
samples `z`, the integral is also bounded by `C`.

The proof splits on integrability: if the function is integrable we use
`integral_mono`; if not, the Bochner integral is 0 by convention, and
`C ≥ 0`. -/
lemma expected_rademacher_le_massart {ι : Type*} [Fintype ι] [Nonempty ι]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    (ν : Measure (Fin n → Z)) [IsProbabilityMeasure ν] :
    ∫ S, empiricalRademacherComplexity ℓ S ∂ν
      ≤ B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ)) := by
  set C := B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
  have hC_nn : (0 : ℝ) ≤ C := by positivity
  -- Massart gives the pointwise bound.
  have h_pointwise : ∀ z : Fin n → Z,
      empiricalRademacherComplexity ℓ z ≤ C :=
    fun z => massart_finite_class hB (fun i k => hℓ_bdd i (z k)) hn hCard
  -- Split on whether the function is integrable.
  by_cases h_int : Integrable (fun z => empiricalRademacherComplexity ℓ z) ν
  · -- Integrable case: use integral_mono.
    calc ∫ S, empiricalRademacherComplexity ℓ S ∂ν
        ≤ ∫ _S, C ∂ν :=
          integral_mono h_int (integrable_const C) h_pointwise
      _ = C := by simp [integral_const]
  · -- Not integrable: Bochner integral is 0 by convention.
    rw [integral_undef h_int]
    exact hC_nn

/-- **High-probability finite-class generalization bound (explicit Massart form).**

For a finite hypothesis class `ι` with `|ι| > 1`, uniformly `B`-bounded loss,
and an iid sample `S ~ μⁿ`:

    P(genGap(S) ≥ 2B · √(2 · log|H| / n) + ε) ≤ exp(-ε²n/(2B²))

Equivalently: with probability at least `1 - exp(-ε²n/(2B²))`,
    genGap(S) < 2B · √(2 · log|H| / n) + ε.

This is obtained by plugging Massart's deterministic Rademacher bound
into the high-probability Rademacher generalization theorem. -/
theorem genGap_highProb_finiteClass {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 2 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + ε ≤ genGap μ ℓ S}
      ≤ Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) := by
  -- The high-prob Rademacher theorem gives:
  -- P(genGap ≥ 2·E[R̂ad] + ε) ≤ exp(-ε²n/(2B²))
  have h_highProb := genGap_highProb_rademacher (μ := μ) (n := n) hB hℓ_meas hℓ_bdd hn hε
  -- Massart gives: E[R̂ad] ≤ B·√(2·log|H|/n)
  have h_massart : ∫ S', empiricalRademacherComplexity ℓ S' ∂(piMeasure μ n)
      ≤ B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ)) := by
    have : IsProbabilityMeasure (piMeasure μ n) := by
      unfold piMeasure; infer_instance
    exact expected_rademacher_le_massart hB hℓ_bdd hn hCard (piMeasure μ n)
  -- Unfold piMeasure.
  simp only [piMeasure] at h_highProb h_massart ⊢
  set μn := Measure.pi (fun _ : Fin n => μ)
  set E_rad := ∫ S', empiricalRademacherComplexity ℓ S' ∂μn
  -- Chain: P(genGap ≥ 2B√(...) + ε) ≤ P(genGap ≥ 2·E_rad + ε) ≤ exp(...)
  calc μn.real {S | 2 * B * Real.sqrt (2 * Real.log ↑(Fintype.card ι) / ↑n)
              + ε ≤ genGap μ ℓ S}
      ≤ μn.real {S | 2 * E_rad + ε ≤ genGap μ ℓ S} := by
        apply measureReal_mono
        · intro S hS
          simp only [Set.mem_setOf_eq] at hS ⊢
          linarith [h_massart]
        · exact measure_ne_top μn _
    _ ≤ Real.exp (-ε ^ 2 * ↑n / (2 * B ^ 2)) := h_highProb

end FormalSLT.Rademacher.FiniteClassHighProb
