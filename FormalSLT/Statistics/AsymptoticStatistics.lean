import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace FormalSLT.Statistics.AsymptoticStatistics

/--
Continuous mapping theorem, globally continuous distributional form.

Scoped wrapper: mathlib proves the global-continuity distributional case. The
governed TheoremPath claim is broader: continuity on a limit-a.s. set, plus
probability and almost-sure variants. This wrapper must therefore stay scoped
and not be used as a full-page claim verification.
Claim-facing wrapper for theorempath.com evidence entry `claim:asymptotic-statistics::continuous-mapping-theorem`.
-/
theorem continuousMappingTheoremContinuous
    {ι E F Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι} {g : E → F}
    (hg : Continuous g) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ μ' :=
  MeasureTheory.TendstoInDistribution.continuous_comp hg h

/--
Slutsky's theorem, joint convergence form.

If `X n` converges in distribution to `Z` and `Y n` converges in probability
to a constant `c`, then the pair `(X n, Y n)` converges in distribution to
`(Z, c)`.

Scoped wrapper: this is the joint-convergence core of Slutsky as proved in
mathlib. The governed TheoremPath claim adds the standard corollaries
(continuous-function, addition, product, ratio with `c ≠ 0`); the addition
case is wrapped separately by `slutskyTheoremAdd`, and other corollaries are
instances of `continuousMappingTheoremContinuous` applied to the joint limit.
This wrapper is therefore a scoped Lean artifact, not a full-page claim
verification.
Claim-facing wrapper for theorempath.com evidence entry `claim:asymptotic-statistics::slutsky-theorem`.
-/
theorem slutskyTheoremPair
    {ι E E' Ω' Ω'' : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} [SeminormedAddCommGroup E]
    [SecondCountableTopology E] [BorelSpace E]
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E']
    (X : ι → Ω'' → E) (Y : ι → Ω'' → E') (Z : Ω' → E) {c : E'}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c))
      (fun _ ↦ μ'') μ' :=
  hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY hY_meas

/--
Slutsky's theorem, additive corollary.

If `X n` converges in distribution to `Z` and `Y n` converges in probability
to a constant `c` (in the same seminormed additive group as `X n`), then
`X n + Y n` converges in distribution to `Z + c`.

This is one of the standard Slutsky corollaries listed on the
`asymptotic-statistics` page. It follows from `slutskyTheoremPair` composed
with the continuous map `(x, y) ↦ x + y`.
-/
theorem slutskyTheoremAdd
    {ι E Ω' Ω'' : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} [SeminormedAddCommGroup E]
    [SecondCountableTopology E] [BorelSpace E]
    {X Y : ι → Ω'' → E} {Z : Ω' → E} {c : E}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c)
      (fun _ ↦ μ'') μ' :=
  hXZ.add_of_tendstoInMeasure_const hY hY_meas

/--
Slutsky's theorem, continuous-function corollary.

If `X n → Z` in distribution, `Y n → c` in probability, and `g` is continuous
on `E × E'`, then `g (X n, Y n) → g (Z, c)` in distribution.

This is the general continuous-function form of Slutsky from which the
addition, multiplication, and (where defined) ratio corollaries follow as
special cases.
-/
theorem slutskyTheoremContinuous
    {ι E E' F Ω' Ω'' : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} [SeminormedAddCommGroup E]
    [SecondCountableTopology E] [BorelSpace E]
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : ι → Ω'' → E} {Y : ι → Ω'' → E'} {Z : Ω' → E} {c : E'} {g : E × E' → F}
    (hg : Continuous g)
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l (fun ω ↦ g (Z ω, c))
      (fun _ ↦ μ'') μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const hg hY hY_meas

end FormalSLT.Statistics.AsymptoticStatistics
