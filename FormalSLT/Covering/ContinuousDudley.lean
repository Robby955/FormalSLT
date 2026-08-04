import FormalSLT.Covering.TotalBoundedDudley
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases

/-!
# Brick 3: the continuous Dudley entropy integral as a measure-theoretic limit

This module is *brick 3* of the Dudley chaining lane. Bricks 1 and 2 are:

* `FormalSLT.Covering.DudleyChaining` — discrete two-scale peeling;
* `FormalSLT.Covering.TotalBoundedDudley` — the total-bounded discrete sum,
  whose terminal bounds pay a finite *truncated* interval integral
  `∫ ε in (radiusScale / 2^(m+1))..(radiusScale / 2), entropyAtRadius ε`.

Brick 3 passes that verified finite machinery to the continuous limit under the
dyadic scale sequence `ε_k = 2^{-k} · diam(F)` (here realized by the dyadic
floor `radiusScale / 2^(k+1)`; choosing `radiusScale = 2 · diam(F)` makes the
floor exactly `2^{-k} · diam(F)` and the integration top exactly `diam(F)`).

## What is proved (and what stays a hypothesis)

This module keeps the honest discipline of brick 2: the genuinely hard analytic
inputs are *explicit hypotheses*, never silently discharged.

* `sup_measurable_countable_dense` — the supremum of a sample-continuous process
  over `T` equals the (countable) supremum over a countable dense subset, hence
  is measurable. This is the separability bridge to the integral. It relies on
  ℝ being a Borel space (`MeasurableSpace.borel`, `BorelSpace ℝ`); the countable
  supremum is measurable by `Measurable.iSup`, and the reduction to the dense
  skeleton is `Dense.ciSup'`. Continuity of paths is a hypothesis.

* `dyadic_limit_of_total_bounded_bricks` — the truncated interval integral from
  brick 2 (equivalently, by
  `FiniteSubGaussianChaining.shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral`,
  the discrete dyadic annulus-integral sum) converges to the continuous Dudley
  integral `∫ ε in 0..(radiusScale / 2), entropyAtRadius ε` as the dyadic scale
  sequence refines (`m → ∞`). Interval-integrability on `[0, radiusScale/2]` is
  a hypothesis; the limit then follows from continuity of the integral primitive
  (`continuousWithinAt_primitive`).

* `continuous_dudley_entropy_integral` — the empirical sub-Gaussian complexity is
  bounded by the *continuous* Dudley entropy integral:

    `E[ sup_F X ] ≤ coarseBudget + 4 · √(2 · σ²) · ∫ ε in 0..(radiusScale/2), entropyAtRadius ε`

  where `σ² = P.varianceProxy` and `entropyAtRadius ε` dominates the chosen
  `√(log N(F, ε))` covering-number envelope. Reading this in the empirical
  Rademacher normalization, `σ²` carries the `1/n` factor (for the Rademacher
  process `σ² ≍ B²/n`), so `4 · √(2 · σ²)` is the `C / √n` constant of
  Boucheron–Lugosi–Massart 2013 §13. The supremum / separability / terminal
  modulus content is carried by the `hchoose`
  (`SeparableTerminalSupremumBoundaryChoice`) hypothesis, exactly as in brick 2;
  this theorem does **not** construct an arbitrary measurable supremum on its
  own — that is the role of `sup_measurable_countable_dense` and of separability.

The contribution of brick 3 is the *limit-based* derivation of the continuous
integral from the verified discrete bricks 1+2, rather than a fresh chaining
proof.

## References (verbatim)

* R. M. Dudley, "The sizes of compact subsets of Hilbert space and continuity of
  Gaussian processes," Journal of Functional Analysis 1 (1967).
* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer
  (2014).
* S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A
  Nonasymptotic Theory of Independence*, Oxford University Press (2013), §13.
* P. Massart, *Concentration Inequalities and Model Selection*, Springer Lecture
  Notes in Mathematics 1896 (2007).

Sonoda et al. 2025 (arXiv:2503.19605) and Zhang–Lee–Liu 2026 (arXiv:2602.02285)
mechanise related continuous Dudley results with different proof strategies; the
contribution of this brick is the limit-based proof from the verified discrete
bricks 1+2.

## Known mathlib4 gap (noted, not blocking)

The *sharp* McDiarmid route this lane ultimately feeds needs the conditional
product-measure kernel decomposition (a measure-theoretic disintegration of a
product measure into a base measure and a conditional kernel). That lemma is not
yet available in mathlib4 in directly usable form; brick 3 does not depend on it
(it works with the sub-Gaussian variance proxy interface), so this is recorded
as a forward dependency only.

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Covering.ContinuousDudley

open MeasureTheory Filter Topology Set
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley

noncomputable section

universe u

variable {T : Type u}

/-! ## Separability bridge: measurability of the supremum over a countable dense set -/

/-- **Measurable supremum over a countable dense subset.**

For a process `g : T → α → ℝ` whose sample paths `t ↦ g t a` are continuous and
whose evaluations `a ↦ g t a` are measurable, the full supremum
`a ↦ ⨆ t, g t a` is measurable, because a countable dense subset `D ⊆ T`
already realizes the supremum (`Dense.ciSup'`) and a countable supremum of
measurable functions is measurable (`Measurable.iSup`, which uses that ℝ is a
Borel space, `MeasurableSpace.borel`).

This is the bridge from a pointwise process to its supremum functional that the
continuous Dudley integral integrates against. Continuity of paths is the
explicit separability/modulus hypothesis. -/
theorem sup_measurable_countable_dense
    {α : Type*} [MeasurableSpace α]
    [PseudoMetricSpace T]
    (g : T → α → ℝ)
    (D : Set T) (hDcount : D.Countable) (hDdense : Dense D)
    (hmeas : ∀ t : T, Measurable (g t))
    (hcont : ∀ a : α, Continuous fun t : T => g t a) :
    Measurable fun a : α => ⨆ t : T, g t a := by
  classical
  haveI : Countable D := (Set.countable_coe_iff).mpr hDcount
  have hrw : (fun a : α => ⨆ t : T, g t a)
      = fun a : α => ⨆ d : D, g (d : T) a := by
    funext a
    exact (hDdense.ciSup' (hcont a)).symm
  rw [hrw]
  exact Measurable.iSup fun d => hmeas (d : T)

/-- **Measurable supremum over a separable index space.**

This is the dense-set-free wrapper around
`sup_measurable_countable_dense`: a separable topological index space supplies
a countable dense subset, so a sample-continuous process with measurable
evaluations has a measurable pointwise supremum. This discharges one explicit
dense-skeleton hypothesis on the path toward the infinite-index Dudley bridge;
the sample-path continuity hypothesis remains the load-bearing separability
input. -/
theorem sup_measurable_of_separableSpace
    {α : Type*} [MeasurableSpace α]
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T]
    (g : T → α → ℝ)
    (hmeas : ∀ t : T, Measurable (g t))
    (hcont : ∀ a : α, Continuous fun t : T => g t a) :
    Measurable fun a : α => ⨆ t : T, g t a := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense T
  exact sup_measurable_countable_dense (g := g) D hDcount hDdense hmeas hcont

/-- **Distance-faithful dense-sequence approximation.**

For a nonempty separable pseudometric index space, Mathlib's dense sequence has
a point inside every positive-radius ball around every target. This is the
metric atom needed to turn the separability bridge into an explicit
`ℕ`-indexed skeleton in later infinite-index Dudley steps. -/
theorem exists_denseSeq_dist_lt
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (t : T) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, dist (TopologicalSpace.denseSeq T n) t < ε := by
  classical
  have hdense : DenseRange (TopologicalSpace.denseSeq T) :=
    TopologicalSpace.denseRange_denseSeq T
  obtain ⟨n, hn⟩ := hdense.exists_mem_open
    (s := Metric.ball t ε) Metric.isOpen_ball ⟨t, by simpa using hε⟩
  exact ⟨n, by simpa [Metric.mem_ball] using hn⟩

/-- **Dense-sequence supremum reduction.**

For a continuous real-valued functional on a nonempty separable pseudometric
space, taking the supremum over Mathlib's dense sequence gives the same value as
taking the supremum over the full index type. This is the `ℕ`-indexed
specialization of the dense-subset reduction used by
`sup_measurable_countable_dense`. -/
theorem iSup_denseSeq_eq_iSup
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (f : T → ℝ) (hf : Continuous f) :
    (⨆ n : ℕ, f (TopologicalSpace.denseSeq T n)) = ⨆ t : T, f t := by
  have hdense : Dense (Set.range (TopologicalSpace.denseSeq T)) :=
    TopologicalSpace.denseRange_denseSeq T
  calc
    (⨆ n : ℕ, f (TopologicalSpace.denseSeq T n))
        = ⨆ s : Set.range (TopologicalSpace.denseSeq T), f (s : T) := by
          exact (iSup_range' f (TopologicalSpace.denseSeq T)).symm
    _ = ⨆ t : T, f t := hdense.ciSup' hf

/-- **Boundedness transfers to the dense-sequence skeleton.**

If a real-valued functional is bounded above on the full index space, then its
restriction to Mathlib's dense sequence is also bounded above. This is the
bounded-range side condition needed by later conditional-supremum arguments on
the countable skeleton. -/
theorem bddAbove_range_denseSeq
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (f : T → ℝ)
    (hbdd : BddAbove (Set.range f)) :
    BddAbove (Set.range fun n : ℕ => f (TopologicalSpace.denseSeq T n)) := by
  rcases hbdd with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hC ⟨TopologicalSpace.denseSeq T n, rfl⟩

/-- **Bounded sample paths from total boundedness and a uniform one-sided modulus.**

If every sample path has a uniform one-sided modulus, then total boundedness of
the index space bounds every sample path above. Taking the modulus at error
`1` gives a positive radius. A finite net at that radius supplies finitely many
centers, and every value of the sample path is at most the value at its chosen
center plus `1`. The finite supremum over the centers plus `1` is therefore a
genuine upper bound for the whole range. -/
theorem bddAbove_range_of_totallyBounded_uniformModulus
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε) :
    ∀ ω : Ω, BddAbove (Set.range (P.X ω)) := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := hmodulus 1 (by norm_num)
  let B := finiteNetOfTotallyBoundedUniv (T := T) hT δ hδ
  let K := B.A
  letI : Fintype K := B.instFintype
  letI : Nonempty K := B.instNonempty
  intro ω
  refine ⟨finiteSup (fun k : K => P.X ω (B.net.center k)) + 1, ?_⟩
  rintro y ⟨t, rfl⟩
  have hcover : dist t (B.net.projection t) ≤ δ := by
    simpa [B] using finiteNetOfTotallyBoundedUniv_covers (T := T) hT hδ t
  have hmod_step : P.X ω t ≤ P.X ω (B.net.projection t) + 1 :=
    hmod ω t (B.net.projection t) hcover
  have hsup :
      P.X ω (B.net.projection t) ≤
        finiteSup (fun k : K => P.X ω (B.net.center k)) := by
    unfold finiteSup
    change P.X ω (B.net.center (B.net.project t)) ≤
      (Finset.univ : Finset K).sup' Finset.univ_nonempty
        (fun k : K => P.X ω (B.net.center k))
    exact Finset.le_sup' (fun k : K => P.X ω (B.net.center k))
      (Finset.mem_univ (B.net.project t))
  linarith

/-- **Measurable supremum over the canonical dense sequence.**

For a process with measurable evaluations, the supremum over Mathlib's
`ℕ`-indexed dense sequence is measurable. No path-continuity assumption is
needed for this countable supremum statement. -/
theorem sup_measurable_denseSeq
    {α : Type*} [MeasurableSpace α]
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (g : T → α → ℝ)
    (hmeas : ∀ t : T, Measurable (g t)) :
    Measurable fun a : α => ⨆ n : ℕ, g (TopologicalSpace.denseSeq T n) a := by
  exact Measurable.iSup fun n => hmeas (TopologicalSpace.denseSeq T n)

/-- **Canonical dense-sequence supremum equals the full supremum pointwise.**

For a sample-continuous process on a nonempty separable pseudometric index
space, the countable dense-sequence supremum agrees pointwise with the full
supremum over the index type. This is the process-level form of
`iSup_denseSeq_eq_iSup`. -/
theorem denseSeq_sup_eq_full_sup
    {α : Type*} [MeasurableSpace α]
    [PseudoMetricSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (g : T → α → ℝ)
    (hcont : ∀ a : α, Continuous fun t : T => g t a) :
    (fun a : α => ⨆ n : ℕ, g (TopologicalSpace.denseSeq T n) a)
      = fun a : α => ⨆ t : T, g t a := by
  funext a
  exact iSup_denseSeq_eq_iSup (T := T) (f := fun t : T => g t a) (hcont a)

/-- **Approximate maximizer for a bounded real supremum.**

If a real-valued functional is bounded above on a nonempty index type, then
every positive error admits a point whose value is within that error of the
conditional supremum. -/
theorem exists_iSup_le_add_of_bddAbove
    [Nonempty T] (f : T → ℝ) (hbdd : BddAbove (Set.range f))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : T, (⨆ t : T, f t) ≤ f t + ε := by
  have hlt : (⨆ t : T, f t) - ε < (⨆ t : T, f t) := sub_lt_self _ hε
  rcases (lt_ciSup_iff (f := f) hbdd).mp hlt with ⟨t, ht⟩
  exact ⟨t, by linarith⟩

/-- **Outcome-indexed approximate maximizers for bounded sample paths.**

For a finite outcome space, bounded-above sample paths admit a single witness
function choosing an approximate maximizer for each outcome. -/
theorem exists_iSup_witness_function
    {Ω : Type*} [Fintype Ω] [Nonempty T]
    (Y : Ω → T → ℝ)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (Y ω)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ witness : Ω → T,
      ∀ ω : Ω, (⨆ t : T, Y ω t) ≤ Y ω (witness ω) + ε := by
  classical
  choose witness hw using
    fun ω : Ω => exists_iSup_le_add_of_bddAbove (T := T) (f := Y ω) (hbdd ω) hε
  exact ⟨witness, hw⟩

/-- **Boundary certificate for the full pointwise supremum.**

This constructs the `SeparableTerminalSupremumBoundaryChoice` certificate for
the actual full supremum functional `ω ↦ ⨆ t, P.X ω t`. Total boundedness
supplies the finite skeleton at `skeletonRadius`; bounded sample paths supply
approximate maximizers for the full supremum; the two pathwise modulus
hypotheses move from ambient points to the finite skeleton and from the
skeleton to the terminal dyadic projection. Entropy side conditions and the
coarse projected budget are still explicit because they are separate analytic
inputs. -/
theorem separableTerminalSupremumBoundaryChoice_of_iSup_pathwiseModuli
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    {eta : ℝ} {m : ℕ}
    (witnessError skeletonRadius skeletonError terminalError : ℝ)
    (hwitnessError : 0 < witnessError)
    (hskeletonRadius : 0 < skeletonRadius)
    (herror : witnessError + skeletonError + terminalError ≤ eta)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hskeletonModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius →
        P.X ω s ≤ P.X ω t + skeletonError)
    (hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m) :
    SeparableTerminalSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  classical
  let B := finiteNetOfTotallyBoundedUniv (T := T) hT skeletonRadius hskeletonRadius
  let K := B.A
  letI : Fintype K := B.instFintype
  letI : Nonempty K := B.instNonempty
  let embed : K → T := B.net.center
  let nearest : T → K := B.net.project
  have hcover : ∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius := by
    intro t
    simpa [B, embed, nearest, FiniteNet.projection] using
      finiteNetOfTotallyBoundedUniv_covers (T := T) hT hskeletonRadius t
  obtain ⟨witness, hwitness⟩ :=
    exists_iSup_witness_function (T := T) (Y := P.X) hbdd hwitnessError
  have hskeletonApprox :
      ∀ ω : Ω, ∀ t : T,
        P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError :=
    skeletonApprox_of_finiteCover_pathwiseModulus
      (P := P) embed nearest skeletonRadius skeletonError hcover hskeletonModulus
  have hseparable :
      ∀ ω : Ω,
        (⨆ t : T, P.X ω t) ≤
          finiteSup (fun k : K => P.X ω (embed k)) +
            (witnessError + skeletonError) :=
    supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
      (embed := embed) (nearest := nearest) (Y := P.X)
      (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
      (witness := witness) (witnessError := witnessError)
      (skeletonError := skeletonError) hwitness hskeletonApprox
  have herror' : (witnessError + skeletonError) + terminalError ≤ eta := by
    linarith
  exact separableTerminalSupremumBoundaryChoice_of_pathwiseTerminalModulus
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius)
    (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
    (eta := eta) (m := m) (embed := embed)
    (separabilityError := witnessError + skeletonError)
    (terminalError := terminalError) herror' hcard hentropyAtRadius
    hintervalIntegrable hseparable hterminalModulus hcoarse

/-- Singleton-safe boundary certificate for the full pointwise supremum.

This is the no-cardinality variant of
`separableTerminalSupremumBoundaryChoice_of_iSup_pathwiseModuli`; it keeps the
finite skeleton nonempty but does not require nontrivial projection-pair
cardinalities. -/
theorem separableTerminalSupremumBoundaryChoiceNonempty_of_iSup_pathwiseModuli
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    {eta : ℝ} {m : ℕ}
    (witnessError skeletonRadius skeletonError terminalError : ℝ)
    (hwitnessError : 0 < witnessError)
    (hskeletonRadius : 0 < skeletonRadius)
    (herror : witnessError + skeletonError + terminalError ≤ eta)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hskeletonModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius →
        P.X ω s ≤ P.X ω t + skeletonError)
    (hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m) :
    SeparableTerminalSupremumBoundaryChoiceNonempty
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  classical
  let B := finiteNetOfTotallyBoundedUniv (T := T) hT skeletonRadius hskeletonRadius
  let K := B.A
  letI : Fintype K := B.instFintype
  letI : Nonempty K := B.instNonempty
  let embed : K → T := B.net.center
  let nearest : T → K := B.net.project
  have hcover : ∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius := by
    intro t
    simpa [B, embed, nearest, FiniteNet.projection] using
      finiteNetOfTotallyBoundedUniv_covers (T := T) hT hskeletonRadius t
  obtain ⟨witness, hwitness⟩ :=
    exists_iSup_witness_function (T := T) (Y := P.X) hbdd hwitnessError
  have hskeletonApprox :
      ∀ ω : Ω, ∀ t : T,
        P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError :=
    skeletonApprox_of_finiteCover_pathwiseModulus
      (P := P) embed nearest skeletonRadius skeletonError hcover hskeletonModulus
  have hseparable :
      ∀ ω : Ω,
        (⨆ t : T, P.X ω t) ≤
          finiteSup (fun k : K => P.X ω (embed k)) +
            (witnessError + skeletonError) :=
    supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
      (embed := embed) (nearest := nearest) (Y := P.X)
      (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
      (witness := witness) (witnessError := witnessError)
      (skeletonError := skeletonError) hwitness hskeletonApprox
  have herror' : (witnessError + skeletonError) + terminalError ≤ eta := by
    linarith
  exact separableTerminalSupremumBoundaryChoiceNonempty_of_pathwiseTerminalModulus
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius)
    (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
    (eta := eta) (m := m) (embed := embed)
    (separabilityError := witnessError + skeletonError)
    (terminalError := terminalError) herror' hentropyAtRadius
    hintervalIntegrable hseparable hterminalModulus hcoarse

/-- The terminal radii of the dyadic chaining net schedule tend to zero. -/
theorem tendsto_dyadicChainingNetRadius_atTop (radiusScale : ℝ) :
    Tendsto (fun m : ℕ => dyadicChainingNetRadius radiusScale m) atTop (𝓝 0) := by
  unfold dyadicChainingNetRadius
  have h12 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshift : Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ (m + 2)) atTop (𝓝 0) :=
    h12.comp (tendsto_add_atTop_nat 2)
  have hmul :
      Tendsto (fun m : ℕ => radiusScale * ((1 : ℝ) / 2) ^ (m + 2)) atTop
        (𝓝 (radiusScale * 0)) := hshift.const_mul radiusScale
  rw [mul_zero] at hmul
  refine hmul.congr ?_
  intro m
  rw [div_pow, one_pow, mul_one_div]

/-- Some dyadic terminal radius is smaller than any positive target scale. -/
theorem exists_dyadicChainingNetRadius_le
    (radiusScale : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, dyadicChainingNetRadius radiusScale m ≤ δ := by
  have hsmall_lt : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m < δ := by
    exact (tendsto_dyadicChainingNetRadius_atTop radiusScale).eventually_lt_const hδ
  have hsmall : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m ≤ δ :=
    hsmall_lt.mono fun _ hm => le_of_lt hm
  rcases Filter.eventually_atTop.mp hsmall with ⟨m, hm⟩
  exact ⟨m, hm m le_rfl⟩

/-- Select a dyadic boundary scale from eventual finite-scale obligations.

The analytic content is the small-radius choice: since the dyadic terminal
radii tend to zero, a sufficiently late scale fits any positive terminal
modulus radius. Intersecting that eventual small-radius condition with eventual
cardinality, entropy-envelope, interval-integrability, and coarse-budget
obligations gives the `hscale` selector used by the full-supremum boundary
constructor. -/
theorem dyadicChainingScaleSelector_of_eventually_obligations
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ δ : ℝ, 0 < δ →
      ∃ m : ℕ,
        dyadicChainingNetRadius radiusScale m ≤ δ ∧
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m) := by
  intro δ hδ
  have hsmall_lt : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m < δ := by
    exact (tendsto_dyadicChainingNetRadius_atTop radiusScale).eventually_lt_const hδ
  have hsmall : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m ≤ δ :=
    hsmall_lt.mono fun _ hm => le_of_lt hm
  have hboth := hsmall.and hobligations
  rcases Filter.eventually_atTop.mp hboth with ⟨m, hm⟩
  rcases hm m le_rfl with ⟨hscale, hcard, hentropyAtRadius,
    hintervalIntegrable, hcoarse⟩
  exact ⟨m, hscale, hcard, hentropyAtRadius, hintervalIntegrable, hcoarse⟩

/-- Singleton-safe dyadic boundary scale selector from eventual finite-scale
obligations. This keeps the analytic small-radius selection and drops only the
nontrivial projection-pair cardinality obligation. -/
theorem dyadicChainingScaleSelector_of_eventually_obligations_nonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ δ : ℝ, 0 < δ →
      ∃ m : ℕ,
        dyadicChainingNetRadius radiusScale m ≤ δ ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m) := by
  intro δ hδ
  have hsmall_lt : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m < δ := by
    exact (tendsto_dyadicChainingNetRadius_atTop radiusScale).eventually_lt_const hδ
  have hsmall : ∀ᶠ m : ℕ in atTop,
      dyadicChainingNetRadius radiusScale m ≤ δ :=
    hsmall_lt.mono fun _ hm => le_of_lt hm
  have hboth := hsmall.and hobligations
  rcases Filter.eventually_atTop.mp hboth with ⟨m, hm⟩
  rcases hm m le_rfl with ⟨hscale, hentropyAtRadius, hintervalIntegrable, hcoarse⟩
  exact ⟨m, hscale, hentropyAtRadius, hintervalIntegrable, hcoarse⟩

/-- **Boundary certificates for the full supremum from a uniform path modulus.**

This packages the choice of witness error, skeleton scale, and terminal dyadic
scale for the full conditional supremum `ω ↦ ⨆ t, P.X ω t`. Bounded sample paths
give approximate maximizers for the supremum; the supplied one-sided uniform
modulus gives the finite skeleton and terminal projection errors; `hscale`
selects a dyadic terminal level whose radius fits the terminal modulus and
supplies the finite entropy/coarse-budget data at that level. -/
theorem separableTerminalSupremumBoundaryChoice_exists_of_iSup_uniformModulus
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hscale : ∀ δ : ℝ, 0 < δ →
      ∃ m : ℕ,
        dyadicChainingNetRadius radiusScale m ≤ δ ∧
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  intro eta heta
  have hthird : 0 < eta / (3 : ℝ) := by positivity
  rcases hmodulus (eta / (3 : ℝ)) hthird with
    ⟨skeletonRadius, hskeletonRadius, hskeletonModulus⟩
  rcases hmodulus (eta / (3 : ℝ)) hthird with
    ⟨terminalRadius, hterminalRadius, hterminalModulus₀⟩
  rcases hscale terminalRadius hterminalRadius with
    ⟨m, hterminalScale, hcard, hentropyAtRadius,
      hintervalIntegrable, hcoarse⟩
  have hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + eta / (3 : ℝ) := by
    intro ω s t hdist
    exact hterminalModulus₀ ω s t (hdist.trans hterminalScale)
  have herror :
      eta / (3 : ℝ) + eta / (3 : ℝ) + eta / (3 : ℝ) ≤ eta := by
    linarith
  refine ⟨m, ?_⟩
  exact separableTerminalSupremumBoundaryChoice_of_iSup_pathwiseModuli
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius)
    (eta := eta) (m := m)
    (witnessError := eta / (3 : ℝ))
    (skeletonRadius := skeletonRadius)
    (skeletonError := eta / (3 : ℝ))
    (terminalError := eta / (3 : ℝ))
    hthird hskeletonRadius herror hbdd hcard hentropyAtRadius
    hintervalIntegrable hskeletonModulus hterminalModulus hcoarse

/-- Singleton-safe boundary certificates for the full supremum from a uniform
path modulus. This version has no nontrivial projection-pair cardinality
obligation; the selected scale supplies only the terminal-radius, entropy,
integrability, and coarse-budget data. -/
theorem separableTerminalSupremumBoundaryChoiceNonempty_exists_of_iSup_uniformModulus
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hscale : ∀ δ : ℝ, 0 < δ →
      ∃ m : ℕ,
        dyadicChainingNetRadius radiusScale m ≤ δ ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  intro eta heta
  have hthird : 0 < eta / (3 : ℝ) := by positivity
  rcases hmodulus (eta / (3 : ℝ)) hthird with
    ⟨skeletonRadius, hskeletonRadius, hskeletonModulus⟩
  rcases hmodulus (eta / (3 : ℝ)) hthird with
    ⟨terminalRadius, hterminalRadius, hterminalModulus₀⟩
  rcases hscale terminalRadius hterminalRadius with
    ⟨m, hterminalScale, hentropyAtRadius, hintervalIntegrable, hcoarse⟩
  have hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + eta / (3 : ℝ) := by
    intro ω s t hdist
    exact hterminalModulus₀ ω s t (hdist.trans hterminalScale)
  have herror :
      eta / (3 : ℝ) + eta / (3 : ℝ) + eta / (3 : ℝ) ≤ eta := by
    linarith
  refine ⟨m, ?_⟩
  exact separableTerminalSupremumBoundaryChoiceNonempty_of_iSup_pathwiseModuli
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius)
    (eta := eta) (m := m)
    (witnessError := eta / (3 : ℝ))
    (skeletonRadius := skeletonRadius)
    (skeletonError := eta / (3 : ℝ))
    (terminalError := eta / (3 : ℝ))
    hthird hskeletonRadius herror hbdd hentropyAtRadius
    hintervalIntegrable hskeletonModulus hterminalModulus hcoarse

/-- Boundary certificates for the full supremum, with the dyadic scale selected
from eventual finite-scale obligations.

This discharges the `hscale` selector in
`separableTerminalSupremumBoundaryChoice_exists_of_iSup_uniformModulus`: the
dyadic terminal radii tend to zero, so any positive terminal modulus radius can
be met at a sufficiently late scale, and the eventual finite-scale obligations
hold at the same selected scale. -/
theorem separableTerminalSupremumBoundaryChoice_exists_of_iSup_uniformModulus_eventually
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  exact separableTerminalSupremumBoundaryChoice_exists_of_iSup_uniformModulus
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius) hbdd hmodulus
    (dyadicChainingScaleSelector_of_eventually_obligations
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius) hobligations)

/-- Singleton-safe boundary certificates for the full supremum, with the dyadic
scale selected from eventual entropy/integrability/coarse obligations. -/
theorem separableTerminalSupremumBoundaryChoiceNonempty_exists_of_iSup_uniformModulus_eventually
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget m)) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
  exact separableTerminalSupremumBoundaryChoiceNonempty_exists_of_iSup_uniformModulus
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (hradiusScale := hradiusScale)
    (entropyAtRadius := entropyAtRadius) hbdd hmodulus
    (dyadicChainingScaleSelector_of_eventually_obligations_nonempty
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius) hobligations)

/-! ## The dyadic refinement limit of the verified discrete bricks -/

/-- **Dyadic limit of the total-bounded discrete bricks.**

The finite truncated interval integral paid by the brick-2 terminal bounds,
`∫ ε in (radiusScale / 2^(m+1))..(radiusScale / 2), entropyAtRadius ε`,
converges to the continuous Dudley entropy integral
`∫ ε in 0..(radiusScale / 2), entropyAtRadius ε` as the dyadic scale sequence
refines (`m → ∞`), provided the entropy profile is interval-integrable on
`[0, radiusScale / 2]`.

By `FiniteSubGaussianChaining.shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral`
the truncated integral equals the discrete dyadic annulus-integral sum, so this
is exactly "the discrete sum converges to the continuous integral." -/
theorem dyadic_limit_of_total_bounded_bricks
    (radiusScale : ℝ) (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2)) :
    Tendsto
      (fun m : ℕ =>
        ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
      atTop
      (𝓝 (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)) := by
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  -- pointwise bounds on the dyadic floor `radiusScale / 2^(m+1)`
  have ha_nonneg : ∀ m : ℕ, (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) := fun m =>
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : ∀ m : ℕ, radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    intro m
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  -- the dyadic floor tends to 0
  have ha_tendsto :
      Tendsto (fun m : ℕ => radiusScale / (2 : ℝ) ^ (m + 1)) atTop (𝓝 0) := by
    have h12 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hshift : Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ (m + 1)) atTop (𝓝 0) :=
      h12.comp (tendsto_add_atTop_nat 1)
    have hmul :
        Tendsto (fun m : ℕ => radiusScale * ((1 : ℝ) / 2) ^ (m + 1)) atTop
          (𝓝 (radiusScale * 0)) := hshift.const_mul radiusScale
    rw [mul_zero] at hmul
    refine hmul.congr ?_
    intro m
    rw [div_pow, one_pow, mul_one_div]
  -- ... refined to land inside `Icc 0 (radiusScale/2)`
  have ha_within :
      Tendsto (fun m : ℕ => radiusScale / (2 : ℝ) ^ (m + 1)) atTop
        (𝓝[Set.Icc (0 : ℝ) (radiusScale / 2)] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ha_tendsto
    · exact Eventually.of_forall (fun m => ⟨ha_nonneg m, ha_le m⟩)
  -- the integral primitive `x ↦ ∫ 0..x` is continuous within `Icc 0 (radiusScale/2)` at 0
  have hcwa :
      ContinuousWithinAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, entropyAtRadius t)
        (Set.Icc 0 (radiusScale / 2)) 0 := by
    refine intervalIntegral.continuousWithinAt_primitive ?_ ?_
    · simp
    · have hmin : min (0 : ℝ) 0 = 0 := min_self 0
      have hmax : max (0 : ℝ) (radiusScale / 2) = radiusScale / 2 := max_eq_right hb_pos.le
      rw [hmin, hmax]; exact hint0
  -- hence `∫ 0..(floor m)` tends to `∫ 0..0 = 0`
  have hsmall :
      Tendsto (fun m : ℕ => ∫ t in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius t)
        atTop (𝓝 0) := by
    have hcomp := (hcwa.tendsto).comp ha_within
    change Tendsto
      (fun m : ℕ => ∫ t in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius t)
      atTop (𝓝 (∫ t in (0 : ℝ)..0, entropyAtRadius t)) at hcomp
    simpa only [intervalIntegral.integral_same] using hcomp
  -- decompose each truncated integral via adjacent-interval additivity
  have hdecomp : ∀ m : ℕ,
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        = (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)
          - (∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε) := by
    intro m
    have hsub1 :
        Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
          ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg m, ha_le m⟩)
    have hsub2 :
        Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
          ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
      Set.uIcc_subset_uIcc
        (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg m, ha_le m⟩)
        Set.right_mem_uIcc
    have hI1 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
      hint0.mono_set hsub1
    have hI2 :
        IntervalIntegrable entropyAtRadius volume (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
      hint0.mono_set hsub2
    have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    linarith [hadd]
  -- assemble: `∫ 0..b - ∫ 0..(floor m) → ∫ 0..b - 0`
  have hmain :
      Tendsto
        (fun m : ℕ => (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)
            - (∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε))
        atTop (𝓝 ((∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) - 0)) :=
    tendsto_const_nhds.sub hsmall
  rw [sub_zero] at hmain
  exact Filter.Tendsto.congr (fun m => (hdecomp m).symm) hmain

/-! ## The continuous Dudley entropy integral bound -/

/-- **Continuous Dudley entropy integral bound.**

The expected supremum of the finite sub-Gaussian process is bounded by the
continuous Dudley entropy integral:

  `E[supFunctional] ≤ coarseBudget + 4 · √(2 · varianceProxy) · ∫₀^{radiusScale/2} entropyAtRadius`.

The bound is obtained from the verified discrete total-bounded bricks via the
global-budget adapter
`TotalBoundedDudley.finite_separableTerminal_dudley_totalBounded_globalBudget`:
each finite truncated integral is dominated by the full continuous integral
(nonnegative entropy profile), and the resulting uniform budget removes the
boundary error. The dyadic refinement
`dyadic_limit_of_total_bounded_bricks` certifies that the continuous integral is
the limit of those finite truncated integrals, so the bound is the tight
limiting object rather than a loose over-estimate.

In the empirical Rademacher normalization `varianceProxy ≍ B²/n`, so
`4 · √(2 · varianceProxy)` is the `C / √n` constant of Boucheron–Lugosi–Massart
2013 §13, and `entropyAtRadius ε` plays the role of `√(log N(F, ε))`. -/
theorem continuous_dudley_entropy_integral
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  -- discharge via the verified brick-2 global-budget adapter; the finite
  -- truncated integrals are each dominated by the full continuous integral
  refine finite_separableTerminal_dudley_totalBounded_globalBudget
    (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := supFunctional)
    (globalBudget := coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
      (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε))
    hradiusScale hdistP hvariance hentropy_antitone hchoose ?_
  intro m
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) :=
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  -- the finite truncated integral is dominated by the full continuous integral
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
  have hsub2 :
      Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
      Set.right_mem_uIcc
  have hI1 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hnn : 0 ≤ ∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε :=
    intervalIntegral.integral_nonneg ha_nonneg (fun u _ => hentropy_nonneg u)
  have hdom :
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        ≤ ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
    linarith [hadd, hnn]
  have hsqrt_nonneg : 0 ≤ 4 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdom hsqrt_nonneg
  linarith [hmul]

/-- Singleton-safe continuous Dudley entropy integral bound.

This is the no-cardinality version of `continuous_dudley_entropy_integral`; the
finite boundary certificates only require nonempty skeletons. -/
theorem continuous_dudley_entropy_integral_nonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  refine finite_separableTerminal_dudley_totalBounded_globalBudget_nonempty
    (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := supFunctional)
    (globalBudget := coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
      (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε))
    hradiusScale hdistP hvariance hentropy_antitone hchoose ?_
  intro m
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) :=
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
  have hsub2 :
      Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
      Set.right_mem_uIcc
  have hI1 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hnn : 0 ≤ ∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε :=
    intervalIntegral.integral_nonneg ha_nonneg (fun u _ => hentropy_nonneg u)
  have hdom :
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        ≤ ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
    linarith [hadd, hnn]
  have hsqrt_nonneg : 0 ≤ 4 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdom hsqrt_nonneg
  linarith [hmul]

/-- **Continuous Dudley bound for the full infinite-index supremum.**

This is the full-supremum corollary over an arbitrary nonempty totally bounded
pseudometric index type. The left side is the genuine pointwise conditional
supremum `ω ↦ ⨆ t, P.X ω t`; the finite boundary certificate is built inside
the proof from bounded sample paths, total-bounded finite skeletons, and the
pathwise modulus data supplied for each positive boundary budget. -/
theorem continuous_dudley_entropy_integral_iSup_of_pathwiseModuli
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ, ∃ witnessError : ℝ, ∃ skeletonRadius : ℝ,
      ∃ skeletonError : ℝ, ∃ terminalError : ℝ,
        0 < witnessError ∧
        0 < skeletonRadius ∧
        witnessError + skeletonError + terminalError ≤ eta ∧
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ ω : Ω, ∀ s t : T,
          dist s t ≤ skeletonRadius →
            P.X ω s ≤ P.X ω t + skeletonError) ∧
        (∀ ω : Ω, ∀ s t : T,
          dist s t ≤ dyadicChainingNetRadius radiusScale m →
            P.X ω s ≤ P.X ω t + terminalError) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget)) :
    finiteExpectation P.weight (fun ω : Ω => ⨆ t : T, P.X ω t) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  have hboundary : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t) eta m := by
    intro eta heta
    rcases hchoose eta heta with
      ⟨m, witnessError, skeletonRadius, skeletonError, terminalError,
        hwitnessError, hskeletonRadius, herror, hcard, hentropyAtRadius,
        hintervalIntegrable, hskeletonModulus, hterminalModulus, hcoarse⟩
    refine ⟨m, ?_⟩
    exact separableTerminalSupremumBoundaryChoice_of_iSup_pathwiseModuli
      (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (eta := eta) (m := m)
      (witnessError := witnessError) (skeletonRadius := skeletonRadius)
      (skeletonError := skeletonError) (terminalError := terminalError)
      hwitnessError hskeletonRadius herror hbdd hcard hentropyAtRadius
      hintervalIntegrable hskeletonModulus hterminalModulus (by simpa using hcoarse)
  exact continuous_dudley_entropy_integral
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
    hradiusScale hdistP hvariance hentropy_antitone hentropy_nonneg hint0
    hboundary

/-- **Continuous Dudley bound for the full supremum from uniform modulus data.**

This variant uses the dyadic scale selector
`dyadicChainingScaleSelector_of_eventually_obligations` to build the
separability/terminal boundary certificate. The caller supplies bounded sample
paths, a one-sided uniform modulus for the process paths, and eventual
finite-scale entropy/cardinality/coarse-budget obligations; the theorem selects
a terminal dyadic level compatible with the terminal modulus radius. -/
theorem continuous_dudley_entropy_integral_iSup_of_uniformModulus_eventually
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget)) :
    finiteExpectation P.weight (fun ω : Ω => ⨆ t : T, P.X ω t) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  exact continuous_dudley_entropy_integral
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
    hradiusScale hdistP hvariance hentropy_antitone hentropy_nonneg hint0
    (separableTerminalSupremumBoundaryChoice_exists_of_iSup_uniformModulus_eventually
      (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius) hbdd hmodulus hobligations)

/-- Singleton-safe continuous Dudley bound for the full supremum from uniform
modulus data and eventual entropy/integrability/coarse obligations. -/
theorem continuous_dudley_entropy_integral_iSup_of_uniformModulus_eventually_nonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hbdd : ∀ ω : Ω, BddAbove (Set.range (P.X ω)))
    (hmodulus : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ ω : Ω, ∀ s t : T,
          dist s t ≤ δ → P.X ω s ≤ P.X ω t + ε)
    (hobligations : ∀ᶠ m : ℕ in atTop,
        (∀ j ∈ Finset.range m,
          FiniteSubGaussianProcess.finitePrefixSupEnvelope
              (fun j => Real.sqrt (Real.log
                (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          coarseBudget)) :
    finiteExpectation P.weight (fun ω : Ω => ⨆ t : T, P.X ω t) ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  exact continuous_dudley_entropy_integral_nonempty
    (P := P) (hT := hT) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := fun ω : Ω => ⨆ t : T, P.X ω t)
    hradiusScale hdistP hvariance hentropy_antitone hentropy_nonneg hint0
    (separableTerminalSupremumBoundaryChoiceNonempty_exists_of_iSup_uniformModulus_eventually
      (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius) hbdd hmodulus hobligations)

end

end FormalSLT.Covering.ContinuousDudley
