import FormalSLT.Covering.ContinuousDudley
import FormalSLT.Covering.DudleySumToIntegral

/-!
# Continuous Dudley entropy integral for a covering-number profile

This module specializes brick 3
(`FormalSLT.Covering.ContinuousDudley.continuous_dudley_entropy_integral`) to the
covering-number entropy profile `entropyAtRadius ε = √(log N(F, ε))`, where
`N(F, ε) = coveringNumberAtRadius ε` is an abstract positive antitone
covering-number function supplied by the caller.

The continuous theorem carries three structural side conditions on the entropy
profile (antitonicity, nonnegativity, interval integrability on
`[0, radiusScale/2]`) plus the separability/terminal boundary certificate
`SeparableTerminalSupremumBoundaryChoice`. For the covering-number profile the
three structural conditions are discharged from the named bricks
`DudleySumToIntegral.coveringNumber_entropy_antitone`,
`Real.sqrt_nonneg`, and
`DudleySumToIntegral.coveringNumber_entropy_integrable_of_antitone`.

The boundary certificate additionally contains a per-scale comparison: the
finite prefix-sup envelope of the dyadic chaining cover-count entropies must be
bounded by the covering-number entropy profile at each annulus floor
`radiusScale / 2^(j+1)`. The single piece of genuine analysis in this module,
`coveringNumber_entropy_dominates_dyadicCoverEnvelope`, produces exactly that
conjunct from a pointwise domination of the dyadic chaining cover counts by the
covering-number profile, using monotonicity of the radius schedule and
antitonicity of `coveringNumberAtRadius`.

The terminal theorem
`continuous_dudley_entropy_integral_of_coveringNumber` then reads, in the
empirical Rademacher normalization `varianceProxy ≍ B²/n`,

  `E[ sup_F X ] ≤ coarseBudget + 4 · √(2 · σ²) · ∫₀^{radiusScale/2} √(log N(F, ε)) dε`,

which is the `C/√n · ∫ √(log N) ` form of the Dudley entropy integral.
-/

namespace FormalSLT.Covering.ContinuousDudleyCovering

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.DudleySumToIntegral

noncomputable section

variable {T : Type u}

/-- The covering-number entropy profile dominates the finite prefix-sup envelope
of the dyadic chaining cover-count entropies at every annulus floor.

From a pointwise domination of the dyadic chaining cover counts by the
covering-number profile at the floor `radiusScale / 2^(j+1)`, together with
antitonicity of the covering-number profile, this produces the per-scale
boundary conjunct required by `SeparableTerminalSupremumBoundaryChoice` for the
entropy profile `ε ↦ √(log N(F, ε))`.

The envelope at scale `j` is the supremum of the initial `j + 1` cover-count
entropies. For every earlier scale `k ≤ j` the cover count is dominated by
`coveringNumberAtRadius (radiusScale / 2^(k+1))`, and since the radius floor at
`k` is no smaller than at `j`, antitonicity moves the bound down to the floor at
`j`; `Real.log` and `Real.sqrt` monotonicity then close each term, and
`Finset.sup'_le` lifts the pointwise bound to the envelope. -/
theorem coveringNumber_entropy_dominates_dyadicCoverEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_dominates : ∀ j : ℕ,
      dyadicChainingCoverCount (T := T) hT hradiusScale j ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (m : ℕ) :
    ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        Real.sqrt (Real.log
          (coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) : ℝ)) := by
  intro j _hj
  -- reduce the envelope to a supremum over the prefix `range (j + 1)`
  unfold FiniteSubGaussianProcess.finitePrefixSupEnvelope
  refine Finset.sup'_le _ _ ?_
  intro k hk
  have hk_le_j : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  -- the floor radius is monotone decreasing in the scale index
  have hradius_floor :
      radiusScale / (2 : ℝ) ^ (j + 1) ≤ radiusScale / (2 : ℝ) ^ (k + 1) := by
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (j + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hk_le_j 1)
    have hk_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    exact div_le_div_of_nonneg_left hradiusScale.le hk_pos hpow
  -- antitonicity of the covering-number profile moves the floor from k to j
  have hcover_step :
      coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (k + 1)) ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) :=
    hcover_antitone hradius_floor
  -- chain the cover-count domination through the floor move (Nat level)
  have hcount_le_nat :
      dyadicChainingCoverCount (T := T) hT hradiusScale k ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) :=
    le_trans (hcover_dominates k) hcover_step
  -- positivity of the cover count at scale k, for `Real.log_le_log`; each
  -- bundled net has a nonempty finite index, so each covering number is
  -- positive and so is their product
  have hcover_pos_of_bundled :
      ∀ i : ℕ,
        0 < (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale i).coveringNumber := by
    intro i
    have :=
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale i).instNonempty
    simpa [BundledFiniteNet.coveringNumber, FiniteNet.coveringNumber] using
      (Fintype.card_pos (α :=
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale i).A))
  have hcount_pos_nat :
      0 < dyadicChainingCoverCount (T := T) hT hradiusScale k := by
    unfold dyadicChainingCoverCount
    exact Nat.mul_pos (hcover_pos_of_bundled k) (hcover_pos_of_bundled (k + 1))
  have hcount_pos_real :
      (0 : ℝ) < (dyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) := by
    exact_mod_cast hcount_pos_nat
  have hcount_le_real :
      (dyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) ≤
        (coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) : ℝ) := by
    exact_mod_cast hcount_le_nat
  -- the exact `Real.sqrt ∘ Real.log` monotonicity step
  exact Real.sqrt_le_sqrt (Real.log_le_log hcount_pos_real hcount_le_real)

/-- **Continuous Dudley entropy integral for a covering-number profile.**

Specialization of `continuous_dudley_entropy_integral` to the entropy profile
`ε ↦ √(log N(F, ε))` for an abstract positive antitone covering-number function
`coveringNumberAtRadius`. The three structural side conditions of the continuous
theorem are discharged from the named bricks; the separability/terminal boundary
certificate is supplied by the caller as `hchoose'`, with its per-scale envelope
conjunct produced from the cover-count domination `hcover_dominates` by
`coveringNumber_entropy_dominates_dyadicCoverEnvelope`.

In the empirical Rademacher normalization `varianceProxy ≍ B²/n`, the constant
`4 · √(2 · varianceProxy)` is the `C/√n` factor and `√(log N(F, ε))` is the
metric-entropy integrand, so the bound is the Dudley entropy integral
`E[ sup_F X ] ≤ coarseBudget + (C/√n) ∫₀^{radiusScale/2} √(log N(F, ε)) dε`. -/
theorem continuous_dudley_entropy_integral_of_coveringNumber
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_dominates : ∀ j : ℕ,
      dyadicChainingCoverCount (T := T) hT hradiusScale j ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hchoose' : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
      ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
      ∃ (embed : K → T), ∃ (separabilityError : ℝ), ∃ (terminalError : ℝ),
        separabilityError + terminalError ≤ eta ∧
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable
            (fun ε : ℝ =>
              Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
            MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        (∀ ω : Ω,
          supFunctional ω ≤
            finiteSup (fun k : K => P.X ω (embed k)) + separabilityError) ∧
        (∀ ω : Ω, ∀ k : K,
          P.X ω (embed k) ≤
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.projection (embed k)) +
              terminalError) ∧
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
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  -- the specialized entropy profile
  set entropyAtRadius : ℝ → ℝ :=
    fun ε => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)) with hentropy_def
  -- structural side conditions of the continuous theorem
  have hentropy_antitone : Antitone entropyAtRadius :=
    coveringNumber_entropy_antitone coveringNumberAtRadius hcover_antitone hcover_pos
  have hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε := by
    intro ε; exact Real.sqrt_nonneg _
  have hint0 :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume 0 (radiusScale / 2) :=
    coveringNumber_entropy_integrable_of_antitone
      coveringNumberAtRadius 0 (radiusScale / 2) hcover_antitone hcover_pos
  -- the per-scale envelope conjunct from the single new analytic lemma
  have henvelope := coveringNumber_entropy_dominates_dyadicCoverEnvelope
    (T := T) hT hradiusScale coveringNumberAtRadius
    hcover_antitone hcover_dominates
  -- assemble the boundary certificate required by the continuous theorem
  have hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        FormalSLT.Covering.TotalBoundedDudley.SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m := by
    intro eta heta
    obtain ⟨m, K, instK, nonemptyK, embed, separabilityError, terminalError,
      herr, hcard, hintegrable, hsep, hterm, hbudget⟩ := hchoose' eta heta
    refine ⟨m, K, instK, nonemptyK, embed, separabilityError, terminalError,
      herr, hcard, ?_, hintegrable, hsep, hterm, hbudget⟩
    -- the envelope conjunct, with the profile rewritten to its closed form
    intro j hj
    have := henvelope m j hj
    simpa [hentropy_def] using this
  -- specialize the continuous Dudley entropy integral to this profile
  have hmain :=
    FormalSLT.Covering.ContinuousDudley.continuous_dudley_entropy_integral
      (P := P) (hT := hT)
      (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional)
      hradiusScale hdistP hvariance hentropy_antitone hentropy_nonneg hint0 hchoose
  simpa [hentropy_def] using hmain

/-- **Continuous Dudley covering-number bound for the full supremum.**

Specialization of
`ContinuousDudley.continuous_dudley_entropy_integral_iSup_of_pathwiseModuli`
to the covering-number entropy profile
`ε ↦ √(log (coveringNumberAtRadius ε))`.

The left side is the full pointwise conditional supremum over the index type:
`ω ↦ ⨆ t, P.X ω t`. The caller supplies bounded sample paths and, for every
positive boundary budget, finite-scale pathwise modulus and coarse-budget data.
This theorem discharges the covering-number entropy profile obligations from
`hcover_antitone`, `hcover_pos`, and `hcover_dominates`. -/
theorem continuous_dudley_entropy_integral_iSup_of_coveringNumber
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_dominates : ∀ j : ℕ,
      dyadicChainingCoverCount (T := T) hT hradiusScale j ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
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
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  set entropyAtRadius : ℝ → ℝ :=
    fun ε => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)) with hentropy_def
  have hentropy_antitone : Antitone entropyAtRadius :=
    coveringNumber_entropy_antitone coveringNumberAtRadius hcover_antitone hcover_pos
  have hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε := by
    intro ε
    exact Real.sqrt_nonneg _
  have hint0 :
      IntervalIntegrable entropyAtRadius MeasureTheory.volume 0 (radiusScale / 2) :=
    coveringNumber_entropy_integrable_of_antitone
      coveringNumberAtRadius 0 (radiusScale / 2) hcover_antitone hcover_pos
  have henvelope := coveringNumber_entropy_dominates_dyadicCoverEnvelope
    (T := T) hT hradiusScale coveringNumberAtRadius
    hcover_antitone hcover_dominates
  have hchoose' : ∀ eta : ℝ, 0 < eta →
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
          coarseBudget) := by
    intro eta heta
    rcases hchoose eta heta with
      ⟨m, witnessError, skeletonRadius, skeletonError, terminalError,
        hwitnessError, hskeletonRadius, herror, hcard, hskeletonModulus,
        hterminalModulus, hcoarse⟩
    refine ⟨m, witnessError, skeletonRadius, skeletonError, terminalError,
      hwitnessError, hskeletonRadius, herror, hcard, ?_, ?_,
      hskeletonModulus, hterminalModulus, hcoarse⟩
    · intro j hj
      have := henvelope m j hj
      simpa [hentropy_def] using this
    · intro j _hj
      simpa [hentropy_def] using
        (coveringNumber_entropy_integrable_of_antitone
          coveringNumberAtRadius
          (radiusScale / (2 : ℝ) ^ (j + 2))
          (radiusScale / (2 : ℝ) ^ (j + 1))
          hcover_antitone hcover_pos)
  have hmain :=
    FormalSLT.Covering.ContinuousDudley.continuous_dudley_entropy_integral_iSup_of_pathwiseModuli
      (P := P) (hT := hT)
      (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (entropyAtRadius := entropyAtRadius)
      hradiusScale hdistP hvariance hentropy_antitone hentropy_nonneg
      hint0 hbdd hchoose'
  simpa [hentropy_def] using hmain

end

end FormalSLT.Covering.ContinuousDudleyCovering
