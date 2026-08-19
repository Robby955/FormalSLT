/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant
import FormalSLT.PACBayes.StabilityBridge

/-!
# Time-uniform empirical transition confidence for finite Markov kernels

For a finite-state Markov path with transition kernel `P`, this module treats
each visit-gated transition indicator

`1{x_k = z, x_{k+1} = y}`

as a bounded trajectory score.  Its predictable conditional mean is
`1{x_k = z} P(z,y)`.  Applying the predictable-mean forward-Bessel theorem to
all source/destination coordinates and to their complements gives one
outer-probability event, uniform over time, on which every transition
coordinate has a two-sided empirical-Bernstein confidence interval.

When a source state has positive visit count, the interval normalizes to an
explicit confidence radius for `P(z,y)`.  Summing coordinate radii gives a
row-total-variation certificate.  The candidate kernel appears only after
the common coordinate event has been constructed, so the final deterministic
substitution permits a candidate selected from the observed path.

The initial state is deterministic, and the first scored transition is
`x 0 -> x 1`.  No positive radius is claimed for an unvisited row; normalized
theorems explicitly assume a positive visit mass.  No invariant law is
estimated here, and no data-dependent Poisson-potential theorem is claimed.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.StochasticDynamics

noncomputable section

attribute [local instance 0] Classical.propDecidable

variable {Z : Type*} [Fintype Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- A finite hypothesis indexing a transition coordinate and whether the
direct indicator or its complement is used. -/
structure TransitionCoordinate (Z : Type*) where
  source : Z
  destination : Z
  complement : Bool
deriving DecidableEq, Fintype

instance transitionCoordinate.instNonempty :
    Nonempty (TransitionCoordinate Z) :=
  let z := Classical.choice (inferInstance : Nonempty Z)
  ⟨⟨z, z, false⟩⟩

/-- The direct visit-gated transition indicator. -/
def transitionIndicatorScore (z y : Z) : MarkovTransitionScore Z :=
  fun current next ↦ if current = z ∧ next = y then 1 else 0

/-- The direct indicator (`complement = false`) or its complement
(`complement = true`). -/
def transitionCoordinateMarkovScore
    (c : TransitionCoordinate Z) : MarkovTransitionScore Z :=
  if c.complement then
    fun current next ↦ 1 - transitionIndicatorScore c.source c.destination current next
  else
    transitionIndicatorScore c.source c.destination

/-- Transition-coordinate scores in the prefix-dependent trajectory API. -/
def transitionCoordinateTrajectoryScore
    (c : TransitionCoordinate Z) : TrajectoryScore Z :=
  markovTransitionTrajectoryScore (transitionCoordinateMarkovScore c)

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma transitionIndicatorScore_mem_Icc (z y current next : Z) :
    transitionIndicatorScore z y current next ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : current = z ∧ next = y <;>
    simp [transitionIndicatorScore, h]

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma transitionCoordinateMarkovScore_mem_Icc
    (c : TransitionCoordinate Z) (current next : Z) :
    transitionCoordinateMarkovScore c current next ∈ Set.Icc (0 : ℝ) 1 := by
  cases h : c.complement
  · simpa [transitionCoordinateMarkovScore, h] using
      transitionIndicatorScore_mem_Icc c.source c.destination current next
  · have hi :=
      transitionIndicatorScore_mem_Icc c.source c.destination current next
    rw [Set.mem_Icc] at hi ⊢
    simp only [transitionCoordinateMarkovScore, h]
    rw [if_pos trivial]
    constructor <;> linarith

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma transitionCoordinateTrajectoryScore_mem_Icc
    (c : TransitionCoordinate Z) (n : ℕ)
    (u : (i : Finset.Iic n) → Z) (next : Z) :
    transitionCoordinateTrajectoryScore c n u next ∈ Set.Icc (0 : ℝ) 1 := by
  exact transitionCoordinateMarkovScore_mem_Icc c
    (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) next

/-- Real-valued number of visits to source state `z` before the first `n`
transitions. -/
def transitionVisitMass (z : Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  ∑ k ∈ Finset.range n, if x k = z then 1 else 0

/-- Real-valued number of observed `z -> y` transitions among the first `n`
transitions. -/
def transitionEdgeMass (z y : Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  ∑ k ∈ Finset.range n, transitionIndicatorScore z y (x k) (x (k + 1))

/-- Empirical transition frequency for a visited row.  Lean division is total,
but statistical theorems using this definition assume positive visit mass. -/
def empiricalTransitionFrequency (z y : Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  transitionEdgeMass z y n x / transitionVisitMass z n x

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma transitionVisitMass_nonneg (z : Z) (n : ℕ) (x : ℕ → Z) :
    0 ≤ transitionVisitMass z n x := by
  unfold transitionVisitMass
  exact Finset.sum_nonneg fun k _hk ↦ by split <;> norm_num

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma observedTrajectoryScore_transitionCoordinate_direct
    (z y : Z) (n : ℕ) (x : ℕ → Z) :
    observedTrajectoryScore
        (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x =
      transitionIndicatorScore z y (x n) (x (n + 1)) := by
  rfl

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
lemma observedTrajectoryScore_transitionCoordinate_complement
    (z y : Z) (n : ℕ) (x : ℕ → Z) :
    observedTrajectoryScore
        (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x =
      1 - transitionIndicatorScore z y (x n) (x (n + 1)) := by
  rfl

omit [Nonempty Z] in
/-- The transition-indicator row risk is its source-visit gate times the true
transition probability. -/
lemma markovRowRisk_transitionIndicatorScore
    (P : Z → PMF Z) (z y current : Z) :
    markovRowRisk P (transitionIndicatorScore z y) current =
      if current = z then (P z y).toReal else 0 := by
  classical
  by_cases hcurrent : current = z
  · subst current
    simp only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul]
    rw [Finset.sum_eq_single y]
    · simp [transitionIndicatorScore]
    · intro b _hb hby
      simp [transitionIndicatorScore, hby]
    · intro hy
      exact False.elim (hy (Finset.mem_univ y))
  · simp only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul]
    simp [transitionIndicatorScore, hcurrent]

omit [Nonempty Z] in
/-- Complementing the indicator complements its row risk. -/
lemma markovRowRisk_transitionCoordinate_complement
    (P : Z → PMF Z) (z y current : Z) :
    markovRowRisk P (transitionCoordinateMarkovScore ⟨z, y, true⟩) current =
      1 - (if current = z then (P z y).toReal else 0) := by
  classical
  simp only [transitionCoordinateMarkovScore]
  rw [if_pos trivial]
  simp only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  have hmass : ∑ next : Z, (P current next).toReal = 1 :=
    finitePMF_real_mass_sum (P current)
  rw [hmass]
  rw [show (∑ next : Z,
      (P current next).toReal * transitionIndicatorScore z y current next) =
        (if current = z then (P z y).toReal else 0) by
    simpa only [markovRowRisk, PMF.integral_eq_sum, smul_eq_mul] using
      markovRowRisk_transitionIndicatorScore P z y current]

omit [Nonempty Z] in
/-- Direct conditional-mean identity at time `k`. -/
lemma conditionalTrajectoryRisk_transitionCoordinate_direct
    (P : Z → PMF Z) (z y : Z) (k : ℕ) (x : ℕ → Z) :
    conditionalTrajectoryRisk (prefixKernel P)
        (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) k x =
      if x k = z then (P z y).toReal else 0 := by
  unfold transitionCoordinateTrajectoryScore
  rw [conditionalTrajectoryRisk_markovTransitionTrajectoryScore]
  simpa [transitionCoordinateMarkovScore] using
    markovRowRisk_transitionIndicatorScore P z y (x k)

omit [Nonempty Z] in
/-- Complement conditional-mean identity at time `k`. -/
lemma conditionalTrajectoryRisk_transitionCoordinate_complement
    (P : Z → PMF Z) (z y : Z) (k : ℕ) (x : ℕ → Z) :
    conditionalTrajectoryRisk (prefixKernel P)
        (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) k x =
      1 - (if x k = z then (P z y).toReal else 0) := by
  unfold transitionCoordinateTrajectoryScore
  rw [conditionalTrajectoryRisk_markovTransitionTrajectoryScore]
  exact markovRowRisk_transitionCoordinate_complement P z y (x k)

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Direct empirical prefix mean is transition count divided by time. -/
lemma trajectoryEmpiricalPrequentialRisk_transitionCoordinate_direct
    (z y : Z) (n : ℕ) (x : ℕ → Z) :
    trajectoryEmpiricalPrequentialRisk
        (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x =
      transitionEdgeMass z y n x / (n : ℝ) := by
  rfl

omit [Nonempty Z] in
/-- Direct predictable prefix mean is the true coordinate probability times
the source visit count, divided by time. -/
lemma trajectoryAverageConditionalRisk_transitionCoordinate_direct
    (P : Z → PMF Z) (z y : Z) (n : ℕ) (x : ℕ → Z) :
    trajectoryAverageConditionalRisk (prefixKernel P)
        (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x =
      (P z y).toReal * transitionVisitMass z n x / (n : ℝ) := by
  unfold trajectoryAverageConditionalRisk runningMean runningSum transitionVisitMass
  simp_rw [conditionalTrajectoryRisk_transitionCoordinate_direct]
  rw [Finset.mul_sum]
  apply congrArg (fun a : ℝ ↦ a / (n : ℝ))
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hkz : x k = z
  · simp [hkz]
  · simp [hkz]

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
/-- Complement empirical prefix mean is one minus the direct empirical mean. -/
lemma trajectoryEmpiricalPrequentialRisk_transitionCoordinate_complement
    (z y : Z) {n : ℕ} (hn : 0 < n) (x : ℕ → Z) :
    trajectoryEmpiricalPrequentialRisk
        (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x =
      1 - transitionEdgeMass z y n x / (n : ℝ) := by
  change forwardPrefixMean
      (fun k ↦ 1 - transitionIndicatorScore z y (x k) (x (k + 1))) n = _
  rw [forwardPrefixMean_one_sub _ hn]
  rfl

omit [Nonempty Z] in
/-- Complement predictable prefix mean is one minus the direct predictable
prefix mean. -/
lemma trajectoryAverageConditionalRisk_transitionCoordinate_complement
    (P : Z → PMF Z) (z y : Z) {n : ℕ} (hn : 0 < n) (x : ℕ → Z) :
    trajectoryAverageConditionalRisk (prefixKernel P)
        (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x =
      1 - (P z y).toReal * transitionVisitMass z n x / (n : ℝ) := by
  change forwardPrefixMean
      (fun k ↦ conditionalTrajectoryRisk (prefixKernel P)
        (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) k x) n = _
  simp_rw [conditionalTrajectoryRisk_transitionCoordinate_complement]
  rw [forwardPrefixMean_one_sub _ hn]
  have hdirect :=
    trajectoryAverageConditionalRisk_transitionCoordinate_direct P z y n x
  unfold trajectoryAverageConditionalRisk runningMean runningSum at hdirect
  simp_rw [conditionalTrajectoryRisk_transitionCoordinate_direct] at hdirect
  change forwardPrefixMean
    (fun k ↦ if x k = z then (P z y).toReal else 0) n = _ at hdirect
  rw [hdirect]

/-- Dirac posterior averages reduce to point evaluation for FormalSLT's finite
KL posterior-average definition. -/
lemma pacBayesPosteriorAverage_dirac
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (g : ι → ℝ) :
    posteriorAverage (diracPosterior i) g = g i := by
  classical
  unfold posteriorAverage diracPosterior
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Uniform real-valued mass on a finite type. -/
def finiteUniformRealPMF
    (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ ↦ 1 / (Fintype.card ι : ℝ)

/-- The uniform real-valued mass has full support on a finite nonempty type. -/
theorem finiteUniformRealPMF_isFullSupport
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsFullSupportPMF (finiteUniformRealPMF ι) := by
  have hcardNat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  constructor
  · constructor
    · intro i
      exact (one_div_pos.mpr hcard).le
    · simp [finiteUniformRealPMF, hcard.ne']
  · intro i
    exact one_div_pos.mpr hcard

/-- A Dirac posterior against the finite uniform prior pays exactly the log
cardinality of the coordinate catalog. -/
theorem klDiv_dirac_finiteUniformRealPMF
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i : ι) :
    klDiv (diracPosterior i) (finiteUniformRealPMF ι) =
      Real.log (Fintype.card ι : ℝ) := by
  have hprior := finiteUniformRealPMF_isFullSupport ι
  rw [diracPosterior_klDiv_eq_neg_log_prior
    (finiteUniformRealPMF ι) i (hprior.pos i)]
  simp [finiteUniformRealPMF, one_div]

/-- Direct or complement Dirac boundary for one transition coordinate. -/
def transitionCoordinateBoundary
    {τ : Type*} [Fintype τ]
    (prior : TransitionCoordinate Z → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (z y : Z) (complement : Bool)
    (delta : ℝ) (j : τ) (n : ℕ) (x : ℕ → Z) : ℝ :=
  trajectoryEmpiricalBernsteinPACBayesBoundary
    prior weight lam transitionCoordinateTrajectoryScore
    (diracPosterior (⟨z, y, complement⟩ : TransitionCoordinate Z))
    delta j n x

/-- Two-sided normalized radius for transition coordinate `(z,y)`.  It is
meaningful only when `transitionVisitMass z n x > 0`. -/
def transitionCoordinateRadius
    {τ : Type*} [Fintype τ]
    (prior : TransitionCoordinate Z → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (z y : Z) (delta : ℝ) (j : τ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  (n : ℝ) / transitionVisitMass z n x *
    max
      (transitionCoordinateBoundary prior weight lam z y false delta j n x)
      (transitionCoordinateBoundary prior weight lam z y true delta j n x)

/-- Empirical row discrepancy between candidate `Q` and the observed
transition frequencies from source `z`. -/
def empiricalCandidateRowTotalVariation
    (Q : Z → PMF Z) (z : Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Z,
    |(Q z y).toReal - empiricalTransitionFrequency z y n x|

/-- Sum of the simultaneous coordinate radii in the total-variation scale. -/
def empiricalTransitionRowRadius
    {τ : Type*} [Fintype τ]
    (prior : TransitionCoordinate Z → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (z : Z) (delta : ℝ) (j : τ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Z,
    transitionCoordinateRadius prior weight lam z y delta j n x

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- One outer-probability event gives a two-sided time-uniform confidence band
for every transition coordinate.  The displayed difference is between the
average predictable visit-gated transition mass and the observed transition
mass; it remains meaningful even when a row has not yet been visited. -/
theorem exists_empiricalTransitionCoordinate_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          ∀ z y : Z,
            |(P z y).toReal * transitionVisitMass z n x / (n : ℝ) -
                transitionEdgeMass z y n x / (n : ℝ)| <
              max
                (transitionCoordinateBoundary
                  prior weight lam z y false delta j n x)
                (transitionCoordinateBoundary
                  prior weight lam z y true delta j n x) := by
  rcases exists_trajectoryEmpiricalBernsteinPACBayes_event
      (ι := TransitionCoordinate Z) (τ := τ)
      (prefixKernel P) x0
      (score := transitionCoordinateTrajectoryScore)
      transitionCoordinateTrajectoryScore_mem_Icc
      hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · simpa [trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass
  · intro x hx j n hn z y
    have hnpos : 0 < n := by omega
    have hdirect := hgood x hx j
      (diracPosterior (⟨z, y, false⟩ : TransitionCoordinate Z))
      (diracPosterior_isPMF (⟨z, y, false⟩ : TransitionCoordinate Z)) n hn
    have hcomplement := hgood x hx j
      (diracPosterior (⟨z, y, true⟩ : TransitionCoordinate Z))
      (diracPosterior_isPMF (⟨z, y, true⟩ : TransitionCoordinate Z)) n hn
    unfold trajectoryPosteriorAverageConditionalRisk
      trajectoryPosteriorEmpiricalPrequentialRisk at hdirect hcomplement
    rw [pacBayesPosteriorAverage_dirac,
      pacBayesPosteriorAverage_dirac] at hdirect hcomplement
    change
      trajectoryAverageConditionalRisk (prefixKernel P)
          (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x <
        trajectoryEmpiricalPrequentialRisk
            (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x +
          transitionCoordinateBoundary
            prior weight lam z y false delta j n x at hdirect
    change
      trajectoryAverageConditionalRisk (prefixKernel P)
          (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x <
        trajectoryEmpiricalPrequentialRisk
            (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x +
          transitionCoordinateBoundary
            prior weight lam z y true delta j n x at hcomplement
    rw [trajectoryAverageConditionalRisk_transitionCoordinate_direct,
      trajectoryEmpiricalPrequentialRisk_transitionCoordinate_direct] at hdirect
    rw [trajectoryAverageConditionalRisk_transitionCoordinate_complement
          P z y hnpos,
      trajectoryEmpiricalPrequentialRisk_transitionCoordinate_complement
          z y hnpos] at hcomplement
    rw [abs_lt]
    constructor
    · calc
        -max
            (transitionCoordinateBoundary
              prior weight lam z y false delta j n x)
            (transitionCoordinateBoundary
              prior weight lam z y true delta j n x) ≤
          -transitionCoordinateBoundary
              prior weight lam z y true delta j n x := by
            exact neg_le_neg (le_max_right _ _)
        _ < (P z y).toReal * transitionVisitMass z n x / (n : ℝ) -
              transitionEdgeMass z y n x / (n : ℝ) := by
            linarith
    · have hmax := le_max_left
        (transitionCoordinateBoundary
          prior weight lam z y false delta j n x)
        (transitionCoordinateBoundary
          prior weight lam z y true delta j n x)
      linarith

/-- On the same event, a visited transition row has an explicit normalized
coordinate radius around the empirical transition frequency. -/
theorem exists_empiricalTransitionFrequency_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          ∀ z : Z, 0 < transitionVisitMass z n x → ∀ y : Z,
            |(P z y).toReal - empiricalTransitionFrequency z y n x| <
              transitionCoordinateRadius
                prior weight lam z y delta j n x := by
  rcases exists_empiricalTransitionCoordinate_event
      P x0 hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn z hvisit y
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hband := hgood x hx j n hn z y
  let boundary : ℝ :=
    max
      (transitionCoordinateBoundary prior weight lam z y false delta j n x)
      (transitionCoordinateBoundary prior weight lam z y true delta j n x)
  have hfactor : 0 < (n : ℝ) / transitionVisitMass z n x :=
    div_pos hnpos hvisit
  have hidentity :
      (P z y).toReal - empiricalTransitionFrequency z y n x =
        ((n : ℝ) / transitionVisitMass z n x) *
          ((P z y).toReal * transitionVisitMass z n x / (n : ℝ) -
            transitionEdgeMass z y n x / (n : ℝ)) := by
    unfold empiricalTransitionFrequency
    field_simp [hnpos.ne', hvisit.ne']
  rw [hidentity, abs_mul, abs_of_pos hfactor]
  change (n : ℝ) / transitionVisitMass z n x *
      |(P z y).toReal * transitionVisitMass z n x / (n : ℝ) -
        transitionEdgeMass z y n x / (n : ℝ)| <
    (n : ℝ) / transitionVisitMass z n x * boundary
  exact mul_lt_mul_of_pos_left hband hfactor

/-- The coordinate bands certify a row-total-variation ball around any
candidate kernel `Q`.  `Q` is universally quantified after the common event,
so this theorem is valid for a candidate chosen from the observed path. -/
theorem exists_empiricalCandidateRowTotalVariation_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          ∀ z : Z, 0 < transitionVisitMass z n x →
            ∀ Q : Z → PMF Z,
              finitePMFTotalVariation (P z) (Q z) ≤
                empiricalCandidateRowTotalVariation Q z n x +
                  empiricalTransitionRowRadius
                    prior weight lam z delta j n x := by
  rcases exists_empiricalTransitionFrequency_event
      P x0 hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn z hvisit Q
  have hcoordinate : ∀ y : Z,
      |(P z y).toReal - (Q z y).toReal| ≤
        |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
          transitionCoordinateRadius
            prior weight lam z y delta j n x := by
    intro y
    calc
      |(P z y).toReal - (Q z y).toReal| ≤
          |(P z y).toReal - empiricalTransitionFrequency z y n x| +
            |empiricalTransitionFrequency z y n x - (Q z y).toReal| :=
        abs_sub_le _ _ _
      _ ≤ transitionCoordinateRadius
              prior weight lam z y delta j n x +
            |empiricalTransitionFrequency z y n x - (Q z y).toReal| :=
        add_le_add (le_of_lt (hgood x hx j n hn z hvisit y)) (le_refl _)
      _ = |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
            transitionCoordinateRadius
              prior weight lam z y delta j n x := by
        rw [abs_sub_comm]
        ring
  unfold finitePMFTotalVariation empiricalCandidateRowTotalVariation
    empiricalTransitionRowRadius
  calc
    (1 / 2 : ℝ) * ∑ y : Z, |(P z y).toReal - (Q z y).toReal| ≤
        (1 / 2 : ℝ) * ∑ y : Z,
          (|(Q z y).toReal - empiricalTransitionFrequency z y n x| +
            transitionCoordinateRadius
              prior weight lam z y delta j n x) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun y _hy ↦ hcoordinate y) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ y : Z,
          |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
        (1 / 2 : ℝ) * ∑ y : Z,
          transitionCoordinateRadius
            prior weight lam z y delta j n x := by
      rw [Finset.sum_add_distrib]
      ring

/-- Explicit substitution for a path- and time-selected candidate kernel.
There is no additional selection cost because the coordinate event is already
uniform before the candidate is introduced. -/
theorem exists_selectedEmpiricalCandidateRowTotalVariation_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1)
    (selectQ : (ℕ → Z) → ℕ → Z → PMF Z) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          ∀ z : Z, 0 < transitionVisitMass z n x →
            finitePMFTotalVariation (P z) (selectQ x n z) ≤
              empiricalCandidateRowTotalVariation (selectQ x n) z n x +
                empiricalTransitionRowRadius
                  prior weight lam z delta j n x := by
  rcases exists_empiricalCandidateRowTotalVariation_event
      P x0 hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  exact ⟨goodEvent, hmass, fun x hx j n hn z hvisit ↦
    hgood x hx j n hn z hvisit (selectQ x n)⟩

/-- Maximum, over all source rows, of empirical candidate discrepancy plus
the simultaneous statistical row radius.  This is the pathwise scalar budget
needed by the robust Dobrushin lemmas. -/
def empiricalCandidateKernelTVBudget
    (Q : Z → PMF Z)
    (prior : TransitionCoordinate Z → ℝ) (weight : τ → ℝ)
    (lam : τ → ℝ) (delta : ℝ) (j : τ)
    (n : ℕ) (x : ℕ → Z) : ℝ :=
  finiteMaximum fun z ↦
    empiricalCandidateRowTotalVariation Q z n x +
      empiricalTransitionRowRadius prior weight lam z delta j n x

/-- If every source row has been visited, the same coordinate event gives one
uniform row-TV budget for every candidate kernel.  Candidate quantification is
inside the event, so subsequent pathwise selection is valid. -/
theorem exists_empiricalCandidateKernelTV_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Z, 0 < transitionVisitMass z n x) →
            ∀ Q : Z → PMF Z, ∀ z : Z,
              finitePMFTotalVariation (P z) (Q z) ≤
                empiricalCandidateKernelTVBudget
                  Q prior weight lam delta j n x := by
  rcases exists_empiricalCandidateRowTotalVariation_event
      P x0 hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn hall Q z
  exact (hgood x hx j n hn z (hall z) Q).trans
    (le_finiteMaximum
      (fun source ↦
        empiricalCandidateRowTotalVariation Q source n x +
          empiricalTransitionRowRadius
            prior weight lam source delta j n x) z)

/-- Direct unknown-kernel plug-in capstone.  On the empirical coordinate event,
a path- and time-selected candidate supplies a certified Dobrushin upper bound.
The oscillation inequality holds at the displayed pathwise factor; if that
factor is below one, the true kernel is a strict contraction and any two
*supplied* invariant PMFs are equal.

This does not construct an invariant PMF.  It also does not make a Poisson
score, potential, or downstream risk e-process selected from the same data;
that requires a separately uniformized catalog or sample splitting. -/
theorem exists_selectedEmpiricalKernelContraction_event
    (P : Z → PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z → ℝ}
    (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1)
    (selectQ : (ℕ → Z) → ℕ → Z → PMF Z) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Z, 0 < transitionVisitMass z n x) →
            let Q := selectQ x n
            let eta := empiricalCandidateKernelTVBudget
              Q prior weight lam delta j n x
            let alpha := finiteDobrushinCoefficient Q + 2 * eta
            finiteDobrushinCoefficient P ≤ alpha ∧
              IsOscillationContraction P alpha ∧
                (alpha < 1 →
                  finiteDobrushinCoefficient P < 1 ∧
                    ∀ stationary₁ stationary₂ : PMF Z,
                      IsInvariantPMF P stationary₁ →
                        IsInvariantPMF P stationary₂ →
                          stationary₁ = stationary₂) := by
  rcases exists_empiricalCandidateKernelTV_event
      P x0 hprior hweight hdelta hlam hlam_one with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn hall
  dsimp only
  let Q := selectQ x n
  let eta := empiricalCandidateKernelTVBudget
    Q prior weight lam delta j n x
  have hrow : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta :=
    hgood x hx j n hn hall Q
  have hcoefficient :=
    finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV P Q hrow
  have hcontraction :=
    candidateDobrushin_add_two_mul_rowTV_isOscillationContraction P Q hrow
  refine ⟨hcoefficient, hcontraction, ?_⟩
  intro hstrict
  refine ⟨finiteDobrushinCoefficient_lt_one_of_candidate_rowTV
      P Q hrow hstrict, ?_⟩
  intro stationary₁ stationary₂ hstationary₁ hstationary₂
  exact invariantPMF_unique_of_candidate_rowTV P Q hrow hstrict
    stationary₁ stationary₂ hstationary₁ hstationary₂

end

end FormalSLT.StochasticDynamics
