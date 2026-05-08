import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import FormalSLT.Risk
import FormalSLT.UniformConvergence

/-!
# Empirical risk minimization on a finite hypothesis class

This module bridges the deterministic uniform-deviation bookkeeping in
`Risk.lean` with the abstract ERM triangle lemma already proved in
`UniformConvergence.lean` (`epsilonRepresentativeERMWorks`). It provides:

- `IsERM` — exact empirical-risk minimization predicate.
- `erm_excessRisk_le_two_uniformDeviation` — the deterministic excess-risk
  bound `R(î) ≤ R(i*) + 2 · uniformDeviation(μ, ℓ, z)` for any exact ERM `î`
  and any comparator `i*` over a finite, nonempty hypothesis class `ι`.
- `IsApproxERM` — approximate empirical-risk minimization predicate, with an
  additive optimization-error slack `optError`.
- `approxERM_excessRisk_le_twoUniformDeviation_plusOptimizationError` — the
  approximate-ERM analogue, adding `optError` to the right-hand side.
- `finiteClass_erm_exists` — existence of an exact ERM on any finite, nonempty
  class for any real-valued empirical-risk function.

All declarations are deterministic; no probability content beyond the inputs.

What this module does NOT provide:

- No PAC abstraction. There is no failure probability `δ` and no rearrangement
  of the deviation into `sqrt(log |ι| / n)`. The uniform deviation is consumed
  as whatever real number the inputs supply.
- No Hoeffding step. Bounded losses, sub-Gaussian inputs, and iid sampling are
  not assumed; this is purely the deterministic triangle inequality.
- No uncountable hypothesis classes. `ι` must be `Fintype` and `Nonempty`.
- No Rademacher / VC / covering-number content.
- No public-facing manifest claim. The exact-ERM excess-risk theorem refines
  the already-governed `claim:uniform-convergence::epsilon-representative-sample`
  and is not separately registered. The approximate-ERM and existence results
  are infrastructure additions and are not yet attached to any
  `claim:learning-theory::*` entry.
-/

namespace FormalSLT.ERM

open FormalSLT.Risk
open FormalSLT.UniformConvergence

variable {ι Z : Type*}

/-- `IsERM Rhat î` says that `î` minimizes the empirical risk `Rhat` over the
finite class `ι`. Stated as a pure first-order predicate; no probabilistic
content. -/
def IsERM [Fintype ι] (Rhat : ι → ℝ) (î : ι) : Prop :=
  ∀ j : ι, Rhat î ≤ Rhat j

/-- Deterministic excess-risk bound for empirical-risk minimization on a
finite, nonempty hypothesis class.

For any empirical-risk minimizer `î` and any comparator `i_star`, the
population risk of `î` exceeds that of `i_star` by at most twice the uniform
deviation. The proof reduces to the abstract triangle lemma
`epsilonRepresentativeERMWorks`, with `ε := uniformDeviation μ ℓ z` supplied
pointwise by `abs_risk_sub_empiricalRisk_le_uniformDeviation`. -/
theorem erm_excessRisk_le_two_uniformDeviation
    [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    {μ : MeasureTheory.Measure Z} {ℓ : ι → Z → ℝ} {n : ℕ} {z : Fin n → Z}
    {î i_star : ι}
    (hERM : IsERM (empiricalRisk z ℓ) î) :
    risk μ ℓ î ≤ risk μ ℓ i_star + 2 * uniformDeviation μ ℓ z := by
  refine epsilonRepresentativeERMWorks
    (risk := fun i => risk μ ℓ i)
    (empiricalRisk := fun i => empiricalRisk z ℓ i)
    (ε := uniformDeviation μ ℓ z)
    (hERM := î) (hComparator := i_star)
    ?hRepresentative ?hERMmin
  · intro i
    exact abs_risk_sub_empiricalRisk_le_uniformDeviation μ ℓ z i
  · intro i
    exact hERM i

/-- `IsApproxERM Rhat optError î` says that `î` minimizes the empirical risk
`Rhat` up to an additive optimization-error slack of `optError`. With
`optError = 0` this collapses to `IsERM`. With `optError < 0` the predicate is
strictly stronger than `IsERM` (and typically vacuous on a finite class), so
callers who want the exact-ERM corollary should pass `optError = 0`.

Stated as a pure first-order predicate; no probabilistic content. -/
def IsApproxERM [Fintype ι] (Rhat : ι → ℝ) (optError : ℝ) (î : ι) : Prop :=
  ∀ j : ι, Rhat î ≤ Rhat j + optError

/-- Approximate-ERM excess-risk bound on a finite, nonempty hypothesis class.

For any `optError`-approximate empirical-risk minimizer `î` and any comparator
`i_star`, the population risk of `î` exceeds that of `i_star` by at most twice
the uniform deviation plus the optimization-error slack:

  `R(î) ≤ R(i*) + 2 · uniformDeviation(μ, ℓ, z) + optError`.

With `optError = 0` this recovers `erm_excessRisk_le_two_uniformDeviation`.
The proof is the same three-step triangle as the exact-ERM case, with the
approximate-minimization step replacing exact minimization.

Scope: deterministic only; no iid hypothesis on `z`; no concentration; no PAC
abstraction; no Rademacher/VC content. -/
theorem approxERM_excessRisk_le_twoUniformDeviation_plusOptimizationError
    [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    {μ : MeasureTheory.Measure Z} {ℓ : ι → Z → ℝ} {n : ℕ} {z : Fin n → Z}
    {î i_star : ι} {optError : ℝ}
    (hApproxERM : IsApproxERM (empiricalRisk z ℓ) optError î) :
    risk μ ℓ î ≤
      risk μ ℓ i_star + 2 * uniformDeviation μ ℓ z + optError := by
  have hRiskUpper :
      risk μ ℓ î ≤ empiricalRisk z ℓ î + uniformDeviation μ ℓ z := by
    have h :=
      (abs_le.mp (abs_risk_sub_empiricalRisk_le_uniformDeviation μ ℓ z î)).2
    linarith
  have hApprox :
      empiricalRisk z ℓ î ≤ empiricalRisk z ℓ i_star + optError :=
    hApproxERM i_star
  have hCompUpper :
      empiricalRisk z ℓ i_star ≤ risk μ ℓ i_star + uniformDeviation μ ℓ z := by
    have h :=
      (abs_le.mp
        (abs_empiricalRisk_sub_risk_le_uniformDeviation μ ℓ z i_star)).2
    linarith
  linarith

/-- Existence of an exact empirical-risk minimizer on a finite, nonempty
hypothesis class. Pure existence statement on a real-valued function over a
finite linearly ordered codomain; no probabilistic content. -/
theorem finiteClass_erm_exists [Fintype ι] [Nonempty ι] (Rhat : ι → ℝ) :
    ∃ î : ι, IsERM Rhat î := by
  obtain ⟨î, _, hMin⟩ :=
    (Finset.univ : Finset ι).exists_min_image Rhat Finset.univ_nonempty
  refine ⟨î, ?_⟩
  intro j
  exact hMin j (Finset.mem_univ j)

end FormalSLT.ERM
