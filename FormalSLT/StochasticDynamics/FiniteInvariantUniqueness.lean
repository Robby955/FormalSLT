/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.FiniteInvariantExistence
import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant

/-!
# Unique invariant laws from finite contraction certificates

Finite-state existence plus the existing Dobrushin uniqueness theorem gives a
unique invariant PMF whenever the computed coefficient is below one.  The same
conclusion follows from a candidate-kernel row-TV certificate.

The public statements are measure-free.  The existing uniqueness proof is
phrased using finite integrals, so its call is discharged internally using the
discrete measurable structure; invariance itself is the algebraic PMF identity
`stationary.bind P = stationary`.
-/

open MeasureTheory ProbabilityTheory

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- Dobrushin contraction below one supplies a unique invariant PMF, not only
uniqueness conditional on a supplied invariant witness. -/
theorem existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one
    (P : Z → PMF Z)
    (hcoefficient : finiteDobrushinCoefficient P < 1) :
    ∃! stationary : PMF Z, IsInvariantPMF P stationary := by
  letI : MeasurableSpace Z := ⊤
  letI : MeasurableSingletonClass Z := ⟨fun _ ↦ trivial⟩
  refine ⟨finiteInvariantPMF P, finiteInvariantPMF_isInvariant P, ?_⟩
  intro stationary hstationary
  exact invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one P
    hcoefficient stationary (finiteInvariantPMF P) hstationary
      (finiteInvariantPMF_isInvariant P)

/-- A candidate-kernel row-TV certificate supplies a unique invariant PMF for
the true finite kernel. -/
theorem existsUnique_invariantPMF_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1) :
    ∃! stationary : PMF Z, IsInvariantPMF P stationary := by
  letI : MeasurableSpace Z := ⊤
  letI : MeasurableSingletonClass Z := ⟨fun _ ↦ trivial⟩
  refine ⟨finiteInvariantPMF P, finiteInvariantPMF_isInvariant P, ?_⟩
  intro stationary hstationary
  exact invariantPMF_unique_of_candidate_rowTV P Q hrowTV hcertificate
    stationary (finiteInvariantPMF P) hstationary
      (finiteInvariantPMF_isInvariant P)

end

end FormalSLT.StochasticDynamics
