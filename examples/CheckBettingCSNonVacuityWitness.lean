/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.BettingCS

/-!
# Non-vacuity witness for the betting confidence sequence

This file instantiates `betting_confidence_sequence_of_condMean` on explicit data,
proving the headline betting/e-process confidence-sequence bound is not vacuous.

The witness is a Rademacher (sign) increment on `Ω = Bool` under the uniform
probability measure: `X 0 ω = if ω then 1 else -1` (so `X 0` takes the values
`±1`, never zero), with `X k = 0` for `k ≥ 1`. The filtration reveals the first
increment one step late: `ℱ 0 = ⊥`, `ℱ k = ⊤` for `k ≥ 1` (the predictable
`IncrementAdapted` model), and the conditional-mean null `μ[X k | ℱ k] ≤ 0`
holds with the candidate mean `m = 0`.

The betting fraction is the constant predictable bet `lambda ≡ 1/4`
(`StronglyAdapted`, bounded, nonnegative). On the positive Rademacher outcome the
wealth genuinely grows past `1` (`bettingWitness_positive_gain`), so the rejection
event has positive mass and the bound is not vacuous. At `delta = 4/5` the
threshold is `5/4` and the time-uniform rejection event has mass at most `4/5`.

The printed axiom set is exactly `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.AnytimeValid.BettingNonVacuityWitness

noncomputable section

namespace FormalSLT.AnytimeValid.CheckBettingCSNonVacuityWitness

/-- The explicit betting confidence-sequence bound, instantiated on the concrete
Rademacher increment `XBool`, constant bet `lambdaBool ≡ 1/4`, candidate mean
`m = 0`, and level `delta = 4/5`. -/
theorem nonVacuityWitness :
    μBool.real (bettingMeanRejectionEvent XBool lambdaBool 0 (4 / 5)) ≤ (4 / 5 : ℝ) :=
  bettingNonVacuityWitness

/-- The same witness genuinely gains wealth on the positive Rademacher outcome,
so the rejection threshold is reachable and the bound above is not vacuous. -/
theorem nonVacuityWitness_positive_gain :
    (1 : ℝ) < bettingWealthProcess XBool lambdaBool 0 1 true :=
  bettingWitness_positive_gain

end FormalSLT.AnytimeValid.CheckBettingCSNonVacuityWitness

end

#print axioms FormalSLT.AnytimeValid.CheckBettingCSNonVacuityWitness.nonVacuityWitness
#print axioms FormalSLT.AnytimeValid.CheckBettingCSNonVacuityWitness.nonVacuityWitness_positive_gain
