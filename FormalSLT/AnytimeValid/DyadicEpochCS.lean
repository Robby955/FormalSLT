/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Analysis.PSeries
import FormalSLT.AnytimeValid.OptimizedLambdaCS

/-!
# Dyadic-epoch obstruction for the literal optimized-lambda CS

This module records why the all-`n` literal `subGammaLogLogWidth` theorem is not
discharged by a countable dyadic mixture.

The finite-grid theorem in `OptimizedLambdaCS` pays a budget
`Real.log ((Lam.card : Real) / delta)`. A countable mixture with epoch weights
`w_j` would pay the corresponding term `Real.log (1 / (delta * w_j))`
(up to the existing two-sided factor). On the dyadic epoch where
`Real.log (Real.log n)` is comparable to `Real.log j`, matching the current
literal budget `logLogBudget n delta` with no extra stitching charge forces
`w_j` to be comparable to `1 / j`.

The checked theorem below records the obstruction: shifted harmonic weights are
not summable, so they cannot be the weights of a probability mixture. A dyadic
stitch with summable weights, for example p-series weights, pays an extra epoch
term in the boundary. That proves a different theorem from the literal
`subGammaLogLogWidth` statement requested here.

A second Lean gap remains if the boundary is weakened: mathlib has finite
supermartingale sums and Bochner `integral_tsum`, but no ready theorem saying
that a countable weighted series of nonnegative supermartingales is again a
supermartingale under the needed measurability and integrability hypotheses.
-/

open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/--
The epoch weights forced by matching the current literal `logLogBudget` with no
extra countable-stitching charge. The shift avoids the zero denominator.
-/
def literalDyadicEpochWeight (j : ℕ) : ℝ :=
  1 / ((j + 1 : ℕ) : ℝ)

/--
Shifted harmonic epoch weights are not summable. Hence they cannot normalize a
countable probability mixture, which is the obstruction to proving the existing
literal `subGammaLogLogWidth` as an unconditional all-`n` stitched CS by the
dyadic-epoch route.
-/
theorem literalDyadicEpochWeight_not_summable :
    ¬ Summable literalDyadicEpochWeight := by
  unfold literalDyadicEpochWeight
  simpa [Nat.cast_add, Nat.cast_one] using
    (mt (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast)

end

end FormalSLT.AnytimeValid
