/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.DyadicEpochCS

/-!
# Dyadic-epoch CS obstruction checker

This checker confirms the named obstruction theorem for the literal
`subGammaLogLogWidth` all-`n` dyadic-epoch route.
-/

open FormalSLT.AnytimeValid

#check literalDyadicEpochWeight
#check literalDyadicEpochWeight_not_summable
#print axioms literalDyadicEpochWeight_not_summable

example : ¬ Summable literalDyadicEpochWeight :=
  literalDyadicEpochWeight_not_summable
