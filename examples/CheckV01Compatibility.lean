/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Stability.BousquetElisseeff

/-!
# FormalSLT v0.1 compatibility signatures

These are the two historical declaration types still used by the exact
v0.1.0 showcase example. Their output is compared with a committed signature
snapshot by `scripts/check_public_api_snapshot.sh`.
-/

#check FormalSLT.AlgorithmicStability.bousquet_elisseeff_azuma_expectedGap_variant
#print axioms FormalSLT.AlgorithmicStability.bousquet_elisseeff_azuma_expectedGap_variant

#check FormalSLT.AlgorithmicStability.bousquet_elisseeff_azuma_expectedGap_variant_of_boundedLoss
#print axioms FormalSLT.AlgorithmicStability.bousquet_elisseeff_azuma_expectedGap_variant_of_boundedLoss
