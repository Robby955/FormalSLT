import FormalSLT

/-!
# Binary classification with 0-1 loss

Shows how the binary VC bridge connects binary classifier traces
to the effective loss-pattern class, removing the user-supplied
growth assumption for 0-1 loss.
-/

open FormalSLT.VC.BinaryVCBridge

-- The bridge equality: for binary classifiers with 0-1 loss,
-- the number of distinct loss patterns equals the number of
-- distinct labeling patterns.
#check effectiveClass_zeroOneLoss_card_eq_binaryClassTrace

-- The Sauer-Shelah corollary: the effective class satisfies
-- the growth-function bound directly from the trace's VC dimension.
#check effectiveClass_zeroOneLoss_card_le_sauerShelah

-- This means for binary classification with 0-1 loss, the
-- VC-style Rademacher bounds do not need a user-supplied
-- growth assumption — the Sauer-Shelah bound on the binary
-- trace provides it automatically.
