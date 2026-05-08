import FormalSLT

/-!
# Massart's finite-class Rademacher bound

Checks that the main Massart theorem and its dependencies are importable
and have the expected types.

**Theorem.** For a finite hypothesis class of size |H| with loss bounded by B:

    Rad_S(H) ≤ B · √(2 · log |H| / n)
-/

open FormalSLT.Rademacher.Massart

-- Massart's finite-class Rademacher bound:
--   empiricalRademacherComplexity ℓ z ≤ B * √(2 * log |H| / n)
#check massart_finite_class

-- Core helper: the log-sum-exp bound on Rademacher MGF
#check rademacher_le_log_sum_mgf

-- The sign-average exponential moment bound
#check sign_avg_exp_le

-- Cosh inequality used in the MGF argument
#check cosh_le_exp_sq_half
