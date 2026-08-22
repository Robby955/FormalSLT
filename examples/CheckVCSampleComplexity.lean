import FormalSLT

/-!
# VC-style sample complexity

Checks the VC-style ERM excess-risk tail and its main components.

**Theorem.** For a finite hypothesis class whose loss and negated-loss
effective classes satisfy the two supplied growth bounds at exponent `d`, with
loss bounded by `B`, sample size `n`, and tolerance `ε ≥ 0`:

    P(excess risk of ERM ≥ 4B · √(2d · log(en/d) / n) + 2ε)
      ≤ 2 · exp(-ε² n / (2B²))

A separate bridge may derive the growth premises from a VC-dimension bound;
the checked theorem below does not assume such a certificate directly.
-/

open FormalSLT.VC.SampleComplexity

-- Full VC-style ERM excess-risk tail
#check vc_erm_excessRisk_tail

-- VC pointwise Rademacher bound: Rad ≤ B · √(2d · log(en/d) / n)
#check vcRademacher_pointwise

-- VC uniform deviation (two-sided)
#check uniformDeviation_highProb_vcClass

-- VC one-sided genGap tail
#check genGap_highProb_vcClass

open FormalSLT.VC.SauerShelah

-- Sauer-Shelah polynomial bound: Σ_{k≤d} C(n,k) ≤ (en/d)^d
#check sauerShelah_polynomial_bound

open FormalSLT.VC.BinaryVCBridge

-- Binary VC bridge: effectiveClass card = binaryClassTrace card
#check effectiveClass_zeroOneLoss_card_eq_binaryClassTrace

-- Sauer-Shelah corollary for binary classification
#check effectiveClass_zeroOneLoss_card_le_sauerShelah
