import FormalSLT

/-!
# Basic import example

Shows how to import the main results and state a corollary.
-/

-- The main ERM excess-risk tail theorem is available:
#check FormalSLT.VC.SampleComplexity.vc_erm_excessRisk_tail

-- The Rademacher symmetrization bound:
#check FormalSLT.Rademacher.Symmetrization.expected_genGap_le_two_expected_empiricalRademacherComplexity

-- Massart's finite-class bound:
#check FormalSLT.Rademacher.Massart.massart_finite_class

-- The binary VC bridge:
#check FormalSLT.VC.BinaryVCBridge.effectiveClass_zeroOneLoss_card_eq_binaryClassTrace

-- Sauer-Shelah polynomial bound:
#check FormalSLT.VC.SauerShelah.sauerShelah_polynomial_bound
