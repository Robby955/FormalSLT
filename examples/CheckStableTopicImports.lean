import FormalSLT.PACBayes
import FormalSLT.VC
import FormalSLT.Sequential

/-!
# Stable topic-import smoke test

The three supported topic umbrellas expose representative finite, continuous,
Gaussian, VC, and sequential endpoints. Compatibility aliases remain usable
without carrying duplicate proof bodies.
-/

#check FormalSLT.PACBayes.TimeUniformGaussian.timeUniformSphericalGaussianPACBayes_bound
#check FormalSLT.PACBayes.TimeUniformIID.timeUniformIIDPACBayes_allPosteriors_bound
#check FormalSLT.VC.SampleComplexity.vc_erm_sample_complexity
#check FormalSLT.AnytimeValid.eProcess_typeI_control

#check FormalSLT.VC.VCSampleComplexity.vc_erm_excessRisk_tail

#print axioms FormalSLT.PACBayes.TimeUniformGaussian.timeUniformSphericalGaussianPACBayes_bound
#print axioms FormalSLT.VC.SampleComplexity.vc_erm_sample_complexity
#print axioms FormalSLT.AnytimeValid.eProcess_typeI_control
