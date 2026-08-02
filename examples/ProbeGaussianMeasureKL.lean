import FormalSLT.PACBayes.GaussianKL
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

#check gaussianReal
#check gaussianReal_of_var_ne_zero
#check instIsProbabilityMeasureGaussianReal
#check gaussianReal_absolutelyContinuous
#check gaussianReal_absolutelyContinuous'
#check rnDeriv_gaussianReal
#check integral_gaussianReal_eq_integral_smul
#check integral_id_gaussianReal
#check variance_id_gaussianReal
#check memLp_id_gaussianReal
#check Measure.rnDeriv_withDensity
#check Measure.rnDeriv_withDensity_left
#check Measure.rnDeriv_withDensity_right
#check Measure.rnDeriv_mul_rnDeriv
#check Measure.withDensity_absolutelyContinuous
#check InformationTheory.klDiv_of_ac_of_integrable
#check InformationTheory.toReal_klDiv
#check InformationTheory.toReal_klDiv_eq_integral_klFun
#check llr
#check llr_def
#check integrable_llr_iff
#check Measure.pi
#check Measure.prod
#check MeasureTheory.Measure.pi_isProbabilityMeasure
#check MeasureTheory.Measure.instIsProbabilityMeasurePi
#check MeasureTheory.Measure.absolutelyContinuous_pi
