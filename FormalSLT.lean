-- Formal Statistical Learning Theory in Lean 4
-- All results verified. No stub tactics. No custom axioms.
-- Axioms: [propext, Classical.choice, Quot.sound] only.

import FormalSLT.Risk
import FormalSLT.ERM
import FormalSLT.UniformConvergence
import FormalSLT.GhostSample

import FormalSLT.Probability.Concentration
import FormalSLT.Probability.FiniteUnionBound
import FormalSLT.Probability.FiniteExpectation
import FormalSLT.Probability.BernsteinMGF
import FormalSLT.Probability.IIDConcentration

import FormalSLT.Concentration.SubGamma.BennettBound
import FormalSLT.Concentration.SubGamma.BoundedExpIntegrable
import FormalSLT.Concentration.SubGamma.CondExpProduct
import FormalSLT.Concentration.SubGamma.CondJensen
import FormalSLT.Concentration.SubGamma.CondMarkov
import FormalSLT.Concentration.SubGamma.CondVarianceFromSquare
import FormalSLT.Concentration.SubGamma.Extractor
import FormalSLT.Concentration.SharpMcDiarmid
import FormalSLT.AnytimeValid.SubGaussianCS

import FormalSLT.Rademacher.FiniteSample
import FormalSLT.Rademacher.FiniteSampleSymmetrization
import FormalSLT.Rademacher.ProbabilityBridge
import FormalSLT.Rademacher.Decoupling
import FormalSLT.Rademacher.Symmetrization
import FormalSLT.Rademacher.Massart
import FormalSLT.Rademacher.HighProbability
import FormalSLT.Rademacher.FiniteClassHighProb
import FormalSLT.Rademacher.UniformDeviation
import FormalSLT.Rademacher.ERMGeneralization
import FormalSLT.Rademacher.Contraction
import FormalSLT.Rademacher.LinearPredictor
import FormalSLT.Rademacher.Localized

import FormalSLT.Azuma.ExposureMartingale
import FormalSLT.Azuma.BoundedDifferences
import FormalSLT.Azuma.BoundedDiffMartingale
import FormalSLT.Azuma.BoundedDiffsAzumaInput
import FormalSLT.Azuma.BoundedIncrementBound
import FormalSLT.Azuma.HasBoundedDifferences
import FormalSLT.Azuma.ExposureIncrementHoeffding
import FormalSLT.Azuma.ExposureIncrementCondMGF
import FormalSLT.Azuma.GenGapTail

import FormalSLT.VC.Dimension
import FormalSLT.VC.PACBridge
import FormalSLT.VC.SauerShelah
import FormalSLT.VC.Rademacher
import FormalSLT.VC.SampleComplexity
import FormalSLT.VC.BinaryVCBridge

import FormalSLT.Covering.Rademacher
import FormalSLT.Covering.DudleyChaining
import FormalSLT.Covering.FiniteSubGaussianChaining
import FormalSLT.Covering.TotalBoundedDudley
import FormalSLT.Covering.UnitIntervalDudley
import FormalSLT.Covering.TwoPointDudley
import FormalSLT.Covering.FiniteDiscreteDudley

import FormalSLT.AlgorithmicStability
import FormalSLT.Stability.BousquetElisseeff
import FormalSLT.Stability.RKHSRegularisedERM
import FormalSLT.PACBayesKL
import FormalSLT.PACBayesFiniteProductMGF
import FormalSLT.PACBayesBoundedLoss
import FormalSLT.PACBayesMcAllester
import FormalSLT.PACBayesSeeger
import FormalSLT.PACBayesBernstein
import FormalSLT.PACBayes.McAllesterBound
import FormalSLT.PACBayes.McAllesterBoundGeneral
import FormalSLT.PACBayes.Compiler
import FormalSLT.PACBayes.Generated.Cert_A
import FormalSLT.PACBayes.Generated.Cert_B
import FormalSLT.PACBayes.Generated.Cert_C
import FormalSLT.PACBayes.Generated.Cert_D
import FormalSLT.PACBayes.Generated.Cert_E

import FormalSLT.OnlineToPAC.RegretConversion
import FormalSLT.OnlineToPAC.CesaBianchi
import FormalSLT.OnlineToPAC.IIDConcentration

import FormalSLT.PACBayes.VitaleLemma
import FormalSLT.PACBayes.GaussianKL
import FormalSLT.PACBayes.StabilityBridge
import FormalSLT.PACBayes.VitaleAnalytic
import FormalSLT.PACBayes.BernsteinAnalytic
import FormalSLT.PACBayes.ContinuousPriorPosterior
import FormalSLT.PACBayes.BernsteinBound

import FormalSLT.TestTimeMeta.Assumptions
import FormalSLT.TestTimeMeta.CompositionLemmas
import FormalSLT.TestTimeMeta.MainTheorem
import FormalSLT.TestTimeMeta.Flagship
import FormalSLT.TestTimeMeta.FlagshipComposition
