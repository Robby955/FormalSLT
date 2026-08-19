#!/usr/bin/env bash
# Witness-quality gate: bans fake (check-only) non-vacuity witnesses.
#
# Why this exists: a `#check`/`#print axioms` file certifies well-typedness and
# axiom-cleanliness, but a `#check` CANNOT fail on a vacuous theorem, so it does
# not certify satisfiability (non-vacuity). For every headline theorem the paper
# cites as "witnessed", the example file must contain a CONCRETE instantiation
# (a `def`/`example`/`theorem`/`lemma`/`instance`/`abbrev`/`structure` that
# discharges the hypotheses on explicit data), not just `#check` lines.
#
# This gate scans the curated list of headline witness files (the concrete
# non-vacuity witnesses built for the 2026-06-23 soundness audit) and FAILS if
# any of them degenerates into a check-only file. It then runs a fixture pair:
# a synthetic check-only file MUST be detected as fake (gate would fail), and a
# synthetic concrete-witness file MUST pass. This proves the detector itself
# works, so a future regression that turns a witness into `#check`-only is caught.
#
# Run from CI alongside the example loop and the axiom gate.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

# A file is a CONCRETE witness if it has at least one top-level declaration that
# instantiates the theorem on explicit data. A FAKE witness has `#check`/`#print`
# lines but ZERO such declarations.
DECL_PATTERN='^[[:space:]]*(noncomputable[[:space:]]+)?(def|example|theorem|lemma|instance|abbrev|structure)[[:space:]]'
CHECK_PATTERN='#check|#print'

# Returns 0 (concrete) / 1 (fake) / 2 (not-a-witness: no checks at all).
classify_witness() {
  local f="$1"
  if [ ! -f "$f" ]; then
    echo "MISSING"
    return 0
  fi
  local decls checks
  decls="$(grep -cE "$DECL_PATTERN" -- "$f" || true)"
  checks="$(grep -cE "$CHECK_PATTERN" -- "$f" || true)"
  if [ "$decls" -ge 1 ]; then
    echo "CONCRETE"
  elif [ "$checks" -ge 1 ]; then
    echo "FAKE"
  else
    echo "NONE"
  fi
}

# Curated headline witnesses: every theorem the paper cites as witnessed must
# point at a file here, and each file MUST be a concrete instantiation. Adding a
# new headline => add its witness file here.
# Each entry: theorem the file witnesses (see comment) -> the witness file.
#   atTop_time_uniform_confidence_sequence_subGamma
#   mixture_confidence_sequence_uniformPrior
#   flagshipFourComponent_conclusion_from_incrementModel
#   flagshipFiveComponent_conclusion_from_incrementModel
#   flagshipAnytimeValid_conclusion_from_incrementModel
#   pacbayes_mcallester_sqrt
#   finiteMcAllesterBoundedComplexity_badEventMass_le_delta
#   finitePACBayesBernsteinMargin_badEventMass_le_delta
#   indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta
#   indicator_posteriorRisk_le_twoThirds_of_not_mem
#   indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta /
#     indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem
#   finiteEmpiricalVariance_eq_pairwise /
#     finiteEmpiricalVariance_unbiased_finiteProduct (nonbinary Fin 3 loss at
#     levels 0, 1/2, 1; exact product-law expectation over all 27 samples)
#   bennett_mgf_le_one_add
#     (fair two-point law, nonconstant centered observable, positive retained
#     correction, and strict improvement over the exponential relaxation)
#   finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin
#     (fair two-point law, nonconstant indicator loss, n = 2, eta = 1)
#   finiteEmpiricalVariancePACBayes_badEventMass_le_delta /
#     posteriorPopulationVariance_le_empiricalVariance_of_not_mem (unequal
#     Bool law, two distinct loss variances, genuinely sample-selected
#     posterior, two positive-mass good samples, certificate below 1/4)
#   finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta /
#     posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
#     (unequal positive weights and distinct tilts, two posterior-dependent
#     selector branches, explicit positive-mass samples, and checked bounds
#     below 1/4)
#   posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem (fair Bool
#     law, nonconstant loss, separate variance/risk budgets, combined bad mass
#     below one, and an existential good-sample final-risk witness)
#   finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le /
#     posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem
#     (two eta entries, two lambda entries, positive half-weights, separate
#     budgets, and genuinely sample-dependent variance/risk selectors)
#   finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem
#     (95% confidence, point-posterior KL = log 2, Bessel variance 16/63,
#     explicit good sample, and final theorem-produced ceiling below one)
#   exists_infiniteEmpiricalBernstein_event
#     (fair-Boolean infinite IID law, one event for every n >= 2, and a point
#     posterior selected from the first path coordinate; this is the structural
#     all-sample-size receipt, while numerical nonvacuity is supplied by the
#     separate balanced-64 fixed-sample witness)
#   exists_continuousInfiniteEmpiricalBernstein_event /
#     gaussianPosterior_nonVacuous_receipt
#     (Theta = (Fin 1 -> Real) x Bool, N(0,1) product fair-Boolean prior,
#      fixed N(1/4,1) product fair-Boolean posterior, posterior finite-set mass
#      zero, KL = 1/32, genuine unscaled zero-one sign-flip mismatch loss,
#      every nonempty-sample posterior empirical risk = 1/2, n = 2^20,
#      delta = 1/2, correction below 1/2, and theorem-produced RHS below 1;
#      gaussianPosterior_goodPath_exists gives a path outside the event;
#      no data-dependent continuous-posterior selection claim)
#   vcPacBayesBernsteinPosteriorRisk_bound
#   empiricalBernstein_confidence_sequence_uniformPrior
#   FormalSLT.Concentration.NamedTails.bernstein_tail (two-sided, Rademacher witness)
#   maurer_pacbayes_kl_bound
#   eProcess_typeI_control / eProcess_product_of_supermartingale / eProcess_optionalContinuation
#   diagonalSpike_scalarCorrection_safe_iff_card_le /
#     diagonalSpike_logCorrection_ge_logCard
#     (fair-Boolean full-support law, exact coordinate expectation one,
#      uncorrected selected expectation two, weighted selected expectation one,
#      and exact raw/log correction necessity on the diagonal witness)
#   optimized_lambda_confidence_sequence_subGamma / subGammaLogLogWidth_loglog_rate
#   betting_confidence_sequence_of_condMean (concrete Rademacher witness, bet 1/4)
#   timeUniformPACBayes_bound (process-level Ville crossing, concrete Rademacher witness)
#   timeUniformPACBayes_tiltMixture_allPosteriors_bound
#     (one finite weighted hypothesis--tilt e-process, two distinct tilts,
#      a nonconstant Rademacher path, and one all-posterior Ville event)
#   timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec /
#     selected_of_not_mem_measurableExceptionalEvent
#     (finite IID/full-support two-tilt catalog, path-selected posterior and
#     atom, evaluated boundary at most 3/8, and an existential good path with
#     selected risk below 7/8; explicit selector-branch exercises are not
#     proved to lie on the good set)
#   timeUniformIIDGaussianPACBayes_bound (fair-Bernoulli product stream with
#     explicit KL, evaluated penalty, and a positive-mass failure cylinder)
#   timeUniformIIDGaussianPACBayes_grid_bound / selected_bound (two fixed
#     Gaussian posterior/tilt entries and an arbitrary sample-dependent selector)
#   cramerRao_unbiased / Bernoulli p = 1/2 Fisher-information witness
#   finiteLogPartition_hasDerivAt / finiteExponentialFamily_fisherInformation_eq_variance
#     (Bernoulli natural-parameter witness at theta = 0)
#   markovPrequentialRiskExceptionalEvent_mass_le_delta
#     (persistent two-state trajectory with an evaluated boundary radius
#      below 1/20 at n = 1024, delta = 1/20, lambda = 1/8)
#   markovPACBayes_prequentialRisk_certificate
#     (asymmetric two-state catalog with a path-selected point posterior)
#   markovPACBayes_tiltMixture_prequentialRisk_certificate
#     (asymmetric finite-state chain with fixed predictors, a full-support
#      two-tilt prior, a path-selected posterior and post-path tilt atom, both
#      selected boundaries below 1/20, and risk below 11/20; the two explicit
#      selector-branch paths are not proved good or positive-probability)
#   trajectoryPACBayes_tiltMixture_prequentialRisk_certificate
#     (prefix-dependent Bool kernel and score with full-support rows; at time
#      two, two prefixes share the fixed initial and current states but differ
#      at the interior state, producing distinct kernel rows and score values;
#      the exact length-three cylinder masses are not evaluated)
#   informative_nonvacuous_receipt /
#     informative_allTime_vanishing_capstone
#     (genuinely prefix-dependent finite dynamics, static and online rules,
#      positive-mass supported branches that each contain a theorem-produced
#      good path for the corresponding data-selected point posterior,
#      KL = log 2, delta = 1/160, Bessel variance 1/512, exact countable-atom
#      costs at n = 512 and 2048, checked boundary enclosures 0.2738--0.2744
#      and 0.1432--0.1434, and strict same-path shrinkage; the catalog is fixed
#      before data and the countable endpoint is not a master selected e-process)
#   countableJointMeanVariance_catalogBadSamples_mass_le_delta /
#     countableJointMeanVariance_priorMoment_le_of_not_mem
#     (predeclared Nat-indexed geometric joint-pair catalog, one existential good
#     sample controlling every entry, explicit first-two confidence shares, and
#     an exercised null guard; the posterior-selector receipt is structural,
#     not a numerical nonvacuity witness)
#   exists_forwardIIDBesselPACBayes_event /
#     fairBoolForwardBessel_selected_goodPath_exists
#     (fair-Bool IID stream, two constant hypotheses, two positive declared
#     tilts, point-posterior KL = log 2, and path/time/posterior-dependent
#     selection; an outer-mass bound below one yields one good path carrying
#     every n >= 2 bound; the hybrid-Bessel width remains symbolic)
#   informative_nonvacuous_receipt
#     (biased-Bool IID stream, path-selected ERM posterior, unequal positive
#     tilt weights, KL = log 2, Bessel variance = 1/32, and a positive-mass
#     prefix cylinder that must contain a common-event good path; on that path
#     the theorem-produced risk ceiling is below 343/1000 and the checked
#     forward-Bessel boundary is strictly below the fixed-proxy sub-Gamma
#     boundary evaluated on the same prefix)
HEADLINE_WITNESSES=(
  "examples/WitnessAtTopCS.lean"
  "examples/CheckAnytimeValidNonVacuityWitness.lean"
  "examples/CheckOptimizedLambdaCS.lean"
  "examples/AdversarialWitnessFlagshipFourComponent.lean"
  "examples/RefuteFlagshipFiveWitness.lean"
  "examples/CheckFlagshipAnytimeValidWitness.lean"
  "examples/CheckPACBayesMcAllesterSqrtWitness.lean"
  "examples/WitnessMcAllesterBadEventNonempty.lean"
  "examples/AdversarialWitnessBernstein.lean"
  "examples/CheckIIDIndicatorPACBayesBernstein.lean"
  "examples/CheckIndicatorBernsteinLowRisk.lean"
  "examples/CheckIndicatorBernsteinTiltCatalog.lean"
  "examples/CheckFiniteEmpiricalVariance.lean"
  "examples/CheckBernsteinMGF.lean"
  "examples/CheckFiniteEmpiricalVarianceMGF.lean"
  "examples/CheckFiniteEmpiricalVariancePACBayes.lean"
  "examples/CheckFiniteEmpiricalVarianceTiltCatalog.lean"
  "examples/CheckFiniteEmpiricalBernsteinRisk.lean"
  "examples/CheckFiniteEmpiricalBernsteinRiskCatalog.lean"
  "examples/CheckFiniteEmpiricalBernsteinSqrt.lean"
  "examples/CheckInfiniteEmpiricalBernsteinStitch.lean"
  "examples/CheckContinuousInfiniteEmpiricalBernsteinGaussianWitness.lean"
  "examples/CheckFiniteJointMeanVariancePACBayes.lean"
  "examples/CheckFiniteJointMeanVarianceResidual.lean"
  "examples/CheckCountableJointMeanVariancePACBayes.lean"
  "examples/CheckVCHybridWitness.lean"
  "examples/CheckEmpiricalBernsteinNonVacuityWitness.lean"
  "examples/CheckNamedTails.lean"
  "examples/CheckMaurerKLNonVacuityWitness.lean"
  "examples/CheckEProcess.lean"
  "examples/CheckSelectionCost.lean"
  "examples/CheckAllocationLogLog.lean"
  "examples/CheckUniversalBoundaryLowerBound.lean"
  "examples/CheckBettingCSNonVacuityWitness.lean"
  "examples/CheckTimeUniformPACBayes.lean"
  "examples/CheckTimeUniformScorePACBayes.lean"
  "examples/CheckTimeUniformTiltMixture.lean"
  "examples/CheckTimeUniformIIDTiltMixture.lean"
  "examples/CheckIIDContinuousGaussianPACBayes.lean"
  "examples/CheckIIDContinuousGaussianGridPACBayes.lean"
  "examples/CheckDyadicEpochCS.lean"
  "examples/CheckDyadicEpochPSeriesCS.lean"
  "examples/CheckCramerRao.lean"
  "examples/CheckExponentialFamily.lean"
  "examples/CheckMarkovRisk.lean"
  "examples/CheckMarkovPACBayes.lean"
  "examples/CheckTrajectoryPACBayes.lean"
  "examples/CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative.lean"
  "examples/CheckForwardBesselPACBayesIID.lean"
  "examples/CheckForwardBesselPACBayesIIDInformative.lean"
)

fail=0

echo "== headline witness-quality gate =="
for f in "${HEADLINE_WITNESSES[@]}"; do
  verdict="$(classify_witness "$f")"
  case "$verdict" in
    CONCRETE) echo "  ok   (concrete)  $f" ;;
    FAKE)
      echo "  FAIL (check-only) $f" >&2
      echo "        a headline witness must instantiate the theorem on explicit" >&2
      echo "        data, not just #check / #print axioms." >&2
      fail=1
      ;;
    MISSING)
      echo "  FAIL (missing)    $f" >&2
      fail=1
      ;;
    NONE)
      echo "  FAIL (empty)      $f  (no #check and no concrete decl)" >&2
      fail=1
      ;;
  esac
done

# --- Fixture pair: prove the detector actually discriminates. -----------------
echo "== detector fixture pair =="
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAKE_FIX="$WORK/FixtureFake.lean"
{
  echo "-- A check-only file: must be classified FAKE."
  echo "#check Nat.add"
  echo "#print axioms Nat.add_comm"
} > "$FAKE_FIX"

CONCRETE_FIX="$WORK/FixtureConcrete.lean"
{
  echo "-- A concrete witness: instantiates on explicit data, must be CONCRETE."
  echo "theorem fixture_witness : (1 : Nat) + 1 = 2 := rfl"
  echo "#print axioms fixture_witness"
} > "$CONCRETE_FIX"

fake_verdict="$(classify_witness "$FAKE_FIX")"
concrete_verdict="$(classify_witness "$CONCRETE_FIX")"

if [ "$fake_verdict" = "FAKE" ]; then
  echo "  ok   check-only fixture detected as FAKE"
else
  echo "  FAIL check-only fixture classified $fake_verdict (expected FAKE)" >&2
  fail=1
fi

if [ "$concrete_verdict" = "CONCRETE" ]; then
  echo "  ok   concrete fixture detected as CONCRETE"
else
  echo "  FAIL concrete fixture classified $concrete_verdict (expected CONCRETE)" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "witness-quality gate FAILED" >&2
  exit 1
fi

echo "witness-quality gate passed: all headline witnesses are concrete, detector verified"
