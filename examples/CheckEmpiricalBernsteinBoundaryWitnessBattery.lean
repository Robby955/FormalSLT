import FormalSLT.AnytimeValid.EmpiricalBernsteinCS
import FormalSLT.AnytimeValid.ForwardBesselProcess

/-!
# Exact empirical-Bernstein / forward-Bessel boundary witness battery

Over the declared cases below, this checker pins the Lean arithmetic used by
an independent exact-rational Python implementation.  All paths are
synthetic.  In particular, none of the values comes from a controlled-queue
retrospective receipt.

This is an arithmetic interface check, not a stochastic non-vacuity receipt.

The cases are deliberately heterogeneous rather than a list of nearby numeric
examples.  Together they distinguish:

* exclusive-prefix indexing and division by the prefix length;
* centered Bessel sums from raw second moments and sample variances;
* prediction from the preceding prefix, including the `1 / 2` seed;
* the affine and harmonic branches of the hybrid minimum;
* the square and the `b * lambda / 3` term in the Bernstein cgf;
* variance, log-budget, and `n * lambda` placement in the closed boundary;
* the logarithmic confidence transform and catalog-weight multiplication in
  the actual forward-Bessel APIs.

Every displayed result is an exact rational equality, comparison, or
enclosure.  The out-of-prefix values are conspicuous sentinels so an
accidental inclusive range is not silently accepted.
-/

open FormalSLT.AnytimeValid

noncomputable section

namespace FormalSLT.Examples.CheckEmpiricalBernsteinBoundaryWitnessBattery

/-! ## Synthetic path arithmetic -/

/-- Four asymmetric observations followed by an out-of-prefix sentinel. -/
def skewFour (k : ℕ) : ℝ :=
  match k with
  | 0 => 0
  | 1 => (1 : ℝ) / 4
  | 2 => (1 : ℝ) / 2
  | 3 => 1
  | _ => (37 : ℝ) / 5

/-- `PM-01`: catches an inclusive upper endpoint or a missing `/ n`.
BOUNDARY_WITNESS|id=PM-01|theorem=skewFour_prefixMean_eq|relation=eq|pin=right:7/16
-/
theorem skewFour_prefixMean_eq :
    forwardPrefixMean skewFour 4 = (7 : ℝ) / 16 := by
  norm_num [forwardPrefixMean, skewFour, Finset.sum_range_succ]

/-- `Q-01`: catches use of a raw second moment, division by `n`, or division
by `n - 1` in place of the centered sum `Q_n`.
BOUNDARY_WITNESS|id=Q-01|theorem=skewFour_besselQ_eq|relation=eq|pin=right:35/64
-/
theorem skewFour_besselQ_eq :
    forwardBesselQ skewFour 4 = (35 : ℝ) / 64 := by
  norm_num [forwardBesselQ, forwardPrefixMean, skewFour, Finset.sum_range_succ]

/-- `PRED-01`: catches using the current prefix mean instead of the preceding
prefix mean, or dropping the initial predictor `1 / 2`.
BOUNDARY_WITNESS|id=PRED-01|theorem=skewFour_predictableQuadratic_eq|relation=eq|pin=right:65/64
-/
theorem skewFour_predictableQuadratic_eq :
    forwardPredictableQuadratic skewFour 4 = (65 : ℝ) / 64 := by
  norm_num [forwardPredictableQuadratic, forwardPredictor, forwardPrefixMean,
    skewFour, Finset.sum_range_succ]

/-- `HYB-A`: the affine branch is strictly selected (`169/128 < 65/48`).
This catches replacing `min` by `max`, selecting the wrong branch, using the
wrong `1/2` intercept, or using the wrong `3/2` coefficient.
BOUNDARY_WITNESS|id=HYB-A|theorem=skewFour_hybridPenalty_eq|relation=eq|pin=right:169/128
-/
theorem skewFour_hybridPenalty_eq :
    forwardHybridBesselPenalty skewFour 4 = (169 : ℝ) / 128 := by
  unfold forwardHybridBesselPenalty
  rw [skewFour_besselQ_eq]
  norm_num [harmonic]

/-- A balanced Boolean prefix with a sentinel after the checked range. -/
def balancedFour (k : ℕ) : ℝ :=
  match k with
  | 0 | 1 => 0
  | 2 | 3 => 1
  | _ => (19 : ℝ) / 7

/-- `Q-02`: the maximum-variance four-point Boolean prefix catches loss of
centering and accidental normalization of `Q_n`.
BOUNDARY_WITNESS|id=Q-02|theorem=balancedFour_besselQ_eq|relation=eq|pin=right:1
-/
theorem balancedFour_besselQ_eq :
    forwardBesselQ balancedFour 4 = (1 : ℝ) := by
  norm_num [forwardBesselQ, forwardPrefixMean, balancedFour,
    Finset.sum_range_succ]

/-- `HYB-H4`: the harmonic branch is strictly selected (`47/24 < 2`).
This catches replacing the hybrid minimum by the affine branch everywhere and
checks the `n / (n - 1)` and `H_(n - 2)` terms at `n = 4`.
BOUNDARY_WITNESS|id=HYB-H4|theorem=balancedFour_hybridPenalty_eq|relation=eq|pin=right:47/24
-/
theorem balancedFour_hybridPenalty_eq :
    forwardHybridBesselPenalty balancedFour 4 = (47 : ℝ) / 24 := by
  unfold forwardHybridBesselPenalty
  rw [balancedFour_besselQ_eq]
  norm_num [harmonic]

/-- Five observations make the harmonic index `n - 2 = 3` observable. -/
def splitFive (k : ℕ) : ℝ :=
  match k with
  | 0 | 1 | 2 => 0
  | 3 | 4 => 1
  | _ => (23 : ℝ) / 9

/-- `Q-03`: an odd-length, unbalanced Boolean prefix catches formulas that
only happen to agree on a balanced even prefix.
BOUNDARY_WITNESS|id=Q-03|theorem=splitFive_besselQ_eq|relation=eq|pin=right:6/5
-/
theorem splitFive_besselQ_eq :
    forwardBesselQ splitFive 5 = (6 : ℝ) / 5 := by
  norm_num [forwardBesselQ, forwardPrefixMean, splitFive,
    Finset.sum_range_succ]

/-- `HYB-H5`: the harmonic branch is `53/24`, using `H_3 = 11/6`.
This distinguishes `H_(n - 2)` from the common off-by-one alternatives.
BOUNDARY_WITNESS|id=HYB-H5|theorem=splitFive_hybridPenalty_eq|relation=eq|pin=right:53/24
-/
theorem splitFive_hybridPenalty_eq :
    forwardHybridBesselPenalty splitFive 5 = (53 : ℝ) / 24 := by
  unfold forwardHybridBesselPenalty
  rw [splitFive_besselQ_eq]
  norm_num [harmonic]

/-- The smallest two-sided sample prefix: one zero and one one. -/
def booleanTwo (k : ℕ) : ℝ :=
  match k with
  | 0 => 0
  | 1 => 1
  | _ => (29 : ℝ) / 11

/-- `Q-N2`: the `n = 2` Boolean edge catches an inclusive range and fixes the
centered sum before either hybrid branch is assembled.
BOUNDARY_WITNESS|id=Q-N2|theorem=booleanTwo_besselQ_eq|relation=eq|pin=right:1/2
-/
theorem booleanTwo_besselQ_eq :
    forwardBesselQ booleanTwo 2 = (1 : ℝ) / 2 := by
  norm_num [forwardBesselQ, forwardPrefixMean, booleanTwo,
    Finset.sum_range_succ]

/-- `HARM-N2`: the harmonic candidate is checked directly, outside `min`.
In particular, this fails if `H_0` is changed from `0` to `1`, even though the
affine branch could otherwise mask that mutation in the hybrid result.
BOUNDARY_WITNESS|id=HARM-N2|theorem=booleanTwo_harmonicCandidate_eq|relation=eq|pin=right:5/4
-/
theorem booleanTwo_harmonicCandidate_eq :
    (2 : ℝ) / ((2 : ℝ) - 1) * forwardBesselQ booleanTwo 2 +
        (1 : ℝ) / 4 *
          (1 + (((harmonic (2 - 2) : ℚ) : ℝ))) =
      (5 : ℝ) / 4 := by
  rw [booleanTwo_besselQ_eq]
  norm_num [harmonic]

/-- `HYB-N2`: at `n = 2`, `H_(n - 2) = H_0 = 0` and both hybrid branches
equal `5/4`.  This pins the totalized small-sample edge used by Python v1.
BOUNDARY_WITNESS|id=HYB-N2|theorem=booleanTwo_hybridPenalty_eq|relation=eq|pin=right:5/4
-/
theorem booleanTwo_hybridPenalty_eq :
    forwardHybridBesselPenalty booleanTwo 2 = (5 : ℝ) / 4 := by
  unfold forwardHybridBesselPenalty
  rw [booleanTwo_besselQ_eq]
  norm_num [harmonic]

/-- A constant prefix with a conspicuous out-of-prefix sentinel. -/
def constantThree (k : ℕ) : ℝ :=
  if k < 3 then (1 : ℝ) / 3 else (31 : ℝ) / 7

/-- `Q-ZERO`: a constant prefix has exactly zero centered Bessel sum.
BOUNDARY_WITNESS|id=Q-ZERO|theorem=constantThree_besselQ_eq|relation=eq|pin=right:0
-/
theorem constantThree_besselQ_eq :
    forwardBesselQ constantThree 3 = 0 := by
  norm_num [forwardBesselQ, forwardPrefixMean, constantThree,
    Finset.sum_range_succ]

/-- `HYB-ZERO`: zero `Q_n` leaves exactly the checked affine seed `1/2`.
This catches an added numerical variance floor while retaining the genuine
predictor-initialization term.
BOUNDARY_WITNESS|id=HYB-ZERO|theorem=constantThree_hybridPenalty_eq|relation=eq|pin=right:1/2
-/
theorem constantThree_hybridPenalty_eq :
    forwardHybridBesselPenalty constantThree 3 = (1 : ℝ) / 2 := by
  unfold forwardHybridBesselPenalty
  rw [constantThree_besselQ_eq]
  norm_num [harmonic]

/-! ## Bernstein cgf and closed-boundary assembly -/

/-- `CGF-01`: checks the complete denominator
`2 * (1 - b * lambda / 3)` at `b = 1`, `lambda = 1/2`.
BOUNDARY_WITNESS|id=CGF-01|theorem=cgf_one_half_eq|relation=eq|pin=right:3/20
-/
theorem cgf_one_half_eq :
    empiricalBernsteinCgf 1 ((1 : ℝ) / 2) = (3 : ℝ) / 20 := by
  norm_num [empiricalBernsteinCgf]

/-- `CGF-02`: keeps `b * lambda` fixed but halves `lambda`; the result is a
quarter of `CGF-01`, so a missing square on `lambda` cannot pass both cases.
BOUNDARY_WITNESS|id=CGF-02|theorem=cgf_two_quarter_eq|relation=eq|pin=right:3/80
-/
theorem cgf_two_quarter_eq :
    empiricalBernsteinCgf 2 ((1 : ℝ) / 4) = (3 : ℝ) / 80 := by
  norm_num [empiricalBernsteinCgf]

/-- `PSI-LOWER`: the first three terms of the exact atanh series at `x = 1/7`
give a rational lower enclosure for the logarithmic cumulant at
`lambda = 1/4`.  The associated log ratio is exactly `log (4/3)`.
BOUNDARY_WITNESS|id=PSI-LOWER|theorem=forwardPsi_quarter_lower|relation=le|pin=left:37999/1008420
-/
theorem forwardPsi_quarter_lower :
    (37999 : ℝ) / 1008420 ≤
      forwardEmpiricalBernsteinPsi ((1 : ℝ) / 4) := by
  have hseries := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 7) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  have hlog : -Real.log ((3 : ℝ) / 4) = Real.log ((4 : ℝ) / 3) := by
    rw [← Real.log_inv]
    norm_num
  unfold forwardEmpiricalBernsteinPsi
  norm_num
  rw [hlog]
  nlinarith

/-- `PSI-UPPER`: the matching exact-rational remainder upper bound gives the
other side of a rational enclosure of width exactly `1/403368`.
BOUNDARY_WITNESS|id=PSI-UPPER|theorem=forwardPsi_quarter_upper|relation=le|pin=right:76003/2016840
-/
theorem forwardPsi_quarter_upper :
    forwardEmpiricalBernsteinPsi ((1 : ℝ) / 4) ≤
      (76003 : ℝ) / 2016840 := by
  have hseries := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 7) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  have hlog : -Real.log ((3 : ℝ) / 4) = Real.log ((4 : ℝ) / 3) := by
    rw [← Real.log_inv]
    norm_num
  unfold forwardEmpiricalBernsteinPsi
  norm_num
  rw [hlog]
  nlinarith

/-- `PSI-DISTINCT`: the tight enclosure separates the logarithmic forward
cumulant from `empiricalBernsteinCgf 1` at the same tilt.  Lean states the
strict comparison; Python derives the positive rational separation margin
from the lower enclosure.  The margin is not itself the Lean theorem's RHS.
BOUNDARY_WITNESS|id=PSI-DISTINCT|theorem=cgf_one_quarter_lt_forwardPsi|relation=lt|pin=derived:79663/22185240
-/
theorem cgf_one_quarter_lt_forwardPsi :
    empiricalBernsteinCgf 1 ((1 : ℝ) / 4) <
      forwardEmpiricalBernsteinPsi ((1 : ℝ) / 4) := by
  have hrat : (3 : ℝ) / 88 < (37999 : ℝ) / 1008420 := by norm_num
  rw [show empiricalBernsteinCgf 1 ((1 : ℝ) / 4) = (3 : ℝ) / 88 by
    norm_num [empiricalBernsteinCgf]]
  exact hrat.trans_le forwardPsi_quarter_lower

/-- `BND-VAR`: isolates the variance contribution and the full `n * lambda`
denominator.
BOUNDARY_WITNESS|id=BND-VAR|theorem=closedBoundary_varianceOnly_eq|relation=eq|pin=right:21/512
-/
theorem closedBoundary_varianceOnly_eq :
    empiricalBernsteinClosedFormBoundary
        (forwardBesselQ skewFour 4)
        (empiricalBernsteinCgf 1 ((1 : ℝ) / 2)) 0 4 ((1 : ℝ) / 2) =
      (21 : ℝ) / 512 := by
  rw [skewFour_besselQ_eq, cgf_one_half_eq]
  norm_num [empiricalBernsteinClosedFormBoundary]

/-- `BND-BUDGET`: zeroes the variance contribution, catching a budget divided
by `n` alone, by `lambda` alone, or not divided at all.
BOUNDARY_WITNESS|id=BND-BUDGET|theorem=closedBoundary_budgetOnly_eq|relation=eq|pin=right:28/45
-/
theorem closedBoundary_budgetOnly_eq :
    empiricalBernsteinClosedFormBoundary
        0 (empiricalBernsteinCgf 1 ((1 : ℝ) / 2))
        ((7 : ℝ) / 9) 5 ((1 : ℝ) / 4) =
      (28 : ℝ) / 45 := by
  rw [cgf_one_half_eq]
  norm_num [empiricalBernsteinClosedFormBoundary]

/-- `BND-JOINT-A`: composes the cgf, the strictly selected affine hybrid
branch, a nonzero budget, and `n * lambda = 2`.  It catches misplaced
parentheses between the variance and confidence terms.
BOUNDARY_WITNESS|id=BND-JOINT-A|theorem=closedBoundary_jointAffine_eq|relation=eq|pin=right:1307/5120
-/
theorem closedBoundary_jointAffine_eq :
    empiricalBernsteinClosedFormBoundary
        (forwardHybridBesselPenalty skewFour 4)
        (empiricalBernsteinCgf 1 ((1 : ℝ) / 2))
        ((5 : ℝ) / 16) 4 ((1 : ℝ) / 2) =
      (1307 : ℝ) / 5120 := by
  rw [skewFour_hybridPenalty_eq, cgf_one_half_eq]
  norm_num [empiricalBernsteinClosedFormBoundary]

/-- `BND-JOINT-H`: the corresponding complete boundary uses the strictly
selected harmonic branch and a different `(b, lambda)` pair.
BOUNDARY_WITNESS|id=BND-JOINT-H|theorem=closedBoundary_jointHarmonic_eq|relation=eq|pin=right:127/640
-/
theorem closedBoundary_jointHarmonic_eq :
    empiricalBernsteinClosedFormBoundary
        (forwardHybridBesselPenalty balancedFour 4)
        (empiricalBernsteinCgf 2 ((1 : ℝ) / 4))
        ((1 : ℝ) / 8) 4 ((1 : ℝ) / 4) =
      (127 : ℝ) / 640 := by
  rw [balancedFour_hybridPenalty_eq, cgf_two_quarter_eq]
  norm_num [empiricalBernsteinClosedFormBoundary]

/-! ## Pins to the actual forward-Bessel boundary APIs -/

/-- Definitional shape pin: the forward-Bessel boundary is the generic
empirical-Bernstein closed form with the hybrid penalty, the logarithmic
`forwardEmpiricalBernsteinPsi` cumulant, and a logarithmic budget. -/
theorem forwardBoundary_eq_closedForm
    {Ω : Type*} (X : ℕ → Ω → ℝ) (lam delta : ℝ) (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinBesselBoundary X lam delta n ω =
      empiricalBernsteinClosedFormBoundary
        (forwardHybridBesselPenalty (fun k ↦ X k ω) n)
        (forwardEmpiricalBernsteinPsi lam) (Real.log (1 / delta)) n lam := by
  unfold forwardEmpiricalBernsteinBesselBoundary
    empiricalBernsteinClosedFormBoundary
  ring

def splitFiveProcess (k : ℕ) (_ω : Unit) : ℝ := splitFive k

/-- The fixed-boundary confidence transform used below has exact log budget
`1/8`.  Keeping this as a named equality makes the sign independently
checkable rather than hiding it inside a one-sided numeric certificate. -/
theorem fixedBoundary_logBudget_eq :
    Real.log (1 / Real.exp (-((1 : ℝ) / 8))) = (1 : ℝ) / 8 := by
  rw [show (1 / Real.exp (-((1 : ℝ) / 8))) = Real.exp ((1 : ℝ) / 8) by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring]
  rw [Real.log_exp]

/-- `BND-FWD`: with `delta = exp (-1/8)`, the actual logarithmic budget is
exactly `1/8`.  After `forwardBoundary_eq_closedForm` pins the exact formula,
the checked quadratic cgf majorant gives the rational upper certificate
`25/144`.  The inequality is a tractable upper witness, not a uniqueness test
for alternative formulas.
BOUNDARY_WITNESS|id=BND-FWD|theorem=forwardBoundary_splitFive_le|relation=le|pin=right:25/144
-/
theorem forwardBoundary_splitFive_le :
    forwardEmpiricalBernsteinBesselBoundary
        splitFiveProcess ((1 : ℝ) / 4) (Real.exp (-((1 : ℝ) / 8))) 5 () ≤
      (25 : ℝ) / 144 := by
  rw [forwardBoundary_eq_closedForm]
  simp only [splitFiveProcess]
  rw [splitFive_hybridPenalty_eq]
  rw [fixedBoundary_logBudget_eq]
  have hpsi := forwardEmpiricalBernsteinPsi_le_quadratic
    (lam := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num [empiricalBernsteinClosedFormBoundary] at hpsi ⊢
  nlinarith

/-- `BND-FWD-LOWER`: the same public API is at least `1/10`.  This is the
confidence-budget contribution alone; the variance contribution is
nonnegative.  Paired with `BND-FWD`, it rejects a wrong-sign log budget.
BOUNDARY_WITNESS|id=BND-FWD-LOWER|theorem=forwardBoundary_splitFive_ge|relation=le|pin=left:1/10
-/
theorem forwardBoundary_splitFive_ge :
    (1 : ℝ) / 10 ≤
      forwardEmpiricalBernsteinBesselBoundary
        splitFiveProcess ((1 : ℝ) / 4) (Real.exp (-((1 : ℝ) / 8))) 5 () := by
  rw [forwardBoundary_eq_closedForm]
  simp only [splitFiveProcess]
  rw [splitFive_hybridPenalty_eq, fixedBoundary_logBudget_eq]
  have hpsi := forwardEmpiricalBernsteinPsi_nonneg
    (lam := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num [empiricalBernsteinClosedFormBoundary] at hpsi ⊢
  nlinarith

/-! ## Two-sided confidence-budget split -/

/-- The total two-sided confidence budget used below is strictly below one. -/
theorem twoSidedBoundary_totalBudget_lt_one :
    2 * Real.exp (-1) < 1 := by
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos 1)]
  exact hexp

/-- For total confidence budget `2 * exp (-1)`, the `delta / 2` endpoint used
by the two-sided theorem has exact log budget `1`.  The total budget is below
one, so this is not a vacuous confidence choice. -/
theorem twoSidedBoundary_logBudget_eq :
    Real.log (1 / ((2 * Real.exp (-1)) / 2)) = 1 := by
  rw [show (2 * Real.exp (-1)) / 2 = Real.exp (-1) by ring]
  rw [show (1 / Real.exp (-1)) = Real.exp 1 by
    rw [one_div, ← Real.exp_neg]
    norm_num]
  rw [Real.log_exp]

/-- `BND-TWO-SIDED-SHAPE`: definitional expansion of the two-sided failure
event.  The theorem mentions the library definition itself, so changing its
endpoint from `delta / 2` to another split breaks this `rfl` witness.
BOUNDARY_WITNESS|id=BND-TWO-SIDED-SHAPE|theorem=twoSidedFailure_halfBudget_eq|relation=eq|pin=right_factor:1/2
-/
theorem twoSidedFailure_halfBudget_eq
    {Omega : Type*} (X : ℕ → Omega → ℝ) (mean lam delta : ℝ) :
    forwardEmpiricalBernsteinTwoSidedBesselFailure X mean lam delta =
      {ω | ∃ n : ℕ, 2 ≤ n ∧
        forwardEmpiricalBernsteinBesselBoundary X lam (delta / 2) n ω ≤
          |mean - forwardPrefixMean (fun k ↦ X k ω) n|} := by
  rfl

/-- `BND-TWO-SIDED`: the exact endpoint appearing in the two-sided guarantee,
evaluated at total budget `delta = 2 * exp (-1)`.  Splitting by two
leaves log budget `1`, and the same checked quadratic cumulant majorant gives
the rational upper certificate `629/720`.
BOUNDARY_WITNESS|id=BND-TWO-SIDED|theorem=twoSidedBoundary_splitFive_le|relation=le|pin=right:629/720
-/
theorem twoSidedBoundary_splitFive_le :
    forwardEmpiricalBernsteinBesselBoundary
        splitFiveProcess ((1 : ℝ) / 4) ((2 * Real.exp (-1)) / 2) 5 () ≤
      (629 : ℝ) / 720 := by
  rw [forwardBoundary_eq_closedForm]
  simp only [splitFiveProcess]
  rw [splitFive_hybridPenalty_eq, twoSidedBoundary_logBudget_eq]
  have hpsi := forwardEmpiricalBernsteinPsi_le_quadratic
    (lam := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num [empiricalBernsteinClosedFormBoundary] at hpsi ⊢
  nlinarith

def halfWeight (_j : Unit) : ℝ := (1 : ℝ) / 2
def quarterTilt (_j : Unit) : ℝ := (1 : ℝ) / 4

/-- `BND-CATALOG-SHAPE`: the exact catalog API specializes to the atom-specific
budget `delta / 2` at atom weight `1/2`.  Unlike the numerical upper
certificate below, this equality fails if the catalog combines `delta` and
the atom weight by a sum or quotient, or omits the weight.
BOUNDARY_WITNESS|id=BND-CATALOG-SHAPE|theorem=catalogBoundary_halfWeight_eq|relation=eq|pin=right_factor:1/2
-/
theorem catalogBoundary_halfWeight_eq
    {Omega : Type*} (X : ℕ → Omega → ℝ) (delta : ℝ)
    (n : ℕ) (omega : Omega) :
    forwardEmpiricalBernsteinTiltCatalogBoundary
        halfWeight quarterTilt X delta () n omega =
      forwardEmpiricalBernsteinBesselBoundary
        X ((1 : ℝ) / 4) (delta / 2) n omega := by
  rw [forwardEmpiricalBernsteinTiltCatalogBoundary_eq]
  congr 2
  · rfl
  · simp [halfWeight]

/-- The catalog choice used below has exact log budget `1` after multiplying
`delta = 2 * exp (-1)` by the atom weight `1/2`. -/
theorem catalogBoundary_logBudget_eq :
    Real.log (1 / ((2 * Real.exp (-1)) * ((1 : ℝ) / 2))) = 1 := by
  rw [show (2 * Real.exp (-1)) * ((1 : ℝ) / 2) = Real.exp (-1) by ring]
  rw [show (1 / Real.exp (-1)) = Real.exp 1 by
    rw [one_div, ← Real.exp_neg]
    norm_num]
  rw [Real.log_exp]

/-- `BND-CATALOG`: `delta = 2 * exp (-1)` and weight `1/2` produce the exact
atom budget `exp (-1)` before inversion and logarithm.  The resulting rational
upper certificate exercises that simplification after
`catalogBoundary_halfWeight_eq` pins the required product.  The inequality is
not by itself a uniqueness test for alternative formulas.
BOUNDARY_WITNESS|id=BND-CATALOG|theorem=catalogBoundary_splitFive_le|relation=le|pin=right:629/720
-/
theorem catalogBoundary_splitFive_le :
    forwardEmpiricalBernsteinTiltCatalogBoundary
        halfWeight quarterTilt splitFiveProcess
        (2 * Real.exp (-1)) () 5 () ≤
      (629 : ℝ) / 720 := by
  unfold forwardEmpiricalBernsteinTiltCatalogBoundary
  simp only [halfWeight, quarterTilt, splitFiveProcess]
  rw [splitFive_hybridPenalty_eq]
  rw [catalogBoundary_logBudget_eq]
  have hpsi := forwardEmpiricalBernsteinPsi_le_quadratic
    (lam := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at hpsi ⊢
  nlinarith

/-- `BND-CATALOG-LOWER`: the catalog API is at least `4/5`, its confidence
contribution alone.  Together with the exact `delta * weight` equality and the
upper certificate, this catches wrong-sign or misplaced catalog budgets.
BOUNDARY_WITNESS|id=BND-CATALOG-LOWER|theorem=catalogBoundary_splitFive_ge|relation=le|pin=left:4/5
-/
theorem catalogBoundary_splitFive_ge :
    (4 : ℝ) / 5 ≤
      forwardEmpiricalBernsteinTiltCatalogBoundary
        halfWeight quarterTilt splitFiveProcess
        (2 * Real.exp (-1)) () 5 () := by
  unfold forwardEmpiricalBernsteinTiltCatalogBoundary
  simp only [halfWeight, quarterTilt, splitFiveProcess]
  rw [splitFive_hybridPenalty_eq, catalogBoundary_logBudget_eq]
  have hpsi := forwardEmpiricalBernsteinPsi_nonneg
    (lam := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at hpsi ⊢
  nlinarith

#check empiricalBernsteinCgf
#check empiricalBernsteinClosedFormBoundary
#check forwardBesselQ
#check forwardPredictableQuadratic
#check forwardHybridBesselPenalty
#check forwardEmpiricalBernsteinBesselBoundary
#check forwardEmpiricalBernsteinTiltCatalogBoundary

#check skewFour_prefixMean_eq
#check skewFour_besselQ_eq
#check skewFour_predictableQuadratic_eq
#check skewFour_hybridPenalty_eq
#check balancedFour_besselQ_eq
#check balancedFour_hybridPenalty_eq
#check splitFive_besselQ_eq
#check splitFive_hybridPenalty_eq
#check booleanTwo_besselQ_eq
#check booleanTwo_harmonicCandidate_eq
#check booleanTwo_hybridPenalty_eq
#check constantThree_besselQ_eq
#check constantThree_hybridPenalty_eq
#check cgf_one_half_eq
#check cgf_two_quarter_eq
#check forwardPsi_quarter_lower
#check forwardPsi_quarter_upper
#check cgf_one_quarter_lt_forwardPsi
#check closedBoundary_varianceOnly_eq
#check closedBoundary_budgetOnly_eq
#check closedBoundary_jointAffine_eq
#check closedBoundary_jointHarmonic_eq
#check forwardBoundary_eq_closedForm
#check fixedBoundary_logBudget_eq
#check forwardBoundary_splitFive_le
#check forwardBoundary_splitFive_ge
#check twoSidedBoundary_totalBudget_lt_one
#check twoSidedBoundary_logBudget_eq
#check twoSidedFailure_halfBudget_eq
#check twoSidedBoundary_splitFive_le
#check catalogBoundary_halfWeight_eq
#check catalogBoundary_logBudget_eq
#check catalogBoundary_splitFive_le
#check catalogBoundary_splitFive_ge

#print axioms skewFour_prefixMean_eq
#print axioms skewFour_besselQ_eq
#print axioms skewFour_predictableQuadratic_eq
#print axioms skewFour_hybridPenalty_eq
#print axioms balancedFour_besselQ_eq
#print axioms balancedFour_hybridPenalty_eq
#print axioms splitFive_besselQ_eq
#print axioms splitFive_hybridPenalty_eq
#print axioms booleanTwo_besselQ_eq
#print axioms booleanTwo_harmonicCandidate_eq
#print axioms booleanTwo_hybridPenalty_eq
#print axioms constantThree_besselQ_eq
#print axioms constantThree_hybridPenalty_eq
#print axioms cgf_one_half_eq
#print axioms cgf_two_quarter_eq
#print axioms forwardPsi_quarter_lower
#print axioms forwardPsi_quarter_upper
#print axioms cgf_one_quarter_lt_forwardPsi
#print axioms closedBoundary_varianceOnly_eq
#print axioms closedBoundary_budgetOnly_eq
#print axioms closedBoundary_jointAffine_eq
#print axioms closedBoundary_jointHarmonic_eq
#print axioms forwardBoundary_eq_closedForm
#print axioms fixedBoundary_logBudget_eq
#print axioms forwardBoundary_splitFive_le
#print axioms forwardBoundary_splitFive_ge
#print axioms twoSidedBoundary_totalBudget_lt_one
#print axioms twoSidedBoundary_logBudget_eq
#print axioms twoSidedFailure_halfBudget_eq
#print axioms twoSidedBoundary_splitFive_le
#print axioms catalogBoundary_halfWeight_eq
#print axioms catalogBoundary_logBudget_eq
#print axioms catalogBoundary_splitFive_le
#print axioms catalogBoundary_splitFive_ge

end FormalSLT.Examples.CheckEmpiricalBernsteinBoundaryWitnessBattery
