import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import FormalSLT.PACBayesBoundedLoss
import FormalSLT.PACBayesFiniteProductMGF
import FormalSLT.Probability.Concentration
import FormalSLT.Probability.FiniteUnionBound
import FormalSLT.Probability.BernsteinMGF
import FormalSLT.Rademacher.FiniteSample

/-!
# Finite localized Rademacher scaffolding

This module starts the localized-complexity / fast-rate lane in a deliberately
finite setting. It provides excess-loss bookkeeping, finite second-moment
localization, Bernstein-condition adapters, and an empirical Rademacher wrapper
over a localized finite subtype.

The statements are intentionally preparatory:

* finite hypothesis index;
* finite outcome/support type for population sums;
* scalar real-valued losses;
* deterministic fixed-point and localized deviation certificates;
* finite bad-event mass adapters for localized upper-deviation events, with
  one-coordinate MGF instantiations left to caller-supplied assumptions;
* no infinite classes, separability, or measurable suprema.

The main mathematical bridge in this file is that a Bernstein condition turns
small excess risk into small second moment, which is the localization shape
needed by local Rademacher fast-rate arguments.
-/

open scoped BigOperators

namespace FormalSLT.Rademacher.Localized

open FormalSLT.Rademacher.FiniteSample
  (empiricalRademacherComplexity signOfBool two_pow_inv_pos)

variable {ι Z : Type*}

/-! ## Excess losses and finite population moments -/

/-- Excess loss of hypothesis `i` relative to a comparator `iStar`. -/
def excessLoss (ℓ : ι → Z → ℝ) (iStar i : ι) (z : Z) : ℝ :=
  ℓ i z - ℓ iStar z

/-- Finite population mean of a scalar observable under weights `p`. The
weights are explicit so this can serve finite-support probability spaces
without measure-theoretic overhead. -/
noncomputable def finiteMean [Fintype Z] (p : Z → ℝ) (f : Z → ℝ) : ℝ :=
  ∑ z, p z * f z

/-- Finite second-moment proxy `E_p[f²]`. -/
noncomputable def finiteSecondMoment [Fintype Z] (p : Z → ℝ) (f : Z → ℝ) : ℝ :=
  ∑ z, p z * f z ^ 2

/-- Finite excess risk of `i` relative to `iStar`. -/
noncomputable def finiteExcessRisk [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι) : ℝ :=
  finiteMean p (excessLoss ℓ iStar i)

/-- Finite-sample mean of a scalar observable on a deterministic sample. -/
noncomputable def empiricalMean {n : ℕ} (z : Fin n → Z) (f : Z → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, f (z k)

/-- Empirical excess risk of `i` relative to `iStar` on a deterministic
sample. -/
noncomputable def empiricalExcessRisk
    (ℓ : ι → Z → ℝ) (iStar i : ι) {n : ℕ} (z : Fin n → Z) : ℝ :=
  empiricalMean z (excessLoss ℓ iStar i)

@[simp] theorem empiricalExcessRisk_self
    (ℓ : ι → Z → ℝ) (iStar : ι) {n : ℕ} (z : Fin n → Z) :
    empiricalExcessRisk ℓ iStar iStar z = 0 := by
  simp [empiricalExcessRisk, empiricalMean, excessLoss]

/-- Finite Bernstein condition for the excess-loss class.

For each hypothesis, the second moment of the excess loss is controlled by a
fixed multiple of its excess risk. This is the variance/localization condition
used in fast-rate local Rademacher arguments. -/
def BernsteinCondition [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι) (c : ℝ) : Prop :=
  ∀ i : ι,
    finiteSecondMoment p (excessLoss ℓ iStar i) ≤
      c * finiteExcessRisk p ℓ iStar i

/-- The finite class localized by a second-moment radius. -/
def LocalizedBySecondMoment [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι) (r : ℝ) (i : ι) : Prop :=
  finiteSecondMoment p (excessLoss ℓ iStar i) ≤ r

/-- The finite class localized by an excess-risk radius. -/
def LocalizedByExcessRisk [Fintype Z]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι) (r : ℝ) (i : ι) : Prop :=
  finiteExcessRisk p ℓ iStar i ≤ r

/-- Second moments are nonnegative under nonnegative finite weights. -/
theorem finiteSecondMoment_nonneg [Fintype Z]
    {p : Z → ℝ} {f : Z → ℝ}
    (hp : ∀ z, 0 ≤ p z) :
    0 ≤ finiteSecondMoment p f := by
  unfold finiteSecondMoment
  exact Finset.sum_nonneg (fun z _hz => mul_nonneg (hp z) (sq_nonneg (f z)))

@[simp] theorem excessLoss_self
    (ℓ : ι → Z → ℝ) (iStar : ι) (z : Z) :
    excessLoss ℓ iStar iStar z = 0 := by
  simp [excessLoss]

/-- The comparator belongs to every nonnegative second-moment localization
radius. -/
theorem self_mem_localizedBySecondMoment [Fintype Z]
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι} {r : ℝ}
    (hr : 0 ≤ r) :
    LocalizedBySecondMoment p ℓ iStar r iStar := by
  simpa [LocalizedBySecondMoment, finiteSecondMoment, excessLoss] using hr

/-- The comparator belongs to every nonnegative excess-risk localization
radius. -/
theorem self_mem_localizedByExcessRisk [Fintype Z]
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι} {r : ℝ}
    (hr : 0 ≤ r) :
    LocalizedByExcessRisk p ℓ iStar r iStar := by
  simpa [LocalizedByExcessRisk, finiteExcessRisk, finiteMean, excessLoss] using hr

/-- Under a finite Bernstein condition with positive constant, excess risks
are nonnegative.

This is a useful sanity lemma for later fixed-point arguments: the Bernstein
condition itself rules out negative excess risk when the weights are
nonnegative and `c > 0`. -/
theorem bernstein_excessRisk_nonneg [Fintype Z]
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι} {c : ℝ}
    (hp : ∀ z, 0 ≤ p z)
    (hc : 0 < c)
    (hbern : BernsteinCondition p ℓ iStar c)
    (i : ι) :
    0 ≤ finiteExcessRisk p ℓ iStar i := by
  have hsecond_nonneg :
      0 ≤ finiteSecondMoment p (excessLoss ℓ iStar i) :=
    finiteSecondMoment_nonneg (p := p) (f := excessLoss ℓ iStar i) hp
  have hsecond_le :
      finiteSecondMoment p (excessLoss ℓ iStar i) ≤
        c * finiteExcessRisk p ℓ iStar i :=
    hbern i
  have hmul_nonneg : 0 ≤ c * finiteExcessRisk p ℓ iStar i :=
    le_trans hsecond_nonneg hsecond_le
  have hmul_nonneg' : 0 ≤ finiteExcessRisk p ℓ iStar i * c := by
    simpa [mul_comm] using hmul_nonneg
  exact nonneg_of_mul_nonneg_left hmul_nonneg' hc

/-- Bernstein turns excess-risk localization into second-moment localization.

If `E[(ℓ_i - ℓ_i*)²] ≤ c · excessRisk(i)` and `excessRisk(i) ≤ r`, then `i`
lies in the second-moment localized class at radius `c * r`. -/
theorem localizedBySecondMoment_of_excessRisk_le [Fintype Z]
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar i : ι} {c r : ℝ}
    (hc : 0 ≤ c)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hrisk : finiteExcessRisk p ℓ iStar i ≤ r) :
    LocalizedBySecondMoment p ℓ iStar (c * r) i := by
  unfold LocalizedBySecondMoment
  exact le_trans (hbern i) (mul_le_mul_of_nonneg_left hrisk hc)

/-! ## Localized empirical Rademacher wrappers -/

/-- Empirical Rademacher complexity of the excess-loss class restricted to a
finite predicate `P`.

This is only a finite-subtype wrapper around
`FiniteSample.empiricalRademacherComplexity`; the caller supplies a witness
that the localized class is nonempty. -/
noncomputable def localizedEmpiricalRademacherComplexity
    [Fintype ι] {n : ℕ}
    (ℓ : ι → Z → ℝ) (iStar : ι) (z : Fin n → Z)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i) : ℝ :=
  letI : Fintype {i : ι // P i} := inferInstance
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  empiricalRademacherComplexity
    (fun (i : {i : ι // P i}) (x : Z) => excessLoss ℓ iStar i.1 x) z

/-- A localized empirical Rademacher complexity is nonnegative if the localized
class contains an identically zero excess-loss comparator.

This is the finite deterministic fact used to compare random fast-rate
thresholds with their fixed-`ε` lower envelope. -/
theorem localizedEmpiricalRademacherComplexity_nonneg_of_zero
    [Fintype ι] {n : ℕ}
    (ℓ : ι → Z → ℝ) (iStar : ι) (z : Fin n → Z)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (i0 : ι) (hi0 : P i0)
    (hzero : ∀ x : Z, excessLoss ℓ iStar i0 x = 0) :
    0 ≤ localizedEmpiricalRademacherComplexity ℓ iStar z P hP := by
  classical
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  unfold localizedEmpiricalRademacherComplexity
  unfold empiricalRademacherComplexity
  apply mul_nonneg
  · exact le_of_lt (two_pow_inv_pos (n := n))
  · apply Finset.sum_nonneg
    intro σ _hσ
    let i0' : {i : ι // P i} := ⟨i0, hi0⟩
    have hsup :
        (n : ℝ)⁻¹ * ∑ k : Fin n,
            signOfBool (σ k) * excessLoss ℓ iStar i0'.1 (z k) ≤
          (Finset.univ : Finset {i : ι // P i}).sup' Finset.univ_nonempty
            (fun i : {i : ι // P i} =>
              (n : ℝ)⁻¹ * ∑ k : Fin n,
                signOfBool (σ k) * excessLoss ℓ iStar i.1 (z k)) :=
      Finset.le_sup'
        (s := (Finset.univ : Finset {i : ι // P i}))
        (f := fun i : {i : ι // P i} =>
          (n : ℝ)⁻¹ * ∑ k : Fin n,
            signOfBool (σ k) * excessLoss ℓ iStar i.1 (z k))
        (b := i0') (Finset.mem_univ i0')
    have hval :
        (n : ℝ)⁻¹ * ∑ k : Fin n,
            signOfBool (σ k) * excessLoss ℓ iStar i0'.1 (z k) = 0 := by
      simp [i0', hzero]
    linarith

/-- Supremum over a finite subtype is monotone under predicate inclusion. -/
private theorem subtype_sup_le_of_imp
    [Fintype ι] {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    [Nonempty {i : ι // P i}] [Nonempty {i : ι // Q i}]
    (hPQ : ∀ i, P i → Q i)
    (f : ι → ℝ) :
    (Finset.univ : Finset {i : ι // P i}).sup' Finset.univ_nonempty
        (fun i => f i.1) ≤
      (Finset.univ : Finset {i : ι // Q i}).sup' Finset.univ_nonempty
        (fun i => f i.1) := by
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro i _hi
  simpa using
    (Finset.le_sup'
      (s := (Finset.univ : Finset {i : ι // Q i}))
      (f := fun i : {i : ι // Q i} => f i.1)
      (b := ⟨i.1, hPQ i.1 i.2⟩)
      (Finset.mem_univ (⟨i.1, hPQ i.1 i.2⟩ : {i : ι // Q i})))

/-- Localized empirical Rademacher complexity is monotone under finite
predicate inclusion.

This is the finite-class monotonicity adapter needed to compare
risk-localized and second-moment-localized excess-loss classes. -/
theorem localizedEmpiricalRademacherComplexity_mono
    [Fintype ι] {n : ℕ}
    (ℓ : ι → Z → ℝ) (iStar : ι) (z : Fin n → Z)
    {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    (hP : ∃ i : ι, P i) (hQ : ∃ i : ι, Q i)
    (hPQ : ∀ i, P i → Q i) :
    localizedEmpiricalRademacherComplexity ℓ iStar z P hP ≤
      localizedEmpiricalRademacherComplexity ℓ iStar z Q hQ := by
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  letI : Nonempty {i : ι // Q i} :=
    ⟨⟨Classical.choose hQ, Classical.choose_spec hQ⟩⟩
  unfold localizedEmpiricalRademacherComplexity
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (two_pow_inv_pos (n := n)))
  refine Finset.sum_le_sum ?_
  intro σ _hσ
  exact subtype_sup_le_of_imp (P := P) (Q := Q) hPQ
    (fun i => (n : ℝ)⁻¹ * ∑ k : Fin n,
      signOfBool (σ k) * excessLoss ℓ iStar i (z k))

/-- Empirical Rademacher complexity of the second-moment localized excess-loss
class at radius `r`.

The comparator `iStar` witnesses nonemptiness whenever `0 ≤ r`, because its
excess loss is identically zero. This is the canonical finite localized class
for the fast-rate/local-Rademacher layer. -/
noncomputable def localizedSecondMomentEmpiricalRademacherComplexity
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) (r : ℝ) (hr : 0 ≤ r) : ℝ := by
  classical
  let P : ι → Prop := LocalizedBySecondMoment p ℓ iStar r
  exact localizedEmpiricalRademacherComplexity ℓ iStar z P
    ⟨iStar, by
      dsimp [P]
      exact self_mem_localizedBySecondMoment
        (p := p) (ℓ := ℓ) (iStar := iStar) hr⟩

/-- Empirical Rademacher complexity of the excess-risk localized excess-loss
class at radius `r`. -/
noncomputable def localizedExcessRiskEmpiricalRademacherComplexity
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) (r : ℝ) (hr : 0 ≤ r) : ℝ := by
  classical
  let P : ι → Prop := LocalizedByExcessRisk p ℓ iStar r
  exact localizedEmpiricalRademacherComplexity ℓ iStar z P
    ⟨iStar, by
      dsimp [P]
      exact self_mem_localizedByExcessRisk
        (p := p) (ℓ := ℓ) (iStar := iStar) hr⟩

/-- The excess-risk localized empirical Rademacher complexity is nonnegative.

The comparator `iStar` belongs to every nonnegative excess-risk localization
radius and has identically zero excess loss. -/
theorem localizedExcessRiskEmpiricalRademacherComplexity_nonneg
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr := by
  classical
  unfold localizedExcessRiskEmpiricalRademacherComplexity
  let P : ι → Prop := LocalizedByExcessRisk p ℓ iStar r
  exact localizedEmpiricalRademacherComplexity_nonneg_of_zero
    (ℓ := ℓ) (iStar := iStar) (z := z) (P := P)
    (hP := ⟨iStar, by
      dsimp [P]
      exact self_mem_localizedByExcessRisk
        (p := p) (ℓ := ℓ) (iStar := iStar) hr⟩)
    iStar
    (by
      dsimp [P]
      exact self_mem_localizedByExcessRisk
        (p := p) (ℓ := ℓ) (iStar := iStar) hr)
    (by intro x; simp [excessLoss])

/-- Bernstein localization bridge for empirical Rademacher complexity.

Under a finite Bernstein condition, the class with excess risk at most `r` is
contained in the class with excess-loss second moment at most `c * r`; hence
the corresponding localized empirical Rademacher complexity is bounded by the
second-moment-localized one. -/
theorem localizedExcessRiskEmpiricalRademacherComplexity_le_secondMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbern : BernsteinCondition p ℓ iStar c) :
    localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr ≤
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z (c * r) (mul_nonneg hc hr) := by
  classical
  unfold localizedExcessRiskEmpiricalRademacherComplexity
  unfold localizedSecondMomentEmpiricalRademacherComplexity
  let P : ι → Prop := LocalizedByExcessRisk p ℓ iStar r
  let Q : ι → Prop := LocalizedBySecondMoment p ℓ iStar (c * r)
  exact localizedEmpiricalRademacherComplexity_mono ℓ iStar z
    (P := P) (Q := Q)
    ⟨iStar, by
      dsimp [P]
      exact self_mem_localizedByExcessRisk
        (p := p) (ℓ := ℓ) (iStar := iStar) hr⟩
    ⟨iStar, by
      dsimp [Q]
      exact self_mem_localizedBySecondMoment
        (p := p) (ℓ := ℓ) (iStar := iStar) (mul_nonneg hc hr)⟩
    (by
      intro i hi
      dsimp [P, Q] at hi ⊢
      exact localizedBySecondMoment_of_excessRisk_le
        (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
        (c := c) (r := r) hc hbern hi)

/-! ## Deterministic fixed-point certificates -/

/-- A finite fixed-point upper certificate for a localized-complexity
envelope.

The intended reading is: once the radius is at least `rStar`, the envelope
`φ` lies below the identity. This is the deterministic algebraic core of the
localized Rademacher fixed-point step; concentration/oracle-inequality layers
can later provide the envelope hypotheses. -/
def FixedPointUpperCertificate (φ : ℝ → ℝ) (rStar : ℝ) : Prop :=
  ∀ ⦃r : ℝ⦄, rStar ≤ r → φ r ≤ r

/-- A fixed-point certificate turns an envelope bound on the second-moment
localized empirical complexity into a bound by the radius itself. -/
theorem localizedSecondMomentEmpiricalRademacherComplexity_le_of_fixedPointCertificate
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {φ : ℝ → ℝ} {rStar r : ℝ} (hr : 0 ≤ r)
    (henvelope :
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z r hr ≤ φ r)
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ r) :
    localizedSecondMomentEmpiricalRademacherComplexity p ℓ iStar z r hr ≤ r :=
  le_trans henvelope (hfixed hrStar)

/-- Bernstein plus a fixed-point certificate bounds excess-risk localized
empirical complexity by the second-moment radius `c * r`.

This composes the existing Bernstein localization bridge with the deterministic
fixed-point certificate above. It is still a finite empirical-complexity
statement: it does not claim the final fast-rate/oracle inequality. -/
theorem localizedExcessRiskEmpiricalRademacherComplexity_le_of_bernstein_fixedPointCertificate
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {c r rStar : ℝ} {φ : ℝ → ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbern : BernsteinCondition p ℓ iStar c)
    (henvelope :
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r))
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r) :
    localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr ≤
      c * r := by
  exact le_trans
    (localizedExcessRiskEmpiricalRademacherComplexity_le_secondMoment
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (c := c) (r := r) hc hr hbern)
    (localizedSecondMomentEmpiricalRademacherComplexity_le_of_fixedPointCertificate
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (φ := φ) (rStar := rStar) (r := c * r)
      (mul_nonneg hc hr) henvelope hfixed hrStar)

/-! ## Localized deviation certificates -/

/-- Deterministic localized upper-deviation certificate.

The intended probabilistic reading is: on a good concentration event, every
hypothesis in the localized predicate `P` has population excess risk at most
its empirical excess risk plus slack `η`. This definition deliberately keeps
the probability layer outside the localized algebra. -/
def LocalizedDeviationCertificate [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) (P : ι → Prop) (η : ℝ) : Prop :=
  ∀ i : ι, P i →
    finiteExcessRisk p ℓ iStar i ≤ empiricalExcessRisk ℓ iStar i z + η

/-- Supremum of the one-sided population-minus-empirical excess-risk gap over a
localized finite predicate.

This is the deterministic statistic whose high-probability control will later
construct `LocalizedDeviationCertificate`. -/
noncomputable def localizedUpperDeviation
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) (P : ι → Prop) [DecidablePred P]
    (hP : ∃ i : ι, P i) : ℝ :=
  letI : Fintype {i : ι // P i} := inferInstance
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  (Finset.univ : Finset {i : ι // P i}).sup' Finset.univ_nonempty
    (fun i =>
      finiteExcessRisk p ℓ iStar i.1 -
        empiricalExcessRisk ℓ iStar i.1 z)

/-- Event that the localized upper-deviation statistic is at most `η`.

This packages the future probability statement as a set of samples while keeping
the current layer deterministic. -/
noncomputable def localizedUpperDeviationEvent
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : ℝ) : Set (Fin n → Z) :=
  {z | localizedUpperDeviation p ℓ iStar z P hP ≤ η}

/-- Event that the localized upper-deviation statistic is controlled by a
sample-dependent slack.

This is only an interface for random-threshold arguments. A probability theorem
must still bound the mass outside this event. -/
noncomputable def localizedSampleDependentUpperDeviationEvent
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) : Set (Fin n → Z) :=
  {z | localizedUpperDeviation p ℓ iStar z P hP ≤ η z}

/-- Sample-dependent upper-deviation event used by the finite fast-rate shell.

The threshold is the empirical localized complexity term plus slack. This
definition does not prove the event has high probability; it names the exact
random-threshold event that must be controlled. -/
noncomputable def localizedFastRateUpperDeviationEvent
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (r : ℝ) (hr : 0 ≤ r) (ε : ℝ)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j) :
    Set (Fin n → Z) :=
  localizedSampleDependentUpperDeviationEvent p ℓ iStar
    (LocalizedByExcessRisk p ℓ iStar r) hP
    (fun z : Fin n → Z =>
      2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr + ε)

/-- Finite weighted mass of the one-hypothesis upper-deviation bad event. -/
noncomputable def localizedPointwiseUpperDeviationBadEventMass
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι) (η : ℝ) : ℝ :=
  ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
    η < finiteExcessRisk p ℓ iStar i - empiricalExcessRisk ℓ iStar i z),
    sampleWeight z

/-- Finite weighted mass of the one-hypothesis upper-deviation bad event with
a sample-dependent threshold. -/
noncomputable def localizedPointwiseSampleDependentUpperDeviationBadEventMass
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    (η : (Fin n → Z) → ℝ) : ℝ :=
  ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
    η z < finiteExcessRisk p ℓ iStar i - empiricalExcessRisk ℓ iStar i z),
    sampleWeight z

/-- Finite weighted mass of samples outside the localized upper-deviation event. -/
noncomputable def localizedUpperDeviationBadEventMass
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : ℝ) : ℝ :=
  ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
    η < localizedUpperDeviation p ℓ iStar z P hP),
    sampleWeight z

/-- Finite weighted mass outside a sample-dependent localized
upper-deviation event. -/
noncomputable def localizedSampleDependentUpperDeviationBadEventMass
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) : ℝ :=
  ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
    η z < localizedUpperDeviation p ℓ iStar z P hP),
    sampleWeight z

/-- Finite weighted mass outside the fast-rate random-threshold localized
upper-deviation event. -/
noncomputable def localizedFastRateUpperDeviationBadEventMass
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (r : ℝ) (hr : 0 ≤ r) (ε : ℝ)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j) : ℝ :=
  localizedSampleDependentUpperDeviationBadEventMass sampleWeight p ℓ iStar
    (LocalizedByExcessRisk p ℓ iStar r) hP
    (fun z : Fin n → Z =>
      2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr + ε)

/-- Finite weighted exponential moment for one localized upper-deviation gap. -/
noncomputable def localizedPointwiseUpperDeviationExpMoment
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι) (lam : ℝ) : ℝ :=
  ∑ z : Fin n → Z,
    sampleWeight z *
      Real.exp (lam * (finiteExcessRisk p ℓ iStar i -
        empiricalExcessRisk ℓ iStar i z))

/-- Shifted exponential moment for one localized upper-deviation gap with a
sample-dependent threshold. -/
noncomputable def localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    (η : (Fin n → Z) → ℝ) (lam : ℝ) : ℝ :=
  ∑ z : Fin n → Z,
    sampleWeight z *
      Real.exp (lam * ((finiteExcessRisk p ℓ iStar i -
        empiricalExcessRisk ℓ iStar i z) - η z))

@[simp] theorem mem_localizedUpperDeviationEvent_iff
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι}
    {P : ι → Prop} [DecidablePred P] {hP : ∃ i : ι, P i}
    {η : ℝ} {z : Fin n → Z} :
    z ∈ localizedUpperDeviationEvent p ℓ iStar P hP η ↔
      localizedUpperDeviation p ℓ iStar z P hP ≤ η :=
  Iff.rfl

@[simp] theorem mem_localizedSampleDependentUpperDeviationEvent_iff
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι}
    {P : ι → Prop} [DecidablePred P] {hP : ∃ i : ι, P i}
    {η : (Fin n → Z) → ℝ} {z : Fin n → Z} :
    z ∈ localizedSampleDependentUpperDeviationEvent p ℓ iStar P hP η ↔
      localizedUpperDeviation p ℓ iStar z P hP ≤ η z :=
  Iff.rfl

/-- Pointwise Markov adapter from an exponential-moment budget to a one-sided
upper-deviation bad-event mass. -/
theorem localizedPointwiseUpperDeviationBadEventMass_le_expMoment_div
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    {lam η C : ℝ}
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hmoment :
      localizedPointwiseUpperDeviationExpMoment
        sampleWeight p ℓ iStar i lam ≤ C) :
    localizedPointwiseUpperDeviationBadEventMass
        sampleWeight p ℓ iStar i η ≤ C / Real.exp (lam * η) := by
  classical
  let gap : (Fin n → Z) → ℝ := fun z =>
    finiteExcessRisk p ℓ iStar i - empiricalExcessRisk ℓ iStar i z
  let x : (Fin n → Z) → ℝ := fun z => Real.exp (lam * gap z)
  let threshold : ℝ := Real.exp (lam * η)
  have hthreshold_pos : 0 < threshold := by
    simpa [threshold] using Real.exp_pos (lam * η)
  have hmarkov :=
    FormalSLT.Probability.Concentration.markovInequalityFiniteWeighted_proof
      (s := (Finset.univ : Finset (Fin n → Z)))
      (w := sampleWeight)
      (x := x)
      (t := threshold)
      hweight
      (fun z : Fin n → Z => le_of_lt (Real.exp_pos (lam * gap z)))
      hthreshold_pos
  unfold FormalSLT.Probability.Concentration.upperTailMass at hmarkov
  unfold FormalSLT.Probability.Concentration.weightedMean at hmarkov
  have hsubset :
      (Finset.univ.filter fun z : Fin n → Z => η < gap z) ⊆
        (Finset.univ.filter fun z : Fin n → Z => threshold ≤ x z) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    have hmul : lam * η ≤ lam * gap z :=
      mul_le_mul_of_nonneg_left (le_of_lt hz.2) (le_of_lt hlam)
    exact Real.exp_le_exp.mpr hmul
  have hmass_subset :
      localizedPointwiseUpperDeviationBadEventMass sampleWeight p ℓ iStar i η ≤
        ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z => threshold ≤ x z),
          sampleWeight z := by
    unfold localizedPointwiseUpperDeviationBadEventMass
    change
      (∑ z ∈ (Finset.univ.filter fun z : Fin n → Z => η < gap z), sampleWeight z) ≤
        ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z => threshold ≤ x z),
          sampleWeight z
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro z _hz _hnot
      exact hweight z)
  have hmarkov' :
      (∑ z ∈ (Finset.univ.filter fun z : Fin n → Z => threshold ≤ x z),
          sampleWeight z) ≤
        localizedPointwiseUpperDeviationExpMoment
          sampleWeight p ℓ iStar i lam / threshold := by
    simpa [localizedPointwiseUpperDeviationExpMoment, gap, x, threshold] using hmarkov
  have hdiv :
      localizedPointwiseUpperDeviationExpMoment
          sampleWeight p ℓ iStar i lam / threshold ≤
        C / threshold :=
    div_le_div_of_nonneg_right hmoment (le_of_lt hthreshold_pos)
  simpa [threshold] using hmass_subset.trans (hmarkov'.trans hdiv)

/-- Finite iid product MGF bridge for one localized upper-deviation gap.

This reuses the generic finite product MGF theorem with the excess-loss class
`j ↦ excessLoss ℓ iStar j`. The caller still supplies the one-coordinate MGF
budget; boundedness/sub-Gaussian/Bernstein instantiations remain separate. -/
theorem localizedPointwiseUpperDeviationExpMoment_finiteProduct_le_of_single
    [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar i : ι) (lam variance : ℝ)
    (hsingle :
      FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
        (n := n) p (fun j z => excessLoss ℓ iStar j z) i lam ≤
        Real.exp (lam ^ 2 * variance / (2 * (n : ℝ) ^ 2))) :
    localizedPointwiseUpperDeviationExpMoment
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar i lam ≤
      Real.exp (lam ^ 2 * variance / (2 * (n : ℝ))) := by
  simpa [localizedPointwiseUpperDeviationExpMoment,
    FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk,
    FormalSLT.PACBayesFiniteProductMGF.finiteEmpiricalRisk,
    finiteExcessRisk, finiteMean, empiricalExcessRisk, empiricalMean] using
      FormalSLT.PACBayesFiniteProductMGF.finiteProduct_mgf_empiricalRiskDeviation_le_of_single
        (ι := ι) (Z := Z) hn p hp
        (fun j z => excessLoss ℓ iStar j z) i lam variance hsingle

/-- One-coordinate MGF budget for bounded excess losses.

If the excess loss for one hypothesis lies in `[-1,1]`, rescale it to
`(excess + 1) / 2` and reuse the existing `[0,1]` bounded-loss MGF lemma.
The resulting Hoeffding budget has variance proxy `1`. -/
theorem localizedOneCoordinateDeviationMGF_le_of_excessLoss_mem_Icc_neg_one_one
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar i : ι) (lam : ℝ)
    (hbound : ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i z ∧ excessLoss ℓ iStar i z ≤ 1) :
    FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
        (n := n) p (fun j z => excessLoss ℓ iStar j z) i lam ≤
      Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ) ^ 2)) := by
  classical
  let ℓ01 : ι → Z → ℝ := fun j z => (excessLoss ℓ iStar j z + 1) / 2
  have hℓ01 : ∀ z : Z, 0 ≤ ℓ01 i z ∧ ℓ01 i z ≤ 1 := by
    intro z
    have hz := hbound z
    constructor <;> dsimp [ℓ01]
    · linarith
    · linarith
  have hpop01 :
      FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk p ℓ01 i =
        (finiteExcessRisk p ℓ iStar i + 1) / 2 := by
    unfold FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk
      finiteExcessRisk finiteMean
    dsimp [ℓ01]
    calc
      (∑ z : Z, p z * ((excessLoss ℓ iStar i z + 1) / 2))
          =
        (∑ z : Z, ((p z * excessLoss ℓ iStar i z) / 2 + p z / 2)) := by
          refine Finset.sum_congr rfl (fun z _hz => ?_)
          ring_nf
      _ =
        (∑ z : Z, (p z * excessLoss ℓ iStar i z) / 2) +
          ∑ z : Z, p z / 2 := by
          rw [Finset.sum_add_distrib]
      _ =
        (∑ z : Z, p z * excessLoss ℓ iStar i z) / 2 +
          (∑ z : Z, p z) / 2 := by
          rw [Finset.sum_div, Finset.sum_div]
      _ =
        ((∑ z : Z, p z * excessLoss ℓ iStar i z) + 1) / 2 := by
          rw [hp.sum_one]
          ring_nf
  have hmgf_eq :
      FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
          (n := n) p ℓ01 i (2 * lam) =
        FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
          (n := n) p (fun j z => excessLoss ℓ iStar j z) i lam := by
    unfold FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
    refine Finset.sum_congr rfl (fun z _hz => ?_)
    rw [hpop01]
    have hpop_excess :
        FormalSLT.PACBayesFiniteProductMGF.finitePopulationRisk
            p (fun j z => excessLoss ℓ iStar j z) i =
          finiteExcessRisk p ℓ iStar i := by
      rfl
    rw [hpop_excess]
    dsimp [ℓ01]
    congr 1
    ring_nf
  have hbounded :=
    FormalSLT.PACBayesBoundedLoss.oneCoordinate_boundedLoss_mgf
      (ι := ι) (Z := Z) hn p hp ℓ01 i (2 * lam) hℓ01
  calc
    FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
        (n := n) p (fun j z => excessLoss ℓ iStar j z) i lam
        =
      FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
        (n := n) p ℓ01 i (2 * lam) := hmgf_eq.symm
    _ ≤ Real.exp ((2 * lam) ^ 2 / (8 * (n : ℝ) ^ 2)) := hbounded
    _ = Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ) ^ 2)) := by
      congr 1
      ring_nf

/-- Finite weighted union bound for the localized upper-deviation bad event.

The probabilistic content is deliberately external: callers supply the finite
sample weights and later instantiate the pointwise bad-event masses from a
one-hypothesis concentration theorem. -/
theorem localizedUpperDeviationBadEventMass_le_sum_pointwise
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z) :
    localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i},
        localizedPointwiseUpperDeviationBadEventMass
          sampleWeight p ℓ iStar i.1 η := by
  classical
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  let pointwiseEvent : {i : ι // P i} → Finset (Fin n → Z) := fun i =>
    Finset.univ.filter fun z : Fin n → Z =>
      η < finiteExcessRisk p ℓ iStar i.1 - empiricalExcessRisk ℓ iStar i.1 z
  let unionEvent : Finset (Fin n → Z) :=
    Finset.univ.filter fun z : Fin n → Z =>
      ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i
  have hsubset :
      (Finset.univ.filter fun z : Fin n → Z =>
        η < localizedUpperDeviation p ℓ iStar z P hP) ⊆ unionEvent := by
    intro z hz
    rw [Finset.mem_filter] at hz
    change z ∈ (Finset.univ.filter fun z : Fin n → Z =>
      ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    have hexists :
        ∃ i ∈ (Finset.univ : Finset {i : ι // P i}),
          η < finiteExcessRisk p ℓ iStar i.1 -
            empiricalExcessRisk ℓ iStar i.1 z := by
      simpa [localizedUpperDeviation] using
        (Finset.lt_sup'_iff
          (s := (Finset.univ : Finset {i : ι // P i}))
          (H := Finset.univ_nonempty)
          (f := fun i : {i : ι // P i} =>
            finiteExcessRisk p ℓ iStar i.1 -
              empiricalExcessRisk ℓ iStar i.1 z)).mp hz.2
    rcases hexists with ⟨i, _hi, hi⟩
    refine ⟨i, ?_⟩
    change z ∈ (Finset.univ.filter fun z : Fin n → Z =>
      η < finiteExcessRisk p ℓ iStar i.1 - empiricalExcessRisk ℓ iStar i.1 z)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hi⟩
  have hmass_subset :
      localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η ≤
        ∑ z ∈ unionEvent, sampleWeight z := by
    unfold localizedUpperDeviationBadEventMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro z _hz _hnot
      exact hweight z)
  have hunion :=
    FormalSLT.Probability.FiniteUnionBound.finiteProbabilityUnionBound_proof
      (support := (Finset.univ : Finset (Fin n → Z)))
      (w := sampleWeight)
      (events := pointwiseEvent)
      (s := (Finset.univ : Finset {i : ι // P i}))
      hweight
  have hunion_mass :
      (∑ z ∈ unionEvent, sampleWeight z) ≤
        ∑ i : {i : ι // P i},
          localizedPointwiseUpperDeviationBadEventMass
            sampleWeight p ℓ iStar i.1 η := by
    change
      (∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
          ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i),
          sampleWeight z) ≤
        ∑ i : {i : ι // P i},
          ∑ z ∈ pointwiseEvent i, sampleWeight z
    unfold FormalSLT.Probability.FiniteUnionBound.finiteUnionEventMass at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMassSum at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMass at hunion
    simp_rw [← Finset.sum_filter] at hunion
    simpa [localizedPointwiseUpperDeviationBadEventMass, pointwiseEvent] using hunion
  exact hmass_subset.trans hunion_mass

/-- Localized upper-deviation bad-event mass controlled by supplied pointwise
tail budgets. -/
theorem localizedUpperDeviationBadEventMass_le_sum_tails
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : ℝ) (pointwiseTail : {i : ι // P i} → ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (htail : ∀ i : {i : ι // P i},
      localizedPointwiseUpperDeviationBadEventMass
        sampleWeight p ℓ iStar i.1 η ≤ pointwiseTail i) :
    localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i}, pointwiseTail i := by
  exact (localizedUpperDeviationBadEventMass_le_sum_pointwise
    sampleWeight p ℓ iStar P hP η hweight).trans
      (Finset.sum_le_sum (fun i _hi => htail i))

/-- Localized bad-event mass controlled by pointwise exponential-moment budgets. -/
theorem localizedUpperDeviationBadEventMass_le_sum_expMoment_div
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    {lam η : ℝ} (momentBudget : {i : ι // P i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hmoment : ∀ i : {i : ι // P i},
      localizedPointwiseUpperDeviationExpMoment
        sampleWeight p ℓ iStar i.1 lam ≤ momentBudget i) :
    localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i}, momentBudget i / Real.exp (lam * η) := by
  exact localizedUpperDeviationBadEventMass_le_sum_tails
    sampleWeight p ℓ iStar P hP η
    (fun i : {i : ι // P i} => momentBudget i / Real.exp (lam * η))
    hweight
    (fun i =>
      localizedPointwiseUpperDeviationBadEventMass_le_expMoment_div
        sampleWeight p ℓ iStar i.1 hlam hweight (hmoment i))

/-- Pointwise sample-dependent bad-event mass controlled by a shifted
exponential moment.

The threshold is already inside the exponential moment, so no fixed-threshold
division term appears. -/
theorem localizedPointwiseSampleDependentUpperDeviationBadEventMass_le_shiftedExpMoment
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    (η : (Fin n → Z) → ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z) :
    localizedPointwiseSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar i η ≤
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i η lam := by
  classical
  unfold localizedPointwiseSampleDependentUpperDeviationBadEventMass
  unfold localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
  have hfilter_le :
      (∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
          η z < finiteExcessRisk p ℓ iStar i -
            empiricalExcessRisk ℓ iStar i z),
          sampleWeight z) ≤
        ∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
          η z < finiteExcessRisk p ℓ iStar i -
            empiricalExcessRisk ℓ iStar i z),
          sampleWeight z *
            Real.exp (lam * ((finiteExcessRisk p ℓ iStar i -
              empiricalExcessRisk ℓ iStar i z) - η z)) := by
    refine Finset.sum_le_sum ?_
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hdiff :
        0 ≤ (finiteExcessRisk p ℓ iStar i -
          empiricalExcessRisk ℓ iStar i z) - η z := by
      linarith
    have hexp :
        1 ≤ Real.exp (lam * ((finiteExcessRisk p ℓ iStar i -
          empiricalExcessRisk ℓ iStar i z) - η z)) := by
      rw [Real.one_le_exp_iff]
      exact mul_nonneg (le_of_lt hlam) hdiff
    calc
      sampleWeight z = sampleWeight z * 1 := by ring
      _ ≤ sampleWeight z *
          Real.exp (lam * ((finiteExcessRisk p ℓ iStar i -
            empiricalExcessRisk ℓ iStar i z) - η z)) :=
        mul_le_mul_of_nonneg_left hexp (hweight z)
  have hsubset :
      (Finset.univ.filter fun z : Fin n → Z =>
          η z < finiteExcessRisk p ℓ iStar i -
            empiricalExcessRisk ℓ iStar i z) ⊆
        (Finset.univ : Finset (Fin n → Z)) := by
    intro z _hz
    exact Finset.mem_univ z
  have htail_nonneg :
      ∀ z ∈ (Finset.univ : Finset (Fin n → Z)),
        z ∉ (Finset.univ.filter fun z : Fin n → Z =>
          η z < finiteExcessRisk p ℓ iStar i -
            empiricalExcessRisk ℓ iStar i z) →
          0 ≤ sampleWeight z *
            Real.exp (lam * ((finiteExcessRisk p ℓ iStar i -
              empiricalExcessRisk ℓ iStar i z) - η z)) := by
    intro z _hz _hnot
    exact mul_nonneg (hweight z) (le_of_lt (Real.exp_pos _))
  exact hfilter_le.trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset htail_nonneg)

/-- A sample-dependent shifted moment is controlled by the fixed-threshold
exponential moment whenever the sample-dependent threshold is pointwise at
least the fixed threshold. -/
theorem localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_le_fixedExpMoment_div
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    (η : (Fin n → Z) → ℝ) {η0 lam : ℝ}
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hlower : ∀ z : Fin n → Z, η0 ≤ η z) :
    localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i η lam ≤
      localizedPointwiseUpperDeviationExpMoment
        sampleWeight p ℓ iStar i lam / Real.exp (lam * η0) := by
  classical
  unfold localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
  unfold localizedPointwiseUpperDeviationExpMoment
  rw [Finset.sum_div]
  refine Finset.sum_le_sum ?_
  intro z _hz
  set gap := finiteExcessRisk p ℓ iStar i -
    empiricalExcessRisk ℓ iStar i z
  have harg :
      lam * (gap - η z) ≤ lam * gap - lam * η0 := by
    have hmul := mul_le_mul_of_nonneg_left (hlower z) (le_of_lt hlam)
    linarith
  have hexp :
      Real.exp (lam * (gap - η z)) ≤
        Real.exp (lam * gap) / Real.exp (lam * η0) := by
    calc
      Real.exp (lam * (gap - η z))
          ≤ Real.exp (lam * gap - lam * η0) := Real.exp_le_exp.mpr harg
      _ = Real.exp (lam * gap) / Real.exp (lam * η0) := by
        rw [Real.exp_sub]
  have hterm := mul_le_mul_of_nonneg_left hexp (hweight z)
  simpa [div_eq_mul_inv, mul_assoc] using hterm

/-- Adding a fixed slack to a sample-dependent threshold factors out of the
shifted exponential moment.

This keeps the genuinely sample-dependent part of the threshold inside the
moment and isolates only the fixed slack as an exponential denominator.

CAVEAT. This is a purely algebraic identity (`exp(λ(g - (η + η₀))) =
exp(λ(g - η)) / exp(λη₀)`); it adds no probabilistic content. See
`localizedFastRatePointwiseShiftedExpMoment_le_centered_div` for the discussion
of why the resulting per-hypothesis "centered" moment cannot, by itself, beat
the conservative fixed-threshold bound. -/
theorem localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_add_const
    [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar i : ι)
    (η : (Fin n → Z) → ℝ) (η0 lam : ℝ) :
    localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i (fun z : Fin n → Z => η z + η0) lam =
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i η lam / Real.exp (lam * η0) := by
  classical
  unfold localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro z _hz
  set gap := finiteExcessRisk p ℓ iStar i -
    empiricalExcessRisk ℓ iStar i z
  have harg :
      lam * (gap - (η z + η0)) = lam * (gap - η z) - lam * η0 := by
    ring
  calc
    sampleWeight z * Real.exp (lam * (gap - (η z + η0)))
        = sampleWeight z *
            (Real.exp (lam * (gap - η z)) / Real.exp (lam * η0)) := by
          rw [harg, Real.exp_sub]
    _ = sampleWeight z * Real.exp (lam * (gap - η z)) /
          Real.exp (lam * η0) := by
          ring

/-- Finite weighted union bound for sample-dependent localized
upper-deviation bad events. -/
theorem localizedSampleDependentUpperDeviationBadEventMass_le_sum_pointwise
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i},
        localizedPointwiseSampleDependentUpperDeviationBadEventMass
          sampleWeight p ℓ iStar i.1 η := by
  classical
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  let pointwiseEvent : {i : ι // P i} → Finset (Fin n → Z) := fun i =>
    Finset.univ.filter fun z : Fin n → Z =>
      η z < finiteExcessRisk p ℓ iStar i.1 -
        empiricalExcessRisk ℓ iStar i.1 z
  let unionEvent : Finset (Fin n → Z) :=
    Finset.univ.filter fun z : Fin n → Z =>
      ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i
  have hsubset :
      (Finset.univ.filter fun z : Fin n → Z =>
        η z < localizedUpperDeviation p ℓ iStar z P hP) ⊆ unionEvent := by
    intro z hz
    rw [Finset.mem_filter] at hz
    change z ∈ (Finset.univ.filter fun z : Fin n → Z =>
      ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    have hexists :
        ∃ i ∈ (Finset.univ : Finset {i : ι // P i}),
          η z < finiteExcessRisk p ℓ iStar i.1 -
            empiricalExcessRisk ℓ iStar i.1 z := by
      simpa [localizedUpperDeviation] using
        (Finset.lt_sup'_iff
          (s := (Finset.univ : Finset {i : ι // P i}))
          (H := Finset.univ_nonempty)
          (f := fun i : {i : ι // P i} =>
            finiteExcessRisk p ℓ iStar i.1 -
              empiricalExcessRisk ℓ iStar i.1 z)).mp hz.2
    rcases hexists with ⟨i, _hi, hi⟩
    refine ⟨i, ?_⟩
    change z ∈ (Finset.univ.filter fun z : Fin n → Z =>
      η z < finiteExcessRisk p ℓ iStar i.1 -
        empiricalExcessRisk ℓ iStar i.1 z)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hi⟩
  have hmass_subset :
      localizedSampleDependentUpperDeviationBadEventMass
          sampleWeight p ℓ iStar P hP η ≤
        ∑ z ∈ unionEvent, sampleWeight z := by
    unfold localizedSampleDependentUpperDeviationBadEventMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro z _hz _hnot
      exact hweight z)
  have hunion :=
    FormalSLT.Probability.FiniteUnionBound.finiteProbabilityUnionBound_proof
      (support := (Finset.univ : Finset (Fin n → Z)))
      (w := sampleWeight)
      (events := pointwiseEvent)
      (s := (Finset.univ : Finset {i : ι // P i}))
      hweight
  have hunion_mass :
      (∑ z ∈ unionEvent, sampleWeight z) ≤
        ∑ i : {i : ι // P i},
          localizedPointwiseSampleDependentUpperDeviationBadEventMass
            sampleWeight p ℓ iStar i.1 η := by
    change
      (∑ z ∈ (Finset.univ.filter fun z : Fin n → Z =>
          ∃ i : {i : ι // P i}, z ∈ pointwiseEvent i),
          sampleWeight z) ≤
        ∑ i : {i : ι // P i},
          ∑ z ∈ pointwiseEvent i, sampleWeight z
    unfold FormalSLT.Probability.FiniteUnionBound.finiteUnionEventMass at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMassSum at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMass at hunion
    simp_rw [← Finset.sum_filter] at hunion
    simpa [localizedPointwiseSampleDependentUpperDeviationBadEventMass,
      pointwiseEvent] using hunion
  exact hmass_subset.trans hunion_mass

/-- Sample-dependent localized bad-event mass controlled by supplied
pointwise tail budgets. -/
theorem localizedSampleDependentUpperDeviationBadEventMass_le_sum_tails
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) (pointwiseTail : {i : ι // P i} → ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (htail : ∀ i : {i : ι // P i},
      localizedPointwiseSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar i.1 η ≤ pointwiseTail i) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i}, pointwiseTail i := by
  exact (localizedSampleDependentUpperDeviationBadEventMass_le_sum_pointwise
    sampleWeight p ℓ iStar P hP η hweight).trans
      (Finset.sum_le_sum (fun i _hi => htail i))

/-- Sample-dependent localized bad-event mass controlled by shifted
exponential-moment budgets. -/
theorem localizedSampleDependentUpperDeviationBadEventMass_le_sum_shiftedExpMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) {lam : ℝ}
    (momentBudget : {i : ι // P i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hmoment : ∀ i : {i : ι // P i},
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i.1 η lam ≤ momentBudget i) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i}, momentBudget i := by
  exact localizedSampleDependentUpperDeviationBadEventMass_le_sum_tails
    sampleWeight p ℓ iStar P hP η momentBudget hweight
    (fun i =>
      (localizedPointwiseSampleDependentUpperDeviationBadEventMass_le_shiftedExpMoment
        sampleWeight p ℓ iStar i.1 η hlam hweight).trans (hmoment i))

/-- Iid product-weight localized bad-event mass controlled by one-coordinate
MGF budgets.

This composes the finite union/Markov adapter above with the finite product MGF
bridge. It is still assumption-facing: the caller supplies one-coordinate MGF
budgets for each member of the localized finite subtype. -/
theorem localizedUpperDeviationBadEventMass_finiteProduct_le_sum_singleMGF
    [Fintype ι] [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    {lam η : ℝ} (variance : {i : ι // P i} → ℝ)
    (hlam : 0 < lam)
    (hsingle : ∀ i : {i : ι // P i},
      FormalSLT.PACBayesFiniteProductMGF.oneCoordinateDeviationMGF
        (n := n) p (fun j z => excessLoss ℓ iStar j z) i.1 lam ≤
        Real.exp (lam ^ 2 * variance i / (2 * (n : ℝ) ^ 2))) :
    localizedUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar P hP η ≤
      ∑ i : {i : ι // P i},
        Real.exp (lam ^ 2 * variance i / (2 * (n : ℝ))) /
          Real.exp (lam * η) := by
  classical
  exact localizedUpperDeviationBadEventMass_le_sum_expMoment_div
    (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
    p ℓ iStar P hP
    (fun i : {i : ι // P i} =>
      Real.exp (lam ^ 2 * variance i / (2 * (n : ℝ))))
    hlam
    (fun z : Fin n → Z => by
      unfold FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
      exact Finset.prod_nonneg (fun k _hk => hp.nonneg (z k)))
    (fun i : {i : ι // P i} =>
      localizedPointwiseUpperDeviationExpMoment_finiteProduct_le_of_single
        (ι := ι) hn p hp ℓ iStar i.1 lam (variance i) (hsingle i))

/-- Iid product-weight localized bad-event mass under bounded excess losses.

This is the first concrete MGF instantiation for the localized upper-deviation
event layer. It remains finite and pointwise: each member of the localized
subtype supplies a `[-1,1]` excess-loss bound. -/
theorem localizedUpperDeviationBadEventMass_finiteProduct_le_sum_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    {lam η : ℝ} (hlam : 0 < lam)
    (hbound : ∀ i : {i : ι // P i}, ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
        excessLoss ℓ iStar i.1 z ≤ 1) :
    localizedUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar P hP η ≤
      ∑ _i : {i : ι // P i},
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
          Real.exp (lam * η) := by
  exact localizedUpperDeviationBadEventMass_finiteProduct_le_sum_singleMGF
    (ι := ι) hn p hp ℓ iStar P hP
    (fun _i : {i : ι // P i} => (1 : ℝ))
    hlam
    (fun i : {i : ι // P i} =>
      localizedOneCoordinateDeviationMGF_le_of_excessLoss_mem_Icc_neg_one_one
        hn p hp ℓ iStar i.1 lam (hbound i))

/-- Delta-form iid product-weight localized concentration under bounded
excess losses.

This closes the fixed-threshold finite concentration statement: if the summed
bounded-excess tail budget is at most `δ`, then the samples outside the
localized upper-deviation event have finite product mass at most `δ`. -/
theorem localizedUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    {lam η δ : ℝ} (hlam : 0 < lam)
    (hbound : ∀ i : {i : ι // P i}, ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
        excessLoss ℓ iStar i.1 z ≤ 1)
    (htail_sum :
      (∑ _i : {i : ι // P i},
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
          Real.exp (lam * η)) ≤ δ) :
    localizedUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar P hP η ≤ δ :=
  (localizedUpperDeviationBadEventMass_finiteProduct_le_sum_boundedExcess
    (ι := ι) hn p hp ℓ iStar P hP hlam hbound).trans htail_sum

/-- Delta-form localized concentration adapter for finite localized classes. -/
theorem localizedUpperDeviationBadEventMass_le_delta
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η δ : ℝ) (pointwiseTail : {i : ι // P i} → ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (htail : ∀ i : {i : ι // P i},
      localizedPointwiseUpperDeviationBadEventMass
        sampleWeight p ℓ iStar i.1 η ≤ pointwiseTail i)
    (htail_sum : (∑ i : {i : ι // P i}, pointwiseTail i) ≤ δ) :
    localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η ≤ δ :=
  (localizedUpperDeviationBadEventMass_le_sum_tails
    sampleWeight p ℓ iStar P hP η pointwiseTail hweight htail).trans
      htail_sum

/-- A sample-dependent bad event is contained in a fixed-threshold bad event
whenever the random threshold is pointwise at least the fixed threshold. -/
theorem localizedSampleDependentUpperDeviationBadEventMass_le_fixed
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) (η0 : ℝ)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hlower : ∀ z : Fin n → Z, η0 ≤ η z) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤
      localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar P hP η0 := by
  classical
  unfold localizedSampleDependentUpperDeviationBadEventMass
  unfold localizedUpperDeviationBadEventMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact lt_of_le_of_lt (hlower z) hz
  · intro z _hfixed _hnot
    exact hweight z

/-- The named fast-rate random-threshold bad-event mass is bounded by the
fixed-`ε` bad-event mass.

This is a conservative bridge: it uses only nonnegativity of the empirical
localized Rademacher term, not a sharp random-threshold concentration
inequality. -/
theorem localizedFastRateUpperDeviationBadEventMass_le_fixed_epsilon
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z) :
    localizedFastRateUpperDeviationBadEventMass
        sampleWeight p ℓ iStar r hr ε hP ≤
      localizedUpperDeviationBadEventMass sampleWeight p ℓ iStar
        (LocalizedByExcessRisk p ℓ iStar r) hP ε := by
  unfold localizedFastRateUpperDeviationBadEventMass
  refine localizedSampleDependentUpperDeviationBadEventMass_le_fixed
    sampleWeight p ℓ iStar (LocalizedByExcessRisk p ℓ iStar r) hP
    (fun z : Fin n → Z =>
      2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr + ε)
    ε hweight ?_
  intro z
  have hrad :
      0 ≤ localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr :=
    localizedExcessRiskEmpiricalRademacherComplexity_nonneg
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z) (r := r) hr
  have hterm :
      0 ≤ 2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr :=
    mul_nonneg (by norm_num) hrad
  linarith

/-- Conservative finite product-mass bound for the named fast-rate localized
bad event.

The random threshold is lower-bounded by `ε`, so the existing fixed-threshold
bounded-excess concentration theorem controls this bad event. This is not the
sharp localized random-threshold theorem, but it gives a closed finite
high-confidence statement for the named fast-rate event. -/
theorem localizedFastRateUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε lam δ : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (hlam : 0 < lam)
    (hbound : ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
      ∀ z : Z,
        (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
          excessLoss ℓ iStar i.1 z ≤ 1)
    (htail_sum :
      (∑ _i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
          Real.exp (lam * ε)) ≤ δ) :
    localizedFastRateUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar r hr ε hP ≤ δ := by
  have hfast_le_fixed :
      localizedFastRateUpperDeviationBadEventMass
          (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
          p ℓ iStar r hr ε hP ≤
        localizedUpperDeviationBadEventMass
          (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
          p ℓ iStar (LocalizedByExcessRisk p ℓ iStar r) hP ε :=
    localizedFastRateUpperDeviationBadEventMass_le_fixed_epsilon
      (sampleWeight :=
        FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
      (p := p) (ℓ := ℓ) (iStar := iStar) (r := r) (ε := ε)
      hr hP
      (by
        intro z
        unfold FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
        exact Finset.prod_nonneg (fun k _hk => hp.nonneg (z k)))
  exact hfast_le_fixed.trans
    (localizedUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess
      (ι := ι) hn p hp ℓ iStar
      (LocalizedByExcessRisk p ℓ iStar r) hP
      (lam := lam) (η := ε) (δ := δ)
      hlam hbound htail_sum)

/-- A deviation certificate for a larger predicate restricts to a smaller
predicate. -/
theorem localizedDeviationCertificate_mono [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι}
    {z : Fin n → Z} {P Q : ι → Prop} {η : ℝ}
    (hdev : LocalizedDeviationCertificate p ℓ iStar z Q η)
    (hPQ : ∀ i : ι, P i → Q i) :
    LocalizedDeviationCertificate p ℓ iStar z P η := by
  intro i hi
  exact hdev i (hPQ i hi)

/-- A bound on the localized upper-deviation statistic constructs the
corresponding localized deviation certificate. -/
theorem localizedDeviationCertificate_of_upperDeviation_le
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι}
    {z : Fin n → Z} {P : ι → Prop} [DecidablePred P]
    {hP : ∃ i : ι, P i} {η : ℝ}
    (hupper : localizedUpperDeviation p ℓ iStar z P hP ≤ η) :
    LocalizedDeviationCertificate p ℓ iStar z P η := by
  classical
  letI : Nonempty {i : ι // P i} :=
    ⟨⟨Classical.choose hP, Classical.choose_spec hP⟩⟩
  intro i hi
  have hgap_le :
      finiteExcessRisk p ℓ iStar i - empiricalExcessRisk ℓ iStar i z ≤
        localizedUpperDeviation p ℓ iStar z P hP := by
    have hsup :=
      Finset.le_sup'
        (s := (Finset.univ : Finset {i : ι // P i}))
        (f := fun j : {i : ι // P i} =>
          finiteExcessRisk p ℓ iStar j.1 -
            empiricalExcessRisk ℓ iStar j.1 z)
        (Finset.mem_univ (⟨i, hi⟩ : {i : ι // P i}))
    simpa [localizedUpperDeviation] using hsup
  linarith

/-- Membership in the localized upper-deviation event yields the deterministic
certificate used by the fast-rate shell. -/
theorem localizedDeviationCertificate_of_mem_upperDeviationEvent
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar : ι}
    {P : ι → Prop} [DecidablePred P] {hP : ∃ i : ι, P i}
    {η : ℝ} {z : Fin n → Z}
    (hz : z ∈ localizedUpperDeviationEvent p ℓ iStar P hP η) :
    LocalizedDeviationCertificate p ℓ iStar z P η :=
  localizedDeviationCertificate_of_upperDeviation_le
    (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
    (P := P) (hP := hP) (η := η) hz

/-- On a localized deviation event, a hypothesis whose empirical excess risk
is nonpositive has population excess risk controlled by the deviation slack. -/
theorem finiteExcessRisk_le_of_localizedDeviation_empirical_nonpos [Fintype Z]
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar i : ι} {n : ℕ}
    {z : Fin n → Z} {P : ι → Prop} {η : ℝ}
    (hdev : LocalizedDeviationCertificate p ℓ iStar z P η)
    (hi : P i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0) :
    finiteExcessRisk p ℓ iStar i ≤ η := by
  have h := hdev i hi
  linarith

/-- Fixed-threshold localized event payoff for empirical competitors.

On the localized upper-deviation event at threshold `η`, any localized
hypothesis with nonpositive empirical excess risk has population excess risk at
most `η`. This is the deterministic payoff paired with the fixed-threshold
finite concentration bounds above. -/
theorem finiteExcessRisk_le_of_localizedUpperDeviationEvent_empirical_nonpos
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar i : ι}
    {P : ι → Prop} [DecidablePred P] {hP : ∃ j : ι, P j}
    {η : ℝ} {z : Fin n → Z}
    (hz : z ∈ localizedUpperDeviationEvent p ℓ iStar P hP η)
    (hi : P i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0) :
    finiteExcessRisk p ℓ iStar i ≤ η :=
  finiteExcessRisk_le_of_localizedDeviation_empirical_nonpos
    (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
    (z := z) (P := P) (η := η)
    (localizedDeviationCertificate_of_mem_upperDeviationEvent
      (p := p) (ℓ := ℓ) (iStar := iStar) (P := P)
      (hP := hP) (η := η) hz)
    hi hemp

/-- Fixed-threshold high-confidence finite-class localized statement under
bounded excess losses.

This packages the two finite ingredients above. The first conjunct bounds the
finite product mass of samples outside the localized upper-deviation event.
The second conjunct records the payoff on the event: any localized empirical
competitor with nonpositive empirical excess risk has population excess risk
at most the fixed threshold `η`.

This is intentionally a fixed-threshold theorem. It does not yet control the
sample-dependent threshold used by the localized fast-rate shell below. -/
theorem localizedFiniteClassHighConfidence_empirical_nonpos_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    {lam η δ : ℝ} (hlam : 0 < lam)
    (hbound : ∀ i : {i : ι // P i}, ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
        excessLoss ℓ iStar i.1 z ≤ 1)
    (htail_sum :
      (∑ _i : {i : ι // P i},
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
          Real.exp (lam * η)) ≤ δ) :
    localizedUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar P hP η ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedUpperDeviationEvent p ℓ iStar P hP η →
          P i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              finiteExcessRisk p ℓ iStar i ≤ η := by
  refine ⟨?_, ?_⟩
  · exact localizedUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess
      (ι := ι) hn p hp ℓ iStar P hP hlam hbound htail_sum
  · intro z i hz hi hemp
    exact finiteExcessRisk_le_of_localizedUpperDeviationEvent_empirical_nonpos
      (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
      (P := P) (hP := hP) (η := η) (z := z)
      hz hi hemp

/-- Sample-dependent localized event payoff for empirical competitors.

This is the deterministic part of a random-threshold theorem: if the sample
belongs to a sample-dependent localized upper-deviation event, the population
excess risk is bounded by that sample's slack. -/
theorem finiteExcessRisk_le_of_localizedSampleDependentUpperDeviationEvent_empirical_nonpos
    [Fintype ι] [Fintype Z] {n : ℕ}
    {p : Z → ℝ} {ℓ : ι → Z → ℝ} {iStar i : ι}
    {P : ι → Prop} [DecidablePred P] {hP : ∃ j : ι, P j}
    {η : (Fin n → Z) → ℝ} {z : Fin n → Z}
    (hz : z ∈ localizedSampleDependentUpperDeviationEvent p ℓ iStar P hP η)
    (hi : P i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0) :
    finiteExcessRisk p ℓ iStar i ≤ η z := by
  have hupper :
      localizedUpperDeviation p ℓ iStar z P hP ≤ η z := by
    simpa using hz
  exact finiteExcessRisk_le_of_localizedDeviation_empirical_nonpos
    (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
    (z := z) (P := P) (η := η z)
    (localizedDeviationCertificate_of_upperDeviation_le
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (P := P) (hP := hP) (η := η z) hupper)
    hi hemp

/-- Supplied-mass high-confidence adapter for sample-dependent localized
upper-deviation events.

The first conjunct is exactly the caller-supplied bad-event mass bound. The
second conjunct is the deterministic payoff on the sample-dependent good event.
This isolates the remaining probabilistic task as proving `hbad`. -/
theorem localizedSampleDependentHighConfidence_empirical_nonpos
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) (δ : ℝ)
    (hbad :
      localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤ δ) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedSampleDependentUpperDeviationEvent p ℓ iStar P hP η →
          P i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              finiteExcessRisk p ℓ iStar i ≤ η z := by
  refine ⟨hbad, ?_⟩
  intro z i hz hi hemp
  exact finiteExcessRisk_le_of_localizedSampleDependentUpperDeviationEvent_empirical_nonpos
    (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
    (P := P) (hP := hP) (η := η) (z := z)
    hz hi hemp

/-- Sample-dependent high-confidence adapter from shifted exponential-moment
budgets.

This composes the shifted-moment bad-event mass bound with the deterministic
sample-dependent payoff. The shifted moments are supplied by the caller; this
theorem only packages the finite union/Markov layer and the payoff. -/
theorem localizedSampleDependentHighConfidence_empirical_nonpos_of_shiftedExpMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (P : ι → Prop) [DecidablePred P] (hP : ∃ i : ι, P i)
    (η : (Fin n → Z) → ℝ) {lam δ : ℝ}
    (momentBudget : {i : ι // P i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hmoment : ∀ i : {i : ι // P i},
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i.1 η lam ≤ momentBudget i)
    (hmoment_sum : (∑ i : {i : ι // P i}, momentBudget i) ≤ δ) :
    localizedSampleDependentUpperDeviationBadEventMass
        sampleWeight p ℓ iStar P hP η ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedSampleDependentUpperDeviationEvent p ℓ iStar P hP η →
          P i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              finiteExcessRisk p ℓ iStar i ≤ η z := by
  refine localizedSampleDependentHighConfidence_empirical_nonpos
    sampleWeight p ℓ iStar P hP η δ ?_
  exact (localizedSampleDependentUpperDeviationBadEventMass_le_sum_shiftedExpMoment
    sampleWeight p ℓ iStar P hP η momentBudget hlam hweight hmoment).trans
      hmoment_sum

/-- Localized deviation plus Bernstein/fixed-point control gives a deterministic
finite fast-rate shell for any localized empirical competitor.

This is still not a probability theorem: the caller supplies the localized
deviation certificate. The statement cleanly exposes the future concentration
task as the construction of `hdev` with high probability. -/
theorem finiteExcessRisk_le_of_localizedDeviation_bernstein_fixedPoint
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {c r rStar ε : ℝ} {φ : ℝ → ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hdev :
      LocalizedDeviationCertificate p ℓ iStar z
        (LocalizedByExcessRisk p ℓ iStar r)
        (2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε))
    {i : ι}
    (hi : LocalizedByExcessRisk p ℓ iStar r i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0)
    (henvelope :
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r))
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r) :
    finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  have hslack :
      finiteExcessRisk p ℓ iStar i ≤
        2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε :=
    finiteExcessRisk_le_of_localizedDeviation_empirical_nonpos
      (p := p) (ℓ := ℓ) (iStar := iStar) (i := i)
      (z := z) (P := LocalizedByExcessRisk p ℓ iStar r)
      hdev hi hemp
  have hrad :
      localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr ≤
        c * r :=
    localizedExcessRiskEmpiricalRademacherComplexity_le_of_bernstein_fixedPointCertificate
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (c := c) (r := r) (rStar := rStar) (φ := φ)
      hc hr hbern henvelope hfixed hrStar
  have htwo :
      2 * localizedExcessRiskEmpiricalRademacherComplexity p ℓ iStar z r hr ≤
        2 * (c * r) :=
    mul_le_mul_of_nonneg_left hrad (by linarith)
  linarith

/-- Event-facing version of the finite fast-rate shell.

This composes `localizedUpperDeviationEvent` with the deterministic shell above.
The remaining probabilistic task is therefore to prove that this event has high
probability for finite localized classes. -/
theorem finiteExcessRisk_le_of_localizedUpperDeviationEvent_bernstein_fixedPoint
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {c r rStar ε : ℝ} {φ : ℝ → ℝ}
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    {hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hupper :
      z ∈ localizedUpperDeviationEvent p ℓ iStar
        (LocalizedByExcessRisk p ℓ iStar r) hP
        (2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε))
    {i : ι}
    (hi : LocalizedByExcessRisk p ℓ iStar r i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0)
    (henvelope :
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r))
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r) :
    finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  classical
  have hdev :
      LocalizedDeviationCertificate p ℓ iStar z
        (LocalizedByExcessRisk p ℓ iStar r)
        (2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε) :=
    localizedDeviationCertificate_of_mem_upperDeviationEvent
      (p := p) (ℓ := ℓ) (iStar := iStar)
      (P := LocalizedByExcessRisk p ℓ iStar r) (hP := hP)
      (η := 2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr + ε)
      hupper
  exact finiteExcessRisk_le_of_localizedDeviation_bernstein_fixedPoint
    (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
    (c := c) (r := r) (rStar := rStar) (ε := ε) (φ := φ)
    hc hr hbern hdev hi hemp henvelope hfixed hrStar

/-- Fast-rate event wrapper using the named sample-dependent event.

This theorem is deterministic: it assumes membership in the fast-rate
upper-deviation event. A separate concentration theorem must prove that this
sample-dependent event has high probability. -/
theorem finiteExcessRisk_le_of_localizedFastRateUpperDeviationEvent_bernstein_fixedPoint
    [Fintype ι] [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    (z : Fin n → Z) {c r rStar ε : ℝ} {φ : ℝ → ℝ}
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    {hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hupper :
      z ∈ localizedFastRateUpperDeviationEvent p ℓ iStar r hr ε hP)
    {i : ι}
    (hi : LocalizedByExcessRisk p ℓ iStar r i)
    (hemp : empiricalExcessRisk ℓ iStar i z ≤ 0)
    (henvelope :
      localizedSecondMomentEmpiricalRademacherComplexity
        p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r))
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r) :
    finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  exact finiteExcessRisk_le_of_localizedUpperDeviationEvent_bernstein_fixedPoint
    (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
    (c := c) (r := r) (rStar := rStar) (ε := ε) (φ := φ)
    (hP := hP) hc hr hbern
    (by
      simpa [localizedFastRateUpperDeviationEvent,
        localizedSampleDependentUpperDeviationEvent] using hupper)
    hi hemp henvelope hfixed hrStar

/-- Named fast-rate bad-event mass controlled by shifted exponential-moment
budgets.

This is the assumption-facing random-threshold interface for the fast-rate
event: the empirical localized complexity term stays inside the shifted
moment. -/
theorem localizedFastRateUpperDeviationBadEventMass_le_sum_shiftedExpMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε lam : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (momentBudget :
      {i : ι // LocalizedByExcessRisk p ℓ iStar r i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hmoment :
      ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr + ε)
          lam ≤ momentBudget i) :
    localizedFastRateUpperDeviationBadEventMass
        sampleWeight p ℓ iStar r hr ε hP ≤
      ∑ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        momentBudget i := by
  unfold localizedFastRateUpperDeviationBadEventMass
  exact localizedSampleDependentUpperDeviationBadEventMass_le_sum_shiftedExpMoment
    sampleWeight p ℓ iStar (LocalizedByExcessRisk p ℓ iStar r) hP
    (fun z : Fin n → Z =>
      2 * localizedExcessRiskEmpiricalRademacherComplexity
        p ℓ iStar z r hr + ε)
    momentBudget hlam hweight hmoment

/-- Pointwise fast-rate shifted moment with the fixed slack factored out.

This is an algebraic/interface lemma: it factors the fixed slack `ε` out of the
sample-dependent shifted moment as `exp(λε)`, leaving the empirical localized
complexity term `2·R̂_loc(z)` syntactically inside the "centered" moment. The
remaining obligation is the centered moment budget supplied by `hcentered`.

CAVEAT — this is NOT a non-conservative concentration result, and the centered
moment is not "sharper" per hypothesis. Because `R̂_loc(z) ≥ 0` and `λ > 0`,
`exp(λ(gap_i(z) - 2·R̂_loc(z))) ≤ exp(λ·gap_i(z))` pointwise, so the centered
moment is `≤` the fixed (un-localized) moment for the *same* hypothesis `i`.
Hence any union bound built from these per-hypothesis centered moments can only
recover the conservative fixed-threshold bound — the `2·R̂_loc` term provably
buys nothing here. The localized-Rademacher benefit is a *supremum*-level
phenomenon: `2·R̂_loc` controls the fluctuation of the whole supremum
`localizedUpperDeviation`, not any individual `gap_i`. The genuine
non-conservative obligation is therefore a whole-supremum random-threshold
concentration of `localizedUpperDeviation - 2·R̂_loc` (symmetrization +
McDiarmid/Azuma), which this per-hypothesis lemma names but does not discharge. -/
theorem localizedFastRatePointwiseShiftedExpMoment_le_centered_div
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε lam C : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i})
    (hcentered :
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr)
          lam ≤ C) :
    localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        sampleWeight p ℓ iStar i.1
        (fun z : Fin n → Z =>
          2 * localizedExcessRiskEmpiricalRademacherComplexity
            p ℓ iStar z r hr + ε)
        lam ≤
      C / Real.exp (lam * ε) := by
  have heq :
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr + ε)
          lam =
        localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr)
          lam / Real.exp (lam * ε) := by
    simpa using
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_add_const
        (sampleWeight := sampleWeight) (p := p) (ℓ := ℓ)
        (iStar := iStar) (i := i.1)
        (η := fun z : Fin n → Z =>
          2 * localizedExcessRiskEmpiricalRademacherComplexity
            p ℓ iStar z r hr)
        (η0 := ε) (lam := lam)
  rw [heq]
  exact div_le_div_of_nonneg_right hcentered
    (le_of_lt (Real.exp_pos (lam * ε)))

/-- Named fast-rate bad-event mass controlled by centered random-threshold
shifted moments.

This factors out only the fixed slack `ε` and leaves the empirical localized
complexity term syntactically inside each pointwise moment. It is an
assumption-facing interface: the `centeredBudget` hypotheses are supplied, not
proved.

CAVEAT — this union-bound interface is conservative-only. As explained in
`localizedFastRatePointwiseShiftedExpMoment_le_centered_div`, each per-hypothesis
centered moment is pointwise `≤` the fixed moment, so `∑ᵢ centeredBudgetᵢ`
cannot improve on the conservative bound. A genuinely non-conservative result
requires a whole-supremum random-threshold concentration argument, not this
per-hypothesis sum. -/
theorem localizedFastRateUpperDeviationBadEventMass_le_sum_centeredShiftedExpMoment_div
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε lam : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (centeredBudget :
      {i : ι // LocalizedByExcessRisk p ℓ iStar r i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hcentered :
      ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr)
          lam ≤ centeredBudget i) :
    localizedFastRateUpperDeviationBadEventMass
        sampleWeight p ℓ iStar r hr ε hP ≤
      ∑ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        centeredBudget i / Real.exp (lam * ε) := by
  exact localizedFastRateUpperDeviationBadEventMass_le_sum_shiftedExpMoment
    sampleWeight p ℓ iStar (r := r) (ε := ε) (lam := lam)
    hr hP
    (fun i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i} =>
      centeredBudget i / Real.exp (lam * ε))
    hlam hweight
    (fun i =>
      localizedFastRatePointwiseShiftedExpMoment_le_centered_div
        (sampleWeight := sampleWeight) (p := p) (ℓ := ℓ)
        (iStar := iStar) (r := r) (ε := ε) (lam := lam)
        (C := centeredBudget i) hr i (hcentered i))

/-- Pointwise shifted-moment budget for the named fast-rate event under
bounded excess losses.

This instantiates the shifted-moment interface for the fast-rate random
threshold by using the fixed-`ε` lower envelope of that threshold. It is still
conservative, but it routes the finite product argument through the
sample-dependent shifted-moment layer rather than directly through set
inclusion. -/
theorem localizedFastRatePointwiseShiftedExpMoment_finiteProduct_le_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    {r ε lam : ℝ} (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i})
    (hlam : 0 < lam)
    (hbound : ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
        excessLoss ℓ iStar i.1 z ≤ 1) :
    localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
          (n := n) p)
        p ℓ iStar i.1
        (fun z : Fin n → Z =>
          2 * localizedExcessRiskEmpiricalRademacherComplexity
            p ℓ iStar z r hr + ε)
        lam ≤
      Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
        Real.exp (lam * ε) := by
  have hweight :
      ∀ z : Fin n → Z,
        0 ≤ FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
          (n := n) p z := by
    intro z
    unfold FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
    exact Finset.prod_nonneg (fun k _hk => hp.nonneg (z k))
  have hlower :
      ∀ z : Fin n → Z,
        ε ≤ 2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε := by
    intro z
    have hrad :
        0 ≤ localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr :=
      localizedExcessRiskEmpiricalRademacherComplexity_nonneg
        (p := p) (ℓ := ℓ) (iStar := iStar) (z := z) (r := r) hr
    have hterm :
        0 ≤ 2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr :=
      mul_nonneg (by norm_num) hrad
    linarith
  have hshift_le_fixed :
      localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
            (n := n) p)
          p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr + ε)
          lam ≤
        localizedPointwiseUpperDeviationExpMoment
          (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
            (n := n) p)
          p ℓ iStar i.1 lam / Real.exp (lam * ε) :=
    localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_le_fixedExpMoment_div
      (sampleWeight :=
        FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
          (n := n) p)
      (p := p) (ℓ := ℓ) (iStar := iStar) (i := i.1)
      (η := fun z : Fin n → Z =>
        2 * localizedExcessRiskEmpiricalRademacherComplexity
          p ℓ iStar z r hr + ε)
      (η0 := ε) (lam := lam) hlam hweight hlower
  have hfixed :
      localizedPointwiseUpperDeviationExpMoment
          (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
            (n := n) p)
          p ℓ iStar i.1 lam ≤
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) :=
    localizedPointwiseUpperDeviationExpMoment_finiteProduct_le_of_single
      (n := n) hn p hp ℓ iStar i.1 lam (1 : ℝ)
      (localizedOneCoordinateDeviationMGF_le_of_excessLoss_mem_Icc_neg_one_one
        (n := n) hn p hp ℓ iStar i.1 lam hbound)
  exact hshift_le_fixed.trans
    (div_le_div_of_nonneg_right hfixed (le_of_lt (Real.exp_pos _)))

/-- Assumption-facing high-confidence finite fast-rate localized statement
from shifted exponential-moment budgets.

Unlike the bounded-excess bridge below, this theorem keeps the random threshold
inside the pointwise shifted moments supplied by the caller. It still does not
prove those shifted-moment budgets; it packages the exact finite interface
needed for that future concentration step. -/
theorem localizedFastRateHighConfidence_bernstein_fixedPoint_of_shiftedExpMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {c r rStar ε lam δ : ℝ} {φ : ℝ → ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (momentBudget :
      {i : ι // LocalizedByExcessRisk p ℓ iStar r i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r)
    (hmoment :
      ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr + ε)
          lam ≤ momentBudget i)
    (hmoment_sum :
      (∑ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        momentBudget i) ≤ δ) :
    localizedFastRateUpperDeviationBadEventMass
        sampleWeight p ℓ iStar r hr ε hP ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedFastRateUpperDeviationEvent p ℓ iStar r hr ε hP →
          LocalizedByExcessRisk p ℓ iStar r i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              localizedSecondMomentEmpiricalRademacherComplexity
                p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r) →
                finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  refine ⟨?_, ?_⟩
  · exact (localizedFastRateUpperDeviationBadEventMass_le_sum_shiftedExpMoment
      sampleWeight p ℓ iStar (r := r) (ε := ε) (lam := lam)
      hr hP momentBudget hlam hweight hmoment).trans hmoment_sum
  · intro z i hz hi hemp henvelope
    exact finiteExcessRisk_le_of_localizedFastRateUpperDeviationEvent_bernstein_fixedPoint
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (c := c) (r := r) (rStar := rStar) (ε := ε) (φ := φ)
      (hP := hP) hc hr hbern hz hi hemp henvelope hfixed hrStar

/-- High-confidence finite fast-rate localized statement from centered
random-threshold shifted moments.

The centered moment keeps the empirical localized complexity term syntactically
in the exponent and factors out only the fixed slack `ε`. This is
assumption-facing: the `centeredBudget` hypotheses are supplied, not proved.

CAVEAT — this wrapper is an interface, not a non-conservative theorem. The
`hcentered` hypotheses it consumes are, per hypothesis, satisfiable only by the
conservative fixed-threshold bound (see
`localizedFastRatePointwiseShiftedExpMoment_le_centered_div`). It names the exact
finite surface a future whole-supremum random-threshold concentration proof
would discharge; it does not itself sharpen the conservative bound. -/
theorem localizedFastRateHighConfidence_bernstein_fixedPoint_of_centeredShiftedExpMoment
    [Fintype ι] [Fintype Z] {n : ℕ}
    (sampleWeight : (Fin n → Z) → ℝ)
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (iStar : ι)
    {c r rStar ε lam δ : ℝ} {φ : ℝ → ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (centeredBudget :
      {i : ι // LocalizedByExcessRisk p ℓ iStar r i} → ℝ)
    (hlam : 0 < lam)
    (hweight : ∀ z : Fin n → Z, 0 ≤ sampleWeight z)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r)
    (hcentered :
      ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment
          sampleWeight p ℓ iStar i.1
          (fun z : Fin n → Z =>
            2 * localizedExcessRiskEmpiricalRademacherComplexity
              p ℓ iStar z r hr)
          lam ≤ centeredBudget i)
    (hcentered_sum :
      (∑ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        centeredBudget i / Real.exp (lam * ε)) ≤ δ) :
    localizedFastRateUpperDeviationBadEventMass
        sampleWeight p ℓ iStar r hr ε hP ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedFastRateUpperDeviationEvent p ℓ iStar r hr ε hP →
          LocalizedByExcessRisk p ℓ iStar r i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              localizedSecondMomentEmpiricalRademacherComplexity
                p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r) →
                finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  refine ⟨?_, ?_⟩
  · exact (localizedFastRateUpperDeviationBadEventMass_le_sum_centeredShiftedExpMoment_div
      sampleWeight p ℓ iStar (r := r) (ε := ε) (lam := lam)
      hr hP centeredBudget hlam hweight hcentered).trans hcentered_sum
  · intro z i hz hi hemp henvelope
    exact finiteExcessRisk_le_of_localizedFastRateUpperDeviationEvent_bernstein_fixedPoint
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (c := c) (r := r) (rStar := rStar) (ε := ε) (φ := φ)
      (hP := hP) hc hr hbern hz hi hemp henvelope hfixed hrStar

/-- Conservative high-confidence finite fast-rate localized statement under
bounded excess losses.

The first conjunct controls the finite product mass outside the named
fast-rate random-threshold event. The second conjunct records the deterministic
fast-rate payoff on that event, under the same Bernstein/fixed-point envelope
hypotheses used by the shell above.

This theorem is conservative because the bad-event mass bound reduces the
random threshold to its fixed-`ε` lower envelope; it is not a sharp
random-threshold concentration inequality. -/
theorem localizedFastRateHighConfidence_bernstein_fixedPoint_boundedExcess
    [Fintype ι] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    {c r rStar ε lam δ : ℝ} {φ : ℝ → ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (hlam : 0 < lam)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hfixed : FixedPointUpperCertificate φ rStar)
    (hrStar : rStar ≤ c * r)
    (hbound : ∀ i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
      ∀ z : Z,
        (-1 : ℝ) ≤ excessLoss ℓ iStar i.1 z ∧
          excessLoss ℓ iStar i.1 z ≤ 1)
    (htail_sum :
      (∑ _i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        Real.exp (lam ^ 2 * (1 : ℝ) / (2 * (n : ℝ))) /
          Real.exp (lam * ε)) ≤ δ) :
    localizedFastRateUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar r hr ε hP ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedFastRateUpperDeviationEvent p ℓ iStar r hr ε hP →
          LocalizedByExcessRisk p ℓ iStar r i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              localizedSecondMomentEmpiricalRademacherComplexity
                p ℓ iStar z (c * r) (mul_nonneg hc hr) ≤ φ (c * r) →
                finiteExcessRisk p ℓ iStar i ≤ 2 * (c * r) + ε := by
  refine ⟨?_, ?_⟩
  · exact localizedFastRateUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess
      (ι := ι) hn p hp ℓ iStar (r := r) (ε := ε) (lam := lam)
      (δ := δ) hr hP hlam hbound htail_sum
  · intro z i hz hi hemp henvelope
    exact finiteExcessRisk_le_of_localizedFastRateUpperDeviationEvent_bernstein_fixedPoint
      (p := p) (ℓ := ℓ) (iStar := iStar) (z := z)
      (c := c) (r := r) (rStar := rStar) (ε := ε) (φ := φ)
      (hP := hP) hc hr hbern hz hi hemp henvelope hfixed hrStar

/-! ## Finite localized Bernstein fast-rate composition

This is the finite Bernstein/localization payoff: composing the reusable
variance-aware Bernstein tail
(`FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail`) with the finite
union bound and the fixed-threshold event payoff yields a high-confidence
localized statement whose bad-event mass carries the *localized variance* `c * r`
in the exponent — a genuine Bernstein/localization improvement over the
conservative global Hoeffding (`variance = 1`) bound. -/

/-- Centered second moment (variance proxy) of the excess loss is at most
`c * r` on the localized class: `Var ≤ second moment ≤ c * r`, via the Bernstein
condition and the excess-risk localization radius. -/
theorem centeredSecondMoment_le_of_bernstein_localized [Fintype Z]
    {p : Z → ℝ} (hp : FormalSLT.PACBayesKL.IsPMF p)
    {ℓ : ι → Z → ℝ} {iStar i : ι} {c r : ℝ} (hc : 0 ≤ c)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hloc : LocalizedByExcessRisk p ℓ iStar r i) :
    ∑ z, p z * (finiteExcessRisk p ℓ iStar i - excessLoss ℓ iStar i z) ^ 2 ≤ c * r := by
  have hSM : finiteSecondMoment p (excessLoss ℓ iStar i) ≤ c * r :=
    localizedBySecondMoment_of_excessRisk_le hc hbern hloc
  have hmean : ∑ z, p z * excessLoss ℓ iStar i z = finiteExcessRisk p ℓ iStar i := rfl
  have hsum_p : ∑ z, p z = 1 := hp.sum_one
  have hexpand : ∑ z, p z * (finiteExcessRisk p ℓ iStar i - excessLoss ℓ iStar i z) ^ 2
      = finiteSecondMoment p (excessLoss ℓ iStar i) - (finiteExcessRisk p ℓ iStar i) ^ 2 := by
    have e1 : (finiteSecondMoment p (excessLoss ℓ iStar i))
          - 2 * finiteExcessRisk p ℓ iStar i * (∑ z, p z * excessLoss ℓ iStar i z)
          + (finiteExcessRisk p ℓ iStar i) ^ 2 * (∑ z, p z)
        = ∑ z, p z * (finiteExcessRisk p ℓ iStar i - excessLoss ℓ iStar i z) ^ 2 := by
      unfold finiteSecondMoment
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [← e1, hmean, hsum_p]; ring
  rw [hexpand]
  nlinarith [sq_nonneg (finiteExcessRisk p ℓ iStar i), hSM]

/-- **Finite localized Bernstein high-confidence theorem.** Under
bounded excess losses (`excessLoss ∈ [-1,1]`) and a finite Bernstein condition,
the bad-event mass outside the fixed-threshold localized upper-deviation event is
controlled by the variance-aware Bernstein tail with the localized variance
`c * r` in the exponent (not a global Hoeffding `1`); and on the event, every
localized empirical competitor (`empiricalExcessRisk ≤ 0`) has population excess
risk at most the fixed threshold `η`.

The bad-event mass per hypothesis is bounded by the *averaged/tensorized*
Bernstein tail `exp(-n·η²/(2(c·r + 2η/3)))`, so the `n·η²` scaling is correct and
the per-coordinate range bound is `b = 2`. This is the honest variance/localization
fast-rate ingredient; it uses the fixed-threshold payoff, not the
empirical-Rademacher random threshold. -/
theorem localizedFiniteClassBernsteinHighConfidence_empirical_nonpos
    [Fintype ι] [Fintype Z] {n : ℕ} (hn : 0 < n)
    (p : Z → ℝ) (hp : FormalSLT.PACBayesKL.IsPMF p)
    (ℓ : ι → Z → ℝ) (iStar : ι)
    {c r η δ : ℝ} (hc : 0 ≤ c) (hcr : 0 < c * r) (hη : 0 ≤ η)
    [DecidablePred (LocalizedByExcessRisk p ℓ iStar r)]
    (hP : ∃ j : ι, LocalizedByExcessRisk p ℓ iStar r j)
    (hbern : BernsteinCondition p ℓ iStar c)
    (hbound : ∀ i : ι, ∀ z : Z,
      (-1 : ℝ) ≤ excessLoss ℓ iStar i z ∧ excessLoss ℓ iStar i z ≤ 1)
    (htail_sum :
      (∑ _i : {i : ι // LocalizedByExcessRisk p ℓ iStar r i},
        Real.exp (-(n : ℝ) * η ^ 2 / (2 * (c * r + 2 * η / 3)))) ≤ δ) :
    localizedUpperDeviationBadEventMass
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p)
        p ℓ iStar (LocalizedByExcessRisk p ℓ iStar r) hP η ≤ δ ∧
      ∀ {z : Fin n → Z} {i : ι},
        z ∈ localizedUpperDeviationEvent p ℓ iStar
            (LocalizedByExcessRisk p ℓ iStar r) hP η →
          LocalizedByExcessRisk p ℓ iStar r i →
            empiricalExcessRisk ℓ iStar i z ≤ 0 →
              finiteExcessRisk p ℓ iStar i ≤ η := by
  classical
  have hW_nonneg : ∀ S : Fin n → Z,
      0 ≤ FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p S := by
    intro S
    unfold FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight
    exact Finset.prod_nonneg (fun k _ => hp.nonneg (S k))
  refine ⟨?_, ?_⟩
  · refine le_trans (localizedUpperDeviationBadEventMass_le_sum_tails
        (FormalSLT.PACBayesFiniteProductMGF.finiteProductSampleWeight (n := n) p) p ℓ iStar
        (LocalizedByExcessRisk p ℓ iStar r) hP η
        (fun _ => Real.exp (-(n : ℝ) * η ^ 2 / (2 * (c * r + 2 * η / 3))))
        hW_nonneg ?_) htail_sum
    intro i
    have hvar := centeredSecondMoment_le_of_bernstein_localized hp hc hbern i.2
    have hR_le : finiteExcessRisk p ℓ iStar i.1 ≤ 1 := by
      unfold finiteExcessRisk finiteMean
      calc ∑ z, p z * excessLoss ℓ iStar i.1 z
          ≤ ∑ z, p z * 1 :=
            Finset.sum_le_sum (fun z _ =>
              mul_le_mul_of_nonneg_left (hbound i.1 z).2 (hp.nonneg z))
        _ = 1 := by simp [hp.sum_one]
    have hbnd : ∀ z, finiteExcessRisk p ℓ iStar i.1 - excessLoss ℓ iStar i.1 z ≤ 2 := by
      intro z; have h2 := (hbound i.1 z).1; linarith [hR_le, h2]
    have htail := FormalSLT.Probability.BernsteinMGF.averaged_bernstein_tail
        (ι := ι) (Z := Z) hn p hp (excessLoss ℓ iStar) i.1
        (b := 2) (v := c * r) (eps := η) (by norm_num) hcr hη hbnd hvar
    refine le_trans ?_ htail
    unfold localizedPointwiseUpperDeviationBadEventMass
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun S _ _ => hW_nonneg S)
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_of_lt hz.2⟩
  · intro z i hz hi hemp
    exact finiteExcessRisk_le_of_localizedUpperDeviationEvent_empirical_nonpos hz hi hemp

end FormalSLT.Rademacher.Localized
