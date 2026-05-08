import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
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
* deterministic fixed-point and localized deviation certificates, but no
  high-probability localized concentration theorem yet;
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
a constant multiple of its excess risk. This is the variance/localization condition
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
for the first fast-rate/local-Rademacher layer. -/
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

end FormalSLT.Rademacher.Localized
