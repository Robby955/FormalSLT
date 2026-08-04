/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Tactic
import FormalSLT.AnytimeValid.VilleMaximalIneq
import FormalSLT.AnytimeValid.SubGaussianCS

/-!
# E-processes, e-values, and safe-testing Type-I control

This file packages the safe-testing / anytime-valid testing layer on top of the
banked nonnegative-supermartingale Ville maximal inequality
`FormalSLT.AnytimeValid.ville_maximal_ineq`. An **e-process** under a null
measure `μ` is a process `E : ℕ → Ω → ℝ` that is (i) nonnegative, (ii)
normalized at the origin (`E 0 = 1`), and (iii) a `𝒢`-supermartingale under `μ`.
Its running prefix maximum is the realized "betting wealth"; rejecting the null
when that wealth reaches `1/α` controls the Type-I error at level `α`, uniformly
over the stopping rule. This is the testing-side counterpart of the
confidence-sequence layer in `SubGaussianCS.lean` / `MixtureCS.lean`.

Three named results, all derived from `ville_maximal_ineq` and elementary
measure theory (no new hard analysis):

* `eProcess_typeI_control`: the safe-testing guarantee. For an `EProcess μ 𝒢 E`
  under a probability measure, level `0 < α`, and horizon `n`, the rejection
  event "the realized prefix max of `E` reaches `1/α`" has `μ`-measure at most
  `α`: `μ.real {ω | 1/α ≤ finiteRunningMax E n ω} ≤ α`. This is the literal
  anytime-valid Type-I statement up to `n` (the running-max event, i.e. rejecting
  at *any* time `≤ n`), not a single fixed-time event. Instantiate
  `ville_maximal_ineq` at `a = 1/α`, divide through, and collapse `∫ E 0 = 1`.

* `eProcess_product_of_supermartingale`: the e-value composition law. The
  pointwise product of two e-processes is again an e-process provided the product
  is again a `𝒢`-supermartingale (the dischargeable hypothesis; full conditional
  independence is out of scope, see the module note). It encodes "products of
  combined e-values are e-values": nonnegative, starts at `1` (`1 * 1 = 1`),
  supermartingale.

* `eProcess_optionalContinuation`: optional continuation / stopped e-value. For
  any `ℕ∞`-valued `𝒢`-stopping time `τ` bounded by `n`, the stopped value
  `stoppedValue E τ` integrates to at most `1`: `∫ ω, stoppedValue E τ ω ∂μ ≤ 1`.
  This is the `E[E_τ] ≤ 1` form of the e-value guarantee under optional stopping;
  it follows from `Submartingale.expected_stoppedValue_mono` applied to `-E`
  (`E[E_τ] ≤ E[E_0] = 1`), the same route the keystone uses.

A genuine non-vacuous witness (the fixed-tilt exponential of a Rademacher
increment, a nonnegative supermartingale with `E 0 = 1` and `E_1 > 1` on a
positive-mass event) is built in `examples/CheckEProcess.lean`, where the
three theorems fire on it with the numeric Type-I bound `≤ 1/4` at threshold
`1/α = 4`.

## References

* Grünwald, P., de Heide, R., Koolen, W. (2024). "Safe testing." *Journal of the
  Royal Statistical Society: Series B* 86(5), 1091–1128.
* Ramdas, A., Grünwald, P., Vovk, V., Shafer, G. (2023). "Game-theoretic
  statistics and safe anytime-valid inference." *Statistical Science* 38(4),
  576–601.
* Howard, S., Ramdas, A., McAuliffe, J., Sekhon, J. (2021). "Time-uniform,
  nonparametric, nonasymptotic confidence sequences." *The Annals of Statistics*
  49(2) / Probability Surveys 17.
* Ville, J. (1939). *Étude critique de la notion de collectif.* (Original
  supermartingale maximal inequality.)

## Formal-methods disambiguation (empty-field audit gates any "first" claim)

To the authors' knowledge this is the first e-process / safe-testing object
mechanised in an interactive theorem prover; that claim is gated on an
empty-field audit handed to the maintainer and is NOT baked into any theorem name
or load-bearing comment. Where this differs from each known nearby effort:
Karayel–Tan (AFP 2023) mechanise Hoeffding/Bernstein/McDiarmid concentration in
Isabelle/HOL (fixed-sample, no anytime-valid object, no e-process, no test
martingale). Sonoda et al. 2025 (arXiv:2503.19605) and Zhang–Lee–Liu 2026
(arXiv:2602.02285) are continuous-process Lean efforts of separate scope, neither
an e-value / safe-testing Type-I guarantee nor an e-process rejection rule.
Tassarotti (2021) is a probabilistic-program / Coq verification line, not
anytime-valid testing. Bagnall–Stewart (2019) is a Coq PAC-learning /
generalization-bound line (fixed-sample, no e-process). None of these formalize
an e-process, e-value composition, or optional-stopping Type-I control. No
"first Lean/Coq/Isabelle e-process" sentence ships until the empty-field audit
clears.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace FormalSLT.AnytimeValid

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0}

/--
An **e-process** for the null `μ` with respect to the filtration `𝒢`: a process
`E : ℕ → Ω → ℝ` that is nonnegative, normalized to `1` at the origin, and a
`𝒢`-supermartingale under `μ`. These are exactly the three structural fields and
nothing that smuggles the Type-I conclusion. The `E 0 = 1` normalization is the
deterministic-start case (`∀ ω, E 0 ω = 1`), so `∫ E 0 = 1` under a probability
measure. -/
structure EProcess (μ : Measure Ω) (𝒢 : Filtration ℕ m0) (E : ℕ → Ω → ℝ) :
    Prop where
  /-- The process is pointwise nonnegative. -/
  nonneg : 0 ≤ E
  /-- The process starts deterministically at `1`. -/
  start_one : ∀ ω, E 0 ω = 1
  /-- The process is a `𝒢`-supermartingale under `μ`. -/
  supermartingale : Supermartingale E 𝒢 μ

/-- For an e-process under a probability measure, `∫ E 0 = 1`. -/
theorem EProcess.integral_start_eq_one [IsProbabilityMeasure μ]
    {E : ℕ → Ω → ℝ} (hE : EProcess μ 𝒢 E) :
    ∫ ω, E 0 ω ∂μ = 1 := by
  have hbody : (fun ω => E 0 ω) =ᵐ[μ] fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall hE.start_one
  rw [integral_congr_ae hbody]
  simp [integral_const]

/--
**Safe-testing Type-I control.** For an `EProcess μ 𝒢 E` under a probability
measure, level `0 < α`, and horizon `n`, the rejection event "the realized
prefix maximum of `E` reaches the threshold `1/α`" has `μ`-measure at most `α`:

`μ.real {ω | 1/α ≤ finiteRunningMax E n ω} ≤ α`.

`finiteRunningMax E n ω = max_{k ≤ n} E_k ω`, so this is the genuine "reject at
any time up to `n`" event — the literal anytime-valid Type-I statement up to `n`,
not a single fixed-time event. The proof instantiates `ville_maximal_ineq` at
`a = 1/α`, uses `∫ E 0 = 1`, and divides through by `1/α > 0`. -/
theorem eProcess_typeI_control [IsProbabilityMeasure μ]
    {E : ℕ → Ω → ℝ} (hE : EProcess μ 𝒢 E) {α : ℝ} (hα : 0 < α) (n : ℕ) :
    μ.real {ω | (1 : ℝ) / α ≤ finiteRunningMax E n ω} ≤ α := by
  have hthr_pos : (0 : ℝ) < 1 / α := by positivity
  have hthr_ne : (1 : ℝ) / α ≠ 0 := ne_of_gt hthr_pos
  have hmax := ville_maximal_ineq (a := 1 / α) hE.supermartingale hE.nonneg n
  rw [hE.integral_start_eq_one] at hmax
  -- `hmax : (1/α) * μ.real {ω | 1/α ≤ max_{k≤n} E_k ω} ≤ 1`; divide by `1/α`.
  simp only [finiteRunningMax]
  set thr : ℝ := 1 / α with hthr_def
  -- From `thr * q ≤ 1` and `thr = 1/α` conclude `q ≤ α`.
  have hkey : ∀ q : ℝ, thr * q ≤ 1 → q ≤ α := by
    intro q hq
    have hαinv : α = thr⁻¹ := by rw [hthr_def, one_div, inv_inv]
    rw [hαinv]
    calc q = thr⁻¹ * (thr * q) := by
            rw [← mul_assoc, inv_mul_cancel₀ hthr_ne, one_mul]
      _ ≤ thr⁻¹ * 1 := mul_le_mul_of_nonneg_left hq (inv_pos.mpr hthr_pos).le
      _ = thr⁻¹ := mul_one _
  exact hkey _ hmax

/--
**E-value composition law (supermartingale form).** The pointwise product of two
e-processes is again an e-process provided the product is again a
`𝒢`-supermartingale (`hprod_sup`). This is the honest, dischargeable hypothesis:
products of *independent* e-values are e-values, and conditional independence
across `𝒢` is exactly what makes the product a supermartingale, but rather than
carry an unverified independence predicate this states the supermartingale
condition directly (it is the property actually used) and is provable on the
witness. Nonnegativity and the `1 * 1 = 1` start are discharged from the two
factor e-processes. -/
theorem eProcess_product_of_supermartingale
    {E F : ℕ → Ω → ℝ} (hE : EProcess μ 𝒢 E) (hF : EProcess μ 𝒢 F)
    (hprod_sup : Supermartingale (fun n ω => E n ω * F n ω) 𝒢 μ) :
    EProcess μ 𝒢 (fun n ω => E n ω * F n ω) where
  nonneg := fun n ω => mul_nonneg (hE.nonneg n ω) (hF.nonneg n ω)
  start_one := fun ω => by rw [hE.start_one ω, hF.start_one ω, mul_one]
  supermartingale := hprod_sup

/--
**Optional continuation / stopped e-value.** For any `ℕ∞`-valued `𝒢`-stopping
time `τ` bounded by `n`, the stopped value `stoppedValue E τ` of an e-process
integrates to at most `1`:

`∫ ω, stoppedValue E τ ω ∂μ ≤ 1`.

This is the `E[E_τ] ≤ 1` form of the e-value guarantee under optional stopping: a
gambler who stops at any (bounded) data-dependent rule still holds an e-value.
The proof applies the supermartingale optional-stopping bound
`E[stoppedValue E τ] ≤ E[stoppedValue E 0] = E[E 0] = 1`, obtained from
`Submartingale.expected_stoppedValue_mono` on `-E`, the same route as the
keystone `ville_maximal_ineq`. -/
theorem eProcess_optionalContinuation [IsProbabilityMeasure μ]
    {E : ℕ → Ω → ℝ} (hE : EProcess μ 𝒢 E)
    {τ : Ω → ℕ∞} (hτ_stop : IsStoppingTime 𝒢 τ) {n : ℕ} (hτ_le : ∀ ω, τ ω ≤ (n : ℕ∞)) :
    ∫ ω, stoppedValue E τ ω ∂μ ≤ 1 := by
  have hint : ∀ i, Integrable (E i) μ := hE.supermartingale.integrable
  -- `E[stoppedValue E τ] ≤ E[stoppedValue E 0] = E[E 0] = 1`.
  have hsub : Submartingale (-E) 𝒢 μ := hE.supermartingale.neg
  have hmono := hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ_stop
      (fun _ => bot_le) hτ_le
  -- `E[stoppedValue (-E) σ] = -E[stoppedValue E σ]` for any stopping time `σ`.
  have key : ∀ σ : Ω → ℕ∞,
      ∫ ω, stoppedValue (-E) σ ω ∂μ = -∫ ω, stoppedValue E σ ω ∂μ := by
    intro σ
    have hfun : (fun ω => stoppedValue (-E) σ ω) = fun ω => -(stoppedValue E σ ω) := by
      funext ω; simp only [stoppedValue, Pi.neg_apply]
    rw [hfun, integral_neg]
  simp only [key] at hmono
  rw [stoppedValue_const] at hmono
  -- `hmono : -∫ stoppedValue E τ ≤ -∫ E 0`, i.e. `∫ E 0 ≤ ∫ stoppedValue E τ`? No:
  -- the *submartingale* bound is `E[stoppedValue (-E) 0] ≤ E[stoppedValue (-E) τ]`,
  -- i.e. `-∫ E 0 ≤ -∫ stoppedValue E τ`, i.e. `∫ stoppedValue E τ ≤ ∫ E 0 = 1`.
  have hE0 : ∫ ω, E 0 ω ∂μ = 1 := hE.integral_start_eq_one
  linarith [hmono, hE0]

end FormalSLT.AnytimeValid
