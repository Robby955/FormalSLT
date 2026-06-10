# Route B blueprint: derived continuous-posterior PAC-Bayes lane

Status: **design only, nothing in this document is verified yet.** This
blueprint was written in an environment that cannot build Lean (see the
environment note in `AGENTS.md`), so every Mathlib citation below was checked
against the Mathlib *source* at the pinned commit
`25b7ac7d0cf8eef34ced5525f4a62b7613ad649b`, not against a compiled build.
Signatures must be re-confirmed by `lake build` before any public claim.

## Why this lane

The repo's PAC-Bayes layer derives every bound for finite PMFs
(`ι → ℝ` posteriors over finite data domains). The continuous-side modules are
currently shells:

- `FormalSLT/PACBayes/ContinuousPriorPosterior.lean`:
  `continuousPriorPosterior_certificate_of_kl` takes the PAC gate
  `populationRisk ≤ bound` as the hypothesis `hpacGate` and returns it.
- `FormalSLT/PACBayes/VitaleLemma.lean`: same shape.
- `FormalSLT/PACBayes/GaussianKL.lean`: real, checked closed-form KL algebra
  for diagonal/spherical Gaussian *parameters*, connected to no derived bound
  and to no Gaussian *measure*.

Route B replaces the assumed gate with a derived one: a measure-theoretic
Donsker-Varadhan inequality, a prior-averaged bounded-loss MGF bound over a
continuous prior, a Markov confidence step, and a Gaussian instantiation whose
KL term is the already-checked closed form. The deliverable is the first
checked PAC-Bayes bound in this library whose posterior ranges over a
non-finite hypothesis space.

## Mathlib tooling (verified against source at the pinned commit)

Available and load-bearing:

- `InformationTheory.klDiv : Measure α → Measure α → ℝ≥0∞`
  (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`), with
  `klDiv_of_ac_of_integrable`, `toReal_klDiv`,
  `toReal_klDiv_of_measure_eq` (probability-measure case: `toReal` of KL is
  `∫ llr dμ` with no separate integrability side condition), and the Gibbs
  nonnegativity content `integral_llr_add_sub_measure_univ_nonneg`.
- `MeasureTheory.llr` (`Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean`)
  with the three tilting lemmas that make Donsker-Varadhan a short
  composition: `llr_tilted_right`, `integrable_llr_tilted_right`,
  `integral_llr_tilted_right` (the last one is exactly the finite
  `klDiv_gibbs_eq` identity of `FormalSLT/PACBayesKL.lean` in measure form).
- `MeasureTheory.Measure.tilted` (`Mathlib/MeasureTheory/Measure/Tilted.lean`)
  with `isProbabilityMeasure_tilted`, `tilted_absolutelyContinuous`,
  `absolutelyContinuous_tilted`, `integral_exp_tilted`. The tilted measure is
  the measure-level Gibbs posterior.
- KL chain rule for composition-products:
  `klDiv_compProd_left`, `klDiv_compProd_eq_add`
  (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`).
- `ProbabilityTheory.gaussianReal` with `rnDeriv_gaussianReal`,
  `integral_id_gaussianReal`, `variance_id_gaussianReal`
  (`Mathlib/Probability/Distributions/Gaussian/Real.lean`).
- `ProbabilityTheory.HasSubgaussianMGF`
  (`Mathlib/Probability/Moments/SubGaussian.lean`), already consumed by
  `FormalSLT/PACBayesBoundedLoss.lean` for the per-coordinate Hoeffding MGF.

Not in Mathlib at the pinned commit (so they are ours to prove):

- a Donsker-Varadhan variational inequality (no `donsker`/`varadhan` hit in
  the source tree);
- KL additivity for finite product measures `Measure.pi`;
- any Gaussian-vs-Gaussian KL closed form.

## Step B1: measure-level Donsker-Varadhan

New module: `FormalSLT/PACBayes/MeasureDV.lean`.

Target signature (names tentative; hypotheses may move after compiling):

```lean
theorem donsker_varadhan_measure
    {Θ : Type*} [MeasurableSpace Θ]
    (ρ π : Measure Θ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (f : Θ → ℝ)
    (hac : ρ ≪ π)
    (hf_int : Integrable f ρ)
    (hexp_int : Integrable (fun θ => Real.exp (f θ)) π)
    (hllr_int : Integrable (MeasureTheory.llr ρ π) ρ) :
    ∫ θ, f θ ∂ρ ≤
      (InformationTheory.klDiv ρ π).toReal + Real.log (∫ θ, Real.exp (f θ) ∂π)
```

Proof plan, mirroring the finite Gibbs argument of
`FormalSLT/PACBayesKL.lean:235`:

1. Let `π' := π.tilted f`; `isProbabilityMeasure_tilted hexp_int` makes it a
   probability measure, and `ρ ≪ π ≪ π'` via `absolutelyContinuous_tilted`.
2. `integral_llr_tilted_right hac hf_int hexp_int hllr_int` gives
   `∫ llr ρ π' dρ = ∫ llr ρ π dρ - ∫ f dρ + log ∫ exp f dπ`.
3. Gibbs: `0 ≤ ∫ llr ρ π' dρ` from
   `integral_llr_add_sub_measure_univ_nonneg` (the measure-univ terms cancel
   for probability measures); integrability from `integrable_llr_tilted_right`.
4. Rewrite `∫ llr ρ π dρ` as `(klDiv ρ π).toReal` with
   `toReal_klDiv_of_measure_eq`.

Estimated size: 30-60 lines plus docstrings. The finite
`donsker_varadhan` stays; the example file checks both and prints axioms.

Edge cases to handle explicitly rather than silently: the
`Integrable (llr ρ π) ρ` hypothesis (callers with `klDiv ρ π ≠ ∞` can
discharge it through `klDiv_ne_top_iff`), and a wrapper stated with the
hypothesis `klDiv ρ π ≠ ∞` instead of raw integrability.

## Step B2: continuous-prior bounded-loss MGF and Markov gate

New module: `FormalSLT/PACBayes/ContinuousMcAllester.lean`.

Scope decision: the *hypothesis* space `Θ` becomes a measure space; the data
side stays the existing finite machinery (`Fintype Z`, finite product weights
`finiteProductSampleWeight`). This isolates the genuinely new step (continuous
prior/posterior) from a measure-theoretic iid sample lift that is not needed
for the Gaussian payoff.

Ingredients:

1. Prior deviation moment at a fixed sample, now an integral over `Θ`:

   ```lean
   noncomputable def continuousPriorDeviationMGF
       {Θ : Type*} [MeasurableSpace Θ] {Z : Type*} [Fintype Z] {n : ℕ}
       (π : Measure Θ) (p : Z → ℝ) (ℓ : Θ → Z → ℝ) (lam : ℝ)
       (S : Fin n → Z) : ℝ :=
     ∫ θ, Real.exp (lam * (populationRisk p ℓ θ - empiricalRisk ℓ θ S)) ∂π
   ```

2. Expected prior moment over the finite sample space: a finite sum of
   integrals. Swapping the finite sum and the integral is
   `integral_finset_sum`; no continuous Fubini is needed. The per-hypothesis
   bound `∑_S weight S · exp(lam·dev) ≤ exp(lam²/(8n))` is exactly the
   existing `sampleAverage_boundedLoss_mgf` applied pointwise in `θ`, then
   integrated over `π`.
3. Markov step on the finite sample mass: re-use
   `markovInequalityFiniteWeighted_proof` exactly as
   `priorAveraged_boundedLoss_mgf_badEventMass_le_delta` does.
4. Deterministic adapter on the good event: apply `donsker_varadhan_measure`
   with `f := fun θ => lam * (risk θ - empiricalRisk θ S)`, mirroring
   `posteriorRisk_bound_of_priorDeviationMGF_le`.

Measurability bookkeeping is the main cost: `ℓ` needs a measurability
hypothesis in `θ` so that the deviation and its exponential are
`π`-integrable. State these as explicit hypotheses; do not bake in a
`StandardBorelSpace` assumption unless compiling forces it.

Target final theorem of B2 (Catoni-style; the McAllester sqrt form follows by
the same algebra as the finite layer):

```lean
theorem continuousPosteriorRisk_bound_badEventMass_le_delta ... :
    (∑ S ∈ badSamples, finiteProductSampleWeight p S) ≤ delta
```

where membership of `S` in `badSamples` quantifies over all posteriors
`ρ : Measure Θ` with `IsProbabilityMeasure ρ`, `ρ ≪ π`,
`(klDiv ρ π).toReal + log (1/δ) ≤ C`, and the risk inequality violated.

## Step B3: replace the assumed-gate shells

Restate `ContinuousPriorPosterior.lean` (and the Vitale wrapper) so the gate
is the *derived* B2 theorem rather than the `hpacGate` hypothesis. Keep the
old shells temporarily with docstrings marking them superseded, or delete
them in the same PR if nothing downstream consumes them (only
`examples/CheckStabilityBridge.lean` and the Bernstein track need checking).

## Step B4: Gaussian measure KL and the nonvacuous certificate

Two sub-steps.

**B4a (analytic): Gaussian measure KL.** New lemmas connecting
`InformationTheory.klDiv` on Gaussian *measures* to the checked parameter
closed form in `GaussianKL.lean`:

1. One-dimensional: for `v, w ≠ 0`,

   ```lean
   theorem klDiv_gaussianReal (m₁ m₂ : ℝ) (v w : ℝ≥0) ... :
       InformationTheory.klDiv (gaussianReal m₁ v) (gaussianReal m₂ w) =
         ENNReal.ofReal
           ((v / w + (m₁ - m₂) ^ 2 / w - 1 + Real.log (w / v)) / 2)
   ```

   Route: `rnDeriv_gaussianReal` gives the density ratio; `llr` becomes a
   quadratic polynomial in `x`; integrate with `integral_id_gaussianReal` and
   `variance_id_gaussianReal`.
2. Finite product: KL additivity for `Measure.pi` over `Fin d`, by induction
   through the compProd chain rule (`klDiv_compProd_eq_add`) or a direct
   product-rnDeriv argument. This lemma is a genuine Mathlib-shaped
   contribution and an upstream candidate.
3. Bridge to the repo's `diagonalGaussianMeasure` /
   `sphericalGaussianMeasure` and the checked
   `sphericalGaussianKL_eq_closedForm`.

**B4b (numeric): the certificate instance.** Validated numerically by
`compiler/gaussian_feasibility.py` (mirrors of the Lean closed forms,
self-checked against the equal-variance collapse):

- `d = 100`, `n = 10000`, `δ = 1/20`,
- posterior `N(μ, 1·I)`, prior `N(0, 1·I)`, `‖μ‖² = 4`,
- KL `= 4/(2·1) = 2` exactly (rational; via the checked
  `sphericalGaussianKL_equalVariance_eq`, no log-term approximation needed),
- complexity `C = 2 + log 20 ≈ 4.9957`, McAllester penalty `≈ 0.0158`,
- risk bound `≈ 0.10 + 0.0158 = 0.116 < 1`: **nonvacuous** with a wide margin.

The equal-variance instance is deliberate: the variance ratio terms vanish, so
the Lean-side complexity budget is `2 + log 20`, and `log 20` is already
within reach of the budget-comparison algebra used by the existing compiler
certificates (rational upper bound on `log 20` via `Real.log` inequalities or
a `norm_num` extension; fallback: certify `C = 5` since
`2 + log 20 < 5` reduces to `log 20 < 3`, i.e. `20 < e³ ≈ 20.09` —
provable from Mathlib's `Real.exp_one_gt_d9`-style bounds).

## Step B5 (after B4): compiler track

Extend `compiler/compile.py` with a `gaussian` spec kind that emits
certificates against the B2/B4 theorems. Out of scope until B4 is checked.

## PR order and acceptance criteria

One step per PR, in order B1 → B2 → B3 → B4a → B4b (→ B5). Each PR:

- builds with `lake build FormalSLT`, zero `sorry` / `admit` / custom axiom;
- adds an `examples/Check*.lean` printing axioms for the new public theorems,
  staying inside `[propext, Classical.choice, Quot.sound]`;
- regenerates the proof-frontier manifest and updates `docs/theorem-map.md`;
- updates this blueprint if a signature had to move.

## Boundaries (do not claim until proved)

- B1-B3 give a continuous-*hypothesis-space* PAC-Bayes bound with a **finite
  data domain and finite iid sample machinery**. Do not call it a general
  measure-theoretic sample theorem.
- The Gaussian instance certifies one posterior/prior pair at explicit
  numerics. Do not call it a trained-network bound: there is no model, no
  dataset, and no claim about test error of any real classifier.
- No all-real-`λ` optimization claim: the B2 gate is fixed-`λ` (plus the
  existing finite-grid peeling if wired through later).
- The repo keeps its existing nonclaims; this lane removes exactly one
  boundary (finite hypothesis class on the PAC-Bayes gate), nothing else.
