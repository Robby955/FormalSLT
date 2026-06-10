# Route B Paper Section Draft: Derived Continuous-Posterior PAC-Bayes

Status: **planned-contribution draft.** Every theorem named here is a target,
not a checked result. Names and signatures come from
`docs/route-b-continuous-pac-bayes-blueprint-2026-06-10.md` and must be
replaced with compiled declarations before any sentence below is published.
Sentences that would become false if a target slips are marked `[PENDING]`.

This draft mirrors the structure of
`docs/pac-bayes-test-time-paper-section.md` so the two paper sections stay
consistent and reusable.

## How to use this document (read first)

This is a working artifact for accelerating the v0.2 release, not prose to be
admired:

1. **As the implementer:** treat the Lean Citations table as the checklist.
   When a target theorem compiles, replace its `[PENDING]` row with the real
   declaration and delete the marker. The section is publishable exactly when
   no `[PENDING]` markers remain and the Verification Paragraph has real
   numbers.
2. **As the writer:** the Paste-Ready LaTeX Block is the deliverable for a
   workshop submission. It is written so that filling the verification numbers
   and removing `[PENDING]` rows is the only editing needed.
3. **As the reviewer (you):** find this from `README.md` "Where to start" and
   from `docs/release-and-submission-strategy.md`. The "What Not To Claim"
   section is the honesty gate; check the published abstract against it.

Cross-references: design in
`docs/route-b-continuous-pac-bayes-blueprint-2026-06-10.md`; release scope in
`docs/v0.2-milestone.md`; methodology framing in
`docs/release-and-submission-strategy.md` section 1.

## Workshop framing

The workshop fit is the verification-first formalization workflow, not a
priority claim on PAC-Bayes mathematics. The contribution is:

- a mechanized derivation that lifts the repository's finite-class PAC-Bayes
  change-of-measure spine to a **continuous (measurable) posterior**, removing
  exactly one boundary from the v0.1 nonclaims list;
- a **kernel-checked, nonvacuous numeric certificate** for a Gaussian
  posterior/prior pair, with the complexity term equal to the repository's
  already-checked closed-form Gaussian KL;
- the same reproducible loop as v0.1: small theorem-slice PRs, explicit
  assumptions in type signatures, cache-aware builds, `#print axioms` audits,
  and conservative nonclaims.

The Lean kernel, CI, and human review decide what is accepted. The novelty is
the verified mechanization and the integrated finite-to-continuous spine in
one library, not new statistical learning theory.

## Section Draft

### Verified continuous-posterior PAC-Bayes certificate

PAC-Bayes generalization bounds are usually stated for posteriors over a
continuous parameter space, with the complexity term a Kullback-Leibler
divergence between measures. The repository's v0.1 PAC-Bayes track derives
every bound for finite hypothesis classes, with the posterior a probability
mass function on a finite index type. v0.2 closes that gap on the change-of-
measure gate.

The derivation has three mechanized steps and one instantiation.

**Step 1: measure-level Donsker-Varadhan.** `[PENDING]`
`donsker_varadhan_measure` lifts the finite Gibbs-posterior variational
inequality to arbitrary probability measures `ρ ≪ π` on a measurable space
`Θ`: for an integrable `f` with integrable exponential under `π`,
\[
  \int_\Theta f \, d\rho \;\le\; \mathrm{KL}(\rho\,\|\,\pi) + \log \int_\Theta e^{f}\, d\pi .
\]
The proof is the measure-level analogue of the finite argument in
`FormalSLT/PACBayesKL.lean`, using mathlib's tilted measure `π.tilted f` as
the Gibbs posterior and the log-likelihood-ratio tilting identity.

**Step 2: continuous-prior bounded-loss gate.** `[PENDING]` With the data
domain finite and an iid sample drawn from a finite product law, a
per-hypothesis Hoeffding sub-Gaussian MGF (already checked, via mathlib's
`HasSubgaussianMGF`) integrated over the continuous prior gives the bound
\(\int_\Theta \mathbb{E}_S\, e^{\lambda(R_\theta - \widehat R_\theta(S))}\, d\pi \le e^{\lambda^2/(8n)}\),
and a Markov step controls the bad-sample mass by `δ`. Combined with Step 1,
this yields the Catoni/McAllester risk inequality for every measurable
posterior, not just finite ones.

**Step 3: derived gate replaces assumed gate.** `[PENDING]` The v0.1
continuous shell carried the PAC inequality as a hypothesis. v0.2 discharges
it, so the continuous-posterior certificate is unconditional given its stated
sample and boundedness assumptions.

**Instantiation: a nonvacuous Gaussian certificate.** `[PENDING]` For a
spherical Gaussian posterior `N(μ, σ²I)` against prior `N(0, σ²I)`, the KL is
the checked closed form `‖μ‖²/(2σ²)`. At `d = 100`, `n = 10000`, `δ = 1/20`,
`σ² = 1`, `‖μ‖² = 4`, the KL is exactly `2`, the McAllester penalty is about
`0.0158`, and with empirical risk `0.10` the population-risk bound is about
`0.116 < 1`: nonvacuous with wide margin. The numeric regime was fixed ahead
of the Lean work by the stdlib mirrors in `compiler/gaussian_feasibility.py`.

## Lean Citations

Replace each `[PENDING]` with the compiled fully-qualified declaration name
and the verified `#print axioms` result when the corresponding blueprint step
lands.

| Role | Target declaration | Module | Status |
|---|---|---|---|
| Measure DV | `FormalSLT.PACBayes.donsker_varadhan_measure` | `PACBayes/MeasureDV.lean` | `[PENDING]` B1 |
| Continuous gate | `continuousPosteriorRisk_bound_badEventMass_le_delta` | `PACBayes/ContinuousMcAllester.lean` | `[PENDING]` B2 |
| Shell replacement | `continuousPriorPosterior_certificate` (derived) | `PACBayes/ContinuousPriorPosterior.lean` | `[PENDING]` B3 |
| Gaussian measure KL (1-d) | `klDiv_gaussianReal` | `PACBayes/GaussianKL.lean` (or new) | `[PENDING]` B4a |
| Product KL additivity | `klDiv_pi_eq_sum` (name tbd) | new | `[PENDING]` B4a |
| Closed-form bridge | `sphericalGaussianKL_eq_closedForm` | `PACBayes/GaussianKL.lean` | checked (v0.1) |
| Nonvacuous certificate | `gaussianPosterior_certificate` (name tbd) | `PACBayes/Generated` or new | `[PENDING]` B4b |

Already-checked dependencies the section may cite as background: the finite
`donsker_varadhan`, `finiteMcAllesterBoundedComplexity_badEventMass_le_delta`,
`oneCoordinate_boundedLoss_mgf`, and `sphericalGaussianKL_equalVariance_eq`.

## Verification Paragraph

Fill the bracketed numbers from the build that lands B4b. Template:

> The continuous-posterior PAC-Bayes derivation and the Gaussian certificate
> are checked in Lean 4 against the standard Lean/mathlib axiom surface
> `[propext, Classical.choice, Quot.sound]`. The focused audit ran
> `lake build FormalSLT` in `[T1]` wallclock (warm), the new
> `examples/Check*` axiom audits in `[T2]`, the proof-frontier manifest
> `--check`, and the `sorry`/`admit`/`axiom`/`constant` scans, all passing.
> The Python tooling suite `python3 -m pytest compiler/` passed `[N]` tests,
> including the generated-certificate golden-file sync test.

Until B4b compiles, this paragraph must not appear in any submitted draft.

## What Not To Claim

- Do not claim a measure-theoretic iid sample theorem. The data side stays
  finite (finite domain, finite product sample) in the v0.2 gate; only the
  hypothesis/posterior side becomes continuous.
- Do not claim all-real-`λ` PAC-Bayes optimization. The gate is fixed-`λ`.
- Do not claim a trained-model or neural-network generalization bound. The
  certificate certifies one posterior/prior pair at explicit numerics; there
  is no model, no dataset, and no test-error claim.
- Do not claim a general Gaussian KL for arbitrary continuous measures beyond
  the diagonal/spherical finite-dimensional forms actually proved.
- Do not make a priority claim. Cite exact Lean declarations and state the
  verified scope; note in `docs/comparison-table.md` that this is, to our
  knowledge, the first derived continuous-posterior gate among the surveyed
  Lean PAC-Bayes efforts, with the data-side assumption stated plainly.

## Paste-Ready LaTeX Block

Publishable only when no `[PENDING]` row remains above.

```tex
\paragraph{Verified continuous-posterior PAC-Bayes certificate.}
We mechanize a continuous-posterior PAC-Bayes generalization gate and a
nonvacuous Gaussian instance. The change-of-measure step is a measure-level
Donsker--Varadhan inequality, \texttt{donsker\_varadhan\_measure}: for
probability measures $\rho \ll \pi$ on a measurable space $\Theta$ and a
suitably integrable $f$,
\[
  \int_\Theta f\, d\rho \le \mathrm{KL}(\rho\,\|\,\pi) + \log\!\int_\Theta e^{f}\, d\pi .
\]
With a finite data domain, an iid sample of size $n$, and $[0,1]$ loss, a
per-hypothesis Hoeffding sub-Gaussian bound integrated over the prior and a
Markov step yield the McAllester gate
\texttt{continuousPosteriorRisk\_bound\_badEventMass\_le\_delta}: outside a
sample event of mass at most $\delta$, every measurable posterior $\rho$ obeys
\[
  R(\rho) \le \widehat R_S(\rho)
    + \frac{\mathrm{KL}(\rho\,\|\,\pi) + \log(1/\delta)}{\lambda}
    + \frac{\lambda}{8n}.
\]
Instantiating with a spherical Gaussian posterior $N(\mu,\sigma^2 I)$ against
prior $N(0,\sigma^2 I)$, the divergence is the checked closed form
$\mathrm{KL} = \lVert\mu\rVert^2/(2\sigma^2)$
(\texttt{sphericalGaussianKL\_eq\_closedForm}). At $d=100$, $n=10^4$,
$\delta=1/20$, $\sigma^2=1$, $\lVert\mu\rVert^2=4$, the certificate
\texttt{gaussianPosterior\_certificate} gives a population-risk bound of about
$0.116$, nonvacuous by a wide margin. All statements are checked by the Lean
kernel against the axioms $[\texttt{propext},\ \texttt{Classical.choice},\
\texttt{Quot.sound}]$, with no \texttt{sorry} or \texttt{admit}.
```
