# StatLean v0.1: a Lean 4 statistics-theorem benchmark (harvest release)

StatLean is a benchmark of Lean 4 *statistics* tasks: concentration inequalities,
tail bounds, uniform-convergence and PAC / PAC-Bayes / VC generalization,
covering and chaining, anytime-valid confidence sequences, and finite-sample
estimator facts. v0.1 is a **harvest**: every task is an already-verified theorem
from FormalSLT, projected into a self-describing benchmark record. No new theorem
is proved in this release.

## Why this benchmark

Existing formal-math benchmarks are weighted toward competition and pure
mathematics: miniF2F and ProofNet (olympiad / undergraduate analysis and
algebra), PutnamBench (Putnam problems), and FormalConjectures (open problems).
Probability is present but thin, and *statistics* (concentration, learning
theory, estimation) is barely represented. StatLean fills that slice. It is not
a first-or-best claim: it is a domain-specific complement that gives a prover or
retrieval system a dense, internally consistent set of statistics statements with
checked proofs to retrieve against and repair.

The checked-in curated task set is fidelity-audited and axiom-clean (only
`propext`, `Classical.choice`, `Quot.sound`), so a candidate proof can be
checked against known-good ground truth in the same toolchain. The full harvest
comes from the sorry-free source library but does not carry a per-declaration
axiom audit.

## What is in v0.1

- A harvest pool of every public declaration resolvable from the FormalSLT
  spine (`statlean-v0.1.full.jsonl`).
- A curated task set of the cleanest named theorems, spread across every
  concept tag represented in the harvest (`statlean-v0.1.jsonl`). The current
  corpus represents 32 of the 33 vocabulary tags; no mapped declaration carries
  the reserved `Chebyshev` tag.
- Per task: an informal statement seeded from the Lean docstring, the verbatim
  Lean signature, a `file:line` pointer to the proof, conservative lexical
  declaration mentions, the live axiom profile, a difficulty tier, and a
  statement-fidelity audit result.

The exact counts (harvested, curated, axiom-clean, fidelity-audited) are written
to `statlean-v0.1.stats.json` by the build, so this README does not pin a number
that can drift.

## Record schema (`statlean-v0.1.jsonl`)

One JSON object per line:

- `id`: stable slug (`module-tail` + theorem short name).
- `schema_version`: record-schema identifier for this release.
- `source`: `{library, repo, module, tree}`, including the immutable Git tree of
  the harvested `FormalSLT/` source.
- `concept_family`: the FormalSLT spine family this theorem sits in.
- `concept_tags`: subset of the 33 concept tags (Markov, Chebyshev, Hoeffding,
  Bernstein, Bennett, Chernoff, sub-Gaussian, sub-Gamma, Azuma, McDiarmid, union
  bound, tail bound, MGF, confidence sequence, PAC-Bayes, KL divergence,
  Rademacher, VC dimension, covering / chaining, ERM, stability, sample
  statistics, Glivenko-Cantelli, Bernoulli, risk, exponential tilting,
  likelihood / MLE, unbiasedness, Fisher information, Cramér-Rao, survey
  sampling, bootstrap, exponential family).
- `informal_statement`: natural-language statement seeded from the `/-- … -/`
  docstring (falls back to the one-line role when no docstring exists).
- `lean_statement`: the verbatim Lean signature, from the declaration head down
  to (not including) the proof body.
- `lean_proof_pointer`: `path/to/Module.lean:line` of the declaration.
- `dependency_edges`: direct FormalSLT imports plus
  `lexical_declaration_mentions`, a conservative list of unambiguous harvested
  names appearing in comment/string-stripped proof source. This field is not an
  elaborated Lean dependency graph.
- `axiom_profile`: live `#print axioms` result, one of `clean{…}`, `axiom-free`,
  or a `NONSTANDARD:…` flag.
- `difficulty`: `easy` / `medium` / `hard`, from proof length plus dependency
  fan-in (heuristic, not a human grade).
- `fidelity`: `{checked, flagged, signed_off, lint}` from the non-vacuity gate.
- `qualified_name`, `short_name`, `kind`, `role`: bookkeeping. Qualified names
  are resolved from the Lean source and are globally unique in the harvest.

## How it is built

```
scripts/build_statlean_manifest.py            # full harvest + curate + fidelity + axioms
scripts/build_statlean_manifest.py --no-axioms   # skip the live #print axioms pass
scripts/build_statlean_manifest.py --limit N     # cap the curated task count
scripts/build_statlean_manifest.py --refresh-selection  # explicitly replace the pinned v0.1 set
```

The harvester reuses the canonical tag vocabulary from
`scripts/generate_theorem_index.py`, the family / declaration / module spine from
`docs/proof-frontier-manifest.json`, the non-vacuity lint
`scripts/statement_fidelity_check.py`, and the axiom-profile convention from
`scripts/check_axioms.sh`. It is read-only over the `.lean` sources. The checked
v0.1 task IDs and source tree are pinned in `statlean-v0.1.selection.json`, so a
later theorem-map change cannot silently recurate the versioned benchmark.

### Fidelity gate

Each curated task is passed through `statement_fidelity_check.py`, which lints the
three near-vacuity shapes (quantifier inversion `∀var ∃const`, trivial `True`
conclusion, `False` hypothesis) and honors a `-- fidelity:` sign-off. The release
build fails if a task is not audited exactly once or has an unsigned flag, so the
benchmark never silently ships a vacuous statement as a target.

### Axiom gate

The build emits one batched scratch that imports every selected module and runs
`#print axioms <fully-qualified-name>` for each task. A task is `clean` only
if its axioms are a subset of `{propext, Classical.choice, Quot.sound}`; anything
else (notably `sorryAx`, or `Lean.ofReduceBool` from `native_decide`) is flagged
`NONSTANDARD`.

## Roadmap after v0.1

The current harvest already includes sample-mean and Bessel-variance
unbiasedness, Bernoulli and known-variance Gaussian MLE witnesses,
Horvitz-Thompson design unbiasedness, a bootstrap-mean identity, Fisher
information, Cramér-Rao, and finite exponential-family curvature results.
Remaining classical-statistics lanes include:

- **Risk decompositions**: bias / variance / MSE identities and finite-sample
  estimator comparisons.
- **Conditioning and efficiency**: a Rao-Blackwell improvement theorem beyond
  the checked Fisher-information and Cramér-Rao surface.
- **Resampling**: bootstrap variance, finite-resample distributional identities,
  and validity statements rather than only the mean identity.
- **Likelihood and inference**: likelihood theory beyond the two checked MLE
  witnesses, plus finite-sample pivots, confidence intervals, and tests.
- **Asymptotics**: consistency and asymptotic-normality results. A Chebyshev lane
  remains absent; the existing finite-sample Hoeffding results can provide a
  separate bounded-data consistency route.

Any net-new task must ship sorry-free with a statement-fidelity audit and a live
axiom profile before entering a curated release.

## Companion baseline (scope only, not built in this release)

The intended use of StatLean is a **retrieval + proof-repair** baseline:

1. Index every harvested theorem by its informal statement and concept tags.
2. Given a held-out target statement, retrieve the k nearest harvested theorems
   and their proofs as in-context exemplars.
3. Ask a prover to produce a candidate proof; check it in the FormalSLT
   toolchain; on failure, feed the Lean error back for one repair round.
4. Score on compile success, axiom cleanliness, and statement-fidelity pass,
   not token overlap.

The lexical declaration mentions and difficulty tiers in each record exist to
support this: retrieval can prefer lower-difficulty exemplars sharing a concept
tag, and the mention list gives the proof-repair loop a conservative candidate
set of supporting declarations. Building the baseline is out of scope for
v0.1.

## Relation to other Lean work

StatLean draws its tasks from FormalSLT, which is itself complementary to the
adjacent Lean learning-theory projects listed in `../related-work.md`
(`lean-rademacher`, `lean-stat-learning-theory`, `formal-learning-theory-kernel`).
StatLean adds no priority claim over any of them; it packages checked statistics
theorems as a retrieval-and-repair benchmark, which those libraries do not set
out to do.
