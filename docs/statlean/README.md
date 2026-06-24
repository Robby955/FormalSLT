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

The whole corpus is sorry-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`), so a candidate proof can be checked against a
known-good ground truth in the same toolchain.

## What is in v0.1

- A harvest pool of every public declaration resolvable from the FormalSLT
  spine (`statlean-v0.1.full.jsonl`).
- A curated task set of the cleanest named theorems, spread across 24 concept
  families so no family is dropped (`statlean-v0.1.jsonl`).
- Per task: an informal statement seeded from the Lean docstring, the verbatim
  Lean signature, a `file:line` pointer to the proof, parsed dependency edges,
  the live axiom profile, a difficulty tier, and a statement-fidelity sign-off.

The exact counts (harvested, curated, axiom-clean, fidelity-audited) are written
to `statlean-v0.1.stats.json` by the build, so this README does not pin a number
that can drift.

## Record schema (`statlean-v0.1.jsonl`)

One JSON object per line:

- `id`: stable slug (`module-tail` + theorem short name).
- `source`: `{library, repo, module}`.
- `concept_family`: the FormalSLT spine family this theorem sits in.
- `concept_tags`: subset of the 24 concept tags (Markov, Chebyshev, Hoeffding,
  Bernstein, Bennett, Chernoff, sub-Gaussian, sub-Gamma, Azuma, McDiarmid, union
  bound, tail bound, MGF, confidence sequence, PAC-Bayes, KL divergence,
  Rademacher, VC dimension, covering / chaining, ERM, stability, sample
  statistics, Glivenko-Cantelli, Bernoulli, risk).
- `informal_statement`: natural-language statement seeded from the `/-- … -/`
  docstring (falls back to the one-line role when no docstring exists).
- `lean_statement`: the verbatim Lean signature, from the declaration head down
  to (not including) the proof body.
- `lean_proof_pointer`: `path/to/Module.lean:line` of the declaration.
- `dependency_edges`: `{imports: [FormalSLT.…], lemma_uses: [intra-corpus calls]}`.
- `axiom_profile`: live `#print axioms` result, one of `clean{…}`, `axiom-free`,
  or a `NONSTANDARD:…` flag.
- `difficulty`: `easy` / `medium` / `hard`, from proof length plus dependency
  fan-in (heuristic, not a human grade).
- `fidelity`: `{checked, flagged, signed_off, lint}` from the non-vacuity gate.
- `qualified_name`, `kind`, `role`: bookkeeping.

## How it is built

```
scripts/build_statlean_manifest.py            # full harvest + curate + fidelity + axioms
scripts/build_statlean_manifest.py --no-axioms   # skip the live #print axioms pass
scripts/build_statlean_manifest.py --limit N     # cap the curated task count
```

The harvester reuses the existing tooling: the 24-concept vocabulary from
`scripts/generate_theorem_index.py`, the family / declaration / module spine from
`docs/proof-frontier-manifest.json`, the non-vacuity lint
`scripts/statement_fidelity_check.py`, and the axiom-profile convention from
`scripts/check_axioms.sh`. It is read-only over the `.lean` sources.

### Fidelity gate

Each curated task is passed through `statement_fidelity_check.py`, which lints the
three near-vacuity shapes (quantifier inversion `∀var ∃const`, trivial `True`
conclusion, `False` hypothesis) and honors a `-- fidelity:` sign-off. A task that
the lint flags without a sign-off is recorded as `flagged: true`, so the benchmark
never silently ships a vacuous statement as a target.

### Axiom gate

The build emits one batched scratch that imports every selected module and runs
`open <namespace> in #print axioms <name>` for each task. A task is `clean` only
if its axioms are a subset of `{propext, Classical.choice, Quot.sound}`; anything
else (notably `sorryAx`, or `Lean.ofReduceBool` from `native_decide`) is flagged
`NONSTANDARD`.

## Roadmap: v0.2 net-new classical-statistics tasks

The harvest is concentration / learning-theory heavy because that is what
FormalSLT proves. The visible gap is **classical inferential statistics**, which a
source scan confirms is absent from the library today (no MLE, unbiasedness,
Cramér-Rao, Fisher information, Horvitz-Thompson, bootstrap, or Rao-Blackwell
declarations). v0.2 plans roughly 30 to 50 net-new tasks to cover it:

- **Point estimation**: sample-mean unbiasedness for the population mean;
  Bessel-corrected sample-variance unbiasedness; MLE for the Bernoulli / Gaussian
  mean; bias / variance / MSE decomposition.
- **Information and efficiency**: Fisher information of a one-parameter family;
  the Cramér-Rao lower bound for an unbiased estimator; the Rao-Blackwell
  improvement step.
- **Survey / design-based estimation**: the Horvitz-Thompson estimator and its
  unbiasedness under known inclusion probabilities.
- **Resampling**: the plug-in / bootstrap mean and a finite-population variance
  identity for it.
- **Asymptotics (finite-n surrogates first)**: consistency of the sample mean as
  a tail statement built on the Chebyshev / Hoeffding tasks already harvested.

These extend the same schema; each will ship sorry-free with a fidelity sign-off
and a live axiom profile before it enters the benchmark.

## Companion baseline (scope only, not built in this release)

The intended use of StatLean is a **retrieval + proof-repair** baseline:

1. Index every harvested theorem by its informal statement and concept tags.
2. Given a held-out target statement, retrieve the k nearest harvested theorems
   and their proofs as in-context exemplars.
3. Ask a prover to produce a candidate proof; check it in the FormalSLT
   toolchain; on failure, feed the Lean error back for one repair round.
4. Score on compile success, axiom cleanliness, and statement-fidelity pass,
   not token overlap.

The dependency edges and difficulty tiers in each record exist to support this:
retrieval can prefer lower-difficulty exemplars sharing a concept tag, and the
`lemma_uses` graph gives the proof-repair loop a candidate set of supporting
lemmas. Building the baseline is out of scope for v0.1.

## Relation to other Lean work

StatLean draws its tasks from FormalSLT, which is itself complementary to the
adjacent Lean learning-theory projects listed in `../related-work.md`
(`lean-rademacher`, `lean-stat-learning-theory`, `formal-learning-theory-kernel`).
StatLean adds no priority claim over any of them; it packages checked statistics
theorems as a retrieval-and-repair benchmark, which those libraries do not set
out to do.
