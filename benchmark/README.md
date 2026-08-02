# FormalSLT Benchmarks

This directory contains small, reproducible Python benchmarks that accompany
the checked Lean surface. They use only the Python 3 standard library unless a
script says otherwise. Benchmark output is empirical evidence or repository
metadata, not an extension of the formal theorem statement.

## Continuous time-uniform PAC-Bayes CPU smoke test

`time_uniform_continuous_pac_bayes_smoke.py` exercises one exact synthetic
specialization of
`FormalSLT.PACBayes.TimeUniformContinuous.timeUniformContinuousPACBayes_bound`.
It uses:

- hypothesis space `R^d`;
- spherical Gaussian prior `N(0, sigma_p^2 I)`;
- fixed spherical Gaussian posterior `N(kappa a, sigma_q^2 I)` with `||a|| = 1`;
- iid observations `Z_i ~ N(0, 1)`;
- bounded loss `ell(theta, z) = 1{z <= a dot theta}`;
- a preregistered finite lambda grid with Bonferroni correction.

The posterior Gibbs population risk, per-observation posterior expected loss,
and spherical Gaussian KL are analytic. No posterior Monte Carlo is used. Each
posterior configuration is evaluated separately, so the script does not claim
a data-dependent posterior choice that the current process theorem does not
provide.

Fast deterministic checks:

```bash
python3 benchmark/time_uniform_continuous_pac_bayes_smoke.py --self-test
python3 benchmark/time_uniform_continuous_pac_bayes_smoke.py --quick
```

Default run:

```bash
python3 benchmark/time_uniform_continuous_pac_bayes_smoke.py
```

The default run uses 500 independent streams, horizon 2,000, familywise
`delta = 0.05` over the fixed lambda grid, and seed `20260802`. It writes:

- `benchmark/output/time_uniform_continuous_pac_bayes_smoke.json`
- `benchmark/output/time_uniform_continuous_pac_bayes_smoke.csv`

The script reports finite-horizon violation frequency, a Wilson interval,
bound tightness, the best observed prefix, and the fraction of horizon bounds
below one. It is a numerical implementation smoke test. It is not a Lean proof
check, a proof of empirical coverage, a data-dependent-posterior theorem, or a
neural-network generalization theorem.

## FormalSLT coverage inventory

`g4_coverage.py` inventories the theorem and lemma surface of FormalSLT by
category and emits a machine-regenerable coverage table and figure.

### Regenerating

```bash
python3 benchmark/g4_coverage.py
```

Outputs land in `benchmark/output/`:

- `coverage_table.txt` — plain-text, human-readable
- `coverage_table.csv` — machine-readable; import into any spreadsheet
- `coverage_figure.png` (or `.svg` if matplotlib is absent)

No dependencies beyond the Python 3 standard library are required.
`matplotlib` is used for the figure if present; otherwise a plain SVG bar chart
is written.

To point at a different source tree or output directory:

```bash
python3 benchmark/g4_coverage.py --src /path/to/FormalSLT --out /path/to/out
```

### What is counted

The script scans all `.lean` files under `FormalSLT/` (the library source
directory), skipping `Test/` and `Generated/` subdirectories. Each file is
routed to one of ten benchmark categories based on its directory path. The
script counts:

- `theorem` declarations (top-level, not inside namespaces with indent)
- `lemma` declarations (same)
- Lines of Lean code (total, including comments and blank lines)
- Whether any real `sorry` / `admit` tactic call appears (documentation
  mentions inside backtick spans and comment lines are excluded)

### Benchmark categories

| Category | What it covers |
|---|---|
| Concentration | Azuma, McDiarmid, sub-Gamma, Bennett |
| Rademacher | Symmetrization, contraction, high-prob bounds, ERM generalization |
| VC Theory | Sauer-Shelah, VC dimension, sample complexity |
| Covering / Dudley | Covering numbers, Dudley chaining, entropy integral |
| PAC-Bayes | McAllester, Seeger, Bernstein, KL, Gaussian certificates, compiler |
| Stability | Bousquet-Elisseeff uniform stability, RKHS regularised ERM |
| Anytime-Valid | Ville maximal inequality, sub-Gamma confidence sequences |
| Online-to-PAC | Cesa-Bianchi-Conconi-Gentile regret conversion |
| Probability Foundations | IID concentration, union bound, sub-Gaussian max, MGF |
| Flagship Meta | Test-time meta composition; online population decomposition |

### Peer library comparison columns

The CSV contains placeholder columns for three peer libraries. These are listed
because they appeared in reviewer feedback; **none of the peer coverage
numbers have been verified against the actual Lean sources**.

- **Sonoda et al. 2025** — arXiv:2503.19605, Lean 4, partial SLT formalization
- **Zhang-Lee-Liu 2026** — arXiv:2602.02285, Lean 4, partial SLT formalization
- **Karayel-Tan 2023** — AFP 2023, Isabelle/HOL (not Lean 4)

All peer columns are marked `TODO/UNVERIFIED` in the output. They must be filled
in manually after checking each library's source before any of this appears in
a paper or talk.

## Honest framing

FormalSLT is one of at least three Lean 4 projects formalizing aspects of
statistical learning theory. Nothing in the coverage inventory claims primacy
or completeness relative to peer libraries; it only reports what is present in
FormalSLT's source at regeneration time.

Generated benchmark outputs are local artifacts unless they are explicitly
reviewed and committed. Do not describe a smoke-test run as a formal proof or a
scientific validation study.
