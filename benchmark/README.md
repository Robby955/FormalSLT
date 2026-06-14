# FormalSLT Coverage Benchmark

This directory contains a single Python script (`g4_coverage.py`) that
inventories the theorem and lemma surface of FormalSLT by category and emits
a machine-regenerable coverage table and figure.

## Regenerating

```
python3 benchmark/g4_coverage.py
```

Outputs land in `benchmark/output/`:

- `coverage_table.txt` — plain-text, human-readable
- `coverage_table.csv` — machine-readable; import into any spreadsheet
- `coverage_figure.png` (or `.svg` if matplotlib is absent)

No dependencies beyond the Python 3 standard library.  `matplotlib` is used
for the figure if present; otherwise a plain SVG bar chart is written.

To point at a different source tree or output directory:

```
python3 benchmark/g4_coverage.py --src /path/to/FormalSLT --out /path/to/out
```

## What is counted

The script scans all `.lean` files under `FormalSLT/` (the library source
directory), skipping `Test/` and `Generated/` subdirectories.  Each file is
routed to one of ten benchmark categories based on its directory path.  The
script counts:

- `theorem` declarations (top-level, not inside namespaces with indent)
- `lemma` declarations (same)
- Lines of Lean code (total, including comments and blank lines)
- Whether any real `sorry` / `admit` tactic call appears (documentation
  mentions inside backtick spans and comment lines are excluded)

## Benchmark categories

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

## Peer library comparison columns

The CSV contains placeholder columns for three peer libraries.  These are
listed because they appeared in reviewer feedback; **none of the peer coverage
numbers have been verified against the actual Lean sources**.

- **Sonoda et al. 2025** — arXiv:2503.19605, Lean 4, partial SLT formalization
- **Zhang-Lee-Liu 2026** — arXiv:2602.02285, Lean 4, partial SLT formalization
- **Karayel-Tan 2023** — AFP 2023, Isabelle/HOL (not Lean 4)

All peer columns are marked `TODO/UNVERIFIED` in the output.  They must be
filled in manually after checking each library's source before any of this
appears in a paper or talk.

## Honest framing

FormalSLT is one of at least three Lean 4 projects formalizing aspects of
statistical learning theory.  Nothing in this benchmark claims primacy or
completeness relative to peer libraries; it only reports what is present in
FormalSLT's source at the time of regeneration.

The benchmark is local-only; it is not pushed or published.
