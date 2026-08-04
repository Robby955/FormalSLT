# Contributing

Thanks for helping improve FormalSLT. The project aims to be readable,
machine-checked statistical learning theory: small theorem steps, explicit
assumptions, reproducible builds, and careful public claims.

## Branch and PR flow

- Open pull requests against the repository default branch, currently `main`.
- Use a topic branch with a descriptive name, for example
  `feat/lean-small-helper-lemma` or `docs/theorem-map-cleanup`.
- Keep theorem PRs small. A good PR usually proves one public theorem or one
  cluster of private helper lemmas for that theorem.
- Do not push directly to a protected default branch. If GitHub shows branch
  protection warnings or disabled protection on a fork, follow the PR flow and
  let maintainers manage repository settings.
- Chained PRs are fine when there is a real dependency. Say clearly which PR
  your branch builds on and whether it can be reviewed independently.

## Contribution responsibility

Review focuses on correctness, clarity, maintainability, and fit with the
theorem roadmap. The standard is the same for every contribution:

- You are responsible for the final code, proof, prose, and citations.
- Every Lean declaration must compile with no `sorry`, no `admit`, and no
  custom axioms or constants.
- Do not paste private data, proprietary text, or unverifiable citations into
  the repo.
- Describe the checks you ran in the PR description.
- Remove phrasing that overstates the result, sounds promotional, or hides
  assumptions. Prefer precise labels such as "Scope", "Assumptions", and
  "Current boundaries".

## Proof style

1. **No sorry, no admit.** Every merged declaration must be fully proved.
2. **Axioms: [propext, Classical.choice, Quot.sound] only.** Verify with `#print axioms`.
3. **Assumptions in types.** If a theorem requires bounded loss, the type signature says so. Do not hide assumptions behind hypotheses that are easy to miss.
4. **One theorem per PR.** Each result is a focused addition to the chain.
5. **Document non-claims.** If a theorem has a scope gap (e.g., Azuma constant instead of sharp McDiarmid), state it in the module docstring.

## Module docstrings

Every module must have a `/-! ... -/` docstring that states:

- What is proved (main theorem name and informal statement)
- The proof strategy (2-3 sentences)
- Current boundaries and assumptions
- Whether sorry/admit/custom axioms are used (should always be "none")

Every new module must also carry the repository copyright and author header.
Follow the subject ownership and import direction in
[`ARCHITECTURE.md`](./ARCHITECTURE.md); avoid adding new top-level implementation
files when an existing subject directory owns the result.

## Naming conventions

- Theorem and lemma names follow nearby Mathlib/FormalSLT APIs, including
  descriptive camelCase segments such as `finiteClassUniformDeviationUnionBound`.
- Definitions use `camelCase`.
- Module names use `PascalCase`.
- Namespace hierarchy follows the module path: `FormalSLT.VC.BinaryVCBridge`.

## Adding a new theorem

1. Create the `.lean` file in the appropriate subdirectory.
2. Write the module docstring.
3. Prove the theorem. No sorry, no admit.
4. Add `import` to `FormalSLT.lean`.
5. Run `lake exe cache get` first in fresh worktrees, then
   `lake build FormalSLT`, and verify it compiles.
6. Run `#print axioms <your_theorem>` and verify only standard axioms.
7. Update `README.md` (module structure, main theorems table, roadmap).
8. Update `docs/theorem-map.md` and `docs/roadmap.md`.
9. Open a PR against `main`.

## Build, tests, and audits

```bash
# First time in a checkout or worktree (downloads pre-built Mathlib oleans):
lake exe cache get
lake build FormalSLT

# Run the v0.1 theorem and axiom checker:
lake env lean examples/CheckV01Usability.lean

# Verify axioms for a specific theorem:
printf 'import FormalSLT\n#print axioms FormalSLT.VC.SampleComplexity.vc_erm_excessRisk_tail\n' | lake env lean --stdin

# Proof-debt scans:
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples

# Whitespace check:
git diff --check
```

If `lake` is not on your shell path, use `~/.elan/bin/lake` for the same
commands. Avoid starting a cold Mathlib source build; it is slow, disk-heavy,
and usually means the cache step was skipped.

The current test surface is Lean-native: full library builds, example checker
files, `#check` / `#print axioms` audits, and CI scans for proof debt. There is
no JavaScript or Python test suite in this repo because the library itself is a
Lean 4 formalization.

## What we are looking for

- Theorems that extend the existing chain in small, reviewable steps.
- Helper lemmas that could be upstreamed to Mathlib.
- Bug reports, proof simplifications, and clearer theorem statements.
- Documentation improvements that make the proof ladder easier to read.
- Example checker additions for public theorem families.

Good first contributions are listed in
[docs/good-first-issues.md](./docs/good-first-issues.md).

## Out of scope

- Proofs that use `sorry` or `admit` "to be filled in later".
- Large refactors that change the namespace structure without a concrete
  benefit.
- New dependencies beyond Lean 4 and Mathlib.
- Headline claims that go beyond the theorem statement.
