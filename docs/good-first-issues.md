# Good First Issues

This list is for contributors who want a useful first PR without taking on a
flagship theorem. Keep PRs small and include the checks you ran.

## Documentation

- Add a missing theorem-map row for a theorem that already appears in a module.
- Improve a module docstring so it states the theorem, assumptions, proof
  strategy, and current boundaries more clearly.
- Add one short example to `docs/how-to-read-the-proofs.md` showing how to find
  a theorem from the README table.
- Check public-facing wording for overclaims. Prefer "finite scaffold",
  "finite bridge", and "current boundary" when those phrases match the theorem.

## Examples and audits

- Add a representative theorem to `examples/CheckShowcaseTheorems.lean` with
  both `#check` and `#print axioms`.
- Add a small topic-specific checker under `examples/` for a theorem family
  that has several public declarations.
- Confirm that a recently added public theorem has only
  `[propext, Classical.choice, Quot.sound]` in its axiom print.

## Small Lean proof tasks

- Prove a local algebra helper that removes repeated `ring` or `linarith`
  blocks from one module.
- Generalize a private helper lemma only when the generalized statement is
  actually used by the next theorem.
- Replace a fragile proof block with a shorter proof that uses an existing
  Mathlib lemma.
- Add a finite, explicitly scoped wrapper theorem around an existing result
  when the wrapper makes the public statement easier to read.

## Mathlib-facing cleanup

- Compare a local helper against Mathlib and document whether an equivalent
  theorem already exists.
- Move a pure order, algebra, or finite-sum helper toward Mathlib style in a
  separate PR before any upstream attempt.
- Add an entry to `docs/upstream-candidates.md` with the exact local theorem
  name, module, and reason it may be broadly useful.

## Good issue labels

Suggested labels for a public repository:

- `good first issue`
- `docs`
- `examples`
- `Lean`
- `theorem-map`
- `proof cleanup`
- `Mathlib candidate`

## Not first issues

These are important but too broad for a first PR:

- continuous Dudley over arbitrary classes;
- sharp McDiarmid/product-kernel decomposition;
- continuous-posterior PAC-Bayes;
- large namespace refactors;
- changing theorem statements without reviewing downstream uses.
