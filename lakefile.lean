import Lake
open Lake DSL

package «formal-slt» where
  -- Formal Statistical Learning Theory in Lean 4.
  -- Verified results: Rademacher complexity, Massart's lemma,
  -- Sauer-Shelah, VC-style sample complexity, ERM generalization.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

meta if get_config? env == some "dev" then
  require «doc-gen4» from git
    "https://github.com/leanprover/doc-gen4" @ "v4.32.2"

@[default_target]
lean_lib FormalSLT where
  roots := #[`FormalSLT]
