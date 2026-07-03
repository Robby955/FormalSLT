import Lake
open Lake DSL

package «formal-slt» where
  -- Formal Statistical Learning Theory in Lean 4.
  -- Verified results: Rademacher complexity, Massart's lemma,
  -- Sauer-Shelah, VC-style sample complexity, ERM generalization.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "25b7ac7d0cf8eef34ced5525f4a62b7613ad649b"

meta if get_config? env == some "dev" then
  require «doc-gen4» from git
    "https://github.com/leanprover/doc-gen4" @ "d555f83"

@[default_target]
lean_lib FormalSLT where
  roots := #[`FormalSLT]
