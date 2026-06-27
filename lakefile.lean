import Lake
open Lake DSL

package «formal-slt» where
  -- Formal Statistical Learning Theory in Lean 4.
  -- Verified results: Rademacher complexity, Massart's lemma, a VC
  -- sample-complexity bridge over Mathlib's Sauer-Shelah, ERM generalization.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "25b7ac7d0cf8eef34ced5525f4a62b7613ad649b"

@[default_target]
lean_lib FormalSLT where
  roots := #[`FormalSLT]
