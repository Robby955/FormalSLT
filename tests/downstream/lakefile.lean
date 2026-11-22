import Lake
open Lake DSL

package «formal-slt-downstream-smoke»

require «formal-slt» from "../.."

@[default_target]
lean_lib Downstream where
  globs := #[`Downstream.+]
