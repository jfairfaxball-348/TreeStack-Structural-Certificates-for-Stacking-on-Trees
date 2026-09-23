import Lake

open Lake DSL

package "treestack" where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "065356127b1dc0016f66b7283ce0ce2c4055aa55"

@[default_target]
lean_lib TreeStack

/-- Palomar's protected Mathlib-only statement surface. -/
lean_lib Challenge where
  roots := #[`Challenge]

/-- Palomar's proved solution surface. -/
lean_lib Solution where
  roots := #[`Solution]
