import Lake

open Lake DSL

package "treestack" where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib TreeStack

/-- Palomar's protected Mathlib-only statement surface. -/
lean_lib Challenge where
  roots := #[`Challenge]

/-- Palomar's proved solution surface. -/
lean_lib Solution where
  roots := #[`Solution]
