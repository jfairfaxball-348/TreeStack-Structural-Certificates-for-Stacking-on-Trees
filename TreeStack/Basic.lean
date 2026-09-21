import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace TreeStack

/-- A pebble configuration on a vertex type. -/
abbrev Configuration (V : Type*) := V → ℕ

/-- Total number of pebbles in a finite configuration. -/
def mass {V : Type*} [Fintype V] (C : Configuration V) : ℕ :=
  ∑ v, C v

/-- The (set-valued) support of a configuration. -/
def support {V : Type*} (C : Configuration V) : Set V :=
  {v | 0 < C v}

/-- A finite simple tree, using Mathlib's connected-acyclic tree predicate. -/
structure FiniteTree (V : Type*) [Fintype V] where
  graph : SimpleGraph V
  isTree : graph.IsTree

@[simp] theorem mem_support_iff {V : Type*} {C : Configuration V} {v : V} :
    v ∈ support C ↔ 0 < C v := Iff.rfl

end TreeStack
