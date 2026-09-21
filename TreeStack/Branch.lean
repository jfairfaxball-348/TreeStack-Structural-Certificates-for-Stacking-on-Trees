import Mathlib
import TreeStack.Basic

namespace TreeStack

/-- An oriented branch is determined by an edge `root → parent`.
Its vertex set is the component containing `root` after deleting that edge. -/
structure OrientedBranch {V : Type*} [Fintype V] (T : FiniteTree V) where
  root : V
  parent : V
  adj : T.graph.Adj root parent

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The tree with the boundary edge of an oriented branch deleted. -/
noncomputable def deletedGraph (B : OrientedBranch T) : SimpleGraph V :=
  T.graph.deleteEdges {s(B.root, B.parent)}

/-- The connected component on the root side of the deleted boundary edge. -/
noncomputable def component (B : OrientedBranch T) :
    B.deletedGraph.ConnectedComponent :=
  B.deletedGraph.connectedComponentMk B.root

/-- The finite vertex set of the oriented branch. -/
noncomputable def vertices (B : OrientedBranch T) : Finset V := by
  classical
  exact B.component.supp.toFinset

/-- Cardinality of an oriented branch, used as the recursion measure later. -/
noncomputable def card (B : OrientedBranch T) : ℕ :=
  B.vertices.card

@[simp] theorem root_ne_parent (B : OrientedBranch T) :
    B.root ≠ B.parent :=
  B.adj.ne

@[simp] theorem root_mem_vertices (B : OrientedBranch T) :
    B.root ∈ B.vertices := by
  classical
  rw [vertices, Set.mem_toFinset]
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- In a tree, the parent endpoint is not in the root-side component after
deleting the boundary edge. -/
theorem parent_not_mem_vertices (B : OrientedBranch T) :
    B.parent ∉ B.vertices := by
  classical
  intro hp
  have hp' : B.parent ∈ B.component.supp := by
    rw [vertices, Set.mem_toFinset] at hp
    exact hp
  have hr' : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root B.parent :=
    B.component.reachable_of_mem_supp hr' hp'
  have hbridge : T.graph.IsBridge s(B.root, B.parent) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) B.adj
  have hnot :
      ¬ (T.graph.deleteEdges {s(B.root, B.parent)}).Reachable B.root B.parent :=
    SimpleGraph.isBridge_iff.mp hbridge
  exact hnot (by simpa [deletedGraph] using hreach)

/-- Every oriented branch is nonempty. -/
theorem vertices_nonempty (B : OrientedBranch T) :
    B.vertices.Nonempty :=
  ⟨B.root, B.root_mem_vertices⟩

theorem card_pos (B : OrientedBranch T) : 0 < B.card := by
  classical
  simpa [card] using Finset.card_pos.mpr B.vertices_nonempty

/-- The branch is a proper subset of the whole finite vertex set. -/
theorem vertices_ssubset_univ (B : OrientedBranch T) :
    B.vertices ⊂ (Finset.univ : Finset V) := by
  classical
  rw [Finset.ssubset_iff_of_subset (Finset.subset_univ B.vertices)]
  exact ⟨B.parent, Finset.mem_univ _, B.parent_not_mem_vertices⟩

/-- The branch-cardinality measure is strictly smaller than the whole tree. -/
theorem card_lt_total (B : OrientedBranch T) :
    B.card < Fintype.card V := by
  classical
  simpa [card] using Finset.card_lt_card B.vertices_ssubset_univ

/-- A child choice at the root of an oriented branch. -/
structure Child (B : OrientedBranch T) where
  vertex : V
  adj : T.graph.Adj B.root vertex
  ne_parent : vertex ≠ B.parent

/-- The oriented branch hanging below a chosen child. -/
def childBranch (B : OrientedBranch T) (c : B.Child) : OrientedBranch T where
  root := c.vertex
  parent := B.root
  adj := c.adj.symm

@[simp] theorem childBranch_root (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).root = c.vertex := rfl

@[simp] theorem childBranch_parent (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).parent = B.root := rfl

end OrientedBranch

end TreeStack
