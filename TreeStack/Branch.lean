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

/-- The child edge differs from the boundary edge of its parent branch. -/
theorem childEdge_ne_boundary (B : OrientedBranch T) (c : B.Child) :
    s(B.root, c.vertex) ≠ s(B.root, B.parent) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact c.ne_parent h.2
  · exact B.root_ne_parent h.1

/-- Every vertex on a genuine child side also lies on the parent branch side.
The proof uses the fact that both deleted edges are bridges in the tree:
a walk in the child side cannot cross the parent's boundary edge without first
reaching the parent-branch root while avoiding the child edge. -/
theorem childBranch_vertices_subset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊆ B.vertices := by
  classical
  intro x hx
  rw [vertices, Set.mem_toFinset] at hx ⊢
  have hc :
      c.vertex ∈ (B.childBranch c).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x :=
    (B.childBranch c).component.reachable_of_mem_supp hc hx
  have hreachChild' :
      (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex x := by
    simpa [deletedGraph, childBranch] using hreachChild
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreachChild' with
    ⟨p, hchildEdge⟩
  have hparentEdge : s(B.root, B.parent) ∉ p.edges := by
    intro hp
    have hrootSupp : B.root ∈ p.support :=
      p.fst_mem_support_of_mem_edges hp
    let q : T.graph.Walk c.vertex B.root := p.takeUntil B.root hrootSupp
    have hqChild : s(c.vertex, B.root) ∉ q.edges := by
      intro hq
      exact hchildEdge (p.edges_takeUntil_subset_edges hrootSupp hq)
    have hreachRoot :
        (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex B.root :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q, hqChild⟩
    have hbridge : T.graph.IsBridge s(c.vertex, B.root) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) c.adj.symm
    exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot
  have hreachInParent :
      B.deletedGraph.Reachable c.vertex x := by
    simpa [deletedGraph] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hparentEdge⟩)
  have hrootChild :
      B.deletedGraph.Adj B.root c.vertex := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨c.adj, ?_⟩
    simpa using B.childEdge_ne_boundary c
  have hrootReach : B.deletedGraph.Reachable B.root x :=
    hrootChild.reachable.trans hreachInParent
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hrootReach).symm

/-- A genuine child branch is a strict subset of its parent branch. -/
theorem childBranch_vertices_ssubset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊂ B.vertices := by
  classical
  rw [Finset.ssubset_iff_of_subset (B.childBranch_vertices_subset c)]
  refine ⟨B.root, B.root_mem_vertices, ?_⟩
  simpa using (B.childBranch c).parent_not_mem_vertices

/-- Child-branch cardinality strictly decreases relative to the parent branch.
This is the recursion measure needed for branch messages. -/
theorem childBranch_card_lt (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).card < B.card := by
  classical
  simpa [card] using Finset.card_lt_card (B.childBranch_vertices_ssubset c)

/-- Any tree edge leaving an oriented branch is exactly its deleted boundary
edge.  Every other adjacent edge survives in the deleted graph and therefore
keeps both endpoints in the same connected component. -/
theorem edge_leaving_vertices_eq_boundary (B : OrientedBranch T)
    {u v : V} (hu : u ∈ B.vertices) (hv : v ∉ B.vertices)
    (huv : T.graph.Adj u v) :
    s(u, v) = s(B.root, B.parent) := by
  classical
  by_contra hne
  have hu' : u ∈ B.component.supp := by
    simpa [vertices] using hu
  have hadjDeleted : B.deletedGraph.Adj u v := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    exact ⟨huv, by simpa using hne⟩
  have hv' : v ∈ B.component.supp :=
    B.component.mem_supp_of_adj_mem_supp hu' hadjDeleted
  exact hv (by simpa [vertices] using hv')

/-- The external boundary vertex has no neighbor inside the branch other than
the branch root. -/
theorem eq_root_of_mem_vertices_adj_parent (B : OrientedBranch T)
    {u : V} (hu : u ∈ B.vertices) (hup : T.graph.Adj u B.parent) :
    u = B.root := by
  have hEdge :=
    B.edge_leaving_vertices_eq_boundary hu B.parent_not_mem_vertices hup
  rw [Sym2.eq_iff] at hEdge
  rcases hEdge with h | h
  · exact h.1
  · exact (B.root_ne_parent h.2.symm).elim


/-- Every non-root vertex of an oriented branch lies in one of the genuine
child branches at the branch root.  This is the existence half of the child
decomposition used by the constructive boundary induction; sibling
disjointness supplies uniqueness. -/
theorem exists_childBranch_mem_of_mem_vertices_ne_root
    (B : OrientedBranch T) {x : V}
    (hx : x ∈ B.vertices) (hxr : x ≠ B.root) :
    ∃ c : B.Child, x ∈ (B.childBranch c).vertices := by
  classical
  have hxComp : x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hrComp : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  rcases hreach.exists_isPath with ⟨p, hp⟩
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr p with
    ⟨v, hrv, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hrv p').mp hp
  have hrootNot : B.root ∉ p'.support := hpData.2
  have hrvData := hrv
  rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hrvData
  rcases hrvData with ⟨hrvT, hedge⟩
  have hvne : v ≠ B.parent := by
    intro hvp
    subst v
    simp at hedge
  let c : B.Child :=
    { vertex := v
      adj := hrvT
      ne_parent := hvne }
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let q : T.graph.Walk v x := p'.mapLe hle
  have havoid : s(v, B.root) ∉ q.edges := by
    intro he
    have he' : s(v, B.root) ∈ p'.edges := by
      simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hrootNot (p'.snd_mem_support_of_mem_edges he')
  let q' : (T.graph.deleteEdges {s(v, B.root)}).Walk v x :=
    q.toDeleteEdges {s(v, B.root)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x := by
    change (T.graph.deleteEdges {s(v, B.root)}).Reachable v x
    exact ⟨q'⟩
  refine ⟨c, ?_⟩
  rw [vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hreachChild).symm

end OrientedBranch

end TreeStack
