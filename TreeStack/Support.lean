import Mathlib
import TreeStack.Defect

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The two orientations of a tree edge determine disjoint vertex sides. -/
theorem vertices_disjoint_reverseBranch (B : OrientedBranch T) :
    Disjoint B.vertices B.reverseBranch.vertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hxR
  have hxComp : x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hrootComp : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootx : B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrootComp hxComp
  have hxRComp : x ∈ B.reverseBranch.component.supp := by
    simpa [vertices] using hxR
  have hparentComp : B.parent ∈ B.reverseBranch.component.supp := by
    simpa using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem :
        B.reverseBranch.root ∈ B.reverseBranch.component.supp)
  have hparentxR :
      B.reverseBranch.deletedGraph.Reachable B.parent x :=
    B.reverseBranch.component.reachable_of_mem_supp hparentComp hxRComp
  have hparentx : B.deletedGraph.Reachable B.parent x := by
    simpa [deletedGraph, reverseBranch] using hparentxR
  have hreach : B.deletedGraph.Reachable B.root B.parent :=
    hrootx.trans hparentx.symm
  have hbridge : T.graph.IsBridge s(B.root, B.parent) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) B.adj
  exact (SimpleGraph.isBridge_iff.mp hbridge) (by
    simpa [deletedGraph] using hreach)

/-- Every vertex lies on one of the two sides of an oriented tree edge. -/
theorem mem_vertices_or_mem_reverseBranch
    (B : OrientedBranch T) (x : V) :
    x ∈ B.vertices ∨ x ∈ B.reverseBranch.vertices := by
  classical
  by_cases hxr : x = B.root
  · left
    simpa [hxr] using B.root_mem_vertices
  · rcases exists_incidentBranch_mem_of_ne_root (T := T) B.root hxr with
      ⟨u, hu, hx⟩
    by_cases hup : u = B.parent
    · right
      subst u
      simpa [reverseBranch, incidentBranch] using hx
    · left
      let c : B.Child :=
        { vertex := u
          adj := hu.symm
          ne_parent := hup }
      have hxChild : x ∈ (B.childBranch c).vertices := by
        simpa [c, childBranch, incidentBranch] using hx
      exact B.childBranch_vertices_subset c hxChild

/-- The two edge sides partition the whole finite vertex type. -/
theorem vertices_union_reverseBranch (B : OrientedBranch T) :
    B.vertices ∪ B.reverseBranch.vertices = (Finset.univ : Finset V) := by
  classical
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  exact B.mem_vertices_or_mem_reverseBranch x

/-- At least one edge side is occupied as soon as the configuration has a
positive pile somewhere. -/
theorem occupied_or_reverse_occupied
    (C : Configuration V) (B : OrientedBranch T)
    {x : V} (hx : 0 < C x) :
    B.Occupied C ∨ B.reverseBranch.Occupied C := by
  rcases B.mem_vertices_or_mem_reverseBranch x with hxB | hxR
  · exact Or.inl ⟨x, hxB, hx⟩
  · exact Or.inr ⟨x, hxR, hx⟩

/-- A retained support edge is a tree edge with occupied configuration support
on both sides.  This is the in-place substitute for transporting the whole
problem to a subtype-valued minimal support tree. -/
def SupportEdge (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C ∧ B.reverseBranch.Occupied C

@[simp] theorem supportEdge_reverse_iff
    (C : Configuration V) (B : OrientedBranch T) :
    B.reverseBranch.SupportEdge C ↔ B.SupportEdge C := by
  simp [SupportEdge, and_comm]

/-- If the exterior side of an oriented edge is empty, its message remains
literally `EMPTY`, and therefore contributes zero to the rooted score. -/
theorem score_eq_effectiveInput_of_reverse_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    score T C B.root = B.effectiveInput C := by
  rw [score_eq_effectiveInput_add_reverse C B,
    branchMessage_eq_empty_of_not_occupied C B.reverseBranch hEmpty]
  rfl

/-- The already-proved local defect classification applies directly to every
retained support edge, without changing the ambient vertex type. -/
theorem defectEdgeState_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by
  exact B.defectEdgeState_of_scores_nonpos C
    hEdge.1 hEdge.2 (hScores B.root) (hScores B.parent)

end OrientedBranch

/-- If all positive piles are concentrated at one vertex, that vertex's rooted
score is exactly its pile size.  Every incident branch is genuinely empty,
not an integer-message zero branch. -/
theorem score_eq_of_support_subset_singleton
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSupport : ∀ v, 0 < C v → v = r) :
    score T C r = (C r : ℤ) := by
  classical
  have hNoOccupied (u : V) :
      ¬ IsOccupiedRootNeighbor T C r u := by
    rintro ⟨hAdj, hOcc⟩
    rcases hOcc with ⟨w, hw, hpos⟩
    have hwr : w = r := hSupport w hpos
    subst w
    exact (incidentBranch T r u hAdj).parent_not_mem_vertices hw
  have hTerm (u : V) :
      rootMessageTerm T C r u = 0 :=
    rootMessageTerm_eq_zero_of_not_occupied T C r (hNoOccupied u)
  rw [score, rootMessageSum]
  simp_rw [hTerm]
  simp

/-- Under all-nonpositive scores, every occupied vertex has another distinct
occupied vertex.  In particular, a nonzero counterconfiguration cannot have
singleton support. -/
theorem exists_other_occupied_of_all_scores_nonpos
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V} (hr : 0 < C r) :
    ∃ v, v ≠ r ∧ 0 < C v := by
  by_contra hOther
  have hSupport : ∀ v, 0 < C v → v = r := by
    intro v hv
    by_contra hvr
    exact hOther ⟨v, hvr, hv⟩
  have hEq := score_eq_of_support_subset_singleton T C r hSupport
  have hPos : 0 < score T C r := by
    rw [hEq]
    exact_mod_cast hr
  exact (not_lt_of_ge (hScores r)) hPos

end TreeStack
