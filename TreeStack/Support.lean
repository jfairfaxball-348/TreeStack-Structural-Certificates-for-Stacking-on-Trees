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
    have hroot := B.reverseBranch.root_mem_vertices
    simpa [vertices] using hroot
  have hparentxR :
      B.reverseBranch.deletedGraph.Reachable B.parent x :=
    B.reverseBranch.component.reachable_of_mem_supp hparentComp hxRComp
  have hparentx : B.deletedGraph.Reachable B.parent x := by
    change
      (T.graph.deleteEdges {s(B.root, B.parent)}).Reachable B.parent x
    rw [Sym2.eq_swap]
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


/-- The occupied exterior side of a retained edge lies on the reverse side of
every genuine child edge.  This is the one-step separation fact that makes the
retained support core path-closed without changing the ambient vertex type. -/
theorem reverse_child_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).reverseBranch.Occupied C := by
  rcases hEdge.2 with ⟨y, hyReverseB, hyPos⟩
  have hyNotChild : y ∉ (B.childBranch c).vertices := by
    intro hyChild
    have hyB : y ∈ B.vertices :=
      B.childBranch_vertices_subset c hyChild
    exact
      (Finset.disjoint_left.mp B.vertices_disjoint_reverseBranch)
        hyB hyReverseB
  rcases (B.childBranch c).mem_vertices_or_mem_reverseBranch y with
    hyChild | hyReverseChild
  · exact (hyNotChild hyChild).elim
  · exact ⟨y, hyReverseChild, hyPos⟩

/-- Below a retained support edge, a genuine child edge is retained exactly
when its child branch contains positive support.  The occupied reverse side is
supplied by the exterior witness of the parent retained edge. -/
theorem child_supportEdge_iff_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).SupportEdge C ↔
      (B.childBranch c).Occupied C := by
  constructor
  · intro hChild
    exact hChild.1
  · intro hChildOcc
    exact
      ⟨hChildOcc,
        B.reverse_child_occupied_of_supportEdge C hEdge c⟩

/-- A rooted certificate that a vertex is reached from an oriented-branch root
by descending only through retained support edges.  It is an in-place path
object for the minimal support core. -/
inductive SupportDescent (C : Configuration V) :
    (B : OrientedBranch T) → V → Prop
  | root (B : OrientedBranch T) :
      SupportDescent C B B.root
  | child (B : OrientedBranch T) (c : B.Child) {x : V}
      (hEdge : (B.childBranch c).SupportEdge C)
      (hTail : SupportDescent C (B.childBranch c) x) :
      SupportDescent C B x

/-- Every positive-support vertex on the root side of a retained edge is joined
to the edge root by a descent consisting entirely of retained support edges.
This is the rooted path-closure form of connectedness of the minimal support
subtree. -/
theorem supportDescent_of_mem_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) {x : V}
    (hx : x ∈ B.vertices) (hxPos : 0 < C x) :
    SupportDescent C B x := by
  classical
  by_cases hxr : x = B.root
  · subst x
    exact SupportDescent.root B
  · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxChild⟩
    have hChildOcc : (B.childBranch c).Occupied C :=
      ⟨x, hxChild, hxPos⟩
    have hChildEdge : (B.childBranch c).SupportEdge C :=
      (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2 hChildOcc
    exact
      SupportDescent.child B c hChildEdge
        (supportDescent_of_mem_pos
          C (B.childBranch c) hChildEdge hxChild hxPos)
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _

/-- If the root of a retained edge is not itself occupied, some retained child
edge continues the support core. -/
theorem exists_child_supportEdge_of_supportEdge_of_root_not_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (hRoot : ¬ 0 < C B.root) :
    ∃ c : B.Child, (B.childBranch c).SupportEdge C := by
  rcases hEdge.1 with ⟨x, hxB, hxPos⟩
  have hxNe : x ≠ B.root := by
    intro hxr
    subst x
    exact hRoot hxPos
  rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hxB hxNe with
    ⟨c, hxChild⟩
  refine ⟨c, ?_⟩
  exact
    (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2
      ⟨x, hxChild, hxPos⟩


/-- If an edge is retained by the support core and there is no retained child
edge at its root, then that root is occupied.  This is the in-place form of
the statement that every leaf of the minimal connected support subtree is
occupied. -/
theorem root_pos_of_supportEdge_of_no_child_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNoChild : ∀ c : B.Child, ¬ (B.childBranch c).SupportEdge C) :
    0 < C B.root := by
  classical
  by_contra hRootPos
  have hRootZero : C B.root = 0 := Nat.eq_zero_of_not_pos hRootPos
  rcases hEdge.1 with ⟨x, hxB, hxPos⟩
  have hxNe : x ≠ B.root := by
    intro hxr
    subst x
    simp [hRootZero] at hxPos
  rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hxB hxNe with
    ⟨c, hxChild⟩
  have hChildOcc : (B.childBranch c).Occupied C :=
    ⟨x, hxChild, hxPos⟩
  rcases hEdge.2 with ⟨y, hyReverseB, hyPos⟩
  have hyNotChild : y ∉ (B.childBranch c).vertices := by
    intro hyChild
    have hyB : y ∈ B.vertices :=
      B.childBranch_vertices_subset c hyChild
    exact
      (Finset.disjoint_left.mp B.vertices_disjoint_reverseBranch)
        hyB hyReverseB
  have hReverseChildOcc : (B.childBranch c).reverseBranch.Occupied C := by
    rcases (B.childBranch c).mem_vertices_or_mem_reverseBranch y with
      hyChild | hyReverseChild
    · exact (hyNotChild hyChild).elim
    · exact ⟨y, hyReverseChild, hyPos⟩
  exact hNoChild c ⟨hChildOcc, hReverseChildOcc⟩

/-- If the exterior side of an oriented edge is empty, its message remains
literally `EMPTY`, and therefore contributes zero to the rooted score. -/
theorem score_eq_effectiveInput_of_reverse_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    score T C B.root = B.effectiveInput C := by
  rw [score_eq_effectiveInput_add_reverse C B,
    branchMessage_eq_empty_of_not_occupied C B.reverseBranch hEmpty]
  simp [messageContribution, EMPTY]

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
