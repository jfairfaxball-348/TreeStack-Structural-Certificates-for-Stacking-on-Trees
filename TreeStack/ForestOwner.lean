import Mathlib
import TreeStack.Support

namespace TreeStack

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The graph of defective retained support edges.  Adjacency is defined by
presenting the ambient tree edge in one orientation and asking for the
orientation-invariant defective-support predicate. -/
noncomputable def defectiveGraph
    (C : Configuration V) : SimpleGraph V where
  Adj u v :=
    ∃ h : T.graph.Adj u v,
      (incidentBranch T v u h).DefectiveSupportEdge C
  symm.symm u v huv := by
    rcases huv with ⟨h, hDef⟩
    refine ⟨h.symm, ?_⟩
    have hRev :
        (incidentBranch T v u h).reverseBranch.DefectiveSupportEdge C :=
      ((incidentBranch T v u h).defectiveSupportEdge_reverse_iff C).2 hDef
    simpa [incidentBranch, reverseBranch] using hRev
  loopless.irrefl u huu := by
    rcases huu with ⟨h, _⟩
    exact h.ne rfl

/-- The defective-edge graph is a spanning subgraph of the ambient tree. -/
theorem defectiveGraph_le_tree
    (C : Configuration V) :
    defectiveGraph (T := T) C ≤ T.graph := by
  intro u v huv
  rcases huv with ⟨h, _⟩
  exact h

/-- Defective retained edges form a forest: their graph is acyclic because it
is a subgraph of the ambient tree. -/
theorem defectiveGraph_isAcyclic
    (C : Configuration V) :
    (defectiveGraph (T := T) C).IsAcyclic := by
  exact
    SimpleGraph.IsAcyclic.anti
      (defectiveGraph_le_tree (T := T) C)
      T.isTree.isAcyclic


/-- For an oriented presentation of a tree edge and a fixed ambient root,
choose the endpoint farther from the root.  Tree acyclicity ensures adjacent
endpoints have distinct distances, so this choice is canonical on the
underlying undirected edge. -/
noncomputable def rootedOwner (r : V) (B : OrientedBranch T) : V :=
  if T.graph.dist r B.root = T.graph.dist r B.parent + 1 then
    B.root
  else
    B.parent

/-- The other endpoint of the edge after choosing `rootedOwner`. -/
noncomputable def rootedOther (r : V) (B : OrientedBranch T) : V :=
  if T.graph.dist r B.root = T.graph.dist r B.parent + 1 then
    B.parent
  else
    B.root

/-- The rooted owner and the other endpoint are adjacent. -/
theorem rootedOther_adj_rootedOwner
    (r : V) (B : OrientedBranch T) :
    T.graph.Adj (B.rootedOther r) (B.rootedOwner r) := by
  classical
  simp only [rootedOther, rootedOwner]
  split
  · exact B.adj.symm
  · exact B.adj

/-- The owner is exactly one level farther from the fixed root than the other
endpoint. -/
theorem rootedOwner_dist_eq_rootedOther_add_one
    (r : V) (B : OrientedBranch T) :
    T.graph.dist r (B.rootedOwner r) =
      T.graph.dist r (B.rootedOther r) + 1 := by
  classical
  simp only [rootedOwner, rootedOther]
  split
  next h =>
    exact h
  next h =>
    rcases T.isTree.dist_eq_dist_add_one_of_adj r B.adj with hForward | hReverse
    · exact (h hForward).elim
    · exact hReverse

/-- If the ambient root lies on the displayed root side of an edge, the
farther endpoint (and hence the rooted owner) is the displayed parent. -/
theorem rootedOwner_eq_parent_of_mem_vertices
    (r : V) (B : OrientedBranch T) (hr : r ∈ B.vertices) :
    B.rootedOwner r = B.parent := by
  classical
  have hdist := B.dist_parent_eq_root_dist_add_one hr
  have hdist' :
      T.graph.dist r B.parent = T.graph.dist r B.root + 1 := by
    simpa only [T.graph.dist_comm] using hdist
  simp only [rootedOwner]
  split
  · next h => omega
  · rfl

/-- Reordering an edge as owner/other does not change its underlying
undirected edge. -/
theorem rootedOwner_other_edge
    (r : V) (B : OrientedBranch T) :
    s(B.rootedOwner r, B.rootedOther r) =
      s(B.root, B.parent) := by
  classical
  simp only [rootedOwner, rootedOther]
  split
  · rfl
  · exact Sym2.eq_swap

/-- A vertex has at most one adjacent predecessor that is exactly one level
closer to a fixed root in a tree. -/
theorem eq_of_adj_owner_of_dist
    (r x u v : V)
    (hu : T.graph.Adj u x) (hv : T.graph.Adj v x)
    (hdu : T.graph.dist r x = T.graph.dist r u + 1)
    (hdv : T.graph.dist r x = T.graph.dist r v + 1) :
    u = v := by
  classical
  obtain ⟨pu, hpu⟩ :=
    (T.isTree.connected r u).exists_walk_length_eq_dist
  obtain ⟨pv, hpv⟩ :=
    (T.isTree.connected r v).exists_walk_length_eq_dist
  have hpuLen :
      (pu.concat hu).length = T.graph.dist r x := by
    simp [hpu, hdu]
  have hpvLen :
      (pv.concat hv).length = T.graph.dist r x := by
    simp [hpv, hdv]
  have hpuPath : (pu.concat hu).IsPath :=
    (pu.concat hu).isPath_of_length_eq_dist hpuLen
  have hpvPath : (pv.concat hv).IsPath :=
    (pv.concat hv).isPath_of_length_eq_dist hpvLen
  have hPathEq :
      (⟨pu.concat hu, hpuPath⟩ : T.graph.Path r x) =
        ⟨pv.concat hv, hpvPath⟩ :=
    T.isTree.isAcyclic.subsingleton_path r x |>.elim _ _
  have hWalkEq : pu.concat hu = pv.concat hv :=
    Subtype.mk.inj hPathEq
  have hPenultimate :=
    congrArg SimpleGraph.Walk.penultimate hWalkEq
  simpa using hPenultimate

/-- The ambient-root owner assignment is injective on underlying tree edges:
two edges with the same owner are the same undirected edge.  Consequently its
restriction to any defective-edge forest is an injective incident-owner
assignment, without rooting forest components separately. -/
theorem edge_eq_of_rootedOwner_eq
    (r : V) (B D : OrientedBranch T)
    (hOwner : B.rootedOwner r = D.rootedOwner r) :
    s(B.root, B.parent) = s(D.root, D.parent) := by
  have hOther :
      B.rootedOther r = D.rootedOther r := by
    apply eq_of_adj_owner_of_dist
      (T := T) r (B.rootedOwner r)
    · exact B.rootedOther_adj_rootedOwner r
    · rw [hOwner]
      exact D.rootedOther_adj_rootedOwner r
    · exact B.rootedOwner_dist_eq_rootedOther_add_one r
    · rw [hOwner]
      exact D.rootedOwner_dist_eq_rootedOther_add_one r
  calc
    s(B.root, B.parent) =
        s(B.rootedOwner r, B.rootedOther r) :=
      (B.rootedOwner_other_edge r).symm
    _ = s(D.rootedOwner r, D.rootedOther r) := by
      rw [hOwner, hOther]
    _ = s(D.root, D.parent) :=
      D.rootedOwner_other_edge r

/-- Reversing the presentation of an edge does not change its rooted owner. -/
theorem rootedOwner_reverse
    (r : V) (B : OrientedBranch T) :
    B.reverseBranch.rootedOwner r = B.rootedOwner r := by
  classical
  rcases T.isTree.dist_eq_dist_add_one_of_adj r B.adj with hForward | hReverse
  · simp [rootedOwner, reverseBranch, hForward]
    omega
  · simp [rootedOwner, reverseBranch, hReverse]
    omega


end OrientedBranch

end TreeStack
