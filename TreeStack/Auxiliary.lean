import Mathlib
import TreeStack.DefectCharge

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Reversing an incident presentation of an edge gives the reverse branch. -/
@[simp] theorem incidentBranch_reverse
    (u v : V) (h : T.graph.Adj u v) :
    incidentBranch T u v h.symm =
      (incidentBranch T v u h).reverseBranch := by
  rfl

/-- In the two-negative state, presenting the edge toward its fixed ambient
rooted owner puts the local defect equation in exactly the orientation used by
`two_negative_excess_le_owner_budget`. -/
theorem two_negative_parameters_toward_rootedOwner
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0)
    (haNeg :
      messageContribution (branchMessage C B) < 0)
    (hbNeg :
      messageContribution (branchMessage C B.reverseBranch) < 0)
    (hOwner : B.parent = B.rootedOwner ambientRoot) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      messageContribution (branchMessage C B) = -(2 * r + 1) ∧
      messageContribution (branchMessage C B.reverseBranch) = -(2 * q + 1) ∧
      scoreDefect T C B.root = r + 2 * q ∧
      scoreDefect T C (B.rootedOwner ambientRoot) = q + 2 * r := by
  have hEq :=
    B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
  rcases
      defect_two_negative
        ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
        ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
        hEq.1 hEq.2 haNeg hbNeg with
    ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
  refine ⟨r, q, hr, hq, ha, hb, hRoot, ?_⟩
  rw [← hOwner]
  exact hParent

/-- A defective two-negative support edge, presented from the other endpoint
toward its injectively chosen ambient-root owner. -/
def TwoNegativeOwnerArrow
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T) : Prop :=
  B.DefectiveSupportEdge C ∧
    messageContribution (branchMessage C B) < 0 ∧
    messageContribution (branchMessage C B.reverseBranch) < 0 ∧
    B.parent = B.rootedOwner ambientRoot

/-- The owner of an edge is one of its endpoints. -/
theorem rootedOwner_eq_root_or_parent
    (ambientRoot : V) (B : OrientedBranch T) :
    B.rootedOwner ambientRoot = B.root ∨
      B.rootedOwner ambientRoot = B.parent := by
  classical
  simp only [rootedOwner]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The same two-negative edge cannot point toward its rooted owner in both
presentations. -/
theorem not_twoNegativeOwnerArrow_reverse
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hArrow : B.TwoNegativeOwnerArrow C ambientRoot) :
    ¬ B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
  intro hReverse
  have hParentOwner :
      B.parent = B.rootedOwner ambientRoot :=
    hArrow.2.2.2
  have hRootOwner :
      B.root = B.rootedOwner ambientRoot := by
    have h := hReverse.2.2.2
    simpa [rootedOwner_reverse] using h
  exact B.root_ne_parent (hRootOwner.trans hParentOwner.symm)

/-- Combined auxiliary orientation on defective support edges.  Oriented-type
edges keep their forced defect-arrow direction.  Two-negative defective edges
are directed toward the fixed rooted owner. -/
def AuxArrow
    (C : Configuration V) (ambientRoot : V) (u v : V) : Prop :=
  ∃ h : T.graph.Adj u v,
    let B := incidentBranch T v u h
    (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
      B.TwoNegativeOwnerArrow C ambientRoot

/-- Every auxiliary arrow is an ambient tree edge. -/
theorem auxArrow_adj
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    T.graph.Adj u v := by
  rcases hArrow with ⟨h, _⟩
  exact h

/-- Every auxiliary arrow lies in the defective retained-edge forest. -/
theorem auxArrow_defectiveGraph
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    defectiveGraph (T := T) C |>.Adj u v := by
  rcases hArrow with ⟨h, hState⟩
  refine ⟨h, ?_⟩
  dsimp only at hState
  rcases hState with hOriented | hTwo
  · exact hOriented.1
  · exact hTwo.1

/-- Under all-nonpositive rooted scores, the combined orientation never places
both directions on the same defective edge. -/
theorem not_auxArrow_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ AuxArrow (T := T) C ambientRoot v u := by
  intro hReverse
  rcases hArrow with ⟨huv, hForwardState⟩
  rcases hReverse with ⟨hvu, hReverseState⟩
  let B : OrientedBranch T := incidentBranch T v u huv
  have hRevBranch :
      incidentBranch T u v hvu = B.reverseBranch := by
    have hp : hvu = huv.symm := Subsingleton.elim _ _
    subst hvu
    rfl
  dsimp only at hForwardState hReverseState
  change
    (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
      B.TwoNegativeOwnerArrow C ambientRoot at hForwardState
  rw [hRevBranch] at hReverseState
  rcases hForwardState with hForward | hForward
  · rcases hReverseState with hReverse | hReverse
    · exact
        (B.not_defectArrow_reverse C hForward.2 hScores)
          hReverse.2
    · exact
        (not_lt_of_ge hForward.2.2)
          hReverse.2.2.1
  · rcases hReverseState with hReverse | hReverse
    · exact
        (not_lt_of_ge hReverse.2.2)
          hForward.2.2.1
    · exact
        (B.not_twoNegativeOwnerArrow_reverse C ambientRoot hForward)
          hReverse

/-- Once an auxiliary arrow crosses an ambient tree edge, there is no directed
return path across that edge.  The proof uses the deleted-edge branch cut:
every path from the parent side back to the root side must cross the same
unique tree edge in the forbidden reverse direction. -/
theorem auxArrow_no_reflTransGen_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ Relation.ReflTransGen
        (AuxArrow (T := T) C ambientRoot) v u := by
  intro hReturn
  let B : OrientedBranch T :=
    incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)
  have hOutside :
      ∀ {x : V},
        Relation.ReflTransGen
            (AuxArrow (T := T) C ambientRoot) v x →
          x ∉ B.vertices := by
    intro x hx
    induction hx with
    | refl =>
        simpa [B] using B.parent_not_mem_vertices
    | tail hReach hStep ih =>
        intro hxIn
        have hAdj :
            T.graph.Adj x _ :=
          (auxArrow_adj C ambientRoot hStep).symm
        have hEdge :=
          B.edge_leaving_vertices_eq_boundary hxIn ih hAdj
        rw [Sym2.eq_iff] at hEdge
        rcases hEdge with hEdge | hEdge
        · have hReverse :
              AuxArrow (T := T) C ambientRoot v u := by
            subst x
            rename_i y
            subst y
            simpa [B] using hStep
          exact
            (not_auxArrow_reverse C ambientRoot hScores hArrow)
              hReverse
        · have : B.parent ∈ B.vertices := by
            rw [← hEdge.1]
            exact hxIn
          exact B.parent_not_mem_vertices this
  have huOutside := hOutside hReturn
  exact huOutside (by simpa [B] using B.root_mem_vertices)

/-- The directed auxiliary relation is acyclic: its transitive closure is
irreflexive.  This is derived directly from the ambient tree cut argument,
without rooting defective-forest components. -/
theorem auxArrow_transGen_irrefl
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    ¬ Relation.TransGen
        (AuxArrow (T := T) C ambientRoot) v v := by
  intro hCycle
  rcases Relation.TransGen.head'_iff.mp hCycle with
    ⟨u, hFirst, hReturn⟩
  exact
    (auxArrow_no_reflTransGen_reverse
      C ambientRoot hScores hFirst) hReturn

/-- Strict directed predecessors of a vertex in the auxiliary DAG. -/
noncomputable def auxPred
    (C : Configuration V) (ambientRoot : V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter fun u =>
    Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v

@[simp] theorem mem_auxPred
    (C : Configuration V) (ambientRoot : V) (u v : V) :
    u ∈ auxPred (T := T) C ambientRoot v ↔
      Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v := by
  simp [auxPred]

/-- A directed edge strictly enlarges the finite set of strict directed
predecessors. -/
theorem auxPred_ssubset_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxPred (T := T) C ambientRoot u ⊂
      auxPred (T := T) C ambientRoot v := by
  have hSubset :
      auxPred (T := T) C ambientRoot u ⊆
        auxPred (T := T) C ambientRoot v := by
    intro x hx
    rw [mem_auxPred] at hx ⊢
    exact Relation.TransGen.tail hx hArrow
  rw [Finset.ssubset_iff_of_subset hSubset]
  refine ⟨u, ?_, ?_⟩
  · rw [mem_auxPred]
    exact Relation.TransGen.single hArrow
  · rw [mem_auxPred]
    exact auxArrow_transGen_irrefl C ambientRoot hScores u

/-- A finite topological rank for the auxiliary DAG, used as the recursion
measure for the genuine longest-directed-path height below. -/
noncomputable def auxRank
    (C : Configuration V) (ambientRoot : V) (v : V) : ℕ :=
  (auxPred (T := T) C ambientRoot v).card

/-- Auxiliary rank strictly increases along every directed edge. -/
theorem auxRank_lt_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxRank (T := T) C ambientRoot u <
      auxRank (T := T) C ambientRoot v := by
  exact Finset.card_lt_card
    (auxPred_ssubset_of_auxArrow
      C ambientRoot hScores hArrow)

end OrientedBranch

end TreeStack
