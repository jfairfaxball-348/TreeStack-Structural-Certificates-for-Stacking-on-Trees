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

end OrientedBranch

end TreeStack
