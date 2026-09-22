import Mathlib
import TreeStack.Auxiliary

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Weighted message contribution of one retained edge, using the auxiliary
powers-of-two weights.  The displayed branch is oriented root (tail) toward
parent (head). -/
noncomputable def auxEdgeContribution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  -(auxWeightInt C ambientRoot hScores B.parent *
        messageContribution (branchMessage C B) +
      auxWeightInt C ambientRoot hScores B.root *
        messageContribution (branchMessage C B.reverseBranch))

/-- A defective forced arrow has its weighted edge excess payable by its tail
defect. -/
theorem defectArrow_auxEdgeContribution_le_tail_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.root *
          scoreDefect T C B.root := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl ⟨hDef, hArrow⟩ :
        (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied
      C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hEdge :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  have hPay :=
    oriented_excess_le_tail_budget
      (auxWeightInt_nonneg C ambientRoot hScores B.root)
      (B.defectArrow_tail_budget C hArrow hScores)
  unfold auxEdgeContribution
  linarith

/-- The same defective forced-arrow excess can instead be paid by its head
defect, using the auxiliary doubling inequality. -/
theorem defectArrow_auxEdgeContribution_le_head_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl ⟨hDef, hArrow⟩ :
        (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied
      C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hEdge :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  have hPay :=
    oriented_excess_le_head_budget
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hDouble
  unfold auxEdgeContribution
  linarith

/-- A defective two-negative edge directed toward its rooted owner has its
entire weighted excess payable by the owner endpoint defect. -/
theorem twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hTwo : B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inr hTwo :
        (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  rcases
      B.two_negative_parameters_toward_rootedOwner
        C ambientRoot hTwo.1.1 hScores
        hTwo.2.1 hTwo.2.2.1 hTwo.2.2.2 with
    ⟨r, q, hr, hq, ha, hb, hRoot, hOwner⟩
  have hParent :
      scoreDefect T C B.parent = q + 2 * r := by
    rw [hTwo.2.2.2]
    exact hOwner
  have hEdge :=
    two_negative_edge_excess_eq
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      ha hb
  have hPay :=
    two_negative_excess_le_owner_budget
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightOwner := auxWeightInt C ambientRoot hScores B.parent)
      (deltaOwner := scoreDefect T C B.parent)
      hq hDouble hParent
  unfold auxEdgeContribution
  linarith

/-- For a displayed auxiliary edge state, the weighted excess is payable by
the fixed rooted owner of the underlying edge.  This is the local statement
that the future global sum will combine with injectivity of `rootedOwner`. -/
theorem auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hState :
      (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
        B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by
  rcases hState with hOriented | hTwo
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · have h :=
        defectArrow_auxEdgeContribution_le_tail_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerRoot]
      exact h
    · have h :=
        defectArrow_auxEdgeContribution_le_head_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerParent]
      exact h
  · have h :=
      twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
        C ambientRoot hScores B hTwo
    rw [← hTwo.2.2.2]
    exact h

end OrientedBranch

end TreeStack
