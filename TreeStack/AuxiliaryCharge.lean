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

/-- The weighted contribution does not depend on which orientation is used to
display the underlying edge. -/
@[simp] theorem auxEdgeContribution_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B.reverseBranch =
      auxEdgeContribution C ambientRoot hScores B := by
  simp [auxEdgeContribution]
  ring

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
      (Or.inl hArrow :
        B.DefectArrow C ∨
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
      (Or.inl hArrow :
        B.DefectArrow C ∨
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
        B.DefectArrow C ∨
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

/-- A forced oriented edge with zero head defect has no positive excess over
the endpoint baseline. -/
theorem defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hDeltaZero : scoreDefect T C B.parent = 0) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by
  have hAux : AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl hArrow :
        B.DefectArrow C ∨ B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hBound :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  unfold auxEdgeContribution
  rw [hDeltaZero] at hBound
  linarith

/-- A retained edge with no positive defect excess contributes at most its two
endpoint weights.  Oriented zero-excess states still use their forced
auxiliary direction, which is why every `DefectArrow` participates in
`AuxArrow`, not only defective ones. -/
theorem nondefectiveSupportEdge_auxEdgeContribution_le_baseline
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNondef : ¬ B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by
  rcases B.supportEdge_defectArrow_or_reverse_or_both_neg C hEdge with
    hForward | hReverse | hBothNeg
  · have hDeltaZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inl ⟨hForward.2, hPos⟩⟩
    exact
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B hForward hDeltaZero
  · have hDeltaZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inl ⟨hReverse.2, hPos⟩)⟩
    have h :=
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B.reverseBranch hReverse (by simpa using hDeltaZero)
    simpa [add_comm] using h
  · have hRootZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inl hPos⟩)⟩
    have hParentZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inr hPos⟩)⟩
    have hEq :=
      B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
    rcases
        defect_two_negative
          ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
          ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
          hEq.1 hEq.2 hBothNeg.1 hBothNeg.2 with
      ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
    have hrZero : r = 0 := by omega
    have hqZero : q = 0 := by omega
    unfold auxEdgeContribution
    rw [ha, hb, hrZero, hqZero]
    ring_nf
    exact le_rfl

/-- Every defective retained edge has its weighted contribution bounded by
the endpoint baseline plus the charge at its injective rooted owner. -/
theorem defectiveSupportEdge_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by
  rcases B.auxArrow_or_reverse_of_defectiveSupportEdge C ambientRoot hDef with
    hForward | hReverse
  · rcases hForward with ⟨h, hState⟩
    have hp : h = B.adj := Subsingleton.elim _ _
    subst h
    simp only [incidentBranch_self] at hState
    have hState' :
        (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
          B.TwoNegativeOwnerArrow C ambientRoot := by
      rcases hState with hArrow | hTwo
      · exact Or.inl ⟨hDef, hArrow⟩
      · exact Or.inr hTwo
    exact
      auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
        C ambientRoot hScores B hState'
  · have hDefReverse : B.reverseBranch.DefectiveSupportEdge C :=
      (B.defectiveSupportEdge_reverse_iff C).2 hDef
    rcases hReverse with ⟨h, hState⟩
    have hp : h = B.adj.symm := Subsingleton.elim _ _
    subst h
    simp only [incidentBranch_reverse_self] at hState
    have hState' :
        (B.reverseBranch.DefectiveSupportEdge C ∧
            B.reverseBranch.DefectArrow C) ∨
          B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
      rcases hState with hArrow | hTwo
      · exact Or.inl ⟨hDefReverse, hArrow⟩
      · exact Or.inr hTwo
    have h :=
      auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
        C ambientRoot hScores B.reverseBranch hState'
    simpa [add_comm, rootedOwner_reverse] using h

/-- Uniform retained-edge estimate, exposing a charge exactly when the edge is
defective. -/
theorem supportEdge_auxEdgeContribution_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        if B.DefectiveSupportEdge C then
          auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
            scoreDefect T C (B.rootedOwner ambientRoot)
        else 0 := by
  by_cases hDef : B.DefectiveSupportEdge C
  · simpa [hDef] using
      defectiveSupportEdge_auxEdgeContribution_le_owner_charge
        C ambientRoot hScores B hDef
  · have h :=
      nondefectiveSupportEdge_auxEdgeContribution_le_baseline
        C ambientRoot hScores B hEdge hDef
    simp only [hDef, ↓reduceIte, add_zero]
    exact h

/-- Across a nonretained edge with an occupied displayed root side, the other
message remains literally `EMPTY`.  The whole weighted edge contribution is
exactly the defect charge at the empty-side endpoint, whose auxiliary weight
is one. -/
theorem auxEdgeContribution_eq_emptySide_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hOccupied : B.Occupied C)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    auxEdgeContribution C ambientRoot hScores B =
      auxWeightInt C ambientRoot hScores B.parent *
        scoreDefect T C B.parent := by
  have hEmptyMessage :=
    branchMessage_eq_empty_of_not_occupied C B.reverseBranch hEmpty
  have hEmptyInput :=
    effectiveInput_eq_zero_of_not_occupied C B.reverseBranch hEmpty
  have hWeight :
      auxWeightInt C ambientRoot hScores B.parent = 1 := by
    simpa using
      auxWeightInt_eq_one_of_not_occupied
        C ambientRoot hScores B.reverseBranch hEmpty
  have hScore := score_eq_effectiveInput_add_reverse C B.reverseBranch
  simp only [reverseBranch_root, reverseBranch_reverse] at hScore
  rw [hEmptyInput] at hScore
  unfold auxEdgeContribution scoreDefect
  rw [hEmptyMessage, hWeight, hScore]
  simp

/-- When the fixed ambient root carries a pebble, the empty-side endpoint of a
nonretained edge is exactly its rooted owner. -/
theorem rootedOwner_eq_emptySide_of_root_pos
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T)
    (hRootPos : 0 < C ambientRoot)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    B.rootedOwner ambientRoot = B.parent := by
  have hNotReverse : ambientRoot ∉ B.reverseBranch.vertices := by
    intro hmem
    exact hEmpty ⟨ambientRoot, hmem, hRootPos⟩
  have hMem : ambientRoot ∈ B.vertices := by
    rcases B.mem_vertices_or_mem_reverseBranch ambientRoot with h | h
    · exact h
    · exact (hNotReverse h).elim
  exact B.rootedOwner_eq_parent_of_mem_vertices ambientRoot hMem

/-- Owner-paid defect excess for a retained edge.  This term is nonzero only
when the retained edge is genuinely defective. -/
noncomputable def retainedDefectCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.DefectiveSupportEdge C then
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)
  else
    0

/-- Cancellation term created by a nonretained edge whose opposite branch is
literally `EMPTY`.  This is deliberately kept separate from retained-edge
defect charging. -/
noncomputable def emptyBoundaryCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.SupportEdge C then
    0
  else
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)

/-- Uniform ambient-edge estimate with the two cancellation mechanisms kept
separate: only genuinely defective retained edges receive owner-paid defect
charge, while nonretained edges use their distinct `EMPTY`-boundary term. -/
theorem auxEdgeContribution_le_endpoint_add_separated_charges
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        retainedDefectCharge C ambientRoot hScores B +
        emptyBoundaryCharge C ambientRoot hScores B := by
  by_cases hEdge : B.SupportEdge C
  · have h :=
      supportEdge_auxEdgeContribution_le
        C ambientRoot hScores B hEdge
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, add_assoc] using h
  · have hNondef : ¬ B.DefectiveSupportEdge C := by
      intro hDef
      exact hEdge hDef.1
    have hOwnerBound :
        auxEdgeContribution C ambientRoot hScores B ≤
          auxWeightInt C ambientRoot hScores B.root +
            auxWeightInt C ambientRoot hScores B.parent +
            auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
              scoreDefect T C (B.rootedOwner ambientRoot) := by
      rcases B.occupied_or_reverse_occupied C hRootPos with hOcc | hRevOcc
      · have hEmpty : ¬ B.reverseBranch.Occupied C := by
          intro hRev
          exact hEdge ⟨hOcc, hRev⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B hOcc hEmpty
        rw [hEq, hOwner]
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
      · have hEmpty : ¬ B.Occupied C := by
          intro hOcc
          exact hEdge ⟨hOcc, hRevOcc⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B.reverseBranch hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B.reverseBranch hRevOcc hEmpty
        have hOwner' : B.rootedOwner ambientRoot = B.root := by
          simpa [rootedOwner_reverse] using hOwner
        have hEq' :
            auxEdgeContribution C ambientRoot hScores B =
              auxWeightInt C ambientRoot hScores B.root *
                scoreDefect T C B.root := by
          simpa using hEq
        rw [hEq', hOwner']
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, hNondef,
      add_assoc] using hOwnerBound

end OrientedBranch

end TreeStack
