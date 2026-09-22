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

/-- Combined auxiliary orientation on retained support edges.  Every
oriented-type edge keeps its forced defect-arrow direction, including the
zero-excess states needed for the powers-of-two baseline estimate.
Two-negative edges are directed only when defective, toward the fixed rooted
owner. -/
def AuxArrow
    (C : Configuration V) (ambientRoot : V) (u v : V) : Prop :=
  ∃ h : T.graph.Adj u v,
    let B := incidentBranch T v u h
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot

/-- Rebuilding an oriented branch from its own endpoints and adjacency proof
returns the same branch. -/
@[simp] theorem incidentBranch_self
    (B : OrientedBranch T) :
    incidentBranch T B.parent B.root B.adj = B := by
  cases B
  rfl

/-- Rebuilding the reverse orientation from the swapped endpoints gives the
stored reverse branch. -/
@[simp] theorem incidentBranch_reverse_self
    (B : OrientedBranch T) :
    incidentBranch T B.root B.parent B.adj.symm = B.reverseBranch := by
  cases B
  rfl

/-- Every defective retained support edge receives an auxiliary direction.
Oriented-type edges use their forced message direction; two-negative edges
point toward the fixed rooted owner. -/
theorem auxArrow_or_reverse_of_defectiveSupportEdge
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    AuxArrow (T := T) C ambientRoot B.root B.parent ∨
      AuxArrow (T := T) C ambientRoot B.parent B.root := by
  rcases
      B.supportEdge_defectArrow_or_reverse_or_both_neg C hDef.1 with
    hForward | hReverse | hBothNeg
  · left
    refine ⟨B.adj, ?_⟩
    simpa using
      (Or.inl hForward :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  · right
    have hDefReverse :
        B.reverseBranch.DefectiveSupportEdge C :=
      (B.defectiveSupportEdge_reverse_iff C).2 hDef
    refine ⟨B.adj.symm, ?_⟩
    have hInc :
        incidentBranch T B.root B.parent B.adj.symm =
          B.reverseBranch := by
      exact incidentBranch_reverse_self B
    change
      (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
        (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
          C ambientRoot
    rw [hInc]
    exact Or.inl hReverse
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · right
      have hDefReverse :
          B.reverseBranch.DefectiveSupportEdge C :=
        (B.defectiveSupportEdge_reverse_iff C).2 hDef
      have hOwnerReverse :
          B.reverseBranch.parent =
            B.reverseBranch.rootedOwner ambientRoot := by
        simpa [rootedOwner_reverse] using hOwnerRoot.symm
      have hTwoReverse :
          B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
        refine ⟨hDefReverse, hBothNeg.2, ?_, hOwnerReverse⟩
        simpa using hBothNeg.1
      refine ⟨B.adj.symm, ?_⟩
      have hInc :
          incidentBranch T B.root B.parent B.adj.symm =
            B.reverseBranch := by
        exact incidentBranch_reverse_self B
      change
        (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
          (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
            C ambientRoot
      rw [hInc]
      exact Or.inr hTwoReverse
    · left
      have hTwo :
          B.TwoNegativeOwnerArrow C ambientRoot :=
        ⟨hDef, hBothNeg.1, hBothNeg.2, hOwnerParent.symm⟩
      refine ⟨B.adj, ?_⟩
      simpa using
        (Or.inr hTwo :
          B.DefectArrow C ∨
            B.TwoNegativeOwnerArrow C ambientRoot)

/-- Every auxiliary arrow is an ambient tree edge. -/
theorem auxArrow_adj
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    T.graph.Adj u v := by
  rcases hArrow with ⟨h, _⟩
  exact h

/-- Every auxiliary arrow lies on a retained support edge. -/
theorem auxArrow_supportEdge
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    (incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)).SupportEdge C := by
  rcases hArrow with ⟨h, hState⟩
  dsimp only at hState
  have hp : h = auxArrow_adj C ambientRoot ⟨h, hState⟩ :=
    Subsingleton.elim _ _
  subst h
  rcases hState with hOriented | hTwo
  · exact hOriented.1
  · exact hTwo.1.1

/-- No auxiliary arrow can enter the root of a configuration-empty oriented
branch.  An arrow across the boundary would retain the empty side, while an
arrow from a genuine child would retain an occupied subbranch inside it. -/
theorem no_auxArrow_to_root_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) (u : V) :
    ¬ AuxArrow (T := T) C ambientRoot u B.root := by
  intro hArrow
  have hAdj := auxArrow_adj C ambientRoot hArrow
  have hSupport := auxArrow_supportEdge C ambientRoot hArrow
  by_cases hup : u = B.parent
  · subst u
    have hBranch :
        incidentBranch T B.root B.parent hAdj = B.reverseBranch := by
      cases B
      rfl
    rw [hBranch] at hSupport
    exact hEmpty hSupport.2
  · let c : B.Child :=
      { vertex := u
        adj := hAdj.symm
        ne_parent := hup }
    have hBranch :
        incidentBranch T B.root u hAdj = B.childBranch c := by
      rfl
    rw [hBranch] at hSupport
    rcases hSupport.1 with ⟨x, hx, hxPos⟩
    exact hEmpty ⟨x, B.childBranch_vertices_subset c hx, hxPos⟩

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
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot at hForwardState
  rw [hRevBranch] at hReverseState
  rcases hForwardState with hForward | hForward
  · rcases hReverseState with hReverse | hReverse
    · exact
        (B.not_defectArrow_reverse C hForward hScores)
          hReverse
    · exact
        (not_lt_of_ge hForward.2)
          hReverse.2.2.1
  · rcases hReverseState with hReverse | hReverse
    · exact
        (not_lt_of_ge hReverse.2)
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
        have hAdj :=
          (auxArrow_adj C ambientRoot hStep).symm
        have hEdge :=
          B.edge_leaving_vertices_eq_boundary hxIn ih hAdj
        rw [Sym2.eq_iff] at hEdge
        rcases hEdge with hEdge | hEdge
        · have hReverse :
              AuxArrow (T := T) C ambientRoot v u := by
            rcases hEdge with ⟨hRoot, hParent⟩
            subst_vars
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

/-- Length of a longest auxiliary directed path ending at a vertex.  The
well-founded measure is the strict-predecessor rank, which increases along
every arrow. -/
noncomputable def auxHeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  (Finset.univ : Finset V).sup fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
termination_by auxRank (T := T) C ambientRoot v
decreasing_by
  exact auxRank_lt_of_auxArrow C ambientRoot hScores h

/-- Every auxiliary arrow extends a longest directed path by one step. -/
theorem auxHeight_succ_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores u + 1 ≤
      auxHeight C ambientRoot hScores v := by
  nth_rewrite 2 [auxHeight]
  have hLe :=
    Finset.le_sup
      (f := fun x : V =>
        if h : AuxArrow (T := T) C ambientRoot x v then
          auxHeight C ambientRoot hScores x + 1
        else
          0)
      (Finset.mem_univ u)
  simpa [hArrow] using hLe

/-- A vertex with no incoming auxiliary arrow has auxiliary height zero. -/
theorem auxHeight_eq_zero_of_no_incoming
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V)
    (hNo : ∀ u, ¬ AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores v = 0 := by
  rw [auxHeight]
  simp [hNo]

/-- The root of an empty branch has unit auxiliary weight. -/
theorem auxWeightInt_eq_one_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) :
    auxWeightInt C ambientRoot hScores B.root = 1 := by
  have hHeight : auxHeight C ambientRoot hScores B.root = 0 :=
    auxHeight_eq_zero_of_no_incoming C ambientRoot hScores B
      (no_auxArrow_to_root_of_not_occupied C ambientRoot B hEmpty)
  simp [auxWeightInt, auxWeight, hHeight]

/-- Powers-of-two auxiliary weights attached to longest-path heights. -/
noncomputable def auxWeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  2 ^ auxHeight C ambientRoot hScores v

/-- Auxiliary weights are positive (and in particular at least one). -/
theorem auxWeight_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 < auxWeight C ambientRoot hScores v := by
  simp [auxWeight]

/-- The key doubling inequality: weights at least double along every auxiliary
directed edge. -/
theorem two_mul_auxWeight_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeight C ambientRoot hScores u ≤
      auxWeight C ambientRoot hScores v := by
  have hHeight :=
    auxHeight_succ_le_of_auxArrow
      C ambientRoot hScores hArrow
  have hPow :
      2 ^ (auxHeight C ambientRoot hScores u + 1) ≤
        2 ^ auxHeight C ambientRoot hScores v :=
    Nat.pow_le_pow_of_le (by omega) hHeight
  simpa [auxWeight, Nat.two_pow_succ, two_mul] using hPow

/-- Integer form of the powers-of-two auxiliary weight, convenient for the
weighted defect inequalities, which are stated over integers. -/
noncomputable def auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℤ :=
  (auxWeight C ambientRoot hScores v : ℤ)

/-- Integer auxiliary weights are nonnegative. -/
theorem auxWeightInt_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 ≤ auxWeightInt C ambientRoot hScores v := by
  simp [auxWeightInt]

/-- Integer doubling form used directly by `DefectCharge.lean`. -/
theorem two_mul_auxWeightInt_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeightInt C ambientRoot hScores u ≤
      auxWeightInt C ambientRoot hScores v := by
  change
    (2 : ℤ) * (auxWeight C ambientRoot hScores u : ℤ) ≤
      (auxWeight C ambientRoot hScores v : ℤ)
  exact_mod_cast
    (two_mul_auxWeight_le_of_auxArrow
      C ambientRoot hScores hArrow)

end OrientedBranch

end TreeStack
