import Mathlib
import TreeStack.LeafSlack

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Positive auxiliary height is realized by an incoming auxiliary arrow whose
height is exactly one smaller. -/
theorem exists_auxHeight_predecessor_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    ∃ u : V,
      AuxArrow (T := T) C ambientRoot u v ∧
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
  let f : V → ℕ := fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
  have hNonempty : (Finset.univ : Finset V).Nonempty :=
    ⟨v, Finset.mem_univ v⟩
  rcases Finset.exists_mem_eq_sup (Finset.univ : Finset V) hNonempty f with
    ⟨u, -, hSup⟩
  have hEq :
      auxHeight C ambientRoot hScores v = f u := by
    rw [auxHeight]
    exact hSup
  by_cases hArrow : AuxArrow (T := T) C ambientRoot u v
  · refine ⟨u, hArrow, ?_⟩
    simpa [f, hArrow] using hEq.symm
  · have hZero : auxHeight C ambientRoot hScores v = 0 := by
      simpa [f, hArrow] using hEq
    omega

/-- A canonical predecessor realizing positive auxiliary height.  At height
zero it is harmlessly defined to be the vertex itself. -/
noncomputable def auxParent
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  if h : 0 < auxHeight C ambientRoot hScores v then
    Classical.choose
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v h)
  else
    v

theorem auxParent_arrow_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    AuxArrow (T := T) C ambientRoot
      (auxParent C ambientRoot hScores v) v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).1

theorem auxParent_height_add_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxHeight C ambientRoot hScores
        (auxParent C ambientRoot hScores v) + 1 =
      auxHeight C ambientRoot hScores v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).2

/-- The canonical height-realizing walk, written from a vertex backwards to
its height-zero source.  Heights strictly decrease at each recursive step. -/
noncomputable def auxSourceWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : Σ r : V, T.graph.Walk v r :=
  if hZero : auxHeight C ambientRoot hScores v = 0 then
    ⟨v, SimpleGraph.Walk.nil⟩
  else
    let hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    let tailCert := auxSourceWalk C ambientRoot hScores u
    ⟨tailCert.1,
      SimpleGraph.Walk.cons
        (auxArrow_adj C ambientRoot
          (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
        tailCert.2⟩
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v
      (Nat.pos_of_ne_zero hZero)
  omega

/-- One-step equation for the canonical source walk at height zero. -/
theorem auxSourceWalk_eq_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSourceWalk C ambientRoot hScores v =
      ⟨v, SimpleGraph.Walk.nil⟩ := by
  rw [auxSourceWalk]
  simp [hZero]

/-- One-step equation for the canonical source walk at positive height. -/
theorem auxSourceWalk_eq_of_height_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSourceWalk C ambientRoot hScores v =
      let u := auxParent C ambientRoot hScores v
      let tailCert := auxSourceWalk C ambientRoot hScores u
      ⟨tailCert.1,
        SimpleGraph.Walk.cons
          (auxArrow_adj C ambientRoot
            (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
          tailCert.2⟩ := by
  rw [auxSourceWalk]
  simp only [dif_neg (Nat.ne_of_gt hPos)]

/-- The height-zero source selected by the canonical predecessor chain. -/
noncomputable def auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  (auxSourceWalk C ambientRoot hScores v).1

/-- The underlying canonical walk from a vertex to its auxiliary source. -/
noncomputable def auxWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    T.graph.Walk v (auxSource C ambientRoot hScores v) :=
  (auxSourceWalk C ambientRoot hScores v).2

/-- Every vertex occurring on the canonical source walk has height at most the
height of the starting vertex. -/
theorem auxSourceWalk_support_height_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxHeight C ambientRoot hScores x ≤
      auxHeight C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero] at hx
    simp at hx
    subst x
    exact le_rfl
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos] at hx
    simp only [SimpleGraph.Walk.support_cons] at hx
    rcases List.mem_cons.mp hx with hEqX | hxTail
    · subst x
      exact le_rfl
    · have hRec :=
        auxSourceWalk_support_height_le
          C ambientRoot hScores u x hxTail
      omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- The canonical source walk is simple because height strictly decreases
backwards along it. -/
theorem auxSourceWalk_isPath
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.IsPath := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]
    simp
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]
    have hTail :
        (auxSourceWalk C ambientRoot hScores u).2.IsPath :=
      auxSourceWalk_isPath C ambientRoot hScores u
    apply (SimpleGraph.Walk.cons_isPath_iff _ _).2
    refine ⟨hTail, ?_⟩
    intro hvMem
    have hLe :=
      auxSourceWalk_support_height_le
        C ambientRoot hScores u v hvMem
    omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- The canonical source walk has exactly the recorded auxiliary height. -/
theorem auxSourceWalk_length
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.length =
      auxHeight C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]
    simp [hZero]
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]
    simp only [SimpleGraph.Walk.length_cons]
    rw [auxSourceWalk_length C ambientRoot hScores u]
    omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- Auxiliary height is a genuine tree distance from the canonical source. -/
theorem auxHeight_eq_dist_auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v := by
  have hPath :=
    auxSourceWalk_isPath C ambientRoot hScores v
  have hDist :=
    tree_path_length_eq_dist
      (T := T) (auxSourceWalk C ambientRoot hScores v).2 hPath
  have hLen :=
    auxSourceWalk_length C ambientRoot hScores v
  change
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v
  calc
    auxHeight C ambientRoot hScores v =
        (auxSourceWalk C ambientRoot hScores v).2.length := hLen.symm
    _ = T.graph.dist v (auxSource C ambientRoot hScores v) := hDist
    _ = T.graph.dist (auxSource C ambientRoot hScores v) v :=
      T.graph.dist_comm

/-- A zero-height vertex is its own canonical source. -/
theorem auxSource_eq_self_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSource C ambientRoot hScores v = v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]

/-- At positive height, passing to the canonical predecessor does not change
the canonical source. -/
theorem auxSource_auxParent_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSource C ambientRoot hScores
        (auxParent C ambientRoot hScores v) =
      auxSource C ambientRoot hScores v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]

/-- Every canonical source really has auxiliary height zero. -/
theorem auxSource_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores
      (auxSource C ambientRoot hScores v) = 0 := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSource_eq_self_of_height_zero
      C ambientRoot hScores v hZero]
    exact hZero
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    have hSource :=
      auxSource_auxParent_of_pos
        C ambientRoot hScores v hPos
    rw [← hSource]
    exact
      auxSource_height_zero C ambientRoot hScores
        (auxParent C ambientRoot hScores v)
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- Every vertex appearing on the canonical source walk has the same canonical
source as the walk's starting vertex.  Thus source fibres are path-connected
inside the ambient tree. -/
theorem auxSource_eq_of_mem_auxSourceWalk_support
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxSource C ambientRoot hScores x =
      auxSource C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero] at hx
    simp at hx
    subst x
    rfl
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hSource :
        auxSource C ambientRoot hScores u =
          auxSource C ambientRoot hScores v := by
      simpa [u] using
        auxSource_auxParent_of_pos C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos] at hx
    simp only [SimpleGraph.Walk.support_cons] at hx
    rcases List.mem_cons.mp hx with hEq | hxTail
    · subst x
      rfl
    · have hRec :=
        auxSource_eq_of_mem_auxSourceWalk_support
          C ambientRoot hScores u x hxTail
      exact hRec.trans hSource
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

end OrientedBranch

end TreeStack
