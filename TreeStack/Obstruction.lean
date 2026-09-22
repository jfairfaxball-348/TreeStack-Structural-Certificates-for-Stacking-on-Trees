import Mathlib
import TreeStack.Estimator
import TreeStack.RootScore

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The explicit rooted estimator obstruction: `sigma T r - 1` pebbles at
the selected root, one pebble at every other leaf, and zero elsewhere. -/
noncomputable def obstruction (T : FiniteTree V) (r : V) : Configuration V := by
  classical
  exact fun v =>
    if v = r then
      sigma T r - 1
    else if v ∈ leafVertices T r then
      1
    else
      0

@[simp] theorem obstruction_root (T : FiniteTree V) (r : V) :
    obstruction T r r = sigma T r - 1 := by
  simp [obstruction]

theorem obstruction_apply_ne (T : FiniteTree V) (r v : V) (hvr : v ≠ r) :
    obstruction T r v = if T.graph.degree v = 1 then 1 else 0 := by
  classical
  simp [obstruction, leafVertices, hvr]

theorem obstruction_leaf (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v = 1) :
    obstruction T r v = 1 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

theorem obstruction_internal (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v ≠ 1) :
    obstruction T r v = 0 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

/-- Exact mass of the explicit rooted obstruction. -/
theorem mass_obstruction (T : FiniteTree V) (r : V) :
    mass (obstruction T r) = rootEstimate T r - 1 := by
  classical
  have hsigma : 1 ≤ sigma T r := by
    simp [sigma]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v =
        leafCount T r := by
    rw [leafCount]
    calc
      (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) =
          ∑ v ∈ (Finset.univ : Finset V).erase r,
            if v ∈ leafVertices T r then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvr : v ≠ r := by
                exact (Finset.mem_erase.mp hv).1
              simp [obstruction, hvr]
      _ = (((Finset.univ : Finset V).erase r).filter
            (fun v => v ∈ leafVertices T r)).card := by
              simpa using
                (Finset.sum_boole (R := ℕ)
                  (fun v : V => v ∈ leafVertices T r)
                  ((Finset.univ : Finset V).erase r))
      _ = (leafVertices T r).card := by
              congr 1
              ext v
              simp [leafVertices]
  rw [mass]
  calc
    (∑ v : V, obstruction T r v) =
        (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) +
          obstruction T r r := by
            symm
            exact Finset.sum_erase_add (Finset.univ : Finset V)
              (obstruction T r) (Finset.mem_univ r)
    _ = leafCount T r + (sigma T r - 1) := by
          rw [hsum, obstruction_root]
    _ = rootEstimate T r - 1 := by
          rw [rootEstimate]
          omega

namespace OrientedBranch

/-- Recursive obstruction height on an oriented branch.  The recursion follows
exactly the genuine child branches used by `branchMessage`. -/
noncomputable def obstructionHeight (B : OrientedBranch T) : ℕ :=
  if hLeaf : T.graph.degree B.root = 1 then
    1
  else
    3 + 2 *
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }

theorem obstructionHeight_leaf (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    obstructionHeight B = 1 := by
  rw [obstructionHeight]
  simp [hLeaf]

theorem obstructionHeight_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    obstructionHeight B =
      3 + 2 *
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            obstructionHeight
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 })
          else
            0 := by
  rw [obstructionHeight]
  simp [show T.graph.degree B.root ≠ 1 by omega]

theorem obstructionHeight_pos (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  rw [obstructionHeight]
  split_ifs <;> positivity


/-- A degree-one branch root has no genuine child besides its boundary parent. -/
theorem no_child_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) (v : V) :
    ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
  intro h
  have huniq :
      ∃! w : V, T.graph.Adj B.root w :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hLeaf
  exact h.2 (huniq.unique h.1 B.adj)

/-- An internal branch root has at least one genuine child. -/
theorem child_nonempty_of_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    Nonempty B.Child := by
  by_contra hnone
  have huniq : ∃! w : V, T.graph.Adj B.root w := by
    refine ⟨B.parent, B.adj, ?_⟩
    intro y hy
    by_contra hyne
    exact hnone
      ⟨{ vertex := y
         adj := hy
         ne_parent := hyne }⟩
  have hdeg :
      T.graph.degree B.root = 1 :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr huniq
  omega


/-- In a tree, every path is the unique shortest path between its endpoints. -/
theorem tree_path_length_eq_dist {u v : V} (p : T.graph.Walk u v)
    (hp : p.IsPath) :
    p.length = T.graph.dist u v := by
  obtain ⟨q, hq, hqdist⟩ :=
    T.isTree.connected.preconnected.exists_path_of_dist u v
  have hEq :
      (⟨p, hp⟩ : T.graph.Path u v) =
        ⟨q, hq⟩ :=
    T.isTree.isAcyclic.subsingleton_path u v |>.elim _ _
  have hpq : p = q := congrArg Subtype.val hEq
  rw [hpq, hqdist]

/-- A degree-one oriented branch consists only of its root. -/
theorem vertices_eq_singleton_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    B.vertices = {B.root} := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    by_cases hxr : x = B.root
    · simpa [hxr]
    · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
        ⟨c, hc⟩
      exact
        (B.no_child_of_degree_one hLeaf c.vertex
          ⟨c.adj, c.ne_parent⟩).elim
  · intro x hx
    simpa using hx


/-- Distances into a genuine child branch increase by exactly one when
measured from the parent-branch root. -/
theorem dist_root_eq_child_dist_add_one
    (B : OrientedBranch T) (c : B.Child) {x : V}
    (hx : x ∈ (B.childBranch c).vertices) :
    T.graph.dist B.root x =
      T.graph.dist c.vertex x + 1 := by
  classical
  have hcComp :
      c.vertex ∈ (B.childBranch c).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ (B.childBranch c).component.supp := by
    simpa [vertices] using hx
  have hreach :
      (B.childBranch c).deletedGraph.Reachable c.vertex x :=
    (B.childBranch c).component.reachable_of_mem_supp hcComp hxComp
  obtain ⟨p₀, hp₀⟩ := hreach.exists_isPath
  have hle :
      (B.childBranch c).deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let p : T.graph.Walk c.vertex x := p₀.mapLe hle
  have hp : p.IsPath := hp₀.mapLe hle
  have hrootNot : B.root ∉ p.support := by
    intro hroot
    have hroot₀ : B.root ∈ p₀.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hroot
    let q₀ :=
      p₀.takeUntil B.root hroot₀
    have hrootMem :
        B.root ∈ (B.childBranch c).vertices := by
      rw [vertices, Set.mem_toFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, component]
      exact
        (SimpleGraph.ConnectedComponent.sound q₀.reachable).symm
    exact
      (B.childBranch c).parent_not_mem_vertices
        (by simpa [childBranch] using hrootMem)
  let q : T.graph.Walk B.root x := p.cons c.adj
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hp, hrootNot⟩
  have hpdist := tree_path_length_eq_dist (T := T) p hp
  have hqdist := tree_path_length_eq_dist (T := T) q hq
  simpa [q, p, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_mapLe, hpdist] using hqdist


/-- Child choices form a finite type because a child is determined by its
underlying vertex. -/
noncomputable instance childFintype (B : OrientedBranch T) :
    Fintype B.Child :=
  Fintype.ofInjective
    (fun c : B.Child => c.vertex)
    (fun _ _ h => Child.eq_of_vertex_eq h)

/-- A child vertex, tagged by the unique genuine child branch containing it. -/
abbrev ChildVertex (B : OrientedBranch T) :=
  Σ c : B.Child, {x : V // x ∈ (B.childBranch c).vertices}

/-- The non-root vertices of an oriented branch. -/
abbrev ProperVertex (B : OrientedBranch T) :=
  {x : V // x ∈ B.vertices.erase B.root}

/-- The child branches partition the non-root vertices of an oriented branch. -/
noncomputable def childVertexEquivProper (B : OrientedBranch T) :
    B.ChildVertex ≃ B.ProperVertex := by
  classical
  let chosen : B.ProperVertex → B.Child := fun x =>
    Classical.choose
      (B.exists_childBranch_mem_of_mem_vertices_ne_root
        (Finset.mem_erase.mp x.2).2
        (by
          intro h
          exact (Finset.mem_erase.mp x.2).1 h))
  have hchosen :
      ∀ x : B.ProperVertex,
        x.1 ∈ (B.childBranch (chosen x)).vertices := by
    intro x
    exact
      Classical.choose_spec
        (B.exists_childBranch_mem_of_mem_vertices_ne_root
          (Finset.mem_erase.mp x.2).2
          (by
            intro h
            exact (Finset.mem_erase.mp x.2).1 h))
  refine
    { toFun := fun z =>
        ⟨z.2.1, Finset.mem_erase.mpr ⟨?_, B.childBranch_vertices_subset z.1 z.2.2⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    subst h
    exact (B.childBranch z.1).parent_not_mem_vertices z.2.2
  · intro z
    apply Sigma.ext
    · apply Child.eq_of_vertex_eq
      by_contra hne
      have hdisj :=
        B.childBranch_vertices_disjoint z.1 (chosen ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨by
              intro h
              subst h
              exact (B.childBranch z.1).parent_not_mem_vertices z.2.2,
             B.childBranch_vertices_subset z.1 z.2.2⟩⟩) hne
      exact
        (Finset.disjoint_left.mp hdisj) z.2.2
          (hchosen
            ⟨z.2.1,
              Finset.mem_erase.mpr
                ⟨by
                  intro h
                  subst h
                  exact (B.childBranch z.1).parent_not_mem_vertices z.2.2,
                 B.childBranch_vertices_subset z.1 z.2.2⟩⟩)
    · apply Subtype.ext
      rfl
  · intro x
    apply Subtype.ext
    rfl


/-- Summing over every child interior is exactly summing over the non-root
vertices of the parent branch. -/
theorem sum_childBranch_vertices (B : OrientedBranch T) (f : V → ℕ) :
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
      ∑ x ∈ B.vertices.erase B.root, f x := by
  classical
  calc
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
        ∑ c : B.Child,
          ∑ x : {x : V // x ∈ (B.childBranch c).vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_subtype
              (B.childBranch c).vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : B.ChildVertex, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : B.ProperVertex, f x.1 := by
          exact
            Fintype.sum_equiv B.childVertexEquivProper
              (fun z : B.ChildVertex => f z.2.1)
              (fun x : B.ProperVertex => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ B.vertices.erase B.root, f x := by
          symm
          exact
            Finset.sum_subtype
              (B.vertices.erase B.root)
              (fun _ => Iff.rfl) f

/-- Every descendant branch of the selected root is occupied by the explicit
obstruction, and its exact recursive message is the negative obstruction
height.  The hypothesis says precisely that the selected root lies outside
the descendant-side component. -/
theorem obstruction_branchMessage (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices) :
    B.Occupied (obstruction T r) ∧
      branchMessage (obstruction T r) B =
        some (-(B.obstructionHeight : ℤ)) := by
  classical
  have hRootNe : B.root ≠ r := by
    intro h
    subst r
    exact hAway B.root_mem_vertices
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hRoot :
        obstruction T r B.root = 1 :=
      obstruction_leaf T r B.root hRootNe hLeaf
    have hOcc : B.Occupied (obstruction T r) := by
      refine ⟨B.root, B.root_mem_vertices, ?_⟩
      rw [hRoot]
      omega
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = 1 := by
      rw [effectiveInput, childMessageSum]
      simp [hRoot, B.no_child_of_degree_one hLeaf]
    rw [hEff, B.obstructionHeight_leaf hLeaf]
    norm_num [F]
  · have hPos : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    have hRoot :
        obstruction T r B.root = 0 :=
      obstruction_internal T r B.root hRootNe hLeaf
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    have hChildSum :
        childMessageSum (obstruction T r) B = -(H : ℤ) := by
      rw [childMessageSum]
      dsimp [H]
      push_cast
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hAwayChild :
            r ∉ (B.childBranch c).vertices := by
          intro hr
          exact hAway (B.childBranch_vertices_subset c hr)
        have hRec :=
          obstruction_branchMessage r (B.childBranch c) hAwayChild
        simp [h, c, hRec.2]
      · simp [h]
    have hOcc : B.Occupied (obstruction T r) := by
      let c : B.Child := Classical.choice (B.child_nonempty_of_internal hInternal)
      have hAwayChild :
          r ∉ (B.childBranch c).vertices := by
        intro hr
        exact hAway (B.childBranch_vertices_subset c hr)
      have hRec :=
        obstruction_branchMessage r (B.childBranch c) hAwayChild
      rcases hRec.1 with ⟨w, hw, hpos⟩
      exact ⟨w, B.childBranch_vertices_subset c hw, hpos⟩
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = -(H : ℤ) := by
      rw [effectiveInput, hRoot, hChildSum]
      simp
    rw [hEff]
    have hle : -(H : ℤ) ≤ 1 := by omega
    rw [F_of_le_one hle, B.obstructionHeight_internal hInternal]
    dsimp [H]
    push_cast
    ring
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _


/-- The same tree edge with its orientation reversed. -/
def reverseBranch (B : OrientedBranch T) : OrientedBranch T where
  root := B.parent
  parent := B.root
  adj := B.adj.symm

@[simp] theorem reverseBranch_root (B : OrientedBranch T) :
    B.reverseBranch.root = B.parent := rfl

@[simp] theorem reverseBranch_parent (B : OrientedBranch T) :
    B.reverseBranch.parent = B.root := rfl

@[simp] theorem reverseBranch_reverse (B : OrientedBranch T) :
    B.reverseBranch.reverseBranch = B := by
  cases B
  rfl

/-- A rooted score at the root of an oriented branch splits into the branch's
effective input from its genuine children plus the message from the reverse
(parent-side) branch. -/
theorem score_eq_effectiveInput_add_reverse
    (C : Configuration V) (B : OrientedBranch T) :
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C B.reverseBranch) := by
  classical
  have hTerm (u : V) :
      rootMessageTerm T C B.root u =
        (if h : T.graph.Adj B.root u ∧ u ≠ B.parent then
          messageContribution
            (branchMessage C
              (B.childBranch
                { vertex := u
                  adj := h.1
                  ne_parent := h.2 }))
        else
          0) +
        if u = B.parent then
          messageContribution (branchMessage C B.reverseBranch)
        else
          0 := by
    by_cases hup : u = B.parent
    · subst u
      simp [rootMessageTerm, reverseBranch, incidentBranch, B.adj]
    · by_cases hadj : T.graph.Adj B.root u
      · have hadj' : T.graph.Adj u B.root := hadj.symm
        simp [rootMessageTerm, reverseBranch, incidentBranch, childBranch,
          hadj, hadj', hup]
      · have hadj' : ¬ T.graph.Adj u B.root := by
          intro h
          exact hadj h.symm
        simp [rootMessageTerm, hadj, hadj', hup]
  rw [score, rootMessageSum, effectiveInput, childMessageSum]
  simp_rw [hTerm]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- If an oriented branch is configuration-empty, its effective input is zero.
This does not identify the branch message with integer zero: its message is
still the separate value \`EMPTY\`. -/
theorem effectiveInput_eq_zero_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.Occupied C) :
    B.effectiveInput C = 0 := by
  classical
  have hZero :=
    (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hRoot : C B.root = 0 :=
    hZero B.root B.root_mem_vertices
  rw [effectiveInput, childMessageSum, hRoot]
  simp only [Nat.cast_zero, zero_add]
  apply Finset.sum_eq_zero
  intro v hv
  by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
  · let c : B.Child :=
      { vertex := v
        adj := h.1
        ne_parent := h.2 }
    have hChildEmpty : ¬ (B.childBranch c).Occupied C := by
      intro hOcc
      rcases hOcc with ⟨w, hw, hpos⟩
      exact hEmpty
        ⟨w, B.childBranch_vertices_subset c hw, hpos⟩
    rw [dif_pos h]
    change
      messageContribution
          (branchMessage C (B.childBranch c)) = 0
    rw [branchMessage_eq_empty_of_not_occupied C (B.childBranch c) hChildEmpty]
    rfl
  · simp [h]

/-- Zero score propagates from the parent of a descendant obstruction branch
to that branch root.  The proof uses the exact reverse-side effective input,
so no executable task is ever introduced for an empty branch. -/
theorem obstruction_score_root_of_parent_score_zero
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    score T (obstruction T r) B.root = 0 := by
  classical
  let C : Configuration V := obstruction T r
  let R : OrientedBranch T := B.reverseBranch
  have hData := obstruction_branchMessage r B hAway
  have hOccB : B.Occupied C := by
    simpa [C] using hData.1
  have hMsgB :
      branchMessage C B =
        some (-(B.obstructionHeight : ℤ)) := by
    simpa [C] using hData.2
  have hFEff :
      F (B.effectiveInput C) =
        -(B.obstructionHeight : ℤ) := by
    have hDef :=
      branchMessage_eq_some_of_occupied C B hOccB
    rw [hMsgB] at hDef
    exact Option.some.inj hDef.symm
  have hParentDecomp :=
    score_eq_effectiveInput_add_reverse C R
  have hRevRev : R.reverseBranch = B := by
    simp [R]
  have hEffR :
      R.effectiveInput C = (B.obstructionHeight : ℤ) := by
    rw [hParent, hRevRev, hMsgB] at hParentDecomp
    simp only [messageContribution_some] at hParentDecomp
    linarith
  have hOccR : R.Occupied C := by
    by_contra hEmpty
    have hZero :=
      effectiveInput_eq_zero_of_not_occupied C R hEmpty
    rw [hZero] at hEffR
    have hPos : 0 < (B.obstructionHeight : ℤ) := by
      exact_mod_cast B.obstructionHeight_pos
    linarith
  have hMsgR :
      branchMessage C R =
        some (F (B.obstructionHeight : ℤ)) := by
    rw [branchMessage_eq_some_of_occupied C R hOccR, hEffR]
  have hRootDecomp :=
    score_eq_effectiveInput_add_reverse C B
  change
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C R) at hRootDecomp
  rw [hMsgR] at hRootDecomp
  simp only [messageContribution_some] at hRootDecomp
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hHeight : B.obstructionHeight = 1 :=
      B.obstructionHeight_leaf hLeaf
    have hFEff' :
        F (B.effectiveInput C) = -(2 * (0 : ℤ) + 1) := by
      simpa [hHeight] using hFEff
    have hInput :
        B.effectiveInput C = 1 := by
      exact
        (F_eq_neg_odd_iff (z := B.effectiveInput C) (r := (0 : ℤ))
          (by omega)).1 hFEff'
    rw [hHeight] at hRootDecomp
    norm_num [F] at hRootDecomp
    linarith
  · have hPosDegree : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    have hHeight :
        B.obstructionHeight = 3 + 2 * H := by
      simpa [H] using B.obstructionHeight_internal hInternal
    have hFEff' :
        F (B.effectiveInput C) =
          -(2 * ((H : ℤ) + 1) + 1) := by
      rw [hHeight] at hFEff
      push_cast at hFEff
      linarith
    have hInput :
        B.effectiveInput C = -(H : ℤ) := by
      have hInv :=
        (F_eq_neg_odd_iff
          (z := B.effectiveInput C)
          (r := (H : ℤ) + 1) (by positivity)).1 hFEff'
      linarith
    have hFHeight :
        F (B.obstructionHeight : ℤ) = (H : ℤ) := by
      apply
        (F_eq_nonneg_iff
          (z := (B.obstructionHeight : ℤ))
          (k := (H : ℤ)) (by positivity)).2
      right
      rw [hHeight]
      push_cast
      ring
    rw [hFHeight, hInput] at hRootDecomp
    linarith

end OrientedBranch

end TreeStack
