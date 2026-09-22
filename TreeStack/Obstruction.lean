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

end OrientedBranch

end TreeStack
