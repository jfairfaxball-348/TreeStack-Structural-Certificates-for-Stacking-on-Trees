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
    T.isTree.connected.exists_path_of_dist u v
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
    have hxr : x = B.root := by
      simpa using hx
    subst x
    exact B.root_mem_vertices



/-- Every vertex of an oriented branch is one edge farther from the external
parent than from the branch root. -/
theorem dist_parent_eq_root_dist_add_one
    (B : OrientedBranch T) {x : V} (hx : x ∈ B.vertices) :
    T.graph.dist B.parent x =
      T.graph.dist B.root x + 1 := by
  classical
  have hrComp :
      B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hreach :
      B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  obtain ⟨p₀, hp₀⟩ := hreach.exists_isPath
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let p : T.graph.Walk B.root x := p₀.mapLe hle
  have hp : p.IsPath := hp₀.mapLe hle
  have hparentNot : B.parent ∉ p.support := by
    intro hparent
    have hparent₀ : B.parent ∈ p₀.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hparent
    let q₀ := p₀.takeUntil B.parent hparent₀
    have hparentMem : B.parent ∈ B.vertices := by
      rw [vertices, Set.mem_toFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, component]
      exact
        (SimpleGraph.ConnectedComponent.sound q₀.reachable).symm
    exact B.parent_not_mem_vertices hparentMem
  let q : T.graph.Walk B.parent x := p.cons B.adj.symm
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hp, hparentNot⟩
  have hpdist := tree_path_length_eq_dist (T := T) p hp
  have hqdist := tree_path_length_eq_dist (T := T) q hq
  simpa [q, p, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_mapLe, hpdist] using hqdist.symm

/-- Distances into a genuine child branch increase by exactly one when
measured from the parent-branch root. -/
theorem dist_root_eq_child_dist_add_one
    (B : OrientedBranch T) (c : B.Child) {x : V}
    (hx : x ∈ (B.childBranch c).vertices) :
    T.graph.dist B.root x =
      T.graph.dist c.vertex x + 1 := by
  simpa [childBranch] using
    (B.childBranch c).dist_parent_eq_root_dist_add_one hx

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
  have hnotRoot :
      ∀ (c : B.Child) {x : V},
        x ∈ (B.childBranch c).vertices → x ≠ B.root := by
    intro c x hx hxr
    apply (B.childBranch c).parent_not_mem_vertices
    simpa [childBranch, hxr] using hx
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
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2,
              B.childBranch_vertices_subset z.1 z.2.2⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    apply Sigma.ext
    · apply Child.eq_of_vertex_eq
      by_contra hne
      let x : B.ProperVertex :=
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2,
              B.childBranch_vertices_subset z.1 z.2.2⟩⟩
      have hdisj :=
        B.childBranch_vertices_disjoint z.1 (chosen x) hne
      exact
        (Finset.disjoint_left.mp hdisj) z.2.2 (hchosen x)
    · apply Subtype.ext
      rfl
  · intro x
    apply Subtype.ext
    rfl

/-- The finite set of genuine child vertices of an oriented branch. -/
noncomputable def childFinset (B : OrientedBranch T) : Finset V :=
  (T.graph.neighborFinset B.root).erase B.parent

@[simp] theorem mem_childFinset (B : OrientedBranch T) (v : V) :
    v ∈ B.childFinset ↔
      T.graph.Adj B.root v ∧ v ≠ B.parent := by
  classical
  simp [childFinset, and_left_comm, and_comm]

/-- A dependent sum over genuine child vertices agrees with the corresponding
sum over the finite child type. -/
theorem sum_dite_children {M : Type*} [AddCommMonoid M]
    (B : OrientedBranch T) (f : B.Child → M) :
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        f { vertex := v, adj := h.1, ne_parent := h.2 }
      else
        0) =
      ∑ c : B.Child, f c := by
  classical
  let term : V → M := fun v =>
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      f { vertex := v, adj := h.1, ne_parent := h.2 }
    else
      0
  have hrestrict :
      (∑ v ∈ B.childFinset, term v) =
        ∑ v : V, term v := by
    apply Finset.sum_subset (Finset.subset_univ B.childFinset)
    intro v hvUniv hvNot
    have hnot :
        ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
      intro h
      exact hvNot ((B.mem_childFinset v).2 h)
    simp [term, hnot]
  rw [← hrestrict]
  change
    (∑ v ∈ B.childFinset, term v) =
      ∑ c ∈ (Finset.univ : Finset B.Child), f c
  apply Finset.sum_bij
    (fun v hv =>
      { vertex := v
        adj := ((B.mem_childFinset v).1 hv).1
        ne_parent := ((B.mem_childFinset v).1 hv).2 })
  · intro v hv
    exact Finset.mem_univ _
  · intro v₁ hv₁ v₂ hv₂ hEq
    exact congrArg Child.vertex hEq
  · intro c hc
    refine ⟨c.vertex, ?_, ?_⟩
    · exact (B.mem_childFinset c.vertex).2 ⟨c.adj, c.ne_parent⟩
    · apply Child.eq_of_vertex_eq
      rfl
  · intro v hv
    have h := (B.mem_childFinset v).1 hv
    simp [term, h]

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


/-- Weighted internal-vertex potential carried by an oriented branch. -/
noncomputable def internalPotential (B : OrientedBranch T) : ℕ :=
  ∑ x ∈ B.vertices,
    if 1 < T.graph.degree x then
      T.graph.degree x * 2 ^ T.graph.dist B.root x
    else
      0

theorem card_childFinset_add_one (B : OrientedBranch T) :
    B.childFinset.card + 1 = T.graph.degree B.root := by
  classical
  have hp : B.parent ∈ T.graph.neighborFinset B.root := by
    simpa using B.adj
  simpa [childFinset] using
    Finset.card_erase_add_one hp

/-- Doubling the total child potential exactly recovers the parent-rooted
potential of all non-root branch vertices. -/
theorem two_mul_sum_child_internalPotential (B : OrientedBranch T) :
    2 * (∑ c : B.Child, (B.childBranch c).internalPotential) =
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0 := by
  classical
  calc
    2 * (∑ c : B.Child, (B.childBranch c).internalPotential) =
        ∑ c : B.Child, 2 * (B.childBranch c).internalPotential := by
          rw [Finset.mul_sum]
    _ = ∑ c : B.Child,
        ∑ x ∈ (B.childBranch c).vertices,
          if 1 < T.graph.degree x then
            T.graph.degree x * 2 ^ T.graph.dist B.root x
          else
            0 := by
          apply Finset.sum_congr rfl
          intro c _
          rw [internalPotential, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hInt : 1 < T.graph.degree x
          · have hdist :=
              B.dist_root_eq_child_dist_add_one c hx
            simp [hInt, hdist, pow_succ]
            ring
          · simp [hInt]
    _ = ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0 := by
          exact
            B.sum_childBranch_vertices
              (fun x =>
                if 1 < T.graph.degree x then
                  T.graph.degree x * 2 ^ T.graph.dist B.root x
                else
                  0)


/-- Closed form for the recursive obstruction height. -/
theorem obstructionHeight_eq_one_add_two_mul_internalPotential
    (B : OrientedBranch T) :
    B.obstructionHeight = 1 + 2 * B.internalPotential := by
  classical
  by_cases hLeaf : T.graph.degree B.root = 1
  · rw [B.obstructionHeight_leaf hLeaf, internalPotential,
      B.vertices_eq_singleton_of_degree_one hLeaf]
    simp [hLeaf]
  · have hPos : 0 < T.graph.degree B.root := by
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
    let P : ℕ :=
      ∑ c : B.Child, (B.childBranch c).internalPotential
    have hRec :
        H =
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              1 + 2 *
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }).internalPotential
            else
              0 := by
      dsimp [H]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · simp [h,
          obstructionHeight_eq_one_add_two_mul_internalPotential
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })]
      · simp [h]
    have hCount :
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
          B.childFinset.card := by
      calc
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
            ((Finset.univ : Finset V).filter
              (fun v => T.graph.Adj B.root v ∧ v ≠ B.parent)).card := by
                simpa using
                  (Finset.sum_boole (R := ℕ)
                    (fun v : V =>
                      T.graph.Adj B.root v ∧ v ≠ B.parent)
                    (Finset.univ : Finset V))
        _ = B.childFinset.card := by
              congr 1
              ext v
              simp [childFinset, and_left_comm, and_comm]
    have hPSum :
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 }).internalPotential
          else
            0) = P := by
      dsimp [P]
      exact
        B.sum_dite_children
          (fun c : B.Child => (B.childBranch c).internalPotential)
    have hH :
        H = B.childFinset.card + 2 * P := by
      rw [hRec]
      calc
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            1 + 2 *
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 }).internalPotential
          else
            0) =
            (∑ v : V,
              if T.graph.Adj B.root v ∧ v ≠ B.parent then
                (1 : ℕ)
              else
                0) +
              2 *
                (∑ v : V,
                  if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }).internalPotential
                  else
                    0) := by
                      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro v _
                      by_cases h :
                          T.graph.Adj B.root v ∧ v ≠ B.parent
                      · simp [h]
                      · simp [h]
        _ = B.childFinset.card + 2 * P := by
              rw [hCount, hPSum]
    let Q : ℕ :=
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
    have hQ : 2 * P = Q := by
      dsimp [P, Q]
      exact B.two_mul_sum_child_internalPotential
    have hPot :
        B.internalPotential = Q + T.graph.degree B.root := by
      let weight : V → ℕ := fun x =>
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
      rw [internalPotential]
      change
        (∑ x ∈ B.vertices, weight x) =
          Q + T.graph.degree B.root
      calc
        (∑ x ∈ B.vertices, weight x) =
            (∑ x ∈ B.vertices.erase B.root, weight x) +
              weight B.root := by
                symm
                exact
                  Finset.sum_erase_add B.vertices weight
                    B.root_mem_vertices
        _ = Q + T.graph.degree B.root := by
              dsimp [Q, weight]
              simp [hInternal]
    rw [B.obstructionHeight_internal hInternal]
    change 3 + 2 * H = 1 + 2 * B.internalPotential
    have hCard := B.card_childFinset_add_one
    omega
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _

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
    ring_nf
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
      have hadj : T.graph.Adj B.parent B.root := B.adj.symm
      rw [rootMessageTerm]
      simp only [dif_pos hadj]
      change
        messageContribution
            (branchMessage C (incidentBranch T B.root B.parent hadj)) =
          messageContribution (branchMessage C B.reverseBranch)
      congr 2
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
  have hParentDecomp :
      score T C B.parent =
        R.effectiveInput C +
          messageContribution (branchMessage C R.reverseBranch) := by
    simpa [R] using score_eq_effectiveInput_add_reverse C R
  have hRevRev : R.reverseBranch = B := by
    simp [R]
  have hParentC : score T C B.parent = 0 := by
    simpa [C] using hParent
  have hEffR :
      R.effectiveInput C = (B.obstructionHeight : ℤ) := by
    rw [hParentC, hRevRev, hMsgB] at hParentDecomp
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

/-- A neighbor of a selected root, oriented toward that root. -/
abbrev RootNeighbor (T : FiniteTree V) (r : V) :=
  {u : V // T.graph.Adj u r}

namespace RootNeighbor

noncomputable def branch {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) : OrientedBranch T :=
  incidentBranch T r n.1 n.2

@[simp] theorem branch_root {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.root = n.1 := rfl

@[simp] theorem branch_parent {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.parent = r := rfl

end RootNeighbor

/-- A vertex tagged by the unique incident root branch containing it. -/
abbrev RootBranchVertex (T : FiniteTree V) (r : V) :=
  Σ n : RootNeighbor T r,
    {x : V // x ∈ n.branch.vertices}

/-- A non-root vertex. -/
abbrev RootProperVertex (r : V) :=
  {x : V // x ∈ (Finset.univ : Finset V).erase r}

/-- Incident branches at a root partition all vertices other than the root. -/
noncomputable def rootBranchVertexEquivProper
    (T : FiniteTree V) (r : V) :
    RootBranchVertex T r ≃ RootProperVertex r := by
  classical
  have hex :
      ∀ x : RootProperVertex r,
        ∃ n : RootNeighbor T r, x.1 ∈ n.branch.vertices := by
    intro x
    have hxr : x.1 ≠ r := (Finset.mem_erase.mp x.2).1
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hxr with
      ⟨u, h, hx⟩
    exact ⟨⟨u, h⟩, hx⟩
  let chosen : RootProperVertex r → RootNeighbor T r :=
    fun x => Classical.choose (hex x)
  have hchosen :
      ∀ x : RootProperVertex r,
        x.1 ∈ (chosen x).branch.vertices := by
    intro x
    exact Classical.choose_spec (hex x)
  refine
    { toFun := fun z =>
        ⟨z.2.1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    subst h
    exact z.1.branch.parent_not_mem_vertices z.2.2
  · intro z
    apply Sigma.ext
    · apply Subtype.ext
      by_contra hne
      let x : RootProperVertex r :=
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨by
              intro h
              subst h
              exact z.1.branch.parent_not_mem_vertices z.2.2,
             Finset.mem_univ _⟩⟩
      have hdisj :=
        incidentBranch_vertices_disjoint
          (T := T) r z.1.2 (chosen x).2 hne
      exact
        (Finset.disjoint_left.mp hdisj)
          z.2.2 (hchosen x)
    · apply Subtype.ext
      rfl
  · intro x
    apply Subtype.ext
    rfl

/-- A dependent sum over root neighbors agrees with the corresponding sum over
the finite subtype of actual neighbors. -/
theorem sum_dite_rootNeighbors {M : Type*} [AddCommMonoid M]
    (T : FiniteTree V) (r : V) (f : RootNeighbor T r → M) :
    (∑ u : V,
      if h : T.graph.Adj u r then
        f ⟨u, h⟩
      else
        0) =
      ∑ n : RootNeighbor T r, f n := by
  classical
  let term : V → M := fun u =>
    if h : T.graph.Adj u r then f ⟨u, h⟩ else 0
  have hrestrict :
      (∑ u ∈ T.graph.neighborFinset r, term u) =
        ∑ u : V, term u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u huUniv huNot
    have hnot : ¬ T.graph.Adj u r := by
      intro h
      exact huNot (by simpa using h.symm)
    simp [term, hnot]
  rw [← hrestrict]
  change
    (∑ u ∈ T.graph.neighborFinset r, term u) =
      ∑ n ∈ (Finset.univ : Finset (RootNeighbor T r)), f n
  apply Finset.sum_bij
    (fun u hu =>
      ⟨u, by simpa using
        (T.graph.mem_neighborFinset.mp hu).symm⟩)
  · intro u hu
    exact Finset.mem_univ _
  · intro u₁ hu₁ u₂ hu₂ hEq
    exact congrArg Subtype.val hEq
  · intro n hn
    refine ⟨n.1, ?_, ?_⟩
    · exact T.graph.mem_neighborFinset.mpr n.2.symm
    · apply Subtype.ext
      rfl
  · intro u hu
    have h : T.graph.Adj u r := by
      simpa using (T.graph.mem_neighborFinset.mp hu).symm
    simp [term, h]

/-- The number of root neighbors is the degree of the root. -/
theorem card_rootNeighbor (T : FiniteTree V) (r : V) :
    Fintype.card (RootNeighbor T r) = T.graph.degree r := by
  classical
  calc
    Fintype.card (RootNeighbor T r) =
        ∑ _n : RootNeighbor T r, (1 : ℕ) := by simp
    _ = ∑ u : V,
        if T.graph.Adj u r then (1 : ℕ) else 0 := by
          symm
          simpa using
            sum_dite_rootNeighbors T r
              (fun _ : RootNeighbor T r => (1 : ℕ))
    _ = T.graph.degree r := by
          simpa [SimpleGraph.degree_eq_sum_if_adj, adj_comm]

/-- Summing over all incident branch interiors is exactly summing over all
non-root vertices. -/
theorem sum_rootBranch_vertices
    (T : FiniteTree V) (r : V) (f : V → ℕ) :
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
      ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
  classical
  calc
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
        ∑ n : RootNeighbor T r,
          ∑ x : {x : V // x ∈ n.branch.vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.sum_subtype
              n.branch.vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : RootBranchVertex T r, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : RootProperVertex r, f x.1 := by
          exact
            Fintype.sum_equiv
              (rootBranchVertexEquivProper T r)
              (fun z : RootBranchVertex T r => f z.2.1)
              (fun x : RootProperVertex r => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
          symm
          exact
            Finset.sum_subtype
              ((Finset.univ : Finset V).erase r)
              (fun _ => Iff.rfl) f

/-- Doubling all incident branch potentials recovers the root-distance
potential of every non-root internal vertex. -/
theorem two_mul_sum_root_internalPotential
    (T : FiniteTree V) (r : V) :
    2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) =
      ∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0 := by
  classical
  calc
    2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) =
        ∑ n : RootNeighbor T r, 2 * n.branch.internalPotential := by
          rw [Finset.mul_sum]
    _ = ∑ n : RootNeighbor T r,
        ∑ x ∈ n.branch.vertices,
          if 1 < T.graph.degree x then
            T.graph.degree x * 2 ^ T.graph.dist r x
          else
            0 := by
          apply Finset.sum_congr rfl
          intro n _
          rw [OrientedBranch.internalPotential, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hInt : 1 < T.graph.degree x
          · have hdist :=
              n.branch.dist_parent_eq_root_dist_add_one hx
            simp [RootNeighbor.branch, hInt] at hdist ⊢
            rw [hdist, pow_succ]
            ring
          · simp [hInt]
    _ = ∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0 := by
          exact
            sum_rootBranch_vertices T r
              (fun x =>
                if 1 < T.graph.degree x then
                  T.graph.degree x * 2 ^ T.graph.dist r x
                else
                  0)

/-- The incident obstruction heights at a selected root sum to exactly
\`sigma T r - 1\`. -/
theorem sum_root_obstructionHeight_eq_sigma_sub_one
    (T : FiniteTree V) (r : V) :
    (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
      sigma T r - 1 := by
  classical
  have hHeights :
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
        Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
    calc
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
          ∑ n : RootNeighbor T r,
            (1 + 2 * n.branch.internalPotential) := by
              apply Finset.sum_congr rfl
              intro n _
              rw [OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential]
      _ = Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
            rw [Finset.sum_add_distrib]
            simp [← Finset.mul_sum]
  have hPotential :=
    two_mul_sum_root_internalPotential T r
  have hInternal :
      (∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0) =
        ∑ x ∈ nonRootInternalVertices T r,
          T.graph.degree x * 2 ^ T.graph.dist r x := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [nonRootInternalVertices, and_left_comm, and_comm]
  rw [hHeights, card_rootNeighbor T r, hPotential, hInternal,
    sigma_corrected_expansion]
  omega

/-- At the selected root itself, the obstruction score is exactly zero. -/
theorem obstruction_score_selected_root
    (T : FiniteTree V) (r : V) :
    score T (obstruction T r) r = 0 := by
  classical
  have hTerms :
      rootMessageSum T (obstruction T r) r =
        -((sigma T r - 1 : ℕ) : ℤ) := by
    rw [rootMessageSum]
    calc
      (∑ u : V, rootMessageTerm T (obstruction T r) r u) =
          ∑ u : V,
            if h : T.graph.Adj u r then
              -((incidentBranch T r u h).obstructionHeight : ℤ)
            else
              0 := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases h : T.graph.Adj u r
                · let B : OrientedBranch T := incidentBranch T r u h
                  have hAway : r ∉ B.vertices := by
                    simpa [B, incidentBranch] using B.parent_not_mem_vertices
                  have hMsg :=
                    (B.obstruction_branchMessage r hAway).2
                  simp [rootMessageTerm, h, B, hMsg]
                · simp [rootMessageTerm, h]
      _ = ∑ n : RootNeighbor T r,
            -((n.branch.obstructionHeight : ℕ) : ℤ) := by
              exact
                sum_dite_rootNeighbors T r
                  (fun n : RootNeighbor T r =>
                    -((n.branch.obstructionHeight : ℕ) : ℤ))
      _ = -((∑ n : RootNeighbor T r,
            n.branch.obstructionHeight : ℕ) : ℤ) := by
              push_cast
              rw [Finset.sum_neg_distrib]
      _ = -((sigma T r - 1 : ℕ) : ℤ) := by
              rw [sum_root_obstructionHeight_eq_sigma_sub_one]
  rw [score, obstruction_root, hTerms]
  ring


namespace OrientedBranch

/-- Once the parent score is zero, zero score propagates recursively through
every vertex of a descendant obstruction branch. -/
theorem obstruction_scores_zero_on_vertices
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    ∀ x ∈ B.vertices,
      score T (obstruction T r) x = 0 := by
  classical
  have hRoot :
      score T (obstruction T r) B.root = 0 :=
    B.obstruction_score_root_of_parent_score_zero r hAway hParent
  intro x hx
  by_cases hxr : x = B.root
  · subst x
    exact hRoot
  · rcases
      B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxc⟩
    have hAwayChild :
        r ∉ (B.childBranch c).vertices := by
      intro hr
      exact hAway (B.childBranch_vertices_subset c hr)
    exact
      obstruction_scores_zero_on_vertices
        r (B.childBranch c) hAwayChild hRoot x hxc
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _

end OrientedBranch

/-- Every rooted score of the explicit estimator obstruction is exactly zero. -/
theorem obstruction_score_eq_zero
    (T : FiniteTree V) (r v : V) :
    score T (obstruction T r) v = 0 := by
  classical
  by_cases hvr : v = r
  · subst v
    exact obstruction_score_selected_root T r
  · rcases
      exists_incidentBranch_mem_of_ne_root (T := T) r hvr with
      ⟨u, h, hv⟩
    let B : OrientedBranch T := incidentBranch T r u h
    have hAway : r ∉ B.vertices := by
      simpa [B, incidentBranch] using B.parent_not_mem_vertices
    have hRoot :
        score T (obstruction T r) r = 0 :=
      obstruction_score_selected_root T r
    exact
      B.obstruction_scores_zero_on_vertices r hAway hRoot v
        (by simpa [B] using hv)

/-- The explicit obstruction is globally non-stackable. -/
theorem obstruction_not_stackable
    (T : FiniteTree V) (r : V) :
    ¬ Stackable T.graph (obstruction T r) := by
  classical
  apply
    (not_stackable_iff_all_scores_nonpos
      T (obstruction T r)).2
  intro v
  rw [obstruction_score_eq_zero T r v]

/-- The finite maximum defining the estimator is attained by some root. -/
theorem exists_rootEstimate_eq_estim
    (T : FiniteTree V) :
    ∃ r : V, rootEstimate T r = estim T := by
  classical
  have hnon :
      (Finset.univ : Finset V).Nonempty :=
    ⟨T.isTree.connected.nonempty.some, Finset.mem_univ _⟩
  have hmem :=
    Finset.sup_mem_of_nonempty
      (s := (Finset.univ : Finset V))
      (f := rootEstimate T) hnon
  rcases hmem with ⟨r, hr, hEq⟩
  refine ⟨r, ?_⟩
  simpa [estim] using hEq

/-- At an estimator-maximizing root there is a non-stackable configuration of
exactly \`estim T - 1\` pebbles. -/
theorem exists_nonstackable_mass_estim_sub_one
    [Nontrivial V] (T : FiniteTree V) :
    ∃ C : Configuration V,
      mass C = estim T - 1 ∧
        ¬ Stackable T.graph C := by
  classical
  rcases exists_rootEstimate_eq_estim T with ⟨r, hr⟩
  refine ⟨obstruction T r, ?_, obstruction_not_stackable T r⟩
  rw [mass_obstruction T r, hr]

end TreeStack
