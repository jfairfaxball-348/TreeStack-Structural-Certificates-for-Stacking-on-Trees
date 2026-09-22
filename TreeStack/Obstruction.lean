import TreeStack.RootScore
import TreeStack.Estimator

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V]

/-- The explicit obstruction rooted at `r`: `sigma T r - 1` pebbles at the
root and one pebble at every degree-one vertex other than the root. -/
noncomputable def obstruction (T : FiniteTree V) (r : V) : Configuration V :=
  fun v =>
    (if v = r then sigma T r - 1 else 0) +
      oneOn (leafVertices T r) v

@[simp] theorem obstruction_apply_root (T : FiniteTree V) (r : V) :
    obstruction T r r = sigma T r - 1 := by
  simp [obstruction, leafVertices]

theorem obstruction_apply_of_mem_leafVertices
    (T : FiniteTree V) (r : V) {v : V}
    (hv : v ∈ leafVertices T r) :
    obstruction T r v = 1 := by
  have hvr : v ≠ r := by
    simpa [leafVertices] using hv
  simp [obstruction, hvr, hv]

theorem obstruction_apply_of_ne_of_degree_ne_one
    (T : FiniteTree V) (r : V) {v : V}
    (hvr : v ≠ r) (hdeg : T.graph.degree v ≠ 1) :
    obstruction T r v = 0 := by
  have hv : v ∉ leafVertices T r := by
    simp [leafVertices, hvr, hdeg]
  simp [obstruction, hvr, hv]

/-- The exact mass of the rooted explicit obstruction before rewriting it as
the rooted estimator minus one. -/
theorem mass_obstruction_eq_sigma_sub_one_add_leafCount
    (T : FiniteTree V) (r : V) :
    mass (obstruction T r) =
      (sigma T r - 1) + leafCount T r := by
  classical
  simp [mass, obstruction, leafCount, oneOn, Finset.sum_add_distrib]

/-- The explicit rooted obstruction has exactly `rootEstimate T r - 1`
pebbles. -/
theorem mass_obstruction (T : FiniteTree V) (r : V) :
    mass (obstruction T r) = rootEstimate T r - 1 := by
  rw [mass_obstruction_eq_sigma_sub_one_add_leafCount]
  have hsigma : 0 < sigma T r := by
    simp [sigma]
  simp [rootEstimate]
  omega

/-- A finite nonempty vertex type has a root attaining the estimator. -/
theorem exists_rootEstimate_eq_estim [Nonempty V] (T : FiniteTree V) :
    ∃ r : V, rootEstimate T r = estim T := by
  rcases Finset.exists_mem_eq_sup (Finset.univ : Finset V)
      Finset.univ_nonempty (rootEstimate T) with
    ⟨r, -, hr⟩
  exact ⟨r, by simpa [estim] using hr.symm⟩

namespace OrientedBranch

variable {T : FiniteTree V}

/-- The recursive positive height of an oriented branch used by the explicit
obstruction.  A degree-one branch root has height one; every other branch root
has height three plus twice the sum of its child heights. -/
noncomputable def obstructionHeight (B : OrientedBranch T) : ℕ :=
  if T.graph.degree B.root = 1 then
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

/-- The sum of all genuine child obstruction heights. -/
noncomputable def childObstructionHeightSum (B : OrientedBranch T) : ℕ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      obstructionHeight
        (B.childBranch
          { vertex := v
            adj := h.1
            ne_parent := h.2 })
    else
      0

theorem obstructionHeight_eq_one_of_degree_eq_one
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root = 1) :
    obstructionHeight B = 1 := by
  rw [obstructionHeight]
  simp [hdeg]

theorem obstructionHeight_eq_three_add_two_mul
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root ≠ 1) :
    obstructionHeight B = 3 + 2 * childObstructionHeightSum B := by
  rw [obstructionHeight]
  simp [hdeg, childObstructionHeightSum]

theorem obstructionHeight_pos (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  by_cases hdeg : T.graph.degree B.root = 1
  · rw [obstructionHeight_eq_one_of_degree_eq_one B hdeg]
    omega
  · rw [obstructionHeight_eq_three_add_two_mul B hdeg]
    omega

theorem not_isChildVertex_of_degree_eq_one
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root = 1)
    (v : V) :
    ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
  rintro ⟨hv, hvp⟩
  rcases (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg) with
    ⟨u, hu, huniq⟩
  have hvu : v = u := huniq v hv
  have hpu : B.parent = u := huniq B.parent B.adj
  exact hvp (hvu.trans hpu.symm)

theorem exists_isChildVertex_of_degree_ne_one [Nontrivial V]
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root ≠ 1) :
    ∃ v : V, T.graph.Adj B.root v ∧ v ≠ B.parent := by
  by_contra h
  push_neg at h
  have hunique : ∃! v : V, T.graph.Adj B.root v := by
    refine ⟨B.parent, B.adj, ?_⟩
    intro v hv
    exact h v hv
  exact hdeg (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr hunique)

/-- The child-side vertex set selected by a possible neighbor. -/
noncomputable def childVerticesAt (B : OrientedBranch T) (v : V) : Finset V :=
  if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
    (B.childBranch
      { vertex := v
        adj := h.1
        ne_parent := h.2 }).vertices
  else
    ∅

theorem vertices_eq_insert_biUnion_childVerticesAt (B : OrientedBranch T) :
    B.vertices =
      insert B.root
        ((Finset.univ : Finset V).biUnion (childVerticesAt B)) := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hxr : x = B.root
    · simp [hxr]
    · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
        ⟨c, hxc⟩
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨c.vertex, Finset.mem_univ _, ?_⟩
      have hchild : T.graph.Adj B.root c.vertex ∧ c.vertex ≠ B.parent :=
        ⟨c.adj, c.ne_parent⟩
      simpa [childVerticesAt, hchild]
  · intro hx
    rcases Finset.mem_insert.mp hx with hxr | hx
    · simpa [hxr] using B.root_mem_vertices
    · rcases Finset.mem_biUnion.mp hx with ⟨v, -, hxv⟩
      by_cases hv : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := hv.1
            ne_parent := hv.2 }
        have hxChild : x ∈ (B.childBranch c).vertices := by
          simpa [childVerticesAt, hv, c] using hxv
        exact B.childBranch_vertices_subset c hxChild
      · simp [childVerticesAt, hv] at hxv

theorem root_not_mem_biUnion_childVerticesAt (B : OrientedBranch T) :
    B.root ∉ (Finset.univ : Finset V).biUnion (childVerticesAt B) := by
  classical
  intro hroot
  rcases Finset.mem_biUnion.mp hroot with ⟨v, -, hv⟩
  by_cases hchild : T.graph.Adj B.root v ∧ v ≠ B.parent
  · let c : B.Child :=
      { vertex := v
        adj := hchild.1
        ne_parent := hchild.2 }
    have : B.root ∈ (B.childBranch c).vertices := by
      simpa [childVerticesAt, hchild, c] using hv
    exact (B.childBranch c).parent_not_mem_vertices this
  · simp [childVerticesAt, hchild] at hv

theorem pairwiseDisjoint_childVerticesAt (B : OrientedBranch T) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset V)) (childVerticesAt B) := by
  classical
  intro u hu v hv huv
  by_cases hchildU : T.graph.Adj B.root u ∧ u ≠ B.parent
  · by_cases hchildV : T.graph.Adj B.root v ∧ v ≠ B.parent
    · let c : B.Child :=
        { vertex := u
          adj := hchildU.1
          ne_parent := hchildU.2 }
      let d : B.Child :=
        { vertex := v
          adj := hchildV.1
          ne_parent := hchildV.2 }
      have hcd : c.vertex ≠ d.vertex := by simpa [c, d] using huv
      simpa [childVerticesAt, hchildU, hchildV, c, d] using
        B.childBranch_vertices_disjoint c d hcd
    · simp [childVerticesAt, hchildV]
  · simp [childVerticesAt, hchildU]

/-- Sum decomposition of a branch into its root and pairwise-disjoint child
branches. -/
theorem sum_vertices_eq_root_add_sum_children
    (B : OrientedBranch T) (f : V → ℕ) :
    ∑ x ∈ B.vertices, f x =
      f B.root +
        ∑ v : V, ∑ x ∈ childVerticesAt B v, f x := by
  classical
  rw [vertices_eq_insert_biUnion_childVerticesAt B,
    Finset.sum_insert (root_not_mem_biUnion_childVerticesAt B),
    Finset.sum_biUnion (pairwiseDisjoint_childVerticesAt B)]

/-- Distances from the external parent to vertices of a branch are one more
than distances from its root. -/
theorem dist_parent_eq_dist_root_add_one
    (B : OrientedBranch T) {w : V} (hw : w ∈ B.vertices) :
    T.graph.dist B.parent w = T.graph.dist B.root w + 1 := by
  classical
  obtain ⟨p, hpPath, hpLen⟩ :=
    T.isTree.connected.exists_path_of_dist B.root w
  have hparentNot : B.parent ∉ p.support := by
    intro hmem
    have heq :=
      T.isTree.isAcyclic.eq_snd_of_adj_start hpPath B.adj hmem
    have hpw : B.parent = w := by simpa using heq
    exact B.parent_not_mem_vertices (hpw ▸ hw)
  have hconsPath : (p.cons B.adj.symm).IsPath :=
    hpPath.cons hparentNot
  obtain ⟨q, hqPath, hqLen⟩ :=
    T.isTree.connected.exists_path_of_dist B.parent w
  have hpaths :
      (⟨p.cons B.adj.symm, hconsPath⟩ : T.graph.Path B.parent w) =
        ⟨q, hqPath⟩ :=
    Subsingleton.elim _ _
  have hlens := congrArg (fun z : T.graph.Path B.parent w => z.val.length) hpaths
  simpa [SimpleGraph.Walk.length_cons, hpLen, hqLen, Nat.add_comm] using hlens.symm

/-- The degree-weighted internal potential of an oriented branch. -/
noncomputable def obstructionInternalWeight (B : OrientedBranch T) : ℕ :=
  ∑ w ∈ B.vertices,
    if 1 < T.graph.degree w then
      T.graph.degree w * 2 ^ T.graph.dist B.root w
    else
      0

noncomputable def childObstructionInternalWeightSum
    (B : OrientedBranch T) : ℕ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      obstructionInternalWeight
        (B.childBranch
          { vertex := v
            adj := h.1
            ne_parent := h.2 })
    else
      0

noncomputable def childCount (B : OrientedBranch T) : ℕ :=
  ∑ v : V, if T.graph.Adj B.root v ∧ v ≠ B.parent then 1 else 0

theorem vertices_eq_singleton_of_degree_eq_one
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root = 1) :
    B.vertices = {B.root} := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxr
    rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, -⟩
    exact (not_isChildVertex_of_degree_eq_one B hdeg c.vertex)
      ⟨c.adj, c.ne_parent⟩
  · intro hx
    simpa using B.root_mem_vertices

theorem obstructionInternalWeight_eq_zero_of_degree_eq_one
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root = 1) :
    obstructionInternalWeight B = 0 := by
  classical
  rw [obstructionInternalWeight, vertices_eq_singleton_of_degree_eq_one B hdeg]
  simp [hdeg]

theorem childCount_eq_degree_sub_one (B : OrientedBranch T) :
    childCount B = T.graph.degree B.root - 1 := by
  classical
  rw [childCount]
  have hmem : B.parent ∈ T.graph.neighborFinset B.root := by
    simpa using B.adj
  calc
    (∑ v : V, if T.graph.Adj B.root v ∧ v ≠ B.parent then 1 else 0) =
        ((T.graph.neighborFinset B.root).erase B.parent).card := by
          simp [Finset.card_erase_of_mem, hmem]
    _ = T.graph.degree B.root - 1 := by
          rw [Finset.card_erase_of_mem hmem]
          rfl

theorem obstructionInternalWeight_eq_degree_add_two_mul [Nontrivial V]
    (B : OrientedBranch T) (hdeg : T.graph.degree B.root ≠ 1) :
    obstructionInternalWeight B =
      T.graph.degree B.root + 2 * childObstructionInternalWeightSum B := by
  classical
  have hdegPos : 0 < T.graph.degree B.root :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial B.root
  have hdegTwo : 1 < T.graph.degree B.root := by omega
  rw [obstructionInternalWeight,
    sum_vertices_eq_root_add_sum_children]
  have hrootTerm :
      (if 1 < T.graph.degree B.root then
          T.graph.degree B.root * 2 ^ T.graph.dist B.root B.root
        else 0) = T.graph.degree B.root := by
    simp [hdegTwo]
  rw [hrootTerm]
  congr 1
  rw [childObstructionInternalWeightSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : T.graph.Adj B.root v ∧ v ≠ B.parent
  · let c : B.Child :=
      { vertex := v
        adj := hv.1
        ne_parent := hv.2 }
    rw [show childVerticesAt B v = (B.childBranch c).vertices by
      simp [childVerticesAt, hv, c]]
    simp only [hv, ↓reduceDIte]
    rw [obstructionInternalWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hwdeg : 1 < T.graph.degree w
    · have hdist := (B.childBranch c).dist_parent_eq_dist_root_add_one hw
      simp only [hwdeg, if_pos]
      rw [hdist, pow_succ']
      ring
    · simp [hwdeg]
  · simp [childVerticesAt, hv]

/-- Closed form for the recursive obstruction height. -/
theorem obstructionHeight_closedForm [Nontrivial V]
    (B : OrientedBranch T) :
    obstructionHeight B = 1 + 2 * obstructionInternalWeight B := by
  by_cases hdeg : T.graph.degree B.root = 1
  · rw [obstructionHeight_eq_one_of_degree_eq_one B hdeg,
      obstructionInternalWeight_eq_zero_of_degree_eq_one B hdeg]
  · rw [obstructionHeight_eq_three_add_two_mul B hdeg,
      obstructionInternalWeight_eq_degree_add_two_mul B hdeg]
    have hheightSum :
        childObstructionHeightSum B =
          childCount B + 2 * childObstructionInternalWeightSum B := by
      rw [childObstructionHeightSum, childCount,
        childObstructionInternalWeightSum,
        Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := hv.1
            ne_parent := hv.2 }
        have ih := obstructionHeight_closedForm (B.childBranch c)
        simp [hv, c, ih]
      · simp [hv]
    rw [hheightSum, childCount_eq_degree_sub_one]
    have hdegPos : 0 < T.graph.degree B.root :=
      T.isTree.connected.preconnected.degree_pos_of_nontrivial B.root
    omega
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c

/-- Every branch directed away from the chosen obstruction root is occupied,
and its genuine integer message is the negative of its recursive height. -/
theorem obstruction_branchMessage_of_root_not_mem [Nontrivial V]
    (T : FiniteTree V) (r : V) (B : OrientedBranch T)
    (hr : r ∉ B.vertices) :
    B.Occupied (obstruction T r) ∧
      branchMessage (obstruction T r) B =
        some (-(obstructionHeight B : ℤ)) := by
  have hroot_ne : B.root ≠ r := by
    intro h
    subst r
    exact hr B.root_mem_vertices
  by_cases hdeg : T.graph.degree B.root = 1
  · have hrootValue : obstruction T r B.root = 1 := by
      apply obstruction_apply_of_mem_leafVertices
      simp [leafVertices, hroot_ne, hdeg]
    have hOcc : B.Occupied (obstruction T r) := by
      exact ⟨B.root, B.root_mem_vertices, by simp [hrootValue]⟩
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ B hOcc]
    have hChild : childMessageSum (obstruction T r) B = 0 := by
      simp [childMessageSum, not_isChildVertex_of_degree_eq_one B hdeg]
    rw [effectiveInput, hChild, hrootValue]
    norm_num [F, obstructionHeight_eq_one_of_degree_eq_one B hdeg]
  · rcases exists_isChildVertex_of_degree_ne_one B hdeg with
      ⟨v, hvAdj, hvParent⟩
    let c : B.Child :=
      { vertex := v
        adj := hvAdj
        ne_parent := hvParent }
    have hrChild : r ∉ (B.childBranch c).vertices := by
      intro hmem
      exact hr (B.childBranch_vertices_subset c hmem)
    have hRec :=
      obstruction_branchMessage_of_root_not_mem T r (B.childBranch c) hrChild
    have hOcc : B.Occupied (obstruction T r) := by
      rcases hRec.1 with ⟨w, hw, hwpos⟩
      exact ⟨w, B.childBranch_vertices_subset c hw, hwpos⟩
    have hrootValue : obstruction T r B.root = 0 := by
      exact obstruction_apply_of_ne_of_degree_ne_one T r hroot_ne hdeg
    have hChild :
        childMessageSum (obstruction T r) B =
          -(childObstructionHeightSum B : ℤ) := by
      rw [childMessageSum, childObstructionHeightSum]
      push_cast
      rw [Finset.neg_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : T.graph.Adj B.root u ∧ u ≠ B.parent
      · let d : B.Child :=
          { vertex := u
            adj := hu.1
            ne_parent := hu.2 }
        have hrD : r ∉ (B.childBranch d).vertices := by
          intro hmem
          exact hr (B.childBranch_vertices_subset d hmem)
        have hRecD :=
          obstruction_branchMessage_of_root_not_mem T r (B.childBranch d) hrD
        simp [hu, d, hRecD.2]
      · simp [hu]
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ B hOcc]
    rw [effectiveInput, hrootValue, Nat.cast_zero, zero_add, hChild]
    have hle : -(childObstructionHeightSum B : ℤ) ≤ 1 := by omega
    rw [F_of_le_one hle,
      obstructionHeight_eq_three_add_two_mul B hdeg]
    push_cast
    congr 1
    ring
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c

end OrientedBranch

/-- The root-side family member selected by a possible neighbor. -/
noncomputable def incidentVerticesAt
    (T : FiniteTree V) (r u : V) : Finset V :=
  if h : T.graph.Adj u r then
    (incidentBranch T r u h).vertices
  else
    ∅

theorem erase_root_eq_biUnion_incidentVerticesAt
    (T : FiniteTree V) (r : V) :
    (Finset.univ : Finset V).erase r =
      (Finset.univ : Finset V).biUnion (incidentVerticesAt T r) := by
  classical
  ext x
  constructor
  · intro hx
    have hxr : x ≠ r := (Finset.mem_erase.mp hx).1
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hxr with
      ⟨u, hu, hxu⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨u, Finset.mem_univ _, by simpa [incidentVerticesAt, hu]⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨u, -, hxu⟩
    by_cases hu : T.graph.Adj u r
    · have hxBranch : x ∈ (incidentBranch T r u hu).vertices := by
        simpa [incidentVerticesAt, hu] using hxu
      apply Finset.mem_erase.mpr
      exact ⟨fun hxr => by
        subst x
        exact (incidentBranch T r u hu).parent_not_mem_vertices hxBranch,
        Finset.mem_univ _⟩
    · simp [incidentVerticesAt, hu] at hxu

theorem pairwiseDisjoint_incidentVerticesAt
    (T : FiniteTree V) (r : V) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset V))
      (incidentVerticesAt T r) := by
  classical
  intro u hu v hv huv
  by_cases hadjU : T.graph.Adj u r
  · by_cases hadjV : T.graph.Adj v r
    · simpa [incidentVerticesAt, hadjU, hadjV] using
        incidentBranch_vertices_disjoint (T := T) r hadjU hadjV huv
    · simp [incidentVerticesAt, hadjV]
  · simp [incidentVerticesAt, hadjU]

theorem sum_erase_root_eq_sum_incident
    (T : FiniteTree V) (r : V) (f : V → ℕ) :
    ∑ x ∈ (Finset.univ : Finset V).erase r, f x =
      ∑ u : V, ∑ x ∈ incidentVerticesAt T r u, f x := by
  classical
  rw [erase_root_eq_biUnion_incidentVerticesAt,
    Finset.sum_biUnion (pairwiseDisjoint_incidentVerticesAt T r)]

/-- Sum of recursive obstruction heights over every branch incident to a
chosen root. -/
noncomputable def rootObstructionHeightSum
    (T : FiniteTree V) (r : V) : ℕ :=
  ∑ u : V,
    if h : T.graph.Adj u r then
      OrientedBranch.obstructionHeight (incidentBranch T r u h)
    else
      0

theorem nonRootInternalVertices_eq_erase_filter
    (T : FiniteTree V) (r : V) :
    nonRootInternalVertices T r =
      (Finset.univ : Finset V).erase r |>.filter
        (fun w => 1 < T.graph.degree w) := by
  ext w
  simp [nonRootInternalVertices, and_left_comm]

theorem two_mul_incidentInternalWeightSum_eq_nonRootInternalSum
    [Nontrivial V] (T : FiniteTree V) (r : V) :
    ∑ u : V,
        if h : T.graph.Adj u r then
          2 * OrientedBranch.obstructionInternalWeight
            (incidentBranch T r u h)
        else
          0 =
      ∑ w ∈ nonRootInternalVertices T r,
        T.graph.degree w * 2 ^ T.graph.dist r w := by
  classical
  let f : V → ℕ := fun w =>
    if 1 < T.graph.degree w then
      T.graph.degree w * 2 ^ T.graph.dist r w
    else
      0
  calc
    (∑ u : V,
        if h : T.graph.Adj u r then
          2 * OrientedBranch.obstructionInternalWeight
            (incidentBranch T r u h)
        else 0) =
        ∑ u : V, ∑ w ∈ incidentVerticesAt T r u, f w := by
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : T.graph.Adj u r
          · let B : OrientedBranch T := incidentBranch T r u hu
            rw [show incidentVerticesAt T r u = B.vertices by
              simp [incidentVerticesAt, hu, B]]
            simp only [hu, ↓reduceDIte]
            rw [OrientedBranch.obstructionInternalWeight, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro w hw
            by_cases hwdeg : 1 < T.graph.degree w
            · have hdist := B.dist_parent_eq_dist_root_add_one hw
              simp only [f, hwdeg, if_pos]
              rw [hdist, pow_succ']
              ring
            · simp [f, hwdeg]
          · simp [incidentVerticesAt, hu]
    _ = ∑ w ∈ (Finset.univ : Finset V).erase r, f w := by
          exact (sum_erase_root_eq_sum_incident T r f).symm
    _ = ∑ w ∈ nonRootInternalVertices T r,
          T.graph.degree w * 2 ^ T.graph.dist r w := by
          rw [nonRootInternalVertices_eq_erase_filter]
          simp [f]

/-- The sum of the incident branch heights is exactly the root pile
`sigma T r - 1`. -/
theorem rootObstructionHeightSum_eq_sigma_sub_one [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    rootObstructionHeightSum T r = sigma T r - 1 := by
  classical
  have hheight :
      rootObstructionHeightSum T r =
        T.graph.degree r +
          ∑ u : V,
            if h : T.graph.Adj u r then
              2 * OrientedBranch.obstructionInternalWeight
                (incidentBranch T r u h)
            else
              0 := by
    rw [rootObstructionHeightSum]
    calc
      (∑ u : V,
          if h : T.graph.Adj u r then
            OrientedBranch.obstructionHeight (incidentBranch T r u h)
          else 0) =
          ∑ u : V,
            ((if T.graph.Adj u r then 1 else 0) +
              if h : T.graph.Adj u r then
                2 * OrientedBranch.obstructionInternalWeight
                  (incidentBranch T r u h)
              else 0) := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : T.graph.Adj u r
            · rw [OrientedBranch.obstructionHeight_closedForm]
              simp [hu]
            · simp [hu]
      _ = T.graph.degree r +
          ∑ u : V,
            if h : T.graph.Adj u r then
              2 * OrientedBranch.obstructionInternalWeight
                (incidentBranch T r u h)
            else 0 := by
              rw [Finset.sum_add_distrib]
              congr 1
              simp [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [hheight,
    two_mul_incidentInternalWeightSum_eq_nonRootInternalSum,
    sigma_corrected_expansion]
  have hdeg : 0 < T.graph.degree r :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial r
  omega

theorem rootMessageSum_obstruction_eq_neg_heightSum [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    rootMessageSum T (obstruction T r) r =
      -(rootObstructionHeightSum T r : ℤ) := by
  classical
  rw [rootMessageSum, rootObstructionHeightSum]
  push_cast
  rw [Finset.neg_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : T.graph.Adj u r
  · let B : OrientedBranch T := incidentBranch T r u hu
    have hr : r ∉ B.vertices := by
      simpa [B, incidentBranch] using B.parent_not_mem_vertices
    have hmsg :=
      OrientedBranch.obstruction_branchMessage_of_root_not_mem T r B hr
    simp [rootMessageTerm, hu, B, hmsg.2]
  · simp [rootMessageTerm, hu]

/-- The chosen root itself has zero obstruction score. -/
theorem score_obstruction_root [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    score T (obstruction T r) r = 0 := by
  rw [score, obstruction_apply_root,
    rootMessageSum_obstruction_eq_neg_heightSum,
    rootObstructionHeightSum_eq_sigma_sub_one]
  omega

theorem obstruction_root_pos [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    0 < obstruction T r r := by
  rw [obstruction_apply_root]
  have hdeg : 0 < T.graph.degree r :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial r
  rw [sigma_corrected_expansion]
  omega

/-- Every oriented branch is configuration-occupied in the explicit
obstruction.  In particular, no edge identity below replaces `EMPTY` by
integer zero. -/
theorem obstruction_branch_occupied [Nontrivial V]
    (T : FiniteTree V) (r : V) (B : OrientedBranch T) :
    B.Occupied (obstruction T r) := by
  by_cases hr : r ∈ B.vertices
  · exact ⟨r, hr, obstruction_root_pos T r⟩
  · exact
      (OrientedBranch.obstruction_branchMessage_of_root_not_mem T r B hr).1

/-- The rooted score splits across an edge into the effective input on one
side and the message arriving from the opposite side. -/
theorem score_eq_effectiveInput_add_oppositeMessage
    (T : FiniteTree V) (C : Configuration V) {u v : V}
    (huv : T.graph.Adj u v) :
    score T C u =
      OrientedBranch.effectiveInput C (incidentBranch T v u huv) +
        OrientedBranch.messageContribution
          (OrientedBranch.branchMessage C
            (incidentBranch T u v huv.symm)) := by
  classical
  let A : OrientedBranch T := incidentBranch T v u huv
  let B : OrientedBranch T := incidentBranch T u v huv.symm
  have hsum :
      rootMessageSum T C u =
        OrientedBranch.childMessageSum C A +
          OrientedBranch.messageContribution
            (OrientedBranch.branchMessage C B) := by
    rw [rootMessageSum, OrientedBranch.childMessageSum]
    calc
      (∑ w : V, rootMessageTerm T C u w) =
          ∑ w : V,
            ((if w = v then
                OrientedBranch.messageContribution
                  (OrientedBranch.branchMessage C B)
              else 0) +
            if h : T.graph.Adj A.root w ∧ w ≠ A.parent then
              OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C
                  (A.childBranch
                    { vertex := w
                      adj := h.1
                      ne_parent := h.2 }))
            else 0) := by
              apply Finset.sum_congr rfl
              intro w _
              by_cases hwv : w = v
              · subst w
                simp [rootMessageTerm, huv, A, B, incidentBranch]
              · by_cases hwu : T.graph.Adj w u
                · have huw : T.graph.Adj u w := hwu.symm
                  have hchild :
                      T.graph.Adj A.root w ∧ w ≠ A.parent := by
                    simpa [A, incidentBranch] using ⟨huw, hwv⟩
                  simp [rootMessageTerm, hwu, hwv, hchild,
                    A, B, incidentBranch]
                · have hnotChild :
                      ¬ (T.graph.Adj A.root w ∧ w ≠ A.parent) := by
                    simpa [A, incidentBranch] using
                      (not_and_or.mpr (Or.inl (by simpa using hwu)))
                  simp [rootMessageTerm, hwu, hwv, hnotChild]
      _ = OrientedBranch.messageContribution
            (OrientedBranch.branchMessage C B) +
          ∑ w : V,
            if h : T.graph.Adj A.root w ∧ w ≠ A.parent then
              OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C
                  (A.childBranch
                    { vertex := w
                      adj := h.1
                      ne_parent := h.2 }))
            else 0 := by
              rw [Finset.sum_add_distrib]
              simp
      _ = OrientedBranch.childMessageSum C A +
          OrientedBranch.messageContribution
            (OrientedBranch.branchMessage C B) := by
              rw [add_comm]
  rw [score, OrientedBranch.effectiveInput, hsum]
  ring

/-- On every branch directed away from the obstruction root, its effective
input cancels the transfer of its positive obstruction height. -/
theorem obstruction_effectiveInput_add_F_height [Nontrivial V]
    (T : FiniteTree V) (r : V) (B : OrientedBranch T)
    (hr : r ∉ B.vertices) :
    OrientedBranch.effectiveInput (obstruction T r) B +
      F (OrientedBranch.obstructionHeight B : ℤ) = 0 := by
  have hmsg :=
    OrientedBranch.obstruction_branchMessage_of_root_not_mem T r B hr
  have hdef :=
    OrientedBranch.branchMessage_eq_some_of_occupied
      (obstruction T r) B hmsg.1
  have hF :
      F (OrientedBranch.effectiveInput (obstruction T r) B) =
        -(OrientedBranch.obstructionHeight B : ℤ) := by
    rw [hmsg.2] at hdef
    exact Option.some.inj hdef.symm
  let W : ℕ := OrientedBranch.obstructionInternalWeight B
  have hheight : OrientedBranch.obstructionHeight B = 1 + 2 * W := by
    simpa [W] using OrientedBranch.obstructionHeight_closedForm B
  have heffective :
      OrientedBranch.effectiveInput (obstruction T r) B = 1 - (W : ℤ) := by
    apply (F_eq_neg_odd_iff (r := (W : ℤ)) (by positivity)).mp
    rw [hF, hheight]
    push_cast
    ring
  by_cases hW : W = 0
  · subst W
    simp [heffective, hheight, F]
  · have hWpos : 0 < (W : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hW
    have htransfer : F (OrientedBranch.obstructionHeight B : ℤ) = (W : ℤ) - 1 := by
      apply (F_eq_nonneg_iff (k := (W : ℤ) - 1) (by omega)).2
      right
      rw [hheight]
      push_cast
      ring
    rw [heffective, htransfer]
    ring

/-- Zero obstruction score propagates across any edge directed away from the
chosen root. -/
theorem score_obstruction_eq_zero_of_adj [Nontrivial V]
    (T : FiniteTree V) (r : V) {u v : V}
    (huv : T.graph.Adj u v)
    (hrv : r ∉ (incidentBranch T u v huv.symm).vertices)
    (hu : score T (obstruction T r) u = 0) :
    score T (obstruction T r) v = 0 := by
  let A : OrientedBranch T := incidentBranch T u v huv.symm
  let B : OrientedBranch T := incidentBranch T v u huv
  have hAmsg :=
    OrientedBranch.obstruction_branchMessage_of_root_not_mem T r A hrv
  have hBocc : B.Occupied (obstruction T r) :=
    obstruction_branch_occupied T r B
  have hsplitU :=
    score_eq_effectiveInput_add_oppositeMessage
      T (obstruction T r) huv
  have hinputB :
      OrientedBranch.effectiveInput (obstruction T r) B =
        (OrientedBranch.obstructionHeight A : ℤ) := by
    rw [hu] at hsplitU
    change
      0 = OrientedBranch.effectiveInput (obstruction T r) B +
        OrientedBranch.messageContribution
          (OrientedBranch.branchMessage (obstruction T r) A) at hsplitU
    rw [hAmsg.2] at hsplitU
    simp only [OrientedBranch.messageContribution_some] at hsplitU
    omega
  have hBmsg :=
    OrientedBranch.branchMessage_eq_some_of_occupied
      (obstruction T r) B hBocc
  have hsplitV :=
    score_eq_effectiveInput_add_oppositeMessage
      T (obstruction T r) huv.symm
  change
    score T (obstruction T r) v =
      OrientedBranch.effectiveInput (obstruction T r) A +
        OrientedBranch.messageContribution
          (OrientedBranch.branchMessage (obstruction T r) B) at hsplitV
  rw [hBmsg, hinputB] at hsplitV
  simp only [OrientedBranch.messageContribution_some] at hsplitV
  rw [hsplitV]
  exact obstruction_effectiveInput_add_F_height T r A hrv

theorem isPath_length_eq_dist
    (T : FiniteTree V) {u v : V} (p : T.graph.Walk u v)
    (hp : p.IsPath) :
    p.length = T.graph.dist u v := by
  obtain ⟨q, hq, hqLen⟩ :=
    T.isTree.connected.exists_path_of_dist u v
  have hpaths :
      (⟨p, hp⟩ : T.graph.Path u v) = ⟨q, hq⟩ :=
    Subsingleton.elim _ _
  have hlens := congrArg (fun z : T.graph.Path u v => z.val.length) hpaths
  simpa [hqLen] using hlens

theorem root_not_mem_forward_incidentBranch_of_dist
    (T : FiniteTree V) (r : V) {u v : V}
    (huv : T.graph.Adj u v)
    (hdist : T.graph.dist r v = T.graph.dist r u + 1) :
    r ∉ (incidentBranch T u v huv.symm).vertices := by
  intro hr
  have hbranch :=
    (incidentBranch T u v huv.symm).dist_parent_eq_dist_root_add_one hr
  simp only [incidentBranch_parent, incidentBranch_root] at hbranch
  rw [T.graph.dist_comm u r, T.graph.dist_comm v r] at hbranch
  omega

/-- Every rooted score of the explicit estimator obstruction is zero. -/
theorem score_obstruction_eq_zero [Nontrivial V]
    (T : FiniteTree V) (r v : V) :
    score T (obstruction T r) v = 0 := by
  by_cases hvr : v = r
  · subst v
    exact score_obstruction_root T r
  · obtain ⟨p, hpPath, hpLen⟩ :=
      T.isTree.connected.exists_path_of_dist r v
    have hpNotNil : ¬ p.Nil := by
      exact hpPath.nil_iff_eq.not.mpr hvr.symm
    let u : V := p.penultimate
    have huv : T.graph.Adj u v := p.adj_penultimate hpNotNil
    have hdropPath : p.dropLast.IsPath := hpPath.dropLast
    have hdropLen : p.dropLast.length = T.graph.dist r u :=
      isPath_length_eq_dist T p.dropLast hdropPath
    have hdist : T.graph.dist r v = T.graph.dist r u + 1 := by
      rw [← hpLen, ← hdropLen]
      exact (p.length_dropLast_add_one hpNotNil).symm
    have hu : score T (obstruction T r) u = 0 :=
      score_obstruction_eq_zero T r u
    exact score_obstruction_eq_zero_of_adj T r huv
      (root_not_mem_forward_incidentBranch_of_dist T r huv hdist) hu
termination_by T.graph.dist r v
decreasing_by omega

/-- The explicit estimator obstruction is not stackable. -/
theorem obstruction_not_stackable [Nontrivial V] [DecidableEq V]
    (T : FiniteTree V) (r : V) :
    ¬ Stackable T.graph (obstruction T r) := by
  apply (not_stackable_iff_all_scores_nonpos T (obstruction T r)).2
  intro v
  rw [score_obstruction_eq_zero T r v]

/-- An estimator-maximizing root supplies a non-stackable configuration of
exactly `estim T - 1` pebbles. -/
theorem exists_nonstackable_mass_estim_sub_one
    [Nontrivial V] [DecidableEq V] (T : FiniteTree V) :
    ∃ C : Configuration V,
      mass C = estim T - 1 ∧ ¬ Stackable T.graph C := by
  rcases exists_rootEstimate_eq_estim T with ⟨r, hr⟩
  refine ⟨obstruction T r, ?_, obstruction_not_stackable T r⟩
  rw [mass_obstruction, hr]

end TreeStack
