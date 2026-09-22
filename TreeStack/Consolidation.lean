import Mathlib
import TreeStack.HeightSource

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The fibre of the canonical height-zero source map.  These fibres are the
connected parts that will be consolidated to a single estimator root. -/
noncomputable def auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v = r

@[simp] theorem mem_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores r ↔
      auxSource C ambientRoot hScores v = r := by
  simp [auxSourceFiber]

/-- Every vertex belongs to the fibre indexed by its canonical source. -/
theorem mem_auxSourceFiber_self_source
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores
      (auxSource C ambientRoot hScores v) := by
  simp

/-- A source fibre is nonempty exactly when its index is itself a canonical
height-zero source. -/
theorem auxSourceFiber_nonempty_iff
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) :
    (auxSourceFiber C ambientRoot hScores r).Nonempty ↔
      auxHeight C ambientRoot hScores r = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hsrc : auxSource C ambientRoot hScores v = r := by
      simpa using hv
    rw [← hsrc]
    exact auxSource_height_zero C ambientRoot hScores v
  · intro hzero
    refine ⟨r, ?_⟩
    simp [auxSource_eq_self_of_height_zero C ambientRoot hScores r hzero]

/-- The canonical walk from a vertex stays entirely in its source fibre. -/
theorem auxWalk_support_subset_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    ∀ x ∈ (auxWalk C ambientRoot hScores v).support,
      x ∈ auxSourceFiber C ambientRoot hScores
        (auxSource C ambientRoot hScores v) := by
  intro x hx
  rw [mem_auxSourceFiber]
  exact
    auxSource_eq_of_mem_auxSourceWalk_support
      C ambientRoot hScores v x hx

/-- Any two vertices in one source fibre are joined by an ambient-tree walk
whose support stays in that fibre.  This is the path-connectedness interface
needed by the connected-partition consolidation argument. -/
theorem exists_walk_within_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      ∀ z ∈ p.support,
        z ∈ auxSourceFiber C ambientRoot hScores r := by
  have hsx : auxSource C ambientRoot hScores x = r := by
    simpa using hx
  have hsy : auxSource C ambientRoot hScores y = r := by
    simpa using hy
  let px : T.graph.Walk x r :=
    (auxWalk C ambientRoot hScores x).copy rfl hsx
  let py : T.graph.Walk y r :=
    (auxWalk C ambientRoot hScores y).copy rfl hsy
  let p : T.graph.Walk x y := px.append py.reverse
  refine ⟨p, ?_⟩
  intro z hz
  have hz' :
      z ∈ px.support ∨ z ∈ py.support := by
    simpa [p] using hz
  rcases hz' with hzx | hzy
  · have hzsrc :=
      auxWalk_support_subset_sourceFiber C ambientRoot hScores x z
        (by simpa [px] using hzx)
    simpa [hsx] using hzsrc
  · have hzsrc :=
      auxWalk_support_subset_sourceFiber C ambientRoot hScores y z
        (by simpa [py] using hzy)
    simpa [hsy] using hzsrc

/-- Distinct canonical sources have disjoint fibres. -/
theorem auxSourceFiber_disjoint_of_ne
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s : V} (hrs : r ≠ s) :
    Disjoint
      (auxSourceFiber C ambientRoot hScores r)
      (auxSourceFiber C ambientRoot hScores s) := by
  rw [Finset.disjoint_left]
  intro v hvr hvs
  have hr : auxSource C ambientRoot hScores v = r := by
    simpa using hvr
  have hs : auxSource C ambientRoot hScores v = s := by
    simpa using hvs
  exact hrs (hr.symm.trans hs)

/-- A source fibre is path-connected by a simple ambient-tree path whose
support remains entirely inside the fibre. -/
theorem exists_path_within_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧
        ∀ z ∈ p.support,
          z ∈ auxSourceFiber C ambientRoot hScores r := by
  rcases
      exists_walk_within_auxSourceFiber
        C ambientRoot hScores r x y hx hy with
    ⟨w, hw⟩
  refine ⟨w.toPath, w.toPath.2, ?_⟩
  intro z hz
  exact hw z (w.support_toPath_subset_support hz)

/-- Across an edge joining two distinct source fibres, tree distance splits
exactly at that boundary edge. -/
theorem dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b x y : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores r x a hx ha with
    ⟨px, hpxPath, hpxFiber⟩
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores s b y hb hy with
    ⟨py, hpyPath, hpyFiber⟩
  have hFibDisj :=
    auxSourceFiber_disjoint_of_ne
      C ambientRoot hScores hrs
  have hbNotPx : b ∉ px.support := by
    intro hbpx
    have hbR := hpxFiber b hbpx
    exact (Finset.disjoint_left.mp hFibDisj) hbR hb
  let q : T.graph.Walk x b := px.concat hadj
  have hqPath : q.IsPath := by
    exact hpxPath.concat hbNotPx hadj
  have hbNotPyTail : b ∉ py.support.tail := by
    have hNodup := hpyPath.support_nodup
    rw [← py.cons_tail_support, List.nodup_cons] at hNodup
    exact hNodup.1
  have hDisjoint : q.support.Disjoint py.support.tail := by
    rw [List.disjoint_left]
    intro z hzq hzpyTail
    have hzpy : z ∈ py.support :=
      List.mem_of_mem_tail hzpyTail
    have hzS := hpyFiber z hzpy
    have hzq' :
        z ∈ px.support ∨ z = b := by
      simpa [q] using hzq
    rcases hzq' with hzpx | rfl
    · have hzR := hpxFiber z hzpx
      exact (Finset.disjoint_left.mp hFibDisj) hzR hzS
    · exact hbNotPyTail hzpyTail
  have hpPath : (q.append py).IsPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append, List.nodup_append']
    exact
      ⟨hqPath.support_nodup, hpyPath.support_nodup.tail, hDisjoint⟩
  have hpxDist :=
    tree_path_length_eq_dist (T := T) px hpxPath
  have hpyDist :=
    tree_path_length_eq_dist (T := T) py hpyPath
  have hpDist :=
    tree_path_length_eq_dist (T := T) (q.append py) hpPath
  calc
    T.graph.dist x y = (q.append py).length := hpDist.symm
    _ = px.length + 1 + py.length := by
      simp [q]
    _ = T.graph.dist x a + 1 + T.graph.dist b y := by
      rw [hpxDist, hpyDist]

/-- The index of every nonempty source fibre belongs to that fibre. -/
theorem source_mem_auxSourceFiber_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V}
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    r ∈ auxSourceFiber C ambientRoot hScores r := by
  have hZero :=
    (auxSourceFiber_nonempty_iff C ambientRoot hScores r).1 hNonempty
  rw [mem_auxSourceFiber]
  exact auxSource_eq_self_of_height_zero
    C ambientRoot hScores r hZero

/-- If the depth of the first source to its boundary endpoint plus the crossing
edge dominates the depth of the second source to its endpoint, then the first
source is at least as far from every vertex in the second fibre as the second
source is. -/
theorem sourceFiber_dist_le_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist s v ≤ T.graph.dist r v := by
  have hr :
      r ∈ auxSourceFiber C ambientRoot hScores r :=
    source_mem_auxSourceFiber_of_nonempty
      C ambientRoot hScores ⟨a, ha⟩
  have hCross :=
    dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
      C ambientRoot hScores hrs ha hb hadj hr hv
  have hTri :
      T.graph.dist s v ≤
        T.graph.dist s b + T.graph.dist b v :=
    T.isTree.connected.dist_triangle
  rw [hCross]
  omega

/-- Under the same boundary-depth comparison, the first source's rooted
power-of-two weight pointwise dominates the auxiliary weight throughout the
second fibre. -/
theorem auxWeight_le_two_pow_dist_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    auxWeight C ambientRoot hScores v ≤
      2 ^ T.graph.dist r v := by
  rw [auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    C ambientRoot hScores s v hv]
  exact Nat.pow_le_pow_right Nat.zero_lt_two
    (sourceFiber_dist_le_of_boundary_depth
      C ambientRoot hScores hrs ha hb hadj hDepth hv)

/-- On a source fibre, the auxiliary weight is exactly the power of two of
ambient-tree distance from that fibre's height-zero source. -/
theorem auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores r) :
    auxWeight C ambientRoot hScores v =
      2 ^ T.graph.dist r v := by
  have hsrc : auxSource C ambientRoot hScores v = r := by
    simpa using hv
  rw [auxWeight, auxHeight_eq_dist_auxSource, hsrc]

end OrientedBranch

end TreeStack
