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

/-- A finite carrier is tree-path-connected when every two of its vertices
are joined by a simple ambient-tree path whose support stays in the carrier. -/
def TreePathConnected (S : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ S → y ∈ S →
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧ ∀ z ∈ p.support, z ∈ S

/-- Every canonical source fibre is tree-path-connected. -/
theorem auxSourceFiber_treePathConnected
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    TreePathConnected (T := T)
      (auxSourceFiber C ambientRoot hScores r) := by
  intro x y hx hy
  exact exists_path_within_auxSourceFiber
    C ambientRoot hScores r x y hx hy

/-- Generic boundary additivity for two disjoint path-connected carriers.
Because the ambient graph is a tree, concatenating an internal path in the
first carrier, the crossing edge, and an internal path in the second carrier
is itself the unique simple path between the endpoints. -/
theorem dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b x y : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ A) (hy : y ∈ B) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by
  rcases hA hx ha with ⟨px, hpxPath, hpxCarrier⟩
  rcases hB hb hy with ⟨py, hpyPath, hpyCarrier⟩
  have hbNotPx : b ∉ px.support := by
    intro hbpx
    have hbA := hpxCarrier b hbpx
    exact (Finset.disjoint_left.mp hDisj) hbA hb
  let q : T.graph.Walk x b := px.concat hadj
  have hqPath : q.IsPath :=
    hpxPath.concat hbNotPx hadj
  have hbNotPyTail : b ∉ py.support.tail := by
    have hNodup := hpyPath.support_nodup
    rw [← py.cons_tail_support, List.nodup_cons] at hNodup
    exact hNodup.1
  have hSupportsDisjoint : q.support.Disjoint py.support.tail := by
    rw [List.disjoint_left]
    intro z hzq hzpyTail
    have hzpy : z ∈ py.support :=
      List.mem_of_mem_tail hzpyTail
    have hzB := hpyCarrier z hzpy
    have hzq' : z ∈ px.support ∨ z = b := by
      simpa [q] using hzq
    rcases hzq' with hzpx | rfl
    · have hzA := hpxCarrier z hzpx
      exact (Finset.disjoint_left.mp hDisj) hzA hzB
    · exact hbNotPyTail hzpyTail
  have hpPath : (q.append py).IsPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append, List.nodup_append']
    exact
      ⟨hqPath.support_nodup,
        hpyPath.support_nodup.tail,
        hSupportsDisjoint⟩
  have hpxDist :=
    tree_path_length_eq_dist (T := T) px hpxPath
  have hpyDist :=
    tree_path_length_eq_dist (T := T) py hpyPath
  have hpDist :=
    tree_path_length_eq_dist (T := T) (q.append py) hpPath
  calc
    T.graph.dist x y = (q.append py).length := hpDist.symm
    _ = px.length + 1 + py.length := by simp [q]
    _ = T.graph.dist x a + 1 + T.graph.dist b y := by
      rw [hpxDist, hpyDist]

/-- A height profile is dominated on a carrier by a root when the root lies
in the carrier and every profile height is at most the ambient distance from
that root. -/
def HeightDominated
    (h : V → ℕ) (S : Finset V) (r : V) : Prop :=
  r ∈ S ∧ ∀ v ∈ S, h v ≤ T.graph.dist r v

/-- The union of two path-connected carriers joined by an ambient edge is
again path-connected. -/
theorem treePathConnected_union_of_adj
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b) :
    TreePathConnected (T := T) (A ∪ B) := by
  intro x y hx hy
  rw [Finset.mem_union] at hx hy
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · rcases hA hxA hyA with ⟨p, hpPath, hpSupp⟩
      refine ⟨p, hpPath, ?_⟩
      intro z hz
      exact Finset.mem_union_left _ (hpSupp z hz)
    · rcases hA hxA ha with ⟨p, hpPath, hpSupp⟩
      rcases hB hb hyB with ⟨q, hqPath, hqSupp⟩
      let w : T.graph.Walk x y := (p.concat hadj).append q
      refine ⟨w.toPath, w.toPath.2, ?_⟩
      intro z hz
      have hzw : z ∈ w.support :=
        w.support_toPath_subset_support hz
      have hzCases :
          (z ∈ p.support ∨ z = b) ∨ z ∈ q.support := by
        simpa [w] using hzw
      rcases hzCases with (hzp | hzb) | hzq
      · exact Finset.mem_union_left _ (hpSupp z hzp)
      · subst z
        exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_right _ (hqSupp z hzq)
  · rcases hy with hyA | hyB
    · rcases hB hxB hb with ⟨p, hpPath, hpSupp⟩
      rcases hA ha hyA with ⟨q, hqPath, hqSupp⟩
      let w : T.graph.Walk x y := (p.concat hadj.symm).append q
      refine ⟨w.toPath, w.toPath.2, ?_⟩
      intro z hz
      have hzw : z ∈ w.support :=
        w.support_toPath_subset_support hz
      have hzCases :
          (z ∈ p.support ∨ z = a) ∨ z ∈ q.support := by
        simpa [w] using hzw
      rcases hzCases with (hzp | hza) | hzq
      · exact Finset.mem_union_right _ (hpSupp z hzp)
      · subst z
        exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_left _ (hqSupp z hzq)
    · rcases hB hxB hyB with ⟨p, hpPath, hpSupp⟩
      refine ⟨p, hpPath, ?_⟩
      intro z hz
      exact Finset.mem_union_right _ (hpSupp z hz)

/-- Merge two disjoint connected dominated carriers across one boundary edge.
The root on the side whose boundary depth is large enough dominates the whole
union; if that comparison fails, the opposite root necessarily works. -/
theorem exists_heightDominatingRoot_union_of_adj
    (h : V → ℕ)
    {A B : Finset V}
    (hAConn : TreePathConnected (T := T) A)
    (hBConn : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b r s : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hADom : HeightDominated (T := T) h A r)
    (hBDom : HeightDominated (T := T) h B s) :
    ∃ t : V,
      HeightDominated (T := T) h (A ∪ B) t := by
  rcases hADom with ⟨hrA, hAHeight⟩
  rcases hBDom with ⟨hsB, hBHeight⟩
  by_cases hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1
  · refine ⟨r, Finset.mem_union_left _ hrA, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · exact hAHeight v hvA
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hAConn hBConn hDisj ha hb hadj hrA hvB
      have hTri :
          T.graph.dist s v ≤
            T.graph.dist s b + T.graph.dist b v :=
        T.isTree.connected.dist_triangle
      have hBase := hBHeight v hvB
      rw [hCross]
      omega
  · have hDepth' :
        T.graph.dist r a ≤ T.graph.dist s b + 1 := by
      omega
    refine ⟨s, Finset.mem_union_right _ hsB, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hBConn hAConn hDisj.symm hb ha hadj.symm hsB hvA
      have hTri :
          T.graph.dist r v ≤
            T.graph.dist r a + T.graph.dist a v :=
        T.isTree.connected.dist_triangle
      have hBase := hAHeight v hvA
      rw [hCross]
      omega
    · exact hBHeight v hvB

/-- Every nonempty proper finite vertex carrier in a connected tree has an
ambient edge crossing from the carrier to its complement. -/
theorem exists_adj_mem_not_mem_of_nonempty_ne_univ
    (S : Finset V)
    (hNonempty : S.Nonempty)
    (hProper : S ≠ (Finset.univ : Finset V)) :
    ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
  classical
  rcases hNonempty with ⟨x, hx⟩
  have hOutside : ∃ y : V, y ∉ S := by
    by_contra hOutside
    apply hProper
    rw [Finset.eq_univ_iff_forall]
    intro y
    by_contra hy
    exact hOutside ⟨y, hy⟩
  rcases hOutside with ⟨y, hy⟩
  rcases T.isTree.connected x y with ⟨p⟩
  have hCross :
      ∀ {u v : V} (q : T.graph.Walk u v),
        u ∈ S → v ∉ S →
          ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
    intro u v q hu hv
    induction q with
    | nil =>
        exact (hv hu).elim
    | @cons u w v hadj q ih =>
        by_cases hw : w ∈ S
        · exact ih hw hv
        · exact ⟨u, w, hu, hw, hadj⟩
  exact hCross p hx hy

/-- Vertices whose selected canonical source belongs to a chosen source set. -/
noncomputable def auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v ∈ R

@[simp] theorem mem_auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (v : V) :
    v ∈ auxSourceCarrier C ambientRoot hScores R ↔
      auxSource C ambientRoot hScores v ∈ R := by
  simp [auxSourceCarrier]

/-- Inserting one source adds exactly its whole canonical fibre. -/
theorem auxSourceCarrier_insert
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V) :
    auxSourceCarrier C ambientRoot hScores (insert r R) =
      auxSourceCarrier C ambientRoot hScores R ∪
        auxSourceFiber C ambientRoot hScores r := by
  ext v
  simp [auxSourceCarrier, auxSourceFiber, or_comm]

/-- A singleton source carrier is exactly its source fibre. -/
theorem auxSourceCarrier_singleton
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    auxSourceCarrier C ambientRoot hScores {r} =
      auxSourceFiber C ambientRoot hScores r := by
  ext v
  simp [auxSourceCarrier, auxSourceFiber]

/-- Selecting every source gives the whole ambient vertex set. -/
theorem auxSourceCarrier_univ
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxSourceCarrier C ambientRoot hScores (Finset.univ : Finset V) =
      (Finset.univ : Finset V) := by
  ext v
  simp [auxSourceCarrier]

/-- If a source has not yet been selected, its entire fibre is disjoint from
the current source carrier. -/
theorem auxSourceCarrier_disjoint_fiber_of_not_mem
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) {s : V} (hs : s ∉ R) :
    Disjoint
      (auxSourceCarrier C ambientRoot hScores R)
      (auxSourceFiber C ambientRoot hScores s) := by
  rw [Finset.disjoint_left]
  intro v hvCarrier hvFiber
  have hmem :
      auxSource C ambientRoot hScores v ∈ R := by
    simpa using hvCarrier
  have heq :
      auxSource C ambientRoot hScores v = s := by
    simpa using hvFiber
  rw [heq] at hmem
  exact hs hmem

/-- Every nonempty canonical source fibre is height-dominated by its own
source, in fact with equality pointwise. -/
theorem auxSourceFiber_heightDominated_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    HeightDominated (T := T)
      (fun v => auxHeight C ambientRoot hScores v)
      (auxSourceFiber C ambientRoot hScores r) r := by
  have hZero :=
    (auxSourceFiber_nonempty_iff C ambientRoot hScores r).1 hNonempty
  have hr :
      r ∈ auxSourceFiber C ambientRoot hScores r := by
    simp [auxSource_eq_self_of_height_zero
      C ambientRoot hScores r hZero]
  refine ⟨hr, ?_⟩
  intro v hv
  have hsrc : auxSource C ambientRoot hScores v = r := by
    simpa using hv
  change auxHeight C ambientRoot hScores v ≤ T.graph.dist r v
  rw [auxHeight_eq_dist_auxSource, hsrc]

/-- Starting from any nonempty connected union of canonical source
fibres whose auxiliary height is dominated by one root, repeatedly adjoin the
source fibre across a boundary edge.  The process terminates when the carrier
is all vertices and returns one ambient root dominating every auxiliary
height. -/
theorem exists_global_heightDominatingRoot_from_sourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V)
    (hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R))
    (hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R) r) :
    ∃ t : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist t v := by
  let S := auxSourceCarrier C ambientRoot hScores R
  by_cases hFull : S = (Finset.univ : Finset V)
  · refine ⟨r, ?_⟩
    intro v
    exact hDom.2 v (by simpa [S, hFull])
  · have hNonempty : S.Nonempty :=
      ⟨r, hDom.1⟩
    rcases
        exists_adj_mem_not_mem_of_nonempty_ne_univ
          (T := T) S hNonempty hFull with
      ⟨a, b, ha, hb, hadj⟩
    let s := auxSource C ambientRoot hScores b
    have hsNotR : s ∉ R := by
      intro hsR
      apply hb
      change b ∈ auxSourceCarrier C ambientRoot hScores R
      rw [mem_auxSourceCarrier]
      simpa [s] using hsR
    have hbFiber :
        b ∈ auxSourceFiber C ambientRoot hScores s := by
      simp [s]
    have hFiberNonempty :
        (auxSourceFiber C ambientRoot hScores s).Nonempty :=
      ⟨b, hbFiber⟩
    have hFiberConn :
        TreePathConnected (T := T)
          (auxSourceFiber C ambientRoot hScores s) :=
      auxSourceFiber_treePathConnected C ambientRoot hScores s
    have hFiberDom :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceFiber C ambientRoot hScores s) s :=
      auxSourceFiber_heightDominated_of_nonempty
        C ambientRoot hScores s hFiberNonempty
    have hDisj :
        Disjoint S (auxSourceFiber C ambientRoot hScores s) := by
      simpa [S] using
        auxSourceCarrier_disjoint_fiber_of_not_mem
          C ambientRoot hScores R hsNotR
    have hMergedConn :
        TreePathConnected (T := T)
          (S ∪ auxSourceFiber C ambientRoot hScores s) :=
      treePathConnected_union_of_adj
        hConn hFiberConn ha hbFiber hadj
    rcases
        exists_heightDominatingRoot_union_of_adj
          (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          hConn hFiberConn hDisj ha hbFiber hadj hDom hFiberDom with
      ⟨t, hMergedDom⟩
    have hCarrierInsert :
        auxSourceCarrier C ambientRoot hScores (insert s R) =
          S ∪ auxSourceFiber C ambientRoot hScores s := by
      simpa [S] using
        auxSourceCarrier_insert C ambientRoot hScores R s
    have hConn' :
        TreePathConnected (T := T)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) := by
      rw [hCarrierInsert]
      exact hMergedConn
    have hDom' :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) t := by
      rw [hCarrierInsert]
      exact hMergedDom
    exact
      exists_global_heightDominatingRoot_from_sourceCarrier
        C ambientRoot hScores (insert s R) t hConn' hDom'
termination_by ((Finset.univ : Finset V) \ R).card
decreasing_by
  have hsDiff : s ∈ ((Finset.univ : Finset V) \ R) := by
    simp [hsNotR]
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem hsDiff

/-- The canonical source partition therefore consolidates to one ambient root
whose distance profile dominates every auxiliary height. -/
theorem exists_root_auxHeight_le_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v := by
  let r₀ := auxSource C ambientRoot hScores ambientRoot
  let R₀ : Finset V := {r₀}
  have hFiberNonempty :
      (auxSourceFiber C ambientRoot hScores r₀).Nonempty := by
    refine ⟨ambientRoot, ?_⟩
    simp [r₀]
  have hCarrier :
      auxSourceCarrier C ambientRoot hScores R₀ =
        auxSourceFiber C ambientRoot hScores r₀ := by
    simpa [R₀] using
      auxSourceCarrier_singleton C ambientRoot hScores r₀
  have hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R₀) := by
    rw [hCarrier]
    exact auxSourceFiber_treePathConnected C ambientRoot hScores r₀
  have hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R₀) r₀ := by
    rw [hCarrier]
    exact
      auxSourceFiber_heightDominated_of_nonempty
        C ambientRoot hScores r₀ hFiberNonempty
  exact
    exists_global_heightDominatingRoot_from_sourceCarrier
      C ambientRoot hScores R₀ r₀ hConn hDom

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

end OrientedBranch

end TreeStack
