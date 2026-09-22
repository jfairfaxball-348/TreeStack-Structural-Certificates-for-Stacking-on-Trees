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
  let px : T.graph.Walk x r := by
    simpa [hsx] using auxWalk C ambientRoot hScores x
  let py : T.graph.Walk y r := by
    simpa [hsy] using auxWalk C ambientRoot hScores y
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
