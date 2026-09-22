import Mathlib
import TreeStack.LeafSlack

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Positive auxiliary height is realized by an incoming auxiliary arrow whose
tail has height exactly one less. -/
theorem exists_auxArrow_height_eq_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hv : 0 < auxHeight C ambientRoot hScores v) :
    ∃ u : V,
      AuxArrow (T := T) C ambientRoot u v ∧
        auxHeight C ambientRoot hScores v =
          auxHeight C ambientRoot hScores u + 1 := by
  letI : Nonempty V := T.isTree.connected.nonempty
  let f : V → ℕ := fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
  obtain ⟨u, huMax⟩ := Finite.exists_max f
  have hEq : auxHeight C ambientRoot hScores v = f u := by
    rw [auxHeight]
    apply le_antisymm
    · exact Finset.sup_le fun x _hx => huMax x
    · exact Finset.le_sup (f := f) (Finset.mem_univ u)
  have hfuPos : 0 < f u := by
    rw [← hEq]
    exact hv
  by_cases hArrow : AuxArrow (T := T) C ambientRoot u v
  · refine ⟨u, hArrow, ?_⟩
    simpa [f, hArrow] using hEq
  · simp [f, hArrow] at hfuPos

/-- A source certificate packages one selected auxiliary path ending at a
vertex.  Its source has height zero; the path is simple; its length is the
endpoint height; and no vertex on the path has larger height than the
endpoint. -/
structure AuxSourceCertificate
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) where
  source : V
  walk : T.graph.Walk source v
  isPath : walk.IsPath
  source_height_zero :
    auxHeight C ambientRoot hScores source = 0
  length_eq_height :
    walk.length = auxHeight C ambientRoot hScores v
  height_le_of_mem_support :
    ∀ x : V, x ∈ walk.support →
      auxHeight C ambientRoot hScores x ≤
        auxHeight C ambientRoot hScores v

/-- Select a height-realizing incoming edge repeatedly until height zero. -/
noncomputable def auxSourceCertificate
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : AuxSourceCertificate C ambientRoot hScores v := by
  by_cases hv : 0 < auxHeight C ambientRoot hScores v
  · obtain ⟨u, hArrow, hHeight⟩ :=
      exists_auxArrow_height_eq_of_pos C ambientRoot hScores v hv
    let cert :=
      auxSourceCertificate C ambientRoot hScores u
    have hvNot : v ∉ cert.walk.support := by
      intro hmem
      have hle := cert.height_le_of_mem_support v hmem
      omega
    refine
      { source := cert.source
        walk := cert.walk.concat (auxArrow_adj C ambientRoot hArrow)
        isPath :=
          cert.isPath.concat hvNot
            (auxArrow_adj C ambientRoot hArrow)
        source_height_zero := cert.source_height_zero
        length_eq_height := ?_
        height_le_of_mem_support := ?_ }
    · simp [cert, hHeight, cert.length_eq_height]
    · intro x hx
      rw [SimpleGraph.Walk.support_concat] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact (cert.height_le_of_mem_support x hx).trans (by omega)
      · exact le_rfl
  · have hZero : auxHeight C ambientRoot hScores v = 0 := by
      omega
    refine
      { source := v
        walk := SimpleGraph.Walk.nil
        isPath := SimpleGraph.Walk.IsPath.nil
        source_height_zero := hZero
        length_eq_height := by simp [hZero]
        height_le_of_mem_support := ?_ }
    intro x hx
    simp at hx
    subst x
    exact le_rfl
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  omega

/-- The selected height-zero source of a vertex. -/
noncomputable def auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) : V :=
  (auxSourceCertificate C ambientRoot hScores v).source

/-- The selected source has auxiliary height zero. -/
theorem auxSource_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    auxHeight C ambientRoot hScores
        (auxSource C ambientRoot hScores v) = 0 := by
  exact
    (auxSourceCertificate C ambientRoot hScores v).source_height_zero

/-- The selected source-to-vertex path is a shortest tree path, so auxiliary
height is exactly ambient-tree distance from the selected source. -/
theorem auxSource_dist_eq_height
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    T.graph.dist (auxSource C ambientRoot hScores v) v =
      auxHeight C ambientRoot hScores v := by
  let cert := auxSourceCertificate C ambientRoot hScores v
  have hdist :=
    tree_path_length_eq_dist (T := T) cert.walk cert.isPath
  have hlen := cert.length_eq_height
  change T.graph.dist cert.source v =
    auxHeight C ambientRoot hScores v
  omega

/-- Auxiliary powers of two are rooted-distance powers at the selected source. -/
theorem auxWeight_eq_two_pow_source_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    auxWeight C ambientRoot hScores v =
      2 ^ T.graph.dist (auxSource C ambientRoot hScores v) v := by
  rw [auxWeight, auxSource_dist_eq_height]

end OrientedBranch

end TreeStack
