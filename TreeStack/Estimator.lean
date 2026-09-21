import Mathlib
import TreeStack.Basic

namespace TreeStack

/-- Degree-one vertices other than the chosen root. -/
noncomputable def leafVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ T.graph.degree v = 1

/-- Vertices that contribute to the source definition of sigma:
the root, together with every vertex of degree greater than one. -/
noncomputable def sigmaVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter fun v =>
    v = r ∨ 1 < T.graph.degree v

/-- Internal vertices different from the root.  This is the part of
`sigmaVertices` left after splitting off the root contribution. -/
noncomputable def nonRootInternalVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ 1 < T.graph.degree v

/-- The source leaf count: degree-one vertices other than the root. -/
noncomputable def leafCount {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  (leafVertices T r).card

/-- The source quantity sigma_T(r), including its leading one. -/
noncomputable def sigma {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  1 + ∑ v in sigmaVertices T r,
    T.graph.degree v * 2 ^ T.graph.dist r v

/-- The source rooted estimator sigma_T(r) + leaf_T(r). -/
noncomputable def rootEstimate {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  sigma T r + leafCount T r

/-- The source tree estimator, the maximum rooted estimator. -/
noncomputable def estim {V : Type*} [Fintype V]
    (T : FiniteTree V) : ℕ :=
  (Finset.univ : Finset V).sup (rootEstimate T)

/-- Split the sigma support into the root and the non-root internal vertices. -/
theorem sigmaVertices_eq_insert {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigmaVertices T r = insert r (nonRootInternalVertices T r) := by
  classical
  ext v
  by_cases hvr : v = r
  · simp [sigmaVertices, nonRootInternalVertices, hvr]
  · simp [sigmaVertices, nonRootInternalVertices, hvr]

/-- Correct root-sensitive expansion of sigma.  In particular, the root
contribution is retained even when the root itself is a leaf. -/
theorem sigma_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigma T r =
      1 + T.graph.degree r +
        ∑ v in nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  classical
  rw [sigma, sigmaVertices_eq_insert]
  have hnot : r ∉ nonRootInternalVertices T r := by
    simp [nonRootInternalVertices]
  rw [Finset.sum_insert hnot]
  simp

/-- Correct root-sensitive expansion of the rooted estimator.
This replaces the false helper identity that drops a degree-one root. -/
theorem rootEstimate_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + leafCount T r + T.graph.degree r +
        ∑ v in nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  rw [rootEstimate, sigma_corrected_expansion]
  omega

/-- If all degrees are positive, every non-root vertex is either a leaf or
a non-root internal vertex. -/
theorem erase_root_eq_leaf_union_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    (Finset.univ : Finset V).erase r =
      leafVertices T r ∪ nonRootInternalVertices T r := by
  classical
  ext v
  by_cases hvr : v = r
  · simp [leafVertices, nonRootInternalVertices, hvr]
  · have hv := hdeg v
    simp [leafVertices, nonRootInternalVertices, hvr]
    omega

theorem leafVertices_disjoint_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    Disjoint (leafVertices T r) (nonRootInternalVertices T r) := by
  classical
  simp [Finset.disjoint_left, leafVertices, nonRootInternalVertices]

theorem card_erase_root_eq_leafCount_add_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    ((Finset.univ : Finset V).erase r).card =
      leafCount T r + (nonRootInternalVertices T r).card := by
  rw [erase_root_eq_leaf_union_internal T r hdeg,
    Finset.card_union_of_disjoint (leafVertices_disjoint_internal T r)]
  rfl

/-- Each weighted non-root internal contribution is at least one. -/
theorem card_internal_le_weighted_sum {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    (nonRootInternalVertices T r).card ≤
      ∑ v in nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
  classical
  calc
    (nonRootInternalVertices T r).card =
        ∑ _v in nonRootInternalVertices T r, 1 := by simp
    _ ≤ ∑ v in nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
      exact Finset.sum_le_sum fun v hv => by
        have hv' : v ≠ r ∧ 1 < T.graph.degree v := by
          simpa [nonRootInternalVertices] using hv
        have hprod :
            0 < T.graph.degree v * 2 ^ T.graph.dist r v := by
          exact Nat.mul_pos (by omega) (by positivity)
        omega

/-- Arithmetic form of the elementary estimator lower bound, assuming
positive degree at every vertex. -/
theorem card_add_one_le_rootEstimate_of_degree_pos
    {V : Type*} [Fintype V] (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  classical
  have hpart := card_erase_root_eq_leafCount_add_internal T r hdeg
  have herase :=
    Finset.card_erase_add_one (s := (Finset.univ : Finset V))
      (a := r) (Finset.mem_univ r)
  have hsum := card_internal_le_weighted_sum T r
  have hroot := hdeg r
  simp only [Finset.card_univ] at herase
  rw [rootEstimate_corrected_expansion]
  omega

/-- Elementary estimator lower bound for every root of a nontrivial finite
tree.  The root may itself have degree one. -/
theorem card_add_one_le_rootEstimate {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  classical
  apply card_add_one_le_rootEstimate_of_degree_pos T r
  intro v
  exact T.isTree.connected.preconnected.degree_pos_of_nontrivial v

/-- Every rooted estimator is bounded by the tree estimator. -/
theorem rootEstimate_le_estim {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r ≤ estim T := by
  classical
  simpa [estim] using
    (Finset.le_sup (f := rootEstimate T) (Finset.mem_univ r))

/-- The tree estimator is at least one more than the vertex count for every
nontrivial finite tree. -/
theorem card_add_one_le_estim {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) :
    Fintype.card V + 1 ≤ estim T := by
  classical
  let r : V := T.isTree.connected.nonempty.some
  exact (card_add_one_le_rootEstimate T r).trans (rootEstimate_le_estim T r)

end TreeStack
