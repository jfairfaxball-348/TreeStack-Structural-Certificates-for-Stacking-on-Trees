import Mathlib
import TreeStack.GlobalCharge

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Ambient degree-one vertices.  Unlike `leafVertices T r`, this set is
independent of a chosen estimator root. -/
noncomputable def ambientLeaves : Finset V :=
  (Finset.univ : Finset V).filter fun v => T.graph.degree v = 1

/-- Number of ambient degree-one vertices. -/
noncomputable def ambientLeafCount : ℕ :=
  (ambientLeaves (T := T)).card

/-- The amount removed when converting auxiliary weighted mass back to ordinary
mass.  Every summand is nonnegative because every auxiliary weight is at least
one. -/
noncomputable def auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ)

/-- The part of the weighted degree potential that must be removed at ambient
leaves. -/
noncomputable def auxLeafSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientLeaves (T := T),
    (auxWeightInt C ambientRoot hScores v - 1)

/-- Integer auxiliary weights are at least one. -/
theorem one_le_auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    1 ≤ auxWeightInt C ambientRoot hScores v := by
  have hpos : 0 < auxWeight C ambientRoot hScores v :=
    auxWeight_pos C ambientRoot hScores v
  have hone : 1 ≤ auxWeight C ambientRoot hScores v := by
    omega
  change (1 : ℤ) ≤ (auxWeight C ambientRoot hScores v : ℤ)
  exact Int.ofNat_le.mpr hone

/-- If an ambient leaf has non-unit auxiliary weight, then it is occupied.
Positive height supplies an incoming auxiliary arrow; that arrow is retained,
and the leaf-side deleted-edge branch is the singleton leaf. -/
theorem leaf_pos_of_auxWeightInt_ne_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1)
    (hWeight : auxWeightInt C ambientRoot hScores v ≠ 1) :
    0 < C v := by
  have hHeightNe : auxHeight C ambientRoot hScores v ≠ 0 := by
    intro hZero
    apply hWeight
    simp [auxWeightInt, auxWeight, hZero]
  have hIncoming :
      ∃ u : V, AuxArrow (T := T) C ambientRoot u v := by
    by_contra hNoExists
    have hNo : ∀ u : V, ¬ AuxArrow (T := T) C ambientRoot u v := by
      intro u hArrow
      exact hNoExists ⟨u, hArrow⟩
    exact hHeightNe
      (auxHeight_eq_zero_of_no_incoming
        C ambientRoot hScores v hNo)
  rcases hIncoming with ⟨u, hArrow⟩
  let B : OrientedBranch T :=
    incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)
  have hSupport : B.SupportEdge C := by
    simpa [B] using auxArrow_supportEdge C ambientRoot hArrow
  rcases hSupport.2 with ⟨x, hx, hxPos⟩
  have hLeaf' : T.graph.degree B.reverseBranch.root = 1 := by
    change T.graph.degree v = 1
    exact hLeaf
  have hSingleton : B.reverseBranch.vertices = {v} := by
    have h :=
      vertices_eq_singleton_of_degree_one B.reverseBranch hLeaf'
    simpa [B] using h
  have hxv : x = v := by
    rw [hSingleton] at hx
    simpa using hx
  simpa [hxv] using hxPos

/-- At an ambient leaf, the configuration-weight slack pays the entire excess
of the auxiliary leaf weight over one. -/
theorem leafWeightSlackTerm_le_configurationSlackTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1) :
    auxWeightInt C ambientRoot hScores v - 1 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
  have hWeightOne :=
    one_le_auxWeightInt C ambientRoot hScores v
  by_cases hEq : auxWeightInt C ambientRoot hScores v = 1
  · simp [hEq]
  · have hCPos :=
      leaf_pos_of_auxWeightInt_ne_one
        C ambientRoot hScores v hLeaf hEq
    have hCOneNat : 1 ≤ C v := by omega
    have hCOne : (1 : ℤ) ≤ (C v : ℤ) := by
      exact_mod_cast hCOneNat
    calc
      auxWeightInt C ambientRoot hScores v - 1 =
          (auxWeightInt C ambientRoot hScores v - 1) * 1 := by ring
      _ ≤
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
        exact mul_le_mul_of_nonneg_left hCOne
          (sub_nonneg.mpr hWeightOne)

/-- Every configuration-slack summand is nonnegative. -/
theorem configurationSlackTerm_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    0 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
  exact mul_nonneg
    (sub_nonneg.mpr (one_le_auxWeightInt C ambientRoot hScores v))
    (by positivity)

/-- The exact conversion identity from weighted mass to ordinary mass. -/
theorem auxWeightedMass_sub_configurationSlack_eq_mass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores -
        auxConfigurationSlack C ambientRoot hScores =
      (mass C : ℤ) := by
  unfold auxWeightedMass auxConfigurationSlack
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ v : V,
        (auxWeightInt C ambientRoot hScores v * (C v : ℤ) -
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ))) =
        ∑ v : V, (C v : ℤ) := by
      apply Fintype.sum_congr
      intro v
      ring
    _ = (mass C : ℤ) := by
      simp [mass]

/-- Occupied ambient leaves pay all of the leaf-weight slack. -/
theorem auxLeafSlack_le_auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxLeafSlack C ambientRoot hScores ≤
      auxConfigurationSlack C ambientRoot hScores := by
  unfold auxLeafSlack auxConfigurationSlack
  calc
    (∑ v ∈ ambientLeaves (T := T),
        (auxWeightInt C ambientRoot hScores v - 1)) ≤
        ∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
      exact Finset.sum_le_sum fun v hv => by
        have hLeaf : T.graph.degree v = 1 := by
          simpa [ambientLeaves] using hv
        exact
          leafWeightSlackTerm_le_configurationSlackTerm
            C ambientRoot hScores v hLeaf
    _ ≤ ∑ v : V,
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun v _ _ =>
          configurationSlackTerm_nonneg C ambientRoot hScores v)

/-- Ordinary mass is bounded by the weighted degree potential after removing
the leaf-weight slack.  This is the ambient-tree leaf-slack conversion and
does not require transporting the configuration to a support subtype. -/
theorem mass_le_auxDegreePotential_sub_leafSlack
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores := by
  have hWeighted :=
    auxWeightedMass_le_auxDegreePotential
      C ambientRoot hRootPos hScores
  have hSlack :=
    auxLeafSlack_le_auxConfigurationSlack
      C ambientRoot hScores
  have hMass :=
    auxWeightedMass_sub_configurationSlack_eq_mass
      C ambientRoot hScores
  linarith

/-- Ambient vertices of degree greater than one. -/
noncomputable def ambientInternalVertices : Finset V :=
  (Finset.univ : Finset V).filter fun v => 1 < T.graph.degree v

/-- The internal-vertex part of the auxiliary degree potential. -/
noncomputable def auxInternalDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    (T.graph.degree v : ℤ) * auxWeightInt C ambientRoot hScores v

/-- Compact auxiliary potential after the occupied-leaf slack has removed the
unwanted powers of two at leaves. -/
noncomputable def auxCompactPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  (ambientLeafCount (T := T) : ℤ) +
    auxInternalDegreePotential C ambientRoot hScores

/-- The rooted internal part of the Csernák--Soukup estimator. -/
noncomputable def rootedInternalPotential
    (T : FiniteTree V) (r : V) : ℕ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    T.graph.degree v * 2 ^ T.graph.dist r v

theorem ambientLeaves_disjoint_ambientInternal :
    Disjoint
      (ambientLeaves (T := T))
      (ambientInternalVertices (T := T)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvLeaf hvInternal
  have hLeaf : T.graph.degree v = 1 := by
    simpa [ambientLeaves] using hvLeaf
  have hInternal : 1 < T.graph.degree v := by
    simpa [ambientInternalVertices] using hvInternal
  omega

/-- In a nontrivial tree, every vertex is either a leaf or has degree greater
than one. -/
theorem ambientLeaves_union_ambientInternal [Nontrivial V] :
    ambientLeaves (T := T) ∪ ambientInternalVertices (T := T) =
      (Finset.univ : Finset V) := by
  classical
  ext v
  have hdeg :
      0 < T.graph.degree v :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial v
  simp [ambientLeaves, ambientInternalVertices]
  omega

/-- Split the weighted degree potential into leaf and internal terms. -/
theorem auxDegreePotential_eq_leaf_add_internal [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores =
      (∑ v ∈ ambientLeaves (T := T),
        auxWeightInt C ambientRoot hScores v) +
      auxInternalDegreePotential C ambientRoot hScores := by
  classical
  unfold auxDegreePotential auxInternalDegreePotential
  have hDis :=
    ambientLeaves_disjoint_ambientInternal (T := T)
  have hUnion :=
    ambientLeaves_union_ambientInternal (T := T)
  have hLeafSum :
      (∑ v ∈ ambientLeaves (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v) =
        ∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hLeaf : T.graph.degree v = 1 := by
      simpa [ambientLeaves] using hv
    simp [hLeaf]
  calc
    (∑ v : V, (T.graph.degree v : ℤ) *
        auxWeightInt C ambientRoot hScores v) =
      ∑ v ∈
          (ambientLeaves (T := T) ∪
            ambientInternalVertices (T := T)),
        (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v := by
      rw [hUnion]
    _ =
      (∑ v ∈ ambientLeaves (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v) +
        ∑ v ∈ ambientInternalVertices (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
      rw [Finset.sum_union hDis]
    _ =
      (∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) +
        ∑ v ∈ ambientInternalVertices (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
      rw [hLeafSum]

/-- Removing the leaf slack from the degree potential leaves exactly one unit
per ambient leaf plus the weighted internal-vertex potential. -/
theorem auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores =
      auxCompactPotential C ambientRoot hScores := by
  rw [auxDegreePotential_eq_leaf_add_internal
    C ambientRoot hScores]
  unfold auxLeafSlack auxCompactPotential ambientLeafCount
  have hLeafDiff :
      (∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1)) =
        ((ambientLeaves (T := T)).card : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v -
            (auxWeightInt C ambientRoot hScores v - 1))) =
          ∑ _v ∈ ambientLeaves (T := T), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = ((ambientLeaves (T := T)).card : ℤ) := by
        simp
  calc
    ((∑ v ∈ ambientLeaves (T := T),
        auxWeightInt C ambientRoot hScores v) +
        auxInternalDegreePotential C ambientRoot hScores) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1)) =
      ((∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1))) +
        auxInternalDegreePotential C ambientRoot hScores := by
      ring
    _ = ((ambientLeaves (T := T)).card : ℤ) +
        auxInternalDegreePotential C ambientRoot hScores := by
      rw [hLeafDiff]

/-- Final ordinary-mass form of the leaf-slack inequality. -/
theorem mass_le_auxCompactPotential [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxCompactPotential C ambientRoot hScores := by
  rw [← auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    C ambientRoot hScores]
  exact
    mass_le_auxDegreePotential_sub_leafSlack
      C ambientRoot hRootPos hScores

theorem ambientLeaves_eq_insert_leafVertices_of_root_leaf
    (T : FiniteTree V) (r : V)
    (hLeaf : T.graph.degree r = 1) :
    ambientLeaves (T := T) = insert r (leafVertices T r) := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientLeaves, leafVertices, hLeaf]
  · simp [ambientLeaves, leafVertices, hvr]

theorem ambientLeaves_eq_leafVertices_of_root_not_leaf
    (T : FiniteTree V) (r : V)
    (hNotLeaf : T.graph.degree r ≠ 1) :
    ambientLeaves (T := T) = leafVertices T r := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientLeaves, leafVertices, hNotLeaf]
  · simp [ambientLeaves, leafVertices, hvr]

theorem ambientInternal_eq_nonRootInternal_of_root_not_internal
    (T : FiniteTree V) (r : V)
    (hNotInternal : ¬ 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      nonRootInternalVertices T r := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientInternalVertices, nonRootInternalVertices, hNotInternal]
  · simp [ambientInternalVertices, nonRootInternalVertices, hvr]

theorem ambientInternal_eq_insert_nonRootInternal_of_root_internal
    (T : FiniteTree V) (r : V)
    (hInternal : 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      insert r (nonRootInternalVertices T r) := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientInternalVertices, nonRootInternalVertices, hInternal]
  · simp [ambientInternalVertices, nonRootInternalVertices, hvr]

/-- Root-insensitive decomposition of the rooted estimator.  This statement
handles degree-one roots explicitly: the root term in `sigma` exactly replaces
the leaf omitted from `leafCount T r`. -/
theorem rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    [Nontrivial V] (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + ambientLeafCount (T := T) + rootedInternalPotential T r := by
  classical
  have hdeg :
      0 < T.graph.degree r :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial r
  by_cases hLeaf : T.graph.degree r = 1
  · have hLeaves :=
      ambientLeaves_eq_insert_leafVertices_of_root_leaf T r hLeaf
    have hrNotLeaf : r ∉ leafVertices T r := by
      simp [leafVertices]
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r + 1 := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
      simp [hrNotLeaf]
    have hNotInternal : ¬ 1 < T.graph.degree r := by
      omega
    have hInternal :=
      ambientInternal_eq_nonRootInternal_of_root_not_internal
        T r hNotInternal
    have hPotential :
        rootedInternalPotential T r =
          ∑ v ∈ nonRootInternalVertices T r,
            T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal]
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential, hLeaf]
    omega
  · have hInternalRoot : 1 < T.graph.degree r := by
      omega
    have hLeaves :=
      ambientLeaves_eq_leafVertices_of_root_not_leaf T r hLeaf
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
    have hInternal :=
      ambientInternal_eq_insert_nonRootInternal_of_root_internal
        T r hInternalRoot
    have hrNotInternal : r ∉ nonRootInternalVertices T r := by
      simp [nonRootInternalVertices]
    have hPotential :
        rootedInternalPotential T r =
          T.graph.degree r +
            ∑ v ∈ nonRootInternalVertices T r,
              T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal, Finset.sum_insert hrNotInternal]
      simp
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential]
    omega

end OrientedBranch

end TreeStack
