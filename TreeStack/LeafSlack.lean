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
  exact_mod_cast hone

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
  have hSingleton : B.reverseBranch.vertices = {v} := by
    apply vertices_eq_singleton_of_degree_one
    simpa [B] using hLeaf
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

end OrientedBranch

end TreeStack
