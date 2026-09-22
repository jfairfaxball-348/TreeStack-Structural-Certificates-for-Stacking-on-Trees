import Mathlib
import TreeStack.Consolidation

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- A pointwise domination of auxiliary height by distance from one root gives
the corresponding powers-of-two domination in the integer weights. -/
theorem auxWeightInt_le_two_pow_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hHeight :
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxWeightInt C ambientRoot hScores v ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
  change
    (auxWeight C ambientRoot hScores v : ℤ) ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ)
  exact_mod_cast
    Nat.pow_le_pow_right Nat.zero_lt_two hHeight

/-- Once one root dominates all auxiliary heights, the weighted internal
degree potential is bounded by the rooted internal estimator potential. -/
theorem auxInternalDegreePotential_le_rootedInternalPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hHeight : ∀ v,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxInternalDegreePotential C ambientRoot hScores ≤
      (rootedInternalPotential T r : ℤ) := by
  unfold auxInternalDegreePotential rootedInternalPotential
  calc
    (∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v) ≤
      ∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
      exact Finset.sum_le_sum fun v _ => by
        exact mul_le_mul_of_nonneg_left
          (auxWeightInt_le_two_pow_dist
            C ambientRoot hScores r v (hHeight v))
          (by positivity)
    _ = (∑ v ∈ ambientInternalVertices (T := T),
          T.graph.degree v * 2 ^ T.graph.dist r v : ℕ) := by
      norm_cast

/-- Consolidation turns the compact auxiliary potential into one rooted
Csernák--Soukup estimator, with the leading one removed. -/
theorem exists_root_auxCompactPotential_le_rootEstimate_sub_one
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V,
      auxCompactPotential C ambientRoot hScores ≤
        (rootEstimate T r : ℤ) - 1 := by
  rcases
      exists_root_auxHeight_le_dist C ambientRoot hScores with
    ⟨r, hHeight⟩
  refine ⟨r, ?_⟩
  have hInternal :=
    auxInternalDegreePotential_le_rootedInternalPotential
      C ambientRoot hScores r hHeight
  rw [rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    T r]
  unfold auxCompactPotential
  push_cast
  linarith

end OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- A positive-mass configuration has an occupied vertex. -/
theorem exists_pos_of_mass_pos
    (C : Configuration V) (hMass : 0 < mass C) :
    ∃ v : V, 0 < C v := by
  by_contra hNone
  push Not at hNone
  have hZero : ∀ v : V, C v = 0 := by
    intro v
    exact Nat.eq_zero_of_not_pos (hNone v)
  have hm : mass C = 0 := by
    simp [mass, hZero]
  omega

/-- The arbitrary-defect upper bound in additive form.  If every rooted score
is nonpositive, then the configuration has at most `estim T - 1` pebbles. -/
theorem mass_add_one_le_estim_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C + 1 ≤ estim T := by
  by_cases hMassZero : mass C = 0
  · rw [hMassZero]
    have hEstim := card_add_one_le_estim T
    omega
  · have hMassPos : 0 < mass C :=
      Nat.pos_of_ne_zero hMassZero
    rcases exists_pos_of_mass_pos C hMassPos with
      ⟨ambientRoot, hRootPos⟩
    have hMassCompact :=
      OrientedBranch.mass_le_auxCompactPotential
        C ambientRoot hRootPos hScores
    rcases
        OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
          C ambientRoot hScores with
      ⟨r, hCompactRoot⟩
    have hRootEstim := rootEstimate_le_estim T r
    have hRootEstimInt :
        (rootEstimate T r : ℤ) ≤ (estim T : ℤ) := by
      exact_mod_cast hRootEstim
    have hMassEstimInt :
        (mass C : ℤ) + 1 ≤ (estim T : ℤ) := by
      linarith
    exact_mod_cast hMassEstimInt

/-- Natural-subtraction form of the arbitrary-defect estimator bound. -/
theorem mass_le_estim_sub_one_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C ≤ estim T - 1 := by
  have h :=
    mass_add_one_le_estim_of_all_scores_nonpos T C hScores
  omega

/-- Every globally non-stackable configuration lies below the estimator
threshold. -/
theorem nonstackable_mass_le_estim_sub_one
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hNot : ¬ Stackable T.graph C) :
    mass C ≤ estim T - 1 := by
  exact
    mass_le_estim_sub_one_of_all_scores_nonpos T C
      ((not_stackable_iff_all_scores_nonpos T C).1 hNot)

/-- Every configuration of exactly the estimator size is stackable. -/
theorem universalStackable_estim
    [Nontrivial V]
    (T : FiniteTree V) :
    UniversalStackable T.graph (estim T) := by
  intro C hMass
  by_contra hNot
  have hUpper :=
    nonstackable_mass_le_estim_sub_one T C hNot
  rw [hMass] at hUpper
  have hEstimPos := card_add_one_le_estim T
  omega

end TreeStack
