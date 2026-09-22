import Mathlib
import TreeStack.Estimator
import TreeStack.RootScore

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Canonical obstruction rooted at r: sigma(r)-1 pebbles at r, one pebble
on every degree-one vertex different from r, and zero elsewhere. -/
noncomputable def extremalConfig
    (T : FiniteTree V) (r : V) : Configuration V :=
  Function.update
    (oneOn (leafVertices T r))
    r
    (sigma T r - 1)

@[simp] theorem root_not_mem_leafVertices
    (T : FiniteTree V) (r : V) :
    r ∉ leafVertices T r := by
  simp [leafVertices]

@[simp] theorem extremalConfig_root
    (T : FiniteTree V) (r : V) :
    extremalConfig T r r = sigma T r - 1 := by
  simp [extremalConfig]

theorem extremalConfig_of_ne_root
    (T : FiniteTree V) (r : V) {v : V}
    (hvr : v ≠ r) :
    extremalConfig T r v =
      if v ∈ leafVertices T r then 1 else 0 := by
  simp [extremalConfig, oneOn, hvr]

theorem extremalConfig_eq_one_of_mem_leafVertices
    (T : FiniteTree V) (r : V) {v : V}
    (hv : v ∈ leafVertices T r) :
    extremalConfig T r v = 1 := by
  have hv' : v ≠ r ∧ T.graph.degree v = 1 := by
    simpa [leafVertices] using hv
  have hvr : v ≠ r := hv'.1
  simp [extremalConfig_of_ne_root T r hvr, hv]

theorem extremalConfig_eq_zero_of_ne_root_not_mem_leafVertices
    (T : FiniteTree V) (r : V) {v : V}
    (hvr : v ≠ r) (hv : v ∉ leafVertices T r) :
    extremalConfig T r v = 0 := by
  simp [extremalConfig_of_ne_root T r hvr, hv]

theorem one_le_sigma (T : FiniteTree V) (r : V) :
    1 ≤ sigma T r := by
  simp [sigma]

/-- Exact mass of the canonical rooted obstruction. -/
theorem mass_extremalConfig
    (T : FiniteTree V) (r : V) :
    mass (extremalConfig T r) = rootEstimate T r - 1 := by
  classical
  have hr : r ∈ (Finset.univ : Finset V) := Finset.mem_univ r
  have hnot : r ∉ leafVertices T r := root_not_mem_leafVertices T r
  have hsumErase :
      ∑ v ∈ (Finset.univ : Finset V).erase r,
        oneOn (leafVertices T r) v =
      leafCount T r := by
    calc
      ∑ v ∈ (Finset.univ : Finset V).erase r,
          oneOn (leafVertices T r) v =
          mass (oneOn (leafVertices T r)) := by
            rw [mass]
            apply Finset.sum_subset (Finset.erase_subset r Finset.univ)
            intro v hvUniv hvNotErase
            have hvr : v = r := by
              by_contra hne
              exact hvNotErase (Finset.mem_erase.mpr ⟨hne, hvUniv⟩)
            subst v
            simp [oneOn, hnot]
      _ = (leafVertices T r).card := mass_oneOn _
      _ = leafCount T r := rfl
  rw [mass, extremalConfig,
    Finset.sum_update_of_mem hr,
    Finset.sdiff_singleton_eq_erase,
    hsumErase,
    rootEstimate]
  have hs := one_le_sigma T r
  omega


/-- Recursive obstruction height of an oriented branch.  At a global leaf it
is one; otherwise it is three plus twice the sum of the genuine child
heights.  This is the integer whose negative is the extremal branch message. -/
noncomputable def obstructionHeight (B : OrientedBranch T) : ℤ :=
  if T.graph.degree B.root = 1 then
    1
  else
    3 + 2 * ∑ v : V,
      if h : B.IsChildVertex v then
        obstructionHeight (B.childBranch (B.childOfVertex v h))
      else
        0
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt (B.childOfVertex v h)

/-- An oriented branch whose root is not a leaf has a genuine child: its
boundary parent is already one neighbor, so degree greater than one supplies
another. -/
theorem OrientedBranch.exists_childVertex_of_degree_ne_one
    (B : OrientedBranch T)
    (hdeg : T.graph.degree B.root ≠ 1) :
    ∃ v : V, B.IsChildVertex v := by
  classical
  have hpos : 0 < T.graph.degree B.root :=
    T.graph.degree_pos_iff_exists_adj.mpr ⟨B.parent, B.adj⟩
  have hgt : 1 < T.graph.degree B.root := by omega
  have hcard : 1 < (T.graph.neighborFinset B.root).card := by
    simpa using hgt
  obtain ⟨v, hv, hvne⟩ :=
    Finset.exists_mem_ne hcard B.parent
  refine ⟨v, ?_, hvne⟩
  exact (T.graph.mem_neighborFinset v).mp hv

/-- If the branch root has degree one, its parent is its unique neighbor and
there is no genuine child branch. -/
theorem OrientedBranch.not_isChildVertex_of_degree_one
    (B : OrientedBranch T)
    (hdeg : T.graph.degree B.root = 1) :
    ∀ v : V, ¬ B.IsChildVertex v := by
  classical
  have huniq :
      ∃! w : V, T.graph.Adj B.root w :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hdeg
  rcases huniq with ⟨w, hw, hunique⟩
  intro v hv
  have hvw : v = w := hunique v hv.1
  have hpw : B.parent = w := hunique B.parent B.adj
  exact hv.2 (hvw.trans hpw.symm)

/-- Obstruction heights are strictly positive. -/
theorem obstructionHeight_pos
    (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  classical
  rw [obstructionHeight]
  by_cases hleaf : T.graph.degree B.root = 1
  · simp [hleaf]
  · simp only [if_neg hleaf]
    have hsum :
        0 ≤ ∑ v : V,
          if h : B.IsChildVertex v then
            obstructionHeight (B.childBranch (B.childOfVertex v h))
          else
            0 := by
      apply Finset.sum_nonneg
      intro v hv
      by_cases h : B.IsChildVertex v
      · simp only [h, dite_true]
        exact le_of_lt
          (obstructionHeight_pos
            (B.childBranch (B.childOfVertex v h)))
      · simp [h]
    linarith
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt (B.childOfVertex v h)

/-- Away from the distinguished root, the extremal configuration is one
exactly at degree-one vertices and zero otherwise. -/
theorem extremalConfig_branch_root
    (T : FiniteTree V) (r : V) (B : OrientedBranch T)
    (hr : r ∉ B.vertices) :
    extremalConfig T r B.root =
      if T.graph.degree B.root = 1 then 1 else 0 := by
  have hne : B.root ≠ r := by
    intro h
    subst r
    exact hr B.root_mem_vertices
  rw [extremalConfig_of_ne_root T r hne]
  by_cases hleaf : T.graph.degree B.root = 1
  · simp [leafVertices, hne, hleaf]
  · simp [leafVertices, hne, hleaf]

/-- On every oriented branch lying away from the distinguished obstruction
root, the recursive message is the negative obstruction height. -/
theorem obstruction_branchMessage
    (T : FiniteTree V) (r : V) (B : OrientedBranch T)
    (hr : r ∉ B.vertices) :
    OrientedBranch.branchMessage (extremalConfig T r) B =
      some (- obstructionHeight B) := by
  classical
  let C : Configuration V := extremalConfig T r
  have hRoot :
      C B.root =
        if T.graph.degree B.root = 1 then 1 else 0 := by
    simpa [C] using extremalConfig_branch_root T r B hr
  by_cases hleaf : T.graph.degree B.root = 1
  · have hNoChild :
        ∀ v : V, ¬ B.IsChildVertex v :=
      B.not_isChildVertex_of_degree_one hleaf
    have hOcc : B.Occupied C := by
      refine ⟨B.root, B.root_mem_vertices, ?_⟩
      rw [hRoot]
      simp [hleaf]
    have hChildZero :
        OrientedBranch.childMessageSum C B = 0 := by
      rw [OrientedBranch.childMessageSum_eq_sum_term]
      apply Finset.sum_eq_zero
      intro v hv
      simp [OrientedBranch.childMessageTerm, hNoChild v]
    rw [OrientedBranch.branchMessage_eq_some_of_occupied C B hOcc]
    congr 1
    rw [OrientedBranch.effectiveInput, hRoot, hChildZero,
      obstructionHeight]
    simp [hleaf, F]
  · obtain ⟨v₀, hv₀⟩ :=
      B.exists_childVertex_of_degree_ne_one hleaf
    let c₀ : B.Child := B.childOfVertex v₀ hv₀
    have hrChild₀ :
        r ∉ (B.childBranch c₀).vertices := by
      intro hmem
      exact hr (B.childBranch_vertices_subset c₀ hmem)
    have hMsgChild₀ :=
      obstruction_branchMessage T r (B.childBranch c₀) hrChild₀
    have hOccChild₀ :
        (B.childBranch c₀).Occupied C := by
      by_contra hEmpty
      have hempty :=
        OrientedBranch.branchMessage_eq_empty_of_not_occupied
          C (B.childBranch c₀) hEmpty
      rw [hMsgChild₀] at hempty
      simp [EMPTY] at hempty
    have hOcc : B.Occupied C := by
      rcases hOccChild₀ with ⟨w, hw, hpos⟩
      exact
        ⟨w, B.childBranch_vertices_subset c₀ hw, hpos⟩
    let H : ℤ :=
      ∑ v : V,
        if h : B.IsChildVertex v then
          obstructionHeight (B.childBranch (B.childOfVertex v h))
        else
          0
    have hHnonneg : 0 ≤ H := by
      dsimp [H]
      apply Finset.sum_nonneg
      intro v hv
      by_cases h : B.IsChildVertex v
      · simp only [h, dite_true]
        exact le_of_lt
          (obstructionHeight_pos
            (B.childBranch (B.childOfVertex v h)))
      · simp [h]
    have hChildSum :
        OrientedBranch.childMessageSum C B = -H := by
      rw [OrientedBranch.childMessageSum_eq_sum_term]
      calc
        (∑ v : V, B.childMessageTerm C v) =
            ∑ v : V,
              -(if h : B.IsChildVertex v then
                  obstructionHeight
                    (B.childBranch (B.childOfVertex v h))
                else
                  0) := by
              apply Finset.sum_congr rfl
              intro v hv
              by_cases h : B.IsChildVertex v
              · let c : B.Child := B.childOfVertex v h
                have hrChild :
                    r ∉ (B.childBranch c).vertices := by
                  intro hmem
                  exact hr (B.childBranch_vertices_subset c hmem)
                have hMsg :=
                  obstruction_branchMessage T r
                    (B.childBranch c) hrChild
                simpa [OrientedBranch.childMessageTerm, h, c] using hMsg
              · simp [OrientedBranch.childMessageTerm, h]
        _ = -H := by
              dsimp [H]
              rw [Finset.sum_neg_distrib]
    rw [OrientedBranch.branchMessage_eq_some_of_occupied C B hOcc]
    congr 1
    have hInput :
        OrientedBranch.effectiveInput C B = -H := by
      rw [OrientedBranch.effectiveInput, hRoot, hChildSum]
      simp [hleaf]
    rw [hInput]
    have hle : -H ≤ 1 := by linarith
    rw [F_of_le_one hle, obstructionHeight]
    simp only [if_neg hleaf]
    dsimp [H]
    ring
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c₀
  exact B.childBranch_card_lt (B.childOfVertex v h)


end TreeStack
