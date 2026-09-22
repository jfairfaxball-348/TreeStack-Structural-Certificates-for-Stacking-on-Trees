import Mathlib
import TreeStack.Estimator
import TreeStack.RootScore

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The explicit rooted estimator obstruction: `sigma T r - 1` pebbles at
the selected root, one pebble at every other leaf, and zero elsewhere. -/
noncomputable def obstruction (T : FiniteTree V) (r : V) : Configuration V := by
  classical
  exact fun v =>
    if v = r then
      sigma T r - 1
    else if v ∈ leafVertices T r then
      1
    else
      0

@[simp] theorem obstruction_root (T : FiniteTree V) (r : V) :
    obstruction T r r = sigma T r - 1 := by
  simp [obstruction]

theorem obstruction_apply_ne (T : FiniteTree V) (r v : V) (hvr : v ≠ r) :
    obstruction T r v = if T.graph.degree v = 1 then 1 else 0 := by
  classical
  simp [obstruction, leafVertices, hvr]

theorem obstruction_leaf (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v = 1) :
    obstruction T r v = 1 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

theorem obstruction_internal (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v ≠ 1) :
    obstruction T r v = 0 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

/-- Exact mass of the explicit rooted obstruction. -/
theorem mass_obstruction (T : FiniteTree V) (r : V) :
    mass (obstruction T r) = rootEstimate T r - 1 := by
  classical
  have hsigma : 1 ≤ sigma T r := by
    simp [sigma]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v =
        leafCount T r := by
    rw [leafCount]
    calc
      (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) =
          ∑ v ∈ (Finset.univ : Finset V).erase r,
            if v ∈ leafVertices T r then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvr : v ≠ r := by
                exact (Finset.mem_erase.mp hv).1
              simp [obstruction, hvr]
      _ = ((Finset.univ : Finset V).erase r).filter
            (fun v => v ∈ leafVertices T r) |>.card := by
              simpa using
                (Finset.sum_boole (R := ℕ)
                  (fun v : V => v ∈ leafVertices T r)
                  ((Finset.univ : Finset V).erase r))
      _ = (leafVertices T r).card := by
              congr 1
              ext v
              simp [leafVertices]
  rw [mass]
  calc
    (∑ v : V, obstruction T r v) =
        (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) +
          obstruction T r r := by
            symm
            exact Finset.sum_erase_add (Finset.univ : Finset V)
              (obstruction T r) (Finset.mem_univ r)
    _ = leafCount T r + (sigma T r - 1) := by
          rw [hsum, obstruction_root]
    _ = rootEstimate T r - 1 := by
          rw [rootEstimate]
          omega

namespace OrientedBranch

/-- Recursive obstruction height on an oriented branch.  The recursion follows
exactly the genuine child branches used by `branchMessage`. -/
noncomputable def obstructionHeight (B : OrientedBranch T) : ℕ :=
  if hLeaf : T.graph.degree B.root = 1 then
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

theorem obstructionHeight_leaf (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    obstructionHeight B = 1 := by
  rw [obstructionHeight]
  simp [hLeaf]

theorem obstructionHeight_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    obstructionHeight B =
      3 + 2 *
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            obstructionHeight
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 })
          else
            0 := by
  rw [obstructionHeight]
  simp [show T.graph.degree B.root ≠ 1 by omega]

theorem obstructionHeight_pos (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  rw [obstructionHeight]
  split_ifs <;> positivity

end OrientedBranch

end TreeStack
