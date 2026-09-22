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
  have hvr : v ≠ r := by
    exact (by simpa [leafVertices] using hv).1
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

end TreeStack
