import Mathlib
import TreeStack.UpperBound

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The exact-size source predicate whose least witness is the stacking
number.  The source convention requires the threshold itself to be at least
two. -/
def StackingCandidate (T : FiniteTree V) (t : ℕ) : Prop :=
  2 ≤ t ∧ UniversalStackable T.graph t

/-- The Csernák--Soukup stacking number: the least exact size at least two
for which every configuration is stackable. -/
noncomputable def stack (T : FiniteTree V) : ℕ :=
  sInf {t : ℕ | StackingCandidate T t}

/-- Exact-size universality propagates to every larger exact size on a
nontrivial connected finite graph. -/
theorem universal_stackable_mono
    [Nontrivial V]
    (T : FiniteTree V) {s t : ℕ}
    (hU : UniversalStackable T.graph s)
    (hs : 2 ≤ s) (hst : s ≤ t) :
    UniversalStackable T.graph t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact hU
  | succ t hst ih =>
      exact
        universal_stackable_succ
          T.isTree.connected ih (by omega)

/-- On every nontrivial finite tree the estimator itself is an admissible
stacking candidate. -/
theorem estim_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (estim T) := by
  constructor
  · have hcard : 1 < Fintype.card V :=
      Fintype.one_lt_card
    have hEstim := card_add_one_le_estim T
    omega
  · exact universalStackable_estim T

/-- The exact-size candidate set is nonempty for every nontrivial finite
tree. -/
theorem stackingCandidate_nonempty
    [Nontrivial V] (T : FiniteTree V) :
    Set.Nonempty {t : ℕ | StackingCandidate T t} :=
  ⟨estim T, estim_stackingCandidate T⟩

/-- The defined stacking number is itself an exact-size stacking candidate. -/
theorem stack_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (stack T) := by
  unfold stack
  exact Nat.sInf_mem (stackingCandidate_nonempty T)

/-- Minimality of the exact-size stacking number. -/
theorem stack_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    stack T ≤ t := by
  unfold stack
  exact Nat.sInf_le ht

/-- Every admissible exact stacking threshold is at least the estimator.
Otherwise exact-size upward closure would make the estimator-minus-one
obstruction stackable. -/
theorem estim_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    estim T ≤ t := by
  rcases ht with ⟨htTwo, hU⟩
  by_contra hNot
  have htLt : t < estim T := Nat.lt_of_not_ge hNot
  have htLe : t ≤ estim T - 1 := by omega
  have hUObs :
      UniversalStackable T.graph (estim T - 1) :=
    universal_stackable_mono T hU htTwo htLe
  rcases exists_nonstackable_mass_estim_sub_one T with
    ⟨C, hMass, hNotStackable⟩
  exact hNotStackable (hUObs C hMass)

/-- Exact Csernák--Soukup stacking equality for every nontrivial finite
tree. -/
theorem stack_eq_estim
    [Nontrivial V] (T : FiniteTree V) :
    stack T = estim T := by
  apply Nat.le_antisymm
  · exact stack_le_of_stackingCandidate T (estim_stackingCandidate T)
  · exact estim_le_of_stackingCandidate T (stack_stackingCandidate T)

/-- Headline form with the source's explicit nontriviality hypothesis.  The
one-vertex tree is intentionally excluded because the source stacking number
uses thresholds at least two while the displayed estimator is one there. -/
theorem stack_eq_estim_of_two_le_card
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T := by
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact stack_eq_estim T

end TreeStack
