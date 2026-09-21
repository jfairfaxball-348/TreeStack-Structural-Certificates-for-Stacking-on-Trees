import Mathlib
import TreeStack.Transfer
import TreeStack.Branch

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The configuration restriction to an oriented branch is nonempty exactly
when some branch vertex carries a pebble.  This is different from structural
nonemptiness: every `OrientedBranch` has at least its root as a vertex. -/
def Occupied (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∃ v ∈ B.vertices, 0 < C v

noncomputable instance (C : Configuration V) (B : OrientedBranch T) :
    Decidable (B.Occupied C) := Classical.dec _

/-- Integer contribution of a message to a parent sum.  `EMPTY` contributes
nothing to the sum, but remains categorically distinct from the integer
message zero. -/
def messageContribution : Message → ℤ
  | none => 0
  | some d => d

@[simp] theorem messageContribution_empty :
    messageContribution EMPTY = 0 := rfl

@[simp] theorem messageContribution_some (d : ℤ) :
    messageContribution (some d) = d := rfl

/-- The audited recursive branch message.  A configuration-empty branch has
the separate message `EMPTY`.  A nonempty branch applies the exact transfer
`F` to the pebbles at its root plus the contributions of every genuine
child branch.

Recursion is by strict child-branch cardinality decrease; no whole-tree bound
is used as the recursive measure. -/
noncomputable def branchMessage (C : Configuration V) (B : OrientedBranch T) :
    Message :=
  if hB : B.Occupied C then
    some <| F <|
      (C B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            messageContribution
              (branchMessage C
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }))
          else
            0
  else
    EMPTY
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }

/-- Sum of the recursively computed genuine-child messages, omitting
configuration-empty child branches.  Omitting an `EMPTY` contribution here
does not identify `EMPTY` with the integer zero as a message. -/
noncomputable def childMessageSum (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      messageContribution
        (branchMessage C
          (B.childBranch
            { vertex := v
              adj := h.1
              ne_parent := h.2 }))
    else
      0

/-- Effective integer input at the root of a nonempty oriented branch. -/
noncomputable def effectiveInput (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  (C B.root : ℤ) + childMessageSum C B

theorem branchMessage_eq_empty_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : ¬ B.Occupied C) :
    branchMessage C B = EMPTY := by
  rw [branchMessage]
  simp [hB]

theorem branchMessage_eq_some_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B = some (F (effectiveInput C B)) := by
  rw [branchMessage]
  simp [hB, effectiveInput, childMessageSum]

/-- Exact empty-state classification for branch messages. -/
theorem branchMessage_eq_empty_iff
    (C : Configuration V) (B : OrientedBranch T) :
    branchMessage C B = EMPTY ↔ ¬ B.Occupied C := by
  constructor
  · intro h
    by_contra hB
    have hs := branchMessage_eq_some_of_occupied C B hB
    rw [hs] at h
    simp [EMPTY] at h
  · exact branchMessage_eq_empty_of_not_occupied C B

/-- A configuration-nonempty branch always has an integer message. -/
theorem branchMessage_ne_empty_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B ≠ EMPTY := by
  rw [branchMessage_eq_some_of_occupied C B hB]
  simp [EMPTY]

end OrientedBranch

end TreeStack
