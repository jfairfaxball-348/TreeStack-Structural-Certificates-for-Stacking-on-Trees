import Mathlib
import TreeStack.Obstruction

namespace TreeStack

/-- If the message from `u` to `v` is nonnegative, then the reverse
message is forced negative and the tail defect is either exactly twice the
head defect or three more than twice the head defect.  The latter alternative
requires a strictly positive forward message. -/
theorem defect_left_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3)) := by
  have hinB : -δv - a ≤ 1 := by
    omega
  have hb' : b = 2 * (-δv - a) - 3 := by
    simpa only [F_of_le_one hinB] using hb
  have hpre :
      (0 < a ∧ -δu - b = 2 * a) ∨
        -δu - b = 2 * a + 3 := by
    exact
      (F_eq_nonneg_iff
        (z := -δu - b) (k := a) ha0).1 ha.symm
  refine ⟨?_, ?_⟩
  · omega
  · rcases hpre with hpre | hpre
    · right
      exact ⟨hpre.1, by omega⟩
    · left
      omega

/-- Symmetric form of `defect_left_nonneg`. -/
theorem defect_right_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3)) := by
  simpa using
    (defect_left_nonneg
      (a := b) (b := a) (δu := δv) (δv := δu)
      hδv hδu hb ha hb0)

/-- Under nonnegative endpoint defects, both edge messages cannot be
nonnegative simultaneously. -/
theorem defect_not_both_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    ¬ (0 ≤ a ∧ 0 ≤ b) := by
  intro hboth
  have h :=
    defect_left_nonneg hδu hδv ha hb hboth.1
  omega

/-- When both edge messages are negative, they are uniquely of odd negative
form and the two endpoint defects are the corresponding linear combinations. -/
theorem defect_two_negative
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (haNeg : a < 0) (hbNeg : b < 0) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by
  have hFaNeg : F (-δu - b) < 0 := by
    simpa [ha] using haNeg
  have hFbNeg : F (-δv - a) < 0 := by
    simpa [hb] using hbNeg
  have hinA : -δu - b ≤ 1 :=
    (F_neg_iff (-δu - b)).1 hFaNeg
  have hinB : -δv - a ≤ 1 :=
    (F_neg_iff (-δv - a)).1 hFbNeg
  have ha' : a = 2 * (-δu - b) - 3 := by
    simpa only [F_of_le_one hinA] using ha
  have hb' : b = 2 * (-δv - a) - 3 := by
    simpa only [F_of_le_one hinB] using hb
  let r : ℤ := 1 + δu + b
  let q : ℤ := 1 + δv + a
  have har : a = -(2 * r + 1) := by
    dsimp [r]
    omega
  have hbq : b = -(2 * q + 1) := by
    dsimp [q]
    omega
  have hr : 0 ≤ r := by
    rw [har] at haNeg
    omega
  have hq : 0 ≤ q := by
    rw [hbq] at hbNeg
    omega
  refine ⟨r, q, hr, hq, har, hbq, ?_, ?_⟩
  · dsimp [r, q]
    omega
  · dsimp [r, q]
    omega

/-- Exhaustive arbitrary-defect classification for the two integer messages
across a genuine edge.  This is the local algebraic core used by the global
defect-flow upper-bound argument. -/
theorem defect_edge_classification
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by
  by_cases ha0 : 0 ≤ a
  · left
    exact ⟨ha0, defect_left_nonneg hδu hδv ha hb ha0⟩
  · have haNeg : a < 0 := by
      omega
    by_cases hb0 : 0 ≤ b
    · right
      left
      exact ⟨hb0, defect_right_nonneg hδu hδv ha hb hb0⟩
    · have hbNeg : b < 0 := by
        omega
      right
      right
      exact defect_two_negative hδu hδv ha hb haNeg hbNeg

/-- In the oriented case, the tail defect always has enough budget to pay
twice the head defect. -/
theorem defect_left_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    2 * δv ≤ δu := by
  rcases (defect_left_nonneg hδu hδv ha hb ha0).2 with h | h
  · omega
  · omega

/-- Symmetric tail-budget inequality. -/
theorem defect_right_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    2 * δu ≤ δv := by
  simpa using
    (defect_left_budget
      (a := b) (b := a) (δu := δv) (δv := δu)
      hδv hδu hb ha hb0)


/-- The nonnegative defect attached to a nonpositive rooted score. -/
noncomputable def scoreDefect
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) : ℤ :=
  -score T C v

@[simp] theorem scoreDefect_nonneg_iff
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) :
    0 ≤ scoreDefect T C v ↔ score T C v ≤ 0 := by
  simp [scoreDefect]

/-- Reusable predicate packaging the exhaustive local defect-edge states. -/
def DefectEdgeState (a b δu δv : ℤ) : Prop :=
  (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r

theorem defectEdgeState_of_equations
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    DefectEdgeState a b δu δv := by
  simpa [DefectEdgeState] using
    (defect_edge_classification hδu hδv ha hb)

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- On an edge whose two sides are both occupied, the actual recursive branch
messages satisfy exactly the abstract defect equations used by the global
defect-flow argument. -/
theorem defect_equations_of_both_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C) :
    let a :=
      messageContribution (branchMessage C B)
    let b :=
      messageContribution (branchMessage C B.reverseBranch)
    let δu := scoreDefect T C B.root
    let δv := scoreDefect T C B.parent
    a = F (-δu - b) ∧
      b = F (-δv - a) := by
  dsimp
  have hMsgB :=
    branchMessage_eq_some_of_occupied C B hB
  have hMsgR :=
    branchMessage_eq_some_of_occupied C B.reverseBranch hR
  have hScoreB :
      score T C B.root =
        B.effectiveInput C +
          F (B.reverseBranch.effectiveInput C) := by
    simpa [hMsgR] using
      (score_eq_effectiveInput_add_reverse C B)
  have hScoreR :
      score T C B.parent =
        B.reverseBranch.effectiveInput C +
          F (B.effectiveInput C) := by
    have h :=
      score_eq_effectiveInput_add_reverse C B.reverseBranch
    simpa [hMsgB] using h
  simp only [scoreDefect, hMsgB, hMsgR,
    messageContribution_some, neg_neg]
  constructor
  · congr 1
    omega
  · congr 1
    omega

/-- Concrete TreeStack form of the arbitrary-defect edge classification:
for an edge with occupied support on both sides and nonpositive endpoint
scores, its two recursive messages lie in one of the exhaustive defect states. -/
theorem defectEdgeState_of_scores_nonpos
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C)
    (hRoot : score T C B.root ≤ 0)
    (hParent : score T C B.parent ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by
  have hEq :=
    B.defect_equations_of_both_occupied C hB hR
  apply defectEdgeState_of_equations
  · exact (scoreDefect_nonneg_iff T C B.root).2 hRoot
  · exact (scoreDefect_nonneg_iff T C B.parent).2 hParent
  · exact hEq.1
  · exact hEq.2

end OrientedBranch

end TreeStack
