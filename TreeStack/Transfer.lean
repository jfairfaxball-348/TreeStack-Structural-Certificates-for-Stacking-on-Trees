import Mathlib
import TreeStack.Basic

namespace TreeStack

/-- Exact integer transfer function from the branch-clearing proof. -/
def F (x : ℤ) : ℤ :=
  if x ≤ 1 then
    2 * x - 3
  else if x = 2 then
    1
  else if x = 3 then
    0
  else if x % 2 = 0 then
    x / 2
  else
    (x - 3) / 2

/-- Branch messages distinguish the empty branch from every integer message. -/
abbrev Message := Option ℤ

def EMPTY : Message := none

@[simp] theorem empty_ne_integer_zero : EMPTY ≠ some 0 := by
  simp [EMPTY]

theorem F_of_le_one {x : ℤ} (h : x ≤ 1) : F x = 2 * x - 3 := by
  simp [F, h]

@[simp] theorem F_two : F 2 = 1 := by
  norm_num [F]

@[simp] theorem F_three : F 3 = 0 := by
  norm_num [F]

theorem F_of_ge_four_even {x : ℤ} (h4 : 4 ≤ x) (he : x % 2 = 0) :
    F x = x / 2 := by
  simp [F, show ¬ x ≤ 1 by omega, show x ≠ 2 by omega,
    show x ≠ 3 by omega, he]

theorem F_of_ge_five_odd {x : ℤ} (h5 : 5 ≤ x) (ho : x % 2 ≠ 0) :
    F x = (x - 3) / 2 := by
  simp [F, show ¬ x ≤ 1 by omega, show x ≠ 2 by omega,
    show x ≠ 3 by omega, ho]

end TreeStack
