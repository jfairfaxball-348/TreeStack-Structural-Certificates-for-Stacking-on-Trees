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

/-- Lowering an effective input by three cannot increase the transfer. -/
theorem F_sub_three_le (z : ℤ) : F (z - 3) ≤ F z := by
  unfold F
  split_ifs <;> omega

/-- The transfer is negative exactly on inputs at most one. -/
theorem F_neg_iff (z : ℤ) : F z < 0 ↔ z ≤ 1 := by
  unfold F
  split_ifs <;> omega

/-- Zero is an exceptional transfer value: it has the unique preimage three. -/
theorem F_eq_zero_iff (z : ℤ) : F z = 0 ↔ z = 3 := by
  unfold F
  split_ifs <;> omega

/-- Negative outputs are precisely the negative odd integers, with their
preimages written in the form used by the branch induction. -/
theorem F_eq_neg_odd_iff {z r : ℤ} (hr : 0 ≤ r) :
    F z = -(2 * r + 1) ↔ z = 1 - r := by
  unfold F
  split_ifs <;> omega

/-- For a nonnegative target transfer value `k`, the two generic preimages
are `2k` and `2k+3`; the first disappears at `k=0`. -/
theorem F_eq_nonneg_iff {z k : ℤ} (hk : 0 ≤ k) :
    F z = k ↔ (0 < k ∧ z = 2 * k) ∨ z = 2 * k + 3 := by
  unfold F
  split_ifs <;> omega

/-- The one-vertex signature inequality. `A` counts outward moves and is
positive; `B` counts inward moves. -/
theorem one_vertex_flux_le {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    A - 2 * B ≤ F y := by
  unfold F
  split_ifs <;> omega

/-- The one-vertex flux and the maximizing transfer have the same residue
modulo three. -/
theorem one_vertex_flux_mod_three {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    (A - 2 * B) % 3 = F y % 3 := by
  unfold F
  split_ifs <;> omega

/-- Equality in the one-vertex bound for effective input at most one. -/
theorem one_vertex_flux_attained_le_one {y : ℤ} (hy : y ≤ 1) :
    let A : ℤ := 1
    let B : ℤ := 2 - y
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  rw [F_of_le_one hy]
  omega

/-- Equality in the one-vertex bound for positive even effective input. -/
theorem one_vertex_flux_attained_even {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k
    let A : ℤ := k
    let B : ℤ := 0
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  have hy : 4 ≤ 2 * k ∨ k = 1 := by omega
  rcases hy with hy | rfl
  · rw [F_of_ge_four_even hy (by omega)]
    omega
  · norm_num

/-- Equality in the one-vertex bound for odd effective input at least three. -/
theorem one_vertex_flux_attained_odd {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k + 1
    let A : ℤ := k + 1
    let B : ℤ := 1
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  by_cases hk1 : k = 1
  · subst k
    norm_num
  · have hy : 5 ≤ 2 * k + 1 := by omega
    rw [F_of_ge_five_odd hy (by omega)]
    omega

end TreeStack
