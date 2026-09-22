import Mathlib
import TreeStack.ForestOwner

namespace TreeStack

/-- Weighted edge estimate for an oriented-type defect edge.  If the auxiliary
weight at the head is at least twice the weight at the tail, the edge
contribution is bounded by the neutral endpoint weights plus the standard
head-defect excess. -/
theorem oriented_edge_excess_bound
    {a b deltaHead weightTail weightHead : ℤ}
    (ha : 0 ≤ a)
    (hb : b = -2 * (a + deltaHead) - 3)
    (hDouble : 2 * weightTail ≤ weightHead) :
    -(weightHead * a + weightTail * b) ≤
      weightTail + weightHead + 2 * weightTail * deltaHead := by
  have hCoeff : 2 * weightTail - weightHead ≤ 0 := by
    linarith
  have hMul : a * (2 * weightTail - weightHead) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hCoeff
  rw [hb]
  calc
    -(weightHead * a + weightTail * (-2 * (a + deltaHead) - 3)) =
        3 * weightTail +
          a * (2 * weightTail - weightHead) +
          2 * weightTail * deltaHead := by
            ring
    _ ≤ 3 * weightTail + 2 * weightTail * deltaHead := by
          linarith
    _ ≤ weightTail + weightHead + 2 * weightTail * deltaHead := by
          linarith

/-- The oriented-edge excess can be paid by the tail endpoint whenever the
local defect classification supplies the factor-two tail budget. -/
theorem oriented_excess_le_tail_budget
    {deltaTail deltaHead weightTail : ℤ}
    (hWeight : 0 ≤ weightTail)
    (hBudget : 2 * deltaHead ≤ deltaTail) :
    2 * weightTail * deltaHead ≤ weightTail * deltaTail := by
  have h :=
    mul_le_mul_of_nonneg_left hBudget hWeight
  nlinarith

/-- The same oriented-edge excess can instead be paid by the head endpoint
whenever the auxiliary orientation doubles weights along the edge. -/
theorem oriented_excess_le_head_budget
    {deltaHead weightTail weightHead : ℤ}
    (hDelta : 0 ≤ deltaHead)
    (hDouble : 2 * weightTail ≤ weightHead) :
    2 * weightTail * deltaHead ≤ weightHead * deltaHead := by
  exact mul_le_mul_of_nonneg_right hDouble hDelta

/-- Exact weighted contribution of a two-negative edge in its odd-negative
parameterization. -/
theorem two_negative_edge_excess_eq
    {a b r q weightTail weightHead : ℤ}
    (ha : a = -(2 * r + 1))
    (hb : b = -(2 * q + 1)) :
    -(weightHead * a + weightTail * b) =
      weightTail + weightHead +
        2 * (weightHead * r + weightTail * q) := by
  rw [ha, hb]
  ring

/-- If a two-negative edge is oriented toward its owner and owner weight is at
least twice tail weight, the complete excess is paid by the owner's endpoint
defect.  Here `deltaOwner = q + 2*r` is exactly the local defect equation. -/
theorem two_negative_excess_le_owner_budget
    {r q deltaOwner weightTail weightOwner : ℤ}
    (hq : 0 ≤ q)
    (hDouble : 2 * weightTail ≤ weightOwner)
    (hDelta : deltaOwner = q + 2 * r) :
    2 * (weightOwner * r + weightTail * q) ≤
      weightOwner * deltaOwner := by
  have hqMul :
      (2 * weightTail) * q ≤ weightOwner * q :=
    mul_le_mul_of_nonneg_right hDouble hq
  rw [hDelta]
  calc
    2 * (weightOwner * r + weightTail * q) =
        2 * weightOwner * r + (2 * weightTail) * q := by
          ring
    _ ≤ 2 * weightOwner * r + weightOwner * q := by
          linarith
    _ = weightOwner * (q + 2 * r) := by
          ring

end TreeStack
