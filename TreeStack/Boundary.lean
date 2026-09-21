import Mathlib
import TreeStack.PebblingMove
import TreeStack.Message

namespace TreeStack

open scoped BigOperators Classical

/-- Oriented move counts extracted from a clearing sequence.  Positive counts
are required to lie on actual tree edges. -/
structure MoveSignature {V : Type*} [Fintype V] (T : FiniteTree V) where
  count : V → V → ℕ
  supported : ∀ {u v}, 0 < count u v → T.graph.Adj u v

namespace MoveSignature

variable {V : Type*} [Fintype V] {T : FiniteTree V}

def incoming (m : MoveSignature T) (v : V) : ℕ :=
  ∑ u, m.count u v

def outgoing (m : MoveSignature T) (v : V) : ℕ :=
  ∑ w, m.count v w

/-- Integer form of the local clearing balance
`C(v) + incoming(v) - 2*outgoing(v) = 0`. -/
def BalancesAt (m : MoveSignature T) (C : Configuration V) (v : V) : Prop :=
  (C v : ℤ) + (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0

/-- The empty move signature. -/
def zero (T : FiniteTree V) : MoveSignature T where
  count := fun _ _ => 0
  supported := by simp

/-- Extend a move signature by one actual oriented move. -/
def extend [DecidableEq V] (m : MoveSignature T) (u v : V)
    (huv : T.graph.Adj u v) : MoveSignature T where
  count := fun a b => m.count a b + if a = u ∧ b = v then 1 else 0
  supported := by
    intro a b hpos
    by_cases hnew : a = u ∧ b = v
    · rcases hnew with ⟨rfl, rfl⟩
      exact huv
    · have hm : 0 < m.count a b := by
        simpa [hnew] using hpos
      exact m.supported hm

@[simp] theorem zero_count (u v : V) :
    (zero T).count u v = 0 := rfl

@[simp] theorem incoming_zero (v : V) :
    (zero T).incoming v = 0 := by
  simp [incoming, zero]

@[simp] theorem outgoing_zero (v : V) :
    (zero T).outgoing v = 0 := by
  simp [outgoing, zero]

@[simp] theorem extend_count_same [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) :
    (m.extend u v huv).count u v = m.count u v + 1 := by
  simp [extend]

theorem incoming_extend [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) (w : V) :
    (m.extend u v huv).incoming w =
      m.incoming w + if w = v then 1 else 0 := by
  classical
  by_cases hw : w = v
  · subst w
    simp [incoming, extend, Finset.sum_add_distrib]
  · simp [incoming, extend, Finset.sum_add_distrib, hw]

theorem outgoing_extend [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) (w : V) :
    (m.extend u v huv).outgoing w =
      m.outgoing w + if w = u then 1 else 0 := by
  classical
  by_cases hw : w = u
  · subst w
    simp [outgoing, extend, Finset.sum_add_distrib]
  · simp [outgoing, extend, Finset.sum_add_distrib, hw]

end MoveSignature

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Vertices on which a branch-local clearing sequence is allowed to move:
the branch itself together with its external boundary vertex. -/
noncomputable def carrier (B : OrientedBranch T) : Finset V :=
  insert B.parent B.vertices

@[simp] theorem root_mem_carrier (B : OrientedBranch T) :
    B.root ∈ B.carrier := by
  classical
  simp [carrier, B.root_mem_vertices]

@[simp] theorem parent_mem_carrier (B : OrientedBranch T) :
    B.parent ∈ B.carrier := by
  classical
  simp [carrier]

/-- A move signature uses no vertex outside the branch plus its boundary
vertex. -/
def MoveSignature.SupportedOn (m : MoveSignature T) (B : OrientedBranch T) : Prop :=
  ∀ ⦃u v⦄, 0 < m.count u v → u ∈ B.carrier ∧ v ∈ B.carrier

/-- Static balance condition imposed by clearing every branch vertex. -/
def MoveSignature.Clears (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∀ v ∈ B.vertices, m.BalancesAt C v

/-- Net change at the external boundary contributed by crossing the unique
boundary edge. -/
def MoveSignature.boundaryFlux (m : MoveSignature T)
    (B : OrientedBranch T) : ℤ :=
  (m.count B.root B.parent : ℤ) -
    2 * (m.count B.parent B.root : ℤ)

/-- The causal condition required for a nonempty branch clearing: at least one
outward crossing of the unique boundary edge occurs. -/
def MoveSignature.CausalOutward (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  0 < m.count B.root B.parent

/-- Signature-level data used by the upper-bound induction for a nonempty
branch.  This deliberately includes causal outward crossing; balance equations
alone permit phantom unschedulable solutions at nonpositive effective input. -/
def MoveSignature.FeasibleClearing (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    MoveSignature.Clears m C B ∧
    MoveSignature.CausalOutward m B

/-- Signature-level balance for an initially and finally empty branch.
Unlike `FeasibleClearing`, no causal outward condition is imposed; these
signatures model optional empty-branch excursions. -/
def MoveSignature.EmptyExcursion (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    ∀ v ∈ B.vertices,
      (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0

section LegalSequences

variable [DecidableEq V]

/-- A legal pebbling move whose endpoints stay inside the branch carrier.
No move elsewhere in the tree is allowed. -/
def BranchPebbleStep (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  ∃ u v,
    T.graph.Adj u v ∧
    2 ≤ C u ∧
    u ∈ B.carrier ∧
    v ∈ B.carrier ∧
    D = move C u v

/-- Reachability using only legal branch-carrier moves. -/
def BranchReach (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen B.BranchPebbleStep C D

/-- All vertices of the branch have been cleared. -/
def Cleared (B : OrientedBranch T) (D : Configuration V) : Prop :=
  ∀ v ∈ B.vertices, D v = 0

/-- Replace the initial number of pebbles at the external boundary vertex by
`q`; branch messages themselves never inspect this boundary value. -/
def withBoundary (B : OrientedBranch T) (C : Configuration V) (q : ℕ) :
    Configuration V :=
  Function.update C B.parent q

@[simp] theorem withBoundary_parent (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) :
    B.withBoundary C q B.parent = q := by
  simp [withBoundary]

@[simp] theorem withBoundary_of_mem_vertices (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) {v : V} (hv : v ∈ B.vertices) :
    B.withBoundary C q v = C v := by
  have hne : v ≠ B.parent := by
    intro h
    subst v
    exact B.parent_not_mem_vertices hv
  simp [withBoundary, hne]

theorem occupied_withBoundary_iff (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) :
    B.Occupied (B.withBoundary C q) ↔ B.Occupied C := by
  constructor
  · rintro ⟨v, hv, hpos⟩
    exact ⟨v, hv, by simpa [B.withBoundary_of_mem_vertices C q hv] using hpos⟩
  · rintro ⟨v, hv, hpos⟩
    exact ⟨v, hv, by simpa [B.withBoundary_of_mem_vertices C q hv] using hpos⟩

/-- A final configuration obtained by a legal branch-local sequence which
clears the entire branch. -/
def ClearOutcome (B : OrientedBranch T) (C : Configuration V)
    (q : ℕ) (D : Configuration V) : Prop :=
  B.BranchReach (B.withBoundary C q) D ∧ B.Cleared D

theorem MoveSignature.zero_supportedOn (B : OrientedBranch T) :
    (MoveSignature.zero T).SupportedOn B := by
  intro u v h
  simp at h

theorem MoveSignature.extend_supportedOn
    (B : OrientedBranch T) (m : MoveSignature T)
    {u v : V} (huv : T.graph.Adj u v)
    (hm : m.SupportedOn B) (hu : u ∈ B.carrier) (hv : v ∈ B.carrier) :
    (m.extend u v huv).SupportedOn B := by
  intro a b hpos
  by_cases hnew : a = u ∧ b = v
  · rcases hnew with ⟨rfl, rfl⟩
    exact ⟨hu, hv⟩
  · apply hm
    simpa [MoveSignature.extend, hnew] using hpos

/-- Exact pointwise integer accounting for one legal move. -/
theorem move_balance_int (C : Configuration V) {u v : V}
    (huv : u ≠ v) (hu : 2 ≤ C u) (w : V) :
    (move C u v w : ℤ) =
      (C w : ℤ) + (if w = v then 1 else 0) -
        2 * (if w = u then 1 else 0) := by
  classical
  by_cases hwu : w = u
  · subst w
    simp [move, huv, hu]
  · by_cases hwv : w = v
    · subst w
      simp [move, huv.symm, hwu]
    · simp [move, hwu, hwv]

/-- A branch-local reachability proof has an exact oriented move-count
signature.  The final clause is causal: if no root-to-parent move occurred,
an initially occupied branch is still occupied. -/
theorem BranchReach.exists_moveSignature
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    ∃ m : MoveSignature T,
      m.SupportedOn B ∧
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (B.Occupied C →
        m.count B.root B.parent = 0 →
        B.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, MoveSignature.zero_supportedOn B, ?_, ?_⟩
      · intro w
        simp
      · intro hOcc _
        exact hOcc
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      rcases ih with ⟨m, hmSupp, hmBal, hmPersist⟩
      let m' : MoveSignature T := m.extend u v huv
      refine ⟨m', ?_, ?_, ?_⟩
      · exact MoveSignature.extend_supportedOn B m huv hmSupp huCarrier hvCarrier
      · intro w
        rw [move_balance_int _ huv.ne hlegal w, hmBal w]
        simp [m', MoveSignature.incoming_extend, MoveSignature.outgoing_extend]
        ring
      · intro hOcc hzero
        have hmzero : m.count B.root B.parent = 0 := by
          have hle :
              m.count B.root B.parent ≤ m'.count B.root B.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        have hnotBoundary : ¬ (u = B.root ∧ v = B.parent) := by
          rintro ⟨rfl, rfl⟩
          dsimp [m', MoveSignature.extend] at hzero
          simp at hzero
        have hvBranch : v ∈ B.vertices := by
          have hvCases : v = B.parent ∨ v ∈ B.vertices := by
            simpa [carrier] using hvCarrier
          rcases hvCases with hvp | hvb
          · subst v
            have huCases : u = B.parent ∨ u ∈ B.vertices := by
              simpa [carrier] using huCarrier
            rcases huCases with hup | hub
            · subst u
              exact (huv.ne rfl).elim
            · have huroot := B.eq_root_of_mem_vertices_adj_parent hub huv
              exact (hnotBoundary ⟨huroot, rfl⟩).elim
          · exact hvb
        refine ⟨v, hvBranch, ?_⟩
        simp [move]

theorem MoveSignature.incoming_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : m.SupportedOn B) :
    m.incoming B.parent = m.count B.root B.parent := by
  classical
  rw [MoveSignature.incoming]
  apply Finset.sum_eq_single B.root
  · intro u _ hune
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hadj := m.supported hpos
    have hcar := (hm hpos).1
    have huCases : u = B.parent ∨ u ∈ B.vertices := by
      simpa [carrier] using hcar
    rcases huCases with hup | hub
    · subst u
      exact hadj.ne rfl
    · exact hune (B.eq_root_of_mem_vertices_adj_parent hub hadj)
  · simp

theorem MoveSignature.outgoing_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : m.SupportedOn B) :
    m.outgoing B.parent = m.count B.parent B.root := by
  classical
  rw [MoveSignature.outgoing]
  apply Finset.sum_eq_single B.root
  · intro v _ hvne
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hadj := m.supported hpos
    have hcar := (hm hpos).2
    have hvCases : v = B.parent ∨ v ∈ B.vertices := by
      simpa [carrier] using hcar
    rcases hvCases with hvp | hvb
    · subst v
      exact hadj.ne rfl
    · exact hvne (B.eq_root_of_mem_vertices_adj_parent hvb hadj.symm)
  · simp

/-- Every legal clearing of an initially occupied branch yields a genuine
feasible clearing signature, and the final boundary pile is exactly the
initial boundary pile plus the signature's boundary flux. -/
theorem ClearOutcome.exists_feasibleClearing_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hOcc : B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      m.FeasibleClearing C B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + m.boundaryFlux B := by
  rcases B.BranchReach.exists_moveSignature hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : m.Clears C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal : m.CausalOutward B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hInitialOcc : B.Occupied (B.withBoundary C q) := by
      exact (B.occupied_withBoundary_iff C q).2 hOcc
    have hFinalOcc := hmPersist hInitialOcc hzero
    rcases hFinalOcc with ⟨v, hv, hpos⟩
    rw [hClear.2 v hv] at hpos
    omega
  refine ⟨m, ⟨hmSupp, hClears, hCausal⟩, ?_⟩
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    m.incoming_parent_eq_boundary B hmSupp,
    m.outgoing_parent_eq_boundary B hmSupp] at hParent
  simpa [MoveSignature.boundaryFlux] using hParent

/-- The exact boundary theorem in the form targeted by the Phase 1 induction.
This is a proposition/target definition; later proofs must establish it from
legal move sequences and the recursive message.

For an occupied branch with integer message `d`, every clear outcome leaves
at most `q+d` pebbles at the boundary; when `q+d>0` that value is attained;
when `q+d≤0` no positive boundary pile after clearing is reachable. -/
def ExactBoundaryInvariant (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C →
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ,
        (0 < (q : ℤ) + d →
          ∃ D : Configuration V,
            B.ClearOutcome C q D ∧
              (D B.parent : ℤ) = (q : ℤ) + d) ∧
        (∀ D : Configuration V,
          B.ClearOutcome C q D →
            (D B.parent : ℤ) ≤ (q : ℤ) + d) ∧
        ((q : ℤ) + d ≤ 0 →
          ¬ ∃ D : Configuration V,
            B.ClearOutcome C q D ∧ 0 < D B.parent)

end LegalSequences

end OrientedBranch

end TreeStack
