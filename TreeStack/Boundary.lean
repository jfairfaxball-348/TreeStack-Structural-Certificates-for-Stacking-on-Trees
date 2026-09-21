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

/-- A final configuration obtained by a legal branch-local sequence which
clears the entire branch. -/
def ClearOutcome (B : OrientedBranch T) (C : Configuration V)
    (q : ℕ) (D : Configuration V) : Prop :=
  B.BranchReach (B.withBoundary C q) D ∧ B.Cleared D

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
