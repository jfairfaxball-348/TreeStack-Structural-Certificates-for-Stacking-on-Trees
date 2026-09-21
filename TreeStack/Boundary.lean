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

@[simp] theorem carrier_erase_parent [DecidableEq V] (B : OrientedBranch T) :
    B.carrier.erase B.parent = B.vertices := by
  ext v
  constructor
  · intro hv
    have hv' : v ≠ B.parent ∧ v ∈ B.carrier := by
      simpa using hv
    have hcases : v = B.parent ∨ v ∈ B.vertices := by
      simpa [carrier] using hv'.2
    exact hcases.resolve_left hv'.1
  · intro hv
    have hne : v ≠ B.parent := by
      intro h
      subst v
      exact B.parent_not_mem_vertices hv
    simp [carrier, hv, hne]

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
    MoveSignature.SupportedOn (MoveSignature.zero T) B := by
  intro u v h
  simp at h

theorem MoveSignature.extend_supportedOn
    (B : OrientedBranch T) (m : MoveSignature T)
    {u v : V} (huv : T.graph.Adj u v)
    (hm : MoveSignature.SupportedOn m B) (hu : u ∈ B.carrier) (hv : v ∈ B.carrier) :
    MoveSignature.SupportedOn (m.extend u v huv) B := by
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
signature.  The final clause is causal on every oriented subbranch contained
in the ambient branch: if no outward boundary move of that subbranch occurs,
initial occupancy of the subbranch persists. -/
theorem BranchReach.exists_moveSignature
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    ∃ m : MoveSignature T,
      MoveSignature.SupportedOn m B ∧
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, MoveSignature.zero_supportedOn B, ?_, ?_⟩
      · intro w
        simp
      · intro A _ hOcc _
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
        by_cases hwu : w = u <;> simp [hwu] <;> ring
      · intro A hAB hOcc hzero
        have hmzero : m.count A.root A.parent = 0 := by
          have hle :
              m.count A.root A.parent ≤ m'.count A.root A.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        rcases hmPersist A hAB hOcc hmzero with ⟨w, hwA, hwpos⟩
        by_cases hvA : v ∈ A.vertices
        · refine ⟨v, hvA, ?_⟩
          simp [move, huv.ne]
        · have huA : u ∉ A.vertices := by
            intro huA
            have hEdge :=
              A.edge_leaving_vertices_eq_boundary huA hvA huv
            rw [Sym2.eq_iff] at hEdge
            rcases hEdge with h | h
            · rcases h with ⟨huRoot, hvParent⟩
              subst u
              subst v
              dsimp [m', MoveSignature.extend] at hzero
              simp at hzero
            · rcases h with ⟨huParent, hvRoot⟩
              subst u
              exact A.parent_not_mem_vertices huA
          have hwu : w ≠ u := by
            intro h
            subst w
            exact huA hwA
          have hwv : w ≠ v := by
            intro h
            subst w
            exact hvA hwA
          refine ⟨w, hwA, ?_⟩
          simpa [move, hwu, hwv] using hwpos

theorem MoveSignature.incoming_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : MoveSignature.SupportedOn m B) :
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
    (hm : MoveSignature.SupportedOn m B) :
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
      MoveSignature.FeasibleClearing m C B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal : MoveSignature.CausalOutward m B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hInitialOcc : B.Occupied (B.withBoundary C q) := by
      exact (B.occupied_withBoundary_iff C q).2 hOcc
    have hFinalOcc :=
      hmPersist B (by intro v hv; exact hv) hInitialOcc hzero
    rcases hFinalOcc with ⟨v, hv, hpos⟩
    rw [hClear.2 v hv] at hpos
    omega
  refine ⟨m, ⟨hmSupp, hClears, hCausal⟩, ?_⟩
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  calc
    (D B.parent : ℤ) =
        (q : ℤ) + (m.count B.root B.parent : ℤ) -
          2 * (m.count B.parent B.root : ℤ) := hParent
    _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
      rw [MoveSignature.boundaryFlux]
      ring


/-- Total pebble mass on the branch carrier. -/
noncomputable def carrierMass (B : OrientedBranch T) (C : Configuration V) : ℕ :=
  ∑ v ∈ B.carrier, C v

theorem carrierMass_move_add_one (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u)
    (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.carrierMass (move C u v) + 1 = B.carrierMass C := by
  classical
  simp only [carrierMass, move]
  rw [Finset.sum_update_of_mem hvB, Finset.sdiff_singleton_eq_erase]
  have hu_mem : u ∈ B.carrier.erase v := by
    simp [huB, huv]
  rw [Finset.sum_update_of_mem (s := B.carrier.erase v) (i := u)
      (f := C) (b := C u - 2) hu_mem,
    Finset.sdiff_singleton_eq_erase]
  have hv := Finset.sum_erase_add B.carrier C hvB
  have hu' := Finset.sum_erase_add (B.carrier.erase v) C hu_mem
  omega

theorem BranchReach.carrierMass_le
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    B.carrierMass D ≤ B.carrierMass C := by
  induction hreach with
  | refl => rfl
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      have hdrop :=
        B.carrierMass_move_add_one _ huv.ne hlegal huB hvB
      omega

theorem not_occupied_iff_zero_on_vertices
    (B : OrientedBranch T) (C : Configuration V) :
    ¬ B.Occupied C ↔ ∀ v ∈ B.vertices, C v = 0 := by
  constructor
  · intro h v hv
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact h ⟨v, hv, hpos⟩
  · intro hz hOcc
    rcases hOcc with ⟨v, hv, hpos⟩
    rw [hz v hv] at hpos
    omega

theorem carrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.carrierMass (B.withBoundary C q) = q := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hsum : ∑ v ∈ B.vertices, B.withBoundary C q v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [B.withBoundary_of_mem_vertices C q hv, hz v hv]
  have hdecomp :=
    Finset.sum_erase_add B.carrier (B.withBoundary C q) hp
  simp only [herase, hsum, B.withBoundary_parent] at hdecomp
  rw [carrierMass]
  omega

theorem carrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.carrierMass D = D B.parent := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hsum : ∑ v ∈ B.vertices, D v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hClear v hv
  have hdecomp := Finset.sum_erase_add B.carrier D hp
  simp only [herase, hsum] at hdecomp
  rw [carrierMass]
  omega

/-- A legal initially empty excursion cannot increase the boundary pile. -/
theorem BranchReach.empty_boundary_nonincrease
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    D B.parent ≤ q := by
  have hle := BranchReach.carrierMass_le B hreach
  rw [B.carrierMass_eq_parent_of_cleared D hClear,
    B.carrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hle
  exact hle

/-- The ±1 bipartite weight based at the exterior boundary vertex. -/
noncomputable def boundaryParityWeight (B : OrientedBranch T) (v : V) : ℤ :=
  if T.graph.dist B.parent v % 2 = 0 then 1 else -1

@[simp] theorem boundaryParityWeight_parent (B : OrientedBranch T) :
    B.boundaryParityWeight B.parent = 1 := by
  simp [boundaryParityWeight]

theorem boundaryParityWeight_adj_neg (B : OrientedBranch T)
    {u v : V} (huv : T.graph.Adj u v) :
    B.boundaryParityWeight v = -B.boundaryParityWeight u := by
  let col := T.isTree.coloringTwoOfVert B.parent
  have hne : col u ≠ col v := col.valid huv
  have hval :
      T.graph.dist B.parent u % 2 ≠ T.graph.dist B.parent v % 2 := by
    intro h
    apply hne
    apply Fin.ext
    exact h
  have huLt : T.graph.dist B.parent u % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have hvLt : T.graph.dist B.parent v % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  unfold boundaryParityWeight
  by_cases hu0 : T.graph.dist B.parent u % 2 = 0
  · have hv0 : T.graph.dist B.parent v % 2 ≠ 0 := by
      intro hv0
      exact hval (hu0.trans hv0.symm)
    simp [hu0, hv0]
  · have hu1 : T.graph.dist B.parent u % 2 = 1 := by omega
    have hv0 : T.graph.dist B.parent v % 2 = 0 := by
      by_contra hv0
      have hv1 : T.graph.dist B.parent v % 2 = 1 := by omega
      exact hval (hu1.trans hv1.symm)
    simp [hu0, hv0]

/-- Signed carrier mass for the tree bipartition based at the boundary. -/
noncomputable def signedCarrierMass
    (B : OrientedBranch T) (C : Configuration V) : ℤ :=
  ∑ v ∈ B.carrier, B.boundaryParityWeight v * (C v : ℤ)

theorem signedCarrierMass_move (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) =
      B.signedCarrierMass C - 3 * B.boundaryParityWeight u := by
  classical
  rw [signedCarrierMass]
  calc
    (∑ w ∈ B.carrier,
        B.boundaryParityWeight w * (move C u v w : ℤ)) =
        ∑ w ∈ B.carrier,
          B.boundaryParityWeight w *
            ((C w : ℤ) + (if w = v then 1 else 0) -
              2 * (if w = u then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [move_balance_int C huv.ne hu w]
    _ =
        (∑ w ∈ B.carrier, B.boundaryParityWeight w * (C w : ℤ)) +
          B.boundaryParityWeight v - 2 * B.boundaryParityWeight u := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        mul_add, mul_sub, huB, hvB] <;> ring
    _ = B.signedCarrierMass C - 3 * B.boundaryParityWeight u := by
      rw [B.boundaryParityWeight_adj_neg huv, signedCarrierMass]
      ring

theorem signedCarrierMass_move_mod_three (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) ≡ B.signedCarrierMass C [ZMOD 3] := by
  rw [B.signedCarrierMass_move C huv hu huB hvB, Int.modEq_iff_dvd]
  refine ⟨B.boundaryParityWeight u, ?_⟩
  ring

theorem BranchReach.signedCarrierMass_modEq
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    B.signedCarrierMass D ≡ B.signedCarrierMass C [ZMOD 3] := by
  induction hreach with
  | refl => exact Int.ModEq.refl _
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      exact (B.signedCarrierMass_move_mod_three _ huv hlegal huB hvB).trans ih

theorem signedCarrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.signedCarrierMass (B.withBoundary C q) = q := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hsum :
      ∑ v ∈ B.vertices,
        B.boundaryParityWeight v * (B.withBoundary C q v : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [B.withBoundary_of_mem_vertices C q hv, hz v hv]
    simp
  have hdecomp :=
    Finset.sum_erase_add B.carrier
      (fun v => B.boundaryParityWeight v * (B.withBoundary C q v : ℤ)) hp
  simp only [herase, hsum, B.withBoundary_parent,
    B.boundaryParityWeight_parent, zero_add, one_mul] at hdecomp
  rw [signedCarrierMass]
  norm_num at hdecomp ⊢
  linarith

theorem signedCarrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.signedCarrierMass D = D B.parent := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hsum :
      ∑ v ∈ B.vertices, B.boundaryParityWeight v * (D v : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hClear v hv]
    simp
  have hdecomp :=
    Finset.sum_erase_add B.carrier
      (fun v => B.boundaryParityWeight v * (D v : ℤ)) hp
  simp only [herase, hsum, B.boundaryParityWeight_parent,
    zero_add, one_mul] at hdecomp
  rw [signedCarrierMass]
  norm_num at hdecomp ⊢
  linarith

/-- An initially and finally empty legal branch excursion preserves the
boundary pile modulo three. -/
theorem BranchReach.empty_boundary_mod_three
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    (D B.parent : ℤ) ≡ (q : ℤ) [ZMOD 3] := by
  have hmod := BranchReach.signedCarrierMass_modEq B hreach
  rw [B.signedCarrierMass_eq_parent_of_cleared D hClear,
    B.signedCarrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hmod
  exact hmod

/-- Every legal empty-branch excursion has exact boundary flux -3k for some
nonnegative integer k.  The branch remains EMPTY at the message level; zero is
used here only as the omitted formal gain in this excursion calculation. -/
theorem ClearOutcome.exists_emptyExcursion_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.EmptyExcursion m B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B ∧
      ∃ k : ℤ, 0 ≤ k ∧ MoveSignature.boundaryFlux m B = -3 * k := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hExc : MoveSignature.EmptyExcursion m B := by
    refine ⟨hmSupp, ?_⟩
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv, hz v hv] at h
    omega
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  have hFlux :
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
    calc
      (D B.parent : ℤ) =
          (q : ℤ) + (m.count B.root B.parent : ℤ) -
            2 * (m.count B.parent B.root : ℤ) := hParent
      _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
        rw [MoveSignature.boundaryFlux]
        ring
  have hNonpos : MoveSignature.boundaryFlux m B ≤ 0 := by
    have hle :=
      BranchReach.empty_boundary_nonincrease B C q hEmpty hClear.1 hClear.2
    omega
  have hBoundaryMod :=
    BranchReach.empty_boundary_mod_three B C q hEmpty hClear.1 hClear.2
  have hFluxMod :
      MoveSignature.boundaryFlux m B ≡ 0 [ZMOD 3] := by
    rw [Int.modEq_iff_dvd] at hBoundaryMod ⊢
    have heq :
        (q : ℤ) - (D B.parent : ℤ) =
          -MoveSignature.boundaryFlux m B := by
      omega
    rw [heq] at hBoundaryMod
    simpa using hBoundaryMod
  have hDvd : (3 : ℤ) ∣ MoveSignature.boundaryFlux m B :=
    Int.modEq_zero_iff_dvd.mp hFluxMod
  rcases hDvd with ⟨a, ha⟩
  have haNonpos : a ≤ 0 := by
    rw [ha] at hNonpos
    omega
  refine ⟨m, hExc, hFlux, -a, by omega, ?_⟩
  rw [ha]
  ring


/-- Net signature flux contributed by all genuine child edges at the branch
root. This is the signature analogue of the recursive child-message sum. -/
noncomputable def signatureChildFluxSum
    (m : MoveSignature T) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
    else
      0

theorem MoveSignature.incoming_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.incoming B.root : ℤ) =
      (m.count B.parent B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count v B.root : ℤ)
          else
            0 := by
  classical
  rw [MoveSignature.incoming]
  push_cast
  calc
    (∑ v : V, (m.count v B.root : ℤ)) =
        ∑ v : V,
          ((if v = B.parent then (m.count B.parent B.root : ℤ) else 0) +
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hvp : v = B.parent
      · subst v
        simp
      · by_cases hadj : T.graph.Adj B.root v
        · simp [hvp, hadj]
        · have hz : m.count v B.root = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hpos
            exact hadj (m.supported hpos).symm
          simp [hvp, hadj, hz]
    _ =
        (m.count B.parent B.root : ℤ) +
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else
              0 := by
      rw [Finset.sum_add_distrib]
      simp

theorem MoveSignature.outgoing_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.outgoing B.root : ℤ) =
      (m.count B.root B.parent : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count B.root v : ℤ)
          else
            0 := by
  classical
  rw [MoveSignature.outgoing]
  push_cast
  calc
    (∑ v : V, (m.count B.root v : ℤ)) =
        ∑ v : V,
          ((if v = B.parent then (m.count B.root B.parent : ℤ) else 0) +
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hvp : v = B.parent
      · subst v
        simp
      · by_cases hadj : T.graph.Adj B.root v
        · simp [hvp, hadj]
        · have hz : m.count B.root v = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hpos
            exact hadj (m.supported hpos)
          simp [hvp, hadj, hz]
    _ =
        (m.count B.root B.parent : ℤ) +
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else
              0 := by
      rw [Finset.sum_add_distrib]
      simp

theorem signatureChildFluxSum_eq
    (m : MoveSignature T) (B : OrientedBranch T) :
    signatureChildFluxSum m B =
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ)
        else
          0) -
      2 * (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count B.root v : ℤ)
        else
          0) := by
  classical
  rw [signatureChildFluxSum]
  calc
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
      else 0) =
        ∑ v : V,
          ((if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else 0) -
            2 * (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent <;> simp [h]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The clearing balance at the branch root, separated into the external
boundary edge and the total flux of genuine child branches. -/
theorem MoveSignature.root_balance_with_child_flux
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hbal : m.BalancesAt C B.root) :
    (C B.root : ℤ) + signatureChildFluxSum m B +
        (m.count B.parent B.root : ℤ) -
      2 * (m.count B.root B.parent : ℤ) = 0 := by
  rw [MoveSignature.BalancesAt,
    MoveSignature.incoming_root_eq_parent_add_children m B,
    MoveSignature.outgoing_root_eq_parent_add_children m B] at hbal
  rw [signatureChildFluxSum_eq]
  ring_nf at hbal ⊢
  exact hbal

/-- If a is no larger than b and the two integers have the same residue
modulo three, then a is exactly b minus three times a natural number. -/
theorem exists_nat_three_loss {a b : ℤ}
    (hle : a ≤ b) (hmod : a % 3 = b % 3) :
    ∃ k : ℕ, a = b - 3 * (k : ℤ) := by
  have hme : a ≡ b [ZMOD 3] := by
    change a % 3 = b % 3
    exact hmod
  have hdvd : (3 : ℤ) ∣ b - a :=
    Int.modEq_iff_dvd.mp hme
  rcases hdvd with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by
    omega
  refine ⟨k.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hk0]
  omega

/-- The transfer keeps the same residue modulo three when its input is
lowered by three. -/
theorem F_sub_three_mod_three (z : ℤ) :
    F (z - 3) % 3 = F z % 3 := by
  unfold F
  split_ifs <;> omega

/-- Iterated form of the three-step transfer inequality. -/
theorem F_sub_three_mul_le (z : ℤ) :
    ∀ k : ℕ, F (z - 3 * (k : ℤ)) ≤ F z
  | 0 => by simp
  | k + 1 => by
      calc
        F (z - 3 * ((k + 1 : ℕ) : ℤ)) =
            F ((z - 3 * (k : ℤ)) - 3) := by
              congr 1
              push_cast
              ring
        _ ≤ F (z - 3 * (k : ℤ)) :=
          F_sub_three_le _
        _ ≤ F z :=
          F_sub_three_mul_le z k

/-- Iterated residue form accompanying the three-step transfer inequality. -/
theorem F_sub_three_mul_mod_three (z : ℤ) :
    ∀ k : ℕ, F (z - 3 * (k : ℤ)) % 3 = F z % 3
  | 0 => by simp
  | k + 1 => by
      have harg :
          z - 3 * ((k + 1 : ℕ) : ℤ) =
            (z - 3 * (k : ℤ)) - 3 := by
        push_cast
        ring
      rw [harg, F_sub_three_mod_three]
      exact F_sub_three_mul_mod_three z k


/-- Recursive signature bound.  Every genuine child contributes its recursive
message minus a nonnegative multiple of three; an empty child contributes only
such a three-step loss.  At an occupied branch the resulting boundary flux is
bounded by the recursive transfer and has the same residue modulo three. -/
theorem signature_branchFlux_bounds
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hClears : MoveSignature.Clears m C B)
    (hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A) :
    (B.Occupied C →
      MoveSignature.boundaryFlux m B ≤ F (effectiveInput C B) ∧
      MoveSignature.boundaryFlux m B % 3 =
        F (effectiveInput C B) % 3) ∧
    (¬ B.Occupied C →
      ∃ k : ℕ,
        MoveSignature.boundaryFlux m B = -3 * (k : ℤ)) := by
  classical
  have hChildLoss :
      ∀ v : V,
        ∃ k : ℕ,
          (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ) -
                2 * (m.count B.root v : ℤ)
            else
              0) =
            (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) -
              3 * (k : ℤ) := by
    intro v
    by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
    · let c : B.Child :=
        { vertex := v
          adj := h.1
          ne_parent := h.2 }
      have hChildClears :
          MoveSignature.Clears m C (B.childBranch c) := by
        intro w hw
        exact hClears w (B.childBranch_vertices_subset c hw)
      have hChildCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ (B.childBranch c).vertices →
            A.Occupied C →
            MoveSignature.CausalOutward m A := by
        intro A hA hOcc
        apply hCausal A
        intro w hw
        exact B.childBranch_vertices_subset c (hA hw)
        exact hOcc
      have hRec :=
        signature_branchFlux_bounds m C (B.childBranch c)
          hChildClears hChildCausal
      by_cases hOcc : (B.childBranch c).Occupied C
      · have hBound := hRec.1 hOcc
        rcases exists_nat_three_loss hBound.1 hBound.2 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_some_of_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
      · rcases hRec.2 hOcc with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
    · refine ⟨0, ?_⟩
      simp [h]
  choose k hk using hChildLoss
  let K : ℕ := ∑ v : V, k v
  have hK :
      (K : ℤ) = ∑ v : V, (k v : ℤ) := by
    simp [K]
  have hChildSum :
      signatureChildFluxSum m B =
        childMessageSum C B - 3 * (K : ℤ) := by
    rw [signatureChildFluxSum, childMessageSum]
    calc
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
        else
          0) =
          ∑ v : V,
            ((if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) - 3 * (k v : ℤ)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hk v
      _ =
          (∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              messageContribution
                (branchMessage C
                  (B.childBranch
                    { vertex := v
                      adj := h.1
                      ne_parent := h.2 }))
            else
              0) -
            3 * (∑ v : V, (k v : ℤ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = childMessageSum C B - 3 * (K : ℤ) := by
        rw [childMessageSum, hK]
        rfl
  have hRoot :=
    MoveSignature.root_balance_with_child_flux m C B
      (hClears B.root B.root_mem_vertices)
  have hBal :
      (effectiveInput C B - 3 * (K : ℤ)) +
          (m.count B.parent B.root : ℤ) -
        2 * (m.count B.root B.parent : ℤ) = 0 := by
    rw [hChildSum] at hRoot
    rw [effectiveInput]
    omega
  constructor
  · intro hOcc
    have hOut :=
      hCausal B (by intro w hw; exact hw) hOcc
    have hA : 1 ≤ (m.count B.root B.parent : ℤ) := by
      exact_mod_cast hOut
    have hIn : 0 ≤ (m.count B.parent B.root : ℤ) := by
      positivity
    have hLocalLe :=
      one_vertex_flux_le
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    have hLocalMod :=
      one_vertex_flux_mod_three
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    constructor
    · rw [MoveSignature.boundaryFlux]
      exact hLocalLe.trans
        (F_sub_three_mul_le (effectiveInput C B) K)
    · rw [MoveSignature.boundaryFlux]
      calc
        ((m.count B.root B.parent : ℤ) -
              2 * (m.count B.parent B.root : ℤ)) % 3 =
            F (effectiveInput C B - 3 * (K : ℤ)) % 3 :=
          hLocalMod
        _ = F (effectiveInput C B) % 3 :=
          F_sub_three_mul_mod_three (effectiveInput C B) K
  · intro hEmpty
    have hZero :=
      (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
    have hRootZero : C B.root = 0 :=
      hZero B.root B.root_mem_vertices
    have hChildMessageZero : childMessageSum C B = 0 := by
      rw [childMessageSum]
      apply Finset.sum_eq_zero
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hChildEmpty : ¬ (B.childBranch c).Occupied C := by
          rintro ⟨w, hw, hwpos⟩
          exact hEmpty
            ⟨w, B.childBranch_vertices_subset c hw, hwpos⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c)
            hChildEmpty
        simp [h, c, hmsg]
      · simp [h]
    rw [hChildSum] at hRoot
    simp [hRootZero, hChildMessageZero] at hRoot
    refine ⟨m.count B.root B.parent + 2 * K, ?_⟩
    rw [MoveSignature.boundaryFlux]
    push_cast
    omega
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c


/-- Necessity half of the exact boundary invariant.  Any legal clearing of an
occupied branch leaves no more than its recursive message gain at the external
boundary. -/
theorem ClearOutcome.boundary_le_message
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hClear : B.ClearOutcome C q D) :
    (D B.parent : ℤ) ≤ (q : ℤ) + d := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A := by
    intro A hAB hAOcc
    apply Nat.pos_of_ne_zero
    intro hzero
    have hAOcc' : A.Occupied (B.withBoundary C q) := by
      rcases hAOcc with ⟨v, hvA, hvpos⟩
      have hvB : v ∈ B.vertices := hAB hvA
      refine ⟨v, hvA, ?_⟩
      simpa [B.withBoundary_of_mem_vertices C q hvB] using hvpos
    have hFinalOcc := hmPersist A hAB hAOcc' hzero
    rcases hFinalOcc with ⟨v, hvA, hvpos⟩
    have hvB : v ∈ B.vertices := hAB hvA
    rw [hClear.2 v hvB] at hvpos
    omega
  have hBound :=
    (signature_branchFlux_bounds m C B hClears hCausal).1 hOcc
  have hMsgCanonical :=
    branchMessage_eq_some_of_occupied C B hOcc
  have hd : d = F (effectiveInput C B) := by
    rw [hMsgCanonical] at hMsg
    exact (Option.some.inj hMsg).symm
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  have hFlux :
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
    calc
      (D B.parent : ℤ) =
          (q : ℤ) + (m.count B.root B.parent : ℤ) -
            2 * (m.count B.parent B.root : ℤ) := hParent
      _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
        rw [MoveSignature.boundaryFlux]
        ring
  rw [hFlux, hd]
  linarith [hBound.1]

/-- If the boundary plus recursive message is nonpositive, no legal clearing
can leave a positive boundary pile. -/
theorem ClearOutcome.no_positive_boundary_of_message_nonpos
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hNonpos : (q : ℤ) + d ≤ 0) :
    ¬ ∃ D : Configuration V,
      B.ClearOutcome C q D ∧ 0 < D B.parent := by
  rintro ⟨D, hClear, hPos⟩
  have hle :=
    ClearOutcome.boundary_le_message B C q hOcc hMsg hClear
  have hPosInt : 0 < (D B.parent : ℤ) := by
    exact_mod_cast hPos
  omega

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
