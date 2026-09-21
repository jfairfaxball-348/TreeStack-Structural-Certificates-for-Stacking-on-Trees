import Mathlib
import TreeStack.Basic

namespace TreeStack

/-- The pointwise configuration obtained by moving two pebbles from `u`
to one pebble at `v`. Legality is recorded separately by `PebbleStep`. -/
def move {V : Type*} [DecidableEq V] (C : Configuration V) (u v : V) :
    Configuration V :=
  Function.update (Function.update C u (C u - 2)) v (C v + 1)

/-- One legal pebbling move along an edge. The source contains at least two
pebbles, so the natural subtraction in `move` has its intended meaning. -/
def PebbleStep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ C u ∧ D = move C u v

/-- Reachability by finitely many legal pebbling moves. -/
def Reach {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen (PebbleStep G) C D

/-- A positive configuration supported exactly at the specified root. -/
def StackedAt {V : Type*} (C : Configuration V) (r : V) : Prop :=
  0 < C r ∧ ∀ v, v ≠ r → C v = 0

/-- Reachability of a stack at a specified root. -/
def StackableAt {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) (r : V) : Prop :=
  ∃ D, Reach G C D ∧ StackedAt D r

/-- Reachability of a stack at some vertex. -/
def Stackable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) : Prop :=
  ∃ r, StackableAt G C r

/-- The source convention: every configuration of exactly `t` pebbles is
stackable. No "at least t" replacement is made. -/
def UniversalStackable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ C : Configuration V, mass C = t → Stackable G C

/-- A legal move lowers total mass by exactly one. -/
theorem mass_move_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u) :
    mass (move C u v) + 1 = mass C := by
  classical
  simp only [mass, move]
  rw [Finset.sum_update_of_mem (Finset.mem_univ v),
    Finset.sdiff_singleton_eq_erase]
  have huv_mem : u ∈ Finset.univ.erase v := by simp [huv]
  rw [Finset.sum_update_of_mem (s := Finset.univ.erase v) (i := u)
      (f := C) (b := C u - 2) huv_mem,
    Finset.sdiff_singleton_eq_erase]
  have hv := Finset.sum_erase_add Finset.univ C (Finset.mem_univ v)
  have hu' := Finset.sum_erase_add (Finset.univ.erase v) C huv_mem
  omega

/-- A stack is already stackable without making a move. -/
theorem stackableAt_of_stackedAt {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : Configuration V) (r : V) (h : StackedAt C r) :
    StackableAt G C r :=
  ⟨C, Relation.ReflTransGen.refl, h⟩

/-- Stackability is preserved when one legal move is prefixed. -/
theorem stackable_of_step {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {C D : Configuration V}
    (hCD : PebbleStep G C D) (hD : Stackable G D) : Stackable G C := by
  rcases hD with ⟨r, E, hDE, hE⟩
  exact ⟨r, E, Relation.ReflTransGen.head hCD hDE, hE⟩

/-- The configuration placing one pebble on every vertex of `s` and none
elsewhere. -/
def oneOn {V : Type*} [DecidableEq V] (s : Finset V) : Configuration V :=
  fun v => if v ∈ s then 1 else 0

@[simp] theorem oneOn_apply {V : Type*} [DecidableEq V] (s : Finset V) (v : V) :
    oneOn s v = if v ∈ s then 1 else 0 := rfl

@[simp] theorem mass_oneOn {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) :
    mass (oneOn s) = s.card := by
  classical
  simp [mass, oneOn]

theorem no_step_oneOn {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Finset V) {D : Configuration V} : ¬ PebbleStep G (oneOn s) D := by
  rintro ⟨u, v, -, hu, -⟩
  by_cases hus : u ∈ s <;> simp [oneOn, hus] at hu

theorem not_stackable_oneOn_of_two_le_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {s : Finset V} (hs : 2 ≤ s.card) :
    ¬ Stackable G (oneOn s) := by
  rintro ⟨r, D, hreach, hstack⟩
  rcases hreach.cases_head with hEq | ⟨E, hstep, -⟩
  · subst D
    have hr : r ∈ s := by
      by_contra hnr
      have hz : oneOn s r = 0 := by simp [oneOn, hnr]
      have hpos := hstack.1
      rw [hz] at hpos
      omega
    have hsub : s ⊆ {r} := by
      intro v hv
      simp only [Finset.mem_singleton]
      by_contra hvr
      have hz := hstack.2 v hvr
      simp [oneOn, hv] at hz
    have hcard : s.card ≤ 1 := by
      simpa using (Finset.card_le_card hsub)
    have : 2 ≤ 1 := le_trans hs hcard
    omega
  · exact no_step_oneOn s hstep

/-- Audit repair for the exact-size convention: if every configuration of
exactly `t` pebbles is stackable and `t ≥ 2`, then `t` strictly exceeds
the number of vertices. -/
theorem universal_stackable_gt_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    Fintype.card V < t := by
  by_contra h
  have hle : t ≤ Fintype.card V := Nat.le_of_not_gt h
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (by simpa using hle)
  have hm : mass (oneOn s) = t := by simpa [hs]
  exact not_stackable_oneOn_of_two_le_card (G := G) (s := s) (by omega)
    (hU (oneOn s) hm)

/-- If the total mass exceeds the vertex count, some vertex carries at least
two pebbles. -/
theorem exists_two_le_of_card_lt_mass {V : Type*} [Fintype V]
    (C : Configuration V) (h : Fintype.card V < mass C) :
    ∃ v, 2 ≤ C v := by
  by_contra hn
  push Not at hn
  have hmass : mass C ≤ Fintype.card V := by
    rw [mass]
    calc
      (∑ v, C v) ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
        have hv := hn v
        omega
      _ = Fintype.card V := by simp
  omega

/-- Audit repair for exact-size universality. On a connected nontrivial finite
graph, universality at an exact size `t ≥ 2` propagates to exact size
`t + 1`. -/
theorem universal_stackable_succ {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} {t : ℕ}
    (hconn : G.Connected) (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    UniversalStackable G (t + 1) := by
  intro C hCmass
  by_cases hstack : Stackable G C
  · exact hstack
  have hcard : Fintype.card V < t := universal_stackable_gt_card hU ht
  have hmassgt : Fintype.card V < mass C := by omega
  obtain ⟨u, hu⟩ := exists_two_le_of_card_lt_mass C hmassgt
  obtain ⟨v, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial u
  let D := move C u v
  have hstep : PebbleStep G C D := ⟨u, v, huv, hu, rfl⟩
  have hdrop := mass_move_add_one C huv.ne hu
  have hDmass : mass D = t := by
    dsimp [D] at hdrop ⊢
    omega
  exact stackable_of_step hstep (hU D hDmass)

end TreeStack
