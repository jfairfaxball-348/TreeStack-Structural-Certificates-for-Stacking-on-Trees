import TreeStack.Basic
import Mathlib.Logic.Relation

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

end TreeStack
