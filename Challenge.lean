import Mathlib

/-!
# TreeStack: advertised Palomar statement

This is the deliberately small Palomar-facing statement surface for the
corrected nontrivial-tree form of the Csernák--Soukup stacking conjecture.

The public definitions below are copied from the proof development rather than
imported from `TreeStack`, so the Challenge has a Mathlib-only transitive import
closure. In particular, `UniversalStackable G t` quantifies over configurations
of exactly mass `t`, and `stack` minimizes only thresholds satisfying `2 ≤ t`.

The proof development's recursive branch-message state uses `Option.none` for
EMPTY and distinguishes it from `some 0`. That implementation state is not in
the definitional surface of the advertised theorem, so it is intentionally not
redefined here; no integer surrogate for EMPTY is introduced.

The final theorem contains the Challenge's one deliberate `sorry`. The proved
declaration is imported by `Solution.lean` from the completed TreeStack
development and is compared mechanically by Comparator.
-/

namespace TreeStack

open scoped BigOperators Classical

/-- A pebble configuration on a vertex type. -/
abbrev Configuration (V : Type*) := V → ℕ

/-- Total number of pebbles in a finite configuration. -/
def mass {V : Type*} [Fintype V] (C : Configuration V) : ℕ :=
  ∑ v, C v

/-- A finite simple tree, using Mathlib's connected-acyclic tree predicate. -/
structure FiniteTree (V : Type*) [Fintype V] where
  graph : SimpleGraph V
  isTree : graph.IsTree

/-- The pointwise configuration obtained by moving two pebbles from `u`
to one pebble at `v`. Legality is recorded separately by `PebbleStep`. -/
def move {V : Type*} [DecidableEq V] (C : Configuration V) (u v : V) :
    Configuration V :=
  Function.update (Function.update C u (C u - 2)) v (C v + 1)

/-- One legal pebbling move along an edge. -/
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

/-- Every configuration of exactly `t` pebbles is stackable. -/
def UniversalStackable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ C : Configuration V, mass C = t → Stackable G C

/-- Degree-one vertices other than the chosen root. -/
noncomputable def leafVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ T.graph.degree v = 1

/-- Vertices contributing to the source quantity sigma. -/
noncomputable def sigmaVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v = r ∨ 1 < T.graph.degree v

/-- The source leaf count. -/
noncomputable def leafCount {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  (leafVertices T r).card

/-- The source quantity sigma_T(r), including its leading one. -/
noncomputable def sigma {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  1 + ∑ v ∈ sigmaVertices T r,
    T.graph.degree v * 2 ^ T.graph.dist r v

/-- The source rooted estimator sigma_T(r) + leaf_T(r). -/
noncomputable def rootEstimate {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  sigma T r + leafCount T r

/-- The source tree estimator, the maximum rooted estimator. -/
noncomputable def estim {V : Type*} [Fintype V]
    (T : FiniteTree V) : ℕ :=
  (Finset.univ : Finset V).sup (rootEstimate T)

/-- Exact-size admissibility for the source stacking number. -/
def StackingCandidate {V : Type*} [Fintype V]
    (T : FiniteTree V) (t : ℕ) : Prop :=
  2 ≤ t ∧ UniversalStackable T.graph t

/-- The Csernák--Soukup stacking number: the least exact size at least two
for which every configuration is stackable. -/
noncomputable def stack {V : Type*} [Fintype V]
    (T : FiniteTree V) : ℕ :=
  sInf {t : ℕ | StackingCandidate T t}

/--
For every finite tree on at least two vertices, the stacking number equals the
explicit Csernák--Soukup tree estimator.

The one-vertex case is deliberately excluded: with the source convention
`2 ≤ t` built into `StackingCandidate`, the displayed estimator is 1 there.
-/
theorem stack_eq_estim_of_two_le_card
    {V : Type*} [Fintype V]
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T := by
  sorry

end TreeStack
