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

section TaskScheduling

variable {α : Type*}

/-- Sum of the integer gains of a finite list of executable tasks. -/
def taskGainSum (gain : α → ℤ) : List α → ℤ
  | [] => 0
  | t :: ts => gain t + taskGainSum gain ts

/-- The recursive task sum is the ordinary sum of the mapped list. -/
theorem taskGainSum_eq_list_sum (gain : α → ℤ) :
    ∀ tasks : List α,
      taskGainSum gain tasks = (tasks.map gain).sum
  | [] => by simp [taskGainSum]
  | t :: ts => by
      simp [taskGainSum, taskGainSum_eq_list_sum gain ts]

/-- The list sum agrees with the corresponding finite-set sum. -/
theorem taskGainSum_toList [DecidableEq α]
    (gain : α → ℤ) (s : Finset α) :
    taskGainSum gain s.toList = Finset.sum s gain := by
  rw [taskGainSum_eq_list_sum]
  exact Finset.sum_map_toList s gain

/-- A task order is safe from an initial pile `a` if every successive task
leaves a strictly positive pile.  This is exactly the precondition needed to
apply the occupied-child boundary invariant task by task. -/
def TaskScheduleSafe (gain : α → ℤ) : ℤ → List α → Prop
  | _, [] => True
  | a, t :: ts =>
      0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts

def positiveTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => 0 < gain t

def zeroTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t = 0

def negativeTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t < 0

/-- Audited scheduling order: positive gains first, then zero gains, then
negative gains.  Empty branches are not represented by tasks at all. -/
def orderedTasks (gain : α → ℤ) (tasks : List α) : List α :=
  positiveTasks gain tasks ++
    (zeroTasks gain tasks ++ negativeTasks gain tasks)

theorem taskGainSum_append (gain : α → ℤ) (xs ys : List α) :
    taskGainSum gain (xs ++ ys) =
      taskGainSum gain xs + taskGainSum gain ys := by
  induction xs with
  | nil => simp [taskGainSum]
  | cons x xs ih =>
      simp [taskGainSum, ih]
      ring

theorem taskScheduleSafe_append (gain : α → ℤ) (a : ℤ)
    (xs ys : List α) :
    TaskScheduleSafe gain a (xs ++ ys) ↔
      TaskScheduleSafe gain a xs ∧
        TaskScheduleSafe gain (a + taskGainSum gain xs) ys := by
  induction xs generalizing a with
  | nil => simp [TaskScheduleSafe, taskGainSum]
  | cons x xs ih =>
      simp [TaskScheduleSafe, taskGainSum, ih, add_assoc, and_assoc]

theorem taskGainSum_nonpos (gain : α → ℤ) :
    ∀ tasks : List α,
      (∀ t ∈ tasks, gain t ≤ 0) →
      taskGainSum gain tasks ≤ 0
  | [], _ => by simp [taskGainSum]
  | t :: ts, h => by
      have ht : gain t ≤ 0 := h t (by simp)
      have hts : ∀ u ∈ ts, gain u ≤ 0 := by
        intro u hu
        exact h u (by simp [hu])
      have ih := taskGainSum_nonpos gain ts hts
      simp only [taskGainSum]
      linarith

theorem taskScheduleSafe_of_all_pos (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 ≤ a →
      (∀ t ∈ tasks, 0 < gain t) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, ha, hpos => by
      have ht : 0 < gain t := hpos t (by simp)
      have hts : ∀ u ∈ ts, 0 < gain u := by
        intro u hu
        exact hpos u (by simp [hu])
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      constructor
      · linarith
      · exact taskScheduleSafe_of_all_pos gain (by linarith) hts

theorem taskScheduleSafe_of_all_zero (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a →
      (∀ t ∈ tasks, gain t = 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, ha, hzero => by
      have ht : gain t = 0 := hzero t (by simp)
      have hts : ∀ u ∈ ts, gain u = 0 := by
        intro u hu
        exact hzero u (by simp [hu])
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      constructor
      · simpa [ht] using ha
      · simpa [ht] using
          (taskScheduleSafe_of_all_zero gain ha hts)

theorem taskScheduleSafe_of_all_nonpos_of_final_pos
    (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a + taskGainSum gain tasks →
      (∀ t ∈ tasks, gain t ≤ 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, hfinal, hnonpos => by
      have ht : gain t ≤ 0 := hnonpos t (by simp)
      have hts : ∀ u ∈ ts, gain u ≤ 0 := by
        intro u hu
        exact hnonpos u (by simp [hu])
      have htail := taskGainSum_nonpos gain ts hts
      have hfirst : 0 < a + gain t := by
        simp only [taskGainSum] at hfinal
        linarith
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      refine ⟨hfirst, ?_⟩
      apply taskScheduleSafe_of_all_nonpos_of_final_pos gain
      · simp only [taskGainSum] at hfinal
        linarith
      · exact hts

/-- Positive, zero, and negative filtering preserves the total task gain. -/
theorem taskGainSum_partition (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (positiveTasks gain tasks) +
        taskGainSum gain (zeroTasks gain tasks) +
        taskGainSum gain (negativeTasks gain tasks) =
      taskGainSum gain tasks := by
  induction tasks with
  | nil =>
      simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks]
  | cons t ts ih =>
      by_cases hp : 0 < gain t
      · have hz : gain t ≠ 0 := by linarith
        have hn : ¬ gain t < 0 := by linarith
        have ih' := ih
        simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
        simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
          hp, hz, hn]
        linarith
      · by_cases hz : gain t = 0
        · have hn : ¬ gain t < 0 := by linarith
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          exact ih'
        · have hn : gain t < 0 := by omega
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          linarith

theorem taskGainSum_orderedTasks (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (orderedTasks gain tasks) =
      taskGainSum gain tasks := by
  rw [orderedTasks, taskGainSum_append, taskGainSum_append]
  linarith [taskGainSum_partition gain tasks]

theorem mem_orderedTasks_iff (gain : α → ℤ) (tasks : List α) (t : α) :
    t ∈ orderedTasks gain tasks ↔ t ∈ tasks := by
  simp [orderedTasks, positiveTasks, zeroTasks, negativeTasks]
  omega

theorem orderedTasks_nodup (gain : α → ℤ) {tasks : List α}
    (h : tasks.Nodup) :
    (orderedTasks gain tasks).Nodup := by
  rw [orderedTasks]
  have hp := h.filter (fun t => 0 < gain t)
  have hz := h.filter (fun t => gain t = 0)
  have hn := h.filter (fun t => gain t < 0)
  rw [List.nodup_append]
  constructor
  · exact hp
  · constructor
    · rw [List.nodup_append]
      exact ⟨hz, hn, by
        intro t htZero htNeg
        simp [zeroTasks] at htZero
        simp [negativeTasks] at htNeg
        omega⟩
    · intro t htPos htRest
      simp [positiveTasks] at htPos
      simp only [List.mem_append] at htRest
      rcases htRest with htZero | htNeg
      · simp [zeroTasks] at htZero
        omega
      · simp [negativeTasks] at htNeg
        omega

/-- Positive/zero/negative scheduling lemma from the audited construction.
If the starting pile is nonnegative and the final total is positive, placing
positive tasks first, zero tasks next, and negative tasks last makes every
individual task executable. -/
theorem orderedTasks_safe (gain : α → ℤ) (tasks : List α) (a : ℤ)
    (ha : 0 ≤ a)
    (hfinal : 0 < a + taskGainSum gain tasks) :
    TaskScheduleSafe gain a (orderedTasks gain tasks) := by
  let ps := positiveTasks gain tasks
  let zs := zeroTasks gain tasks
  let ns := negativeTasks gain tasks
  have hpos : ∀ t ∈ ps, 0 < gain t := by
    intro t ht
    have ht' : t ∈ tasks ∧ 0 < gain t := by
      simpa [ps, positiveTasks] using ht
    exact ht'.2
  have hnonpos : ∀ t ∈ zs ++ ns, gain t ≤ 0 := by
    intro t ht
    have ht' :
        (t ∈ tasks ∧ gain t = 0) ∨
          (t ∈ tasks ∧ gain t < 0) := by
      simpa [zs, ns, zeroTasks, negativeTasks] using ht
    rcases ht' with ht' | ht' <;> linarith [ht'.2]
  have hsafePos :
      TaskScheduleSafe gain a ps :=
    taskScheduleSafe_of_all_pos gain ha hpos
  have horderedFinal :
      0 < a + taskGainSum gain (orderedTasks gain tasks) := by
    rw [taskGainSum_orderedTasks]
    exact hfinal
  have hrestFinal :
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns) := by
    rw [orderedTasks, taskGainSum_append] at horderedFinal
    change
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns)
    simpa [ps, zs, ns, add_assoc] using horderedFinal
  have hsafeRest :
      TaskScheduleSafe gain
        (a + taskGainSum gain ps) (zs ++ ns) :=
    taskScheduleSafe_of_all_nonpos_of_final_pos gain
      hrestFinal hnonpos
  rw [orderedTasks, taskScheduleSafe_append]
  simpa [ps, zs, ns] using And.intro hsafePos hsafeRest

end TaskScheduling

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

theorem occupied_congr_vertices
    (B : OrientedBranch T) (C D : Configuration V)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    B.Occupied C ↔ B.Occupied D := by
  constructor
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [← hCD v hv]
    exact hpos
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [hCD v hv]
    exact hpos

/-- Recursive branch messages are insensitive to configuration values outside
the branch.  In particular, changing a child's external boundary pile does not
change that child's message. -/
theorem branchMessage_congr_vertices
    (C D : Configuration V) (B : OrientedBranch T)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    branchMessage C B = branchMessage D B := by
  have hOcc := B.occupied_congr_vertices C D hCD
  by_cases hC : B.Occupied C
  · have hD : B.Occupied D := hOcc.mp hC
    have hRoot : (C B.root : ℤ) = (D B.root : ℤ) := by
      exact_mod_cast hCD B.root B.root_mem_vertices
    have hChild :
        childMessageSum C B = childMessageSum D B := by
      rw [childMessageSum, childMessageSum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hSub :
            ∀ w ∈ (B.childBranch c).vertices, C w = D w := by
          intro w hw
          exact hCD w (B.childBranch_vertices_subset c hw)
        have hRec :=
          branchMessage_congr_vertices C D (B.childBranch c) hSub
        simp [h, c, hRec]
      · simp [h]
    rw [branchMessage_eq_some_of_occupied C B hC,
      branchMessage_eq_some_of_occupied D B hD]
    congr 2
    rw [effectiveInput, effectiveInput, hRoot, hChild]
  · have hD : ¬ B.Occupied D := by
      intro hD
      exact hC (hOcc.mpr hD)
    rw [branchMessage_eq_empty_of_not_occupied C B hC,
      branchMessage_eq_empty_of_not_occupied D B hD]
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c

/-- A genuine child carrier lies entirely inside the parent branch carrier. -/
theorem childBranch_carrier_subset
    (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).carrier ⊆ B.carrier := by
  classical
  intro v hv
  have hvCases :
      v = (B.childBranch c).parent ∨
        v ∈ (B.childBranch c).vertices := by
    simpa [carrier] using hv
  rcases hvCases with hp | hvChild
  · subst v
    simpa [childBranch] using B.root_mem_carrier
  · have hvB := B.childBranch_vertices_subset c hvChild
    rw [carrier]
    exact Finset.mem_insert.mpr (Or.inr hvB)

/-- The external parent of a branch is outside every genuine child carrier. -/
theorem parent_not_mem_childBranch_carrier
    (B : OrientedBranch T) (c : B.Child) :
    B.parent ∉ (B.childBranch c).carrier := by
  classical
  intro hp
  have hpCases :
      B.parent = B.root ∨
        B.parent ∈ (B.childBranch c).vertices := by
    simpa [carrier, childBranch] using hp
  rcases hpCases with hroot | hpChild
  · exact B.root_ne_parent hroot.symm
  · exact B.parent_not_mem_vertices
      (B.childBranch_vertices_subset c hpChild)

/-- Distinct genuine child branches of the same oriented branch have disjoint
vertex sets.  A common vertex would give a path in one child component that
crosses the other's unique boundary edge and hence reaches the deleted parent
edge endpoint, contradicting the bridge separation. -/
theorem childBranch_vertices_disjoint
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) :
    Disjoint (B.childBranch c).vertices (B.childBranch d).vertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hxc hxd
  have hdOutside : d.vertex ∉ (B.childBranch c).vertices := by
    intro hd
    have heq :=
      (B.childBranch c).eq_root_of_mem_vertices_adj_parent
        hd d.adj.symm
    exact hcd heq.symm
  have hdComp :
      d.vertex ∈ (B.childBranch d).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ (B.childBranch d).component.supp := by
    simpa [vertices] using hxd
  have hreach :
      (B.childBranch d).deletedGraph.Reachable d.vertex x :=
    (B.childBranch d).component.reachable_of_mem_supp hdComp hxComp
  have hreach' :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable d.vertex x := by
    simpa [deletedGraph, childBranch] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidD⟩
  have hxcSet :
      x ∈ ((B.childBranch c).vertices : Set V) := by
    simpa using hxc
  have hdOutsideSet :
      d.vertex ∉ ((B.childBranch c).vertices : Set V) := by
    simpa using hdOutside
  rcases p.reverse.exists_boundary_dart
      ((B.childBranch c).vertices : Set V)
      hxcSet hdOutsideSet with
    ⟨⟨⟨u, v⟩, huv⟩, hdart, huSet, hvSet⟩
  have huFin : u ∈ (B.childBranch c).vertices := by
    simpa using huSet
  have hvFin : v ∉ (B.childBranch c).vertices := by
    simpa using hvSet
  have hedge :=
    (B.childBranch c).edge_leaving_vertices_eq_boundary
      huFin hvFin huv
  have hvRoot : v = B.root := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · simpa [childBranch] using h.2
    · have huParent : u = (B.childBranch c).parent := h.1
      subst u
      exact ((B.childBranch c).parent_not_mem_vertices huFin).elim
  have hrootRev : B.root ∈ p.reverse.support := by
    rw [← hvRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hroot : B.root ∈ p.support := by
    simpa using hrootRev
  let q : T.graph.Walk d.vertex B.root :=
    p.takeUntil B.root hroot
  have hqAvoid : s(d.vertex, B.root) ∉ q.edges := by
    intro hq
    exact havoidD (p.edges_takeUntil_subset_edges hroot hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable
        d.vertex B.root :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(d.vertex, B.root) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) d.adj.symm
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot


/-- A vertex in one child branch is outside the full carrier of every
distinct sibling.  The only extra carrier vertex of a child is the common
parent root, which lies in no child vertex set. -/
theorem mem_childBranch_vertices_not_mem_sibling_carrier
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) {w : V}
    (hw : w ∈ (B.childBranch c).vertices) :
    w ∉ (B.childBranch d).carrier := by
  classical
  intro hwCarrier
  have hwCases :
      w = B.root ∨ w ∈ (B.childBranch d).vertices := by
    simpa [carrier, childBranch] using hwCarrier
  rcases hwCases with hroot | hwd
  · subst w
    exact (B.childBranch c).parent_not_mem_vertices hw
  · exact
      (Finset.disjoint_left.mp
        (B.childBranch_vertices_disjoint c d hcd)) hw hwd

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

/-- A branch-local legal sequence cannot alter a vertex outside its carrier. -/
theorem BranchReach.eq_of_not_mem_carrier
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) {w : V}
    (hw : w ∉ B.carrier) :
    D w = C w := by
  induction hreach with
  | refl => rfl
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, hu, hv, rfl⟩
      have hwu : w ≠ u := by
        intro h
        subst w
        exact hw hu
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw hv
      simp [move, hwu, hwv, ih]

/-- A legal sequence inside a genuine child carrier is also a legal sequence
inside the parent branch carrier. -/
theorem BranchReach.of_child
    (B : OrientedBranch T) (c : B.Child)
    {C D : Configuration V}
    (hreach : (B.childBranch c).BranchReach C D) :
    B.BranchReach C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, hu, hv, rfl⟩
      exact
        ⟨u, v, huv, hlegal,
          B.childBranch_carrier_subset c hu,
          B.childBranch_carrier_subset c hv, rfl⟩

/-- Repeating one legal oriented edge move a prescribed number of times
gives exact endpoint counts and leaves every other vertex unchanged. -/
theorem BranchReach.repeat_move
    (B : OrientedBranch T) {u v : V}
    (huv : T.graph.Adj u v)
    (huCarrier : u ∈ B.carrier) (hvCarrier : v ∈ B.carrier) :
    ∀ (C : Configuration V) (n : ℕ),
      2 * n ≤ C u →
      ∃ D : Configuration V,
        B.BranchReach C D ∧
        D u = C u - 2 * n ∧
        D v = C v + n ∧
        (∀ w : V, w ≠ u → w ≠ v → D w = C w) := by
  classical
  intro C n
  induction n generalizing C with
  | zero =>
      intro h
      refine ⟨C, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro w hwu hwv
        rfl
  | succ n ih =>
      intro hTotal
      have hLegal : 2 ≤ C u := by omega
      let E : Configuration V := move C u v
      have hStep : B.BranchPebbleStep C E :=
        ⟨u, v, huv, hLegal, huCarrier, hvCarrier, rfl⟩
      have hReachStep : B.BranchReach C E :=
        Relation.ReflTransGen.single hStep
      have hEu : E u = C u - 2 := by
        simp [E, move, huv.ne]
      have hEv : E v = C v + 1 := by
        simp [E, move, huv.ne]
      have hRemain : 2 * n ≤ E u := by
        rw [hEu]
        omega
      rcases ih E hRemain with ⟨D, hReachRest, hDu, hDv, hOther⟩
      have hReach : B.BranchReach C D :=
        Relation.ReflTransGen.trans hReachStep hReachRest
      refine ⟨D, hReach, ?_, ?_, ?_⟩
      · rw [hDu, hEu]
        omega
      · rw [hDv, hEv]
        omega
      · intro w hwu hwv
        rw [hOther w hwu hwv]
        simp [E, move, hwu, hwv]

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

@[simp] theorem withBoundary_self (B : OrientedBranch T)
    (C : Configuration V) :
    B.withBoundary C (C B.parent) = C := by
  funext v
  by_cases h : v = B.parent <;> simp [withBoundary, h]

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

/-- Predicate saying that a vertex indexes a genuine child branch. -/
def IsChildVertex (B : OrientedBranch T) (v : V) : Prop :=
  T.graph.Adj B.root v ∧ v ≠ B.parent

/-- The genuine child branch indexed by a vertex satisfying the child predicate. -/
def childOfVertex (B : OrientedBranch T) (v : V)
    (h : B.IsChildVertex v) : B.Child where
  vertex := v
  adj := h.1
  ne_parent := h.2

/-- Predicate for vertices indexing occupied genuine children. -/
def IsOccupiedChildVertex
    (B : OrientedBranch T) (C : Configuration V) (v : V) : Prop :=
  ∃ h : B.IsChildVertex v,
    (B.childBranch (B.childOfVertex v h)).Occupied C

/-- An executable child task is a genuine child branch that is occupied in
the original configuration. Empty child branches are absent from this type,
rather than represented by zero-gain tasks. -/
def OccupiedChild (B : OrientedBranch T) (C : Configuration V) :=
  {v : V // B.IsOccupiedChildVertex C v}

noncomputable instance OccupiedChild.instFintype
    (B : OrientedBranch T) (C : Configuration V) :
    Fintype (B.OccupiedChild C) :=
  Fintype.ofInjective
    (fun t : B.OccupiedChild C => (t.1 : V))
    Subtype.val_injective

/-- The genuine child carried by an occupied-child task. -/
noncomputable def OccupiedChild.child
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : B.Child :=
  B.childOfVertex t.1 (Classical.choose t.2)

/-- The child represented by an occupied-child task is occupied. -/
theorem OccupiedChild.occupied
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    (B.childBranch t.child).Occupied C := by
  exact Classical.choose_spec t.2

@[simp] theorem OccupiedChild.child_vertex
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.child.vertex = t.1 := rfl

/-- The summand appearing in childMessageSum at a vertex. -/
noncomputable def childMessageTerm
    (B : OrientedBranch T) (C : Configuration V) (v : V) : ℤ :=
  if h : B.IsChildVertex v then
    messageContribution
      (branchMessage C (B.childBranch (B.childOfVertex v h)))
  else
    0

theorem childMessageSum_eq_sum_term
    (B : OrientedBranch T) (C : Configuration V) :
    childMessageSum C B = ∑ v : V, B.childMessageTerm C v := by
  rw [childMessageSum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
  · simp [childMessageTerm, IsChildVertex, childOfVertex, h]
  · simp [childMessageTerm, IsChildVertex, h]

theorem childMessageTerm_eq_zero_of_not_occupiedChild
    (B : OrientedBranch T) (C : Configuration V) {v : V}
    (hv : ¬ B.IsOccupiedChildVertex C v) :
    B.childMessageTerm C v = 0 := by
  by_cases h : B.IsChildVertex v
  · have hnot :
        ¬ (B.childBranch (B.childOfVertex v h)).Occupied C := by
      intro hocc
      exact hv ⟨h, hocc⟩
    simp [childMessageTerm, h,
      branchMessage_eq_empty_of_not_occupied C
        (B.childBranch (B.childOfVertex v h)) hnot]
  · simp [childMessageTerm, h]

/-- Recursive integer gain attached to an occupied child task. -/
noncomputable def OccupiedChild.gain
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : ℤ :=
  messageContribution (branchMessage C (B.childBranch t.child))

theorem OccupiedChild.gain_eq_F
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = F (effectiveInput C (B.childBranch t.child)) := by
  rw [OccupiedChild.gain,
    branchMessage_eq_some_of_occupied C (B.childBranch t.child) t.occupied]
  rfl

theorem OccupiedChild.gain_eq_term
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = B.childMessageTerm C t.1 := by
  have h : B.IsChildVertex t.1 := Classical.choose t.2
  simp [OccupiedChild.gain, OccupiedChild.child,
    childMessageTerm, h]

/-- The unscheduled child-task list contains every occupied genuine child once
and contains no empty branch. -/
noncomputable def occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    List (B.OccupiedChild C) := by
  classical
  exact (Finset.univ : Finset (B.OccupiedChild C)).toList

theorem occupiedChildTasks_nodup
    (B : OrientedBranch T) (C : Configuration V) :
    (B.occupiedChildTasks C).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (B.OccupiedChild C))

@[simp] theorem mem_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V)
    (t : B.OccupiedChild C) :
    t ∈ B.occupiedChildTasks C := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

/-- The occupied executable tasks carry exactly the recursive child-message
sum. Empty genuine children contribute zero to childMessageSum but are absent
from the task list. -/
theorem taskGainSum_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
      childMessageSum C B := by
  classical
  calc
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
        ∑ t : B.OccupiedChild C, t.gain := by
          rw [occupiedChildTasks, taskGainSum_toList]
    _ = ∑ t : B.OccupiedChild C,
          B.childMessageTerm C t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ v ∈
          (Finset.univ.filter fun v : V =>
            B.IsOccupiedChildVertex C v),
          B.childMessageTerm C v := by
          symm
          simpa [OccupiedChild] using
            (Finset.sum_subtype
              (Finset.univ.filter fun v : V =>
                B.IsOccupiedChildVertex C v)
              (fun v => by simp)
              (fun v => B.childMessageTerm C v))
    _ = ∑ v : V, B.childMessageTerm C v := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro v hvUniv hvNot
          have hvNotOcc : ¬ B.IsOccupiedChildVertex C v := by
            intro hvOcc
            exact hvNot (Finset.mem_filter.mpr ⟨hvUniv, hvOcc⟩)
          exact B.childMessageTerm_eq_zero_of_not_occupiedChild C hvNotOcc
    _ = childMessageSum C B := (B.childMessageSum_eq_sum_term C).symm

/-- A final configuration obtained by a legal branch-local sequence which
clears the entire branch. -/
def ClearOutcome (B : OrientedBranch T) (C : Configuration V)
    (q : ℕ) (D : Configuration V) : Prop :=
  B.BranchReach (B.withBoundary C q) D ∧ B.Cleared D

/-- Execute a safe list of occupied child tasks by recursively attaining each
child's exact boundary gain.  The theorem records the parent-root gain,
preservation of the external boundary, clearing of every scheduled child, and
pointwise preservation of every sibling omitted from the list. -/
theorem executeOccupiedTaskSchedule
    (B : OrientedBranch T) (C : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q D ∧
            (D B.root : ℤ) = (q : ℤ) + d) :
    ∀ (tasks : List (B.OccupiedChild C)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v) →
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ) tasks →
      ∃ D : Configuration V,
        B.BranchReach E D ∧
        (D B.root : ℤ) =
          (E B.root : ℤ) +
            taskGainSum
              (fun t : B.OccupiedChild C => t.gain) tasks ∧
        D B.parent = E B.parent ∧
        (∀ t ∈ tasks, (B.childBranch t.child).Cleared D) ∧
        (∀ c : B.Child,
          (∀ t ∈ tasks, t.1 ≠ c.vertex) →
          ∀ v ∈ (B.childBranch c).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, rfl, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro c hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E B.root : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            ((E B.root : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ (B.childBranch t.child).vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ (B.childBranch t.child).vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE :
          (B.childBranch t.child).Occupied E :=
        ((B.childBranch t.child).occupied_congr_vertices C E hCE).mp
          t.occupied
      have hMsgC :
          branchMessage C (B.childBranch t.child) = some t.gain := by
        rw [branchMessage_eq_some_of_occupied C
          (B.childBranch t.child) t.occupied, t.gain_eq_F]
      have hMsgE :
          branchMessage E (B.childBranch t.child) = some t.gain := by
        calc
          branchMessage E (B.childBranch t.child) =
              branchMessage C (B.childBranch t.child) :=
            (branchMessage_congr_vertices C E
              (B.childBranch t.child) hCE).symm
          _ = some t.gain := hMsgC
      rcases hChildAttain t.child E t.gain (E B.root)
          hOccE hMsgE hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart :
          (B.childBranch t.child).withBoundary E (E B.root) = E := by
        have hSelf := (B.childBranch t.child).withBoundary_self E
        simpa [childBranch] using hSelf
      have hReachChild :
          (B.childBranch t.child).BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachParent : B.BranchReach E E₁ :=
        BranchReach.of_child B t.child hReachChild
      have hParent₁ : E₁ B.parent = E B.parent :=
        BranchReach.eq_of_not_mem_carrier
          (B.childBranch t.child) hReachChild
          (B.parent_not_mem_childBranch_carrier t.child)
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ (B.childBranch s.child).vertices,
            E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hChildNe : s.child.vertex ≠ t.child.vertex := by
          simpa using hst
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            s.child t.child hChildNe hv
        have hEqStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            (E₁ B.root : ℤ) ts := by
        rw [hRoot₁]
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hParentTail,
          hClearedTail, hUntouchedTail⟩
      have hReachAll : B.BranchReach E D :=
        Relation.ReflTransGen.trans hReachParent hReachTail
      have hRootAll :
          (D B.root : ℤ) =
            (E B.root : ℤ) +
              taskGainSum
                (fun s : B.OccupiedChild C => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁]
        simp only [taskGainSum]
        ring
      have hParentAll : D B.parent = E B.parent := by
        rw [hParentTail, hParent₁]
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.child.vertex := by
        intro s hs hEq
        have hEq' : s.1 = t.1 := by
          simpa using hEq
        have hObj : s = t := Subtype.ext hEq'
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ (B.childBranch t.child).vertices, D v = E₁ v :=
        hUntouchedTail t.child hHeadNotTail
      have hClearedHead :
          (B.childBranch t.child).Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, (B.childBranch s.child).Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ c : B.Child,
            (∀ s ∈ t :: ts, s.1 ≠ c.vertex) →
            ∀ v ∈ (B.childBranch c).vertices, D v = E v := by
        intro c hnot v hv
        have hnotHead : t.1 ≠ c.vertex :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ c.vertex := by
          intro s hs
          exact hnot s (by simp [hs])
        have hcHead : c.vertex ≠ t.child.vertex := by
          simpa using hnotHead.symm
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            c t.child hcHead hv
        have hStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          D v = E₁ v := hUntouchedTail c hnotTail v hv
          _ = E v := hStep
      exact
        ⟨D, hReachAll, hRootAll, hParentAll,
          hClearedAll, hUntouchedAll⟩

/-- Execute every occupied genuine child in the audited order.  The resulting
configuration has accumulated exactly childMessageSum at the root, leaves the
external parent unchanged, and clears every non-root vertex of the branch.
Configuration-empty children are never tasks and remain untouched. -/
theorem executeAllOccupiedChildren
    (B : OrientedBranch T) (C E : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E' : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E' →
        branchMessage E' (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E' q D ∧
            (D B.root : ℤ) = (q : ℤ) + d)
    (hSame :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = C v)
    (hSafe :
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ)
        (orderedTasks
          (fun t : B.OccupiedChild C => t.gain)
          (B.occupiedChildTasks C))) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B ∧
      D B.parent = E B.parent ∧
      (∀ v ∈ B.vertices, v ≠ B.root → D v = 0) := by
  classical
  let gain : B.OccupiedChild C → ℤ := fun t => t.gain
  let baseTasks : List (B.OccupiedChild C) := B.occupiedChildTasks C
  let scheduled : List (B.OccupiedChild C) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using B.occupiedChildTasks_nodup C
  have hNodupScheduled : scheduled.Nodup := by
    exact orderedTasks_nodup gain hNodupBase
  have hSameScheduled :
      ∀ t ∈ scheduled, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v := by
    intro t ht v hv
    have hvB : v ∈ B.vertices :=
      B.childBranch_vertices_subset t.child hv
    have hvRoot : v ≠ B.root := by
      intro hvr
      subst v
      exact (B.childBranch t.child).parent_not_mem_vertices
        (by simpa using hv)
    exact hSame v hvB hvRoot
  have hSafe' :
      TaskScheduleSafe gain (E B.root : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeOccupiedTaskSchedule B C hChildAttain
      scheduled E hNodupScheduled hSameScheduled hSafe' with
    ⟨D, hReach, hRoot, hParent, hCleared, hUntouched⟩
  have hRoot' :
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B := by
    calc
      (D B.root : ℤ) =
          (E B.root : ℤ) + taskGainSum gain scheduled := hRoot
      _ =
          (E B.root : ℤ) + taskGainSum gain baseTasks := by
            change
              (E B.root : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (E B.root : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (E B.root : ℤ) + childMessageSum C B := by
            change
              (E B.root : ℤ) +
                  taskGainSum
                    (fun t : B.OccupiedChild C => t.gain)
                    (B.occupiedChildTasks C) =
                (E B.root : ℤ) + childMessageSum C B
            rw [taskGainSum_occupiedChildTasks]
  have hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → D v = 0 := by
    intro v hvB hvRoot
    rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hvB hvRoot with
      ⟨c, hvc⟩
    by_cases hOcc : (B.childBranch c).Occupied C
    · let hcv : B.IsChildVertex c.vertex := ⟨c.adj, c.ne_parent⟩
      have hcEq : B.childOfVertex c.vertex hcv = c :=
        Child.eq_of_vertex_eq rfl
      let t : B.OccupiedChild C :=
        ⟨c.vertex, ⟨hcv, by
          rw [hcEq]
          exact hOcc⟩⟩
      have htChild : t.child = c := by
        apply Child.eq_of_vertex_eq
        calc
          t.child.vertex = t.1 := t.child_vertex
          _ = c.vertex := rfl
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using B.mem_occupiedChildTasks C t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htClear := hCleared t htScheduled
      rw [htChild] at htClear
      exact htClear v hvc
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ c.vertex := by
        intro t ht hEq
        have htc : t.child = c := by
          apply Child.eq_of_vertex_eq
          simpa using hEq
        have htOcc := t.occupied
        rw [htc] at htOcc
        exact hOcc htOcc
      have hPres : D v = E v :=
        hUntouched c hNoTask v hvc
      have hEC : E v = C v :=
        hSame v hvB hvRoot
      have hC0 : C v = 0 := by
        by_contra hne
        exact hOcc ⟨v, hvc, Nat.pos_of_ne_zero hne⟩
      calc
        D v = E v := hPres
        _ = C v := hEC
        _ = 0 := hC0
  exact ⟨D, hReach, hRoot', hParent, hNonroot⟩

/-- Once all non-root branch vertices are clear, an even root pile 2k
with k at least one is cleared optimally by k outward boundary moves. -/
theorem attainRootTransfer_even
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  have hEnough : 2 * k ≤ E B.root := by
    omega
  rcases BranchReach.repeat_move B B.adj
      B.root_mem_carrier B.parent_mem_carrier E k hEnough with
    ⟨D, hReach, hDroot, hDparent, hOther⟩
  have hRootZero : D B.root = 0 := by
    rw [hDroot, hRoot]
    omega
  have hCleared : B.Cleared D := by
    intro v hv
    by_cases hvr : v = B.root
    · subst v
      exact hRootZero
    · have hvp : v ≠ B.parent := by
        intro hvp
        subst v
        exact B.parent_not_mem_vertices hv
      rw [hOther v hvr hvp]
      exact hNonroot v hv hvr
  have hkZ : 0 ≤ (k : ℤ) := by positivity
  have hkPosZ : 0 < (k : ℤ) := by exact_mod_cast hk
  have hRootZ : (E B.root : ℤ) = 2 * (k : ℤ) := by
    exact_mod_cast hRoot
  have hF : F (E B.root : ℤ) = (k : ℤ) := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ)) hkZ).2
    exact Or.inl ⟨hkPosZ, hRootZ⟩
  have hParentZ :
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + (k : ℤ) := by
    exact_mod_cast hDparent
  refine ⟨D, hReach, hCleared, ?_⟩
  rw [hF]
  exact hParentZ

/-- Once all non-root branch vertices are clear, an odd root pile 2k+1
with k at least one attains the exact transfer by an explicit legal sequence.
If the boundary is empty, two outward moves are made first; otherwise one
outward move suffices to fund the single inward move. -/
theorem attainRootTransfer_odd
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k + 1)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  have hkMinus : 0 ≤ (k : ℤ) - 1 := by
    exact_mod_cast hk
    omega
  have hRootZ :
      (E B.root : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hRoot
  have hF :
      F (E B.root : ℤ) = (k : ℤ) - 1 := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ) - 1) hkMinus).2
    exact Or.inr (by
      rw [hRootZ]
      ring)
  by_cases hq : E B.parent = 0
  · have hk2 : 2 ≤ k := by
      rw [hF, hq] at hPos
      norm_num at hPos
      omega
    have hEnough1 : 2 * 2 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 2 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      rw [h1parent, hq]
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * (k - 1) ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ (k - 1) hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
      rw [h3root, h2root, h1root, hRoot]
      omega
    have hCleared : B.Cleared D := by
      intro v hv
      by_cases hvr : v = B.root
      · subst v
        exact hRootZero
      · have hvp : v ≠ B.parent := by
          intro hvp
          subst v
          exact B.parent_not_mem_vertices hv
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + (k - 1) := by
      rw [h3parent, h2parent, h1parent, hq]
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      exact_mod_cast hParentNat
      omega
    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ
  · have hq1 : 1 ≤ E B.parent := Nat.one_le_iff_ne_zero.mpr hq
    have hEnough1 : 2 * 1 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 1 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      rw [h1parent]
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * k ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ k hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
      rw [h3root, h2root, h1root, hRoot]
      omega
    have hCleared : B.Cleared D := by
      intro v hv
      by_cases hvr : v = B.root
      · subst v
        exact hRootZero
      · have hvp : v ≠ B.parent := by
          intro hvp
          subst v
          exact B.parent_not_mem_vertices hv
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + k - 1 := by
      rw [h3parent, h2parent, h1parent]
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      exact_mod_cast hParentNat
      omega
    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ

/-- Root/boundary attainment for every effective root pile at least two. -/
theorem attainRootTransfer_ge_two
    (B : OrientedBranch T) (E : Configuration V)
    (hRootTwo : 2 ≤ E B.root)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  by_cases hEven : Even (E B.root)
  · rcases hEven with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_even E k hk hRoot hNonroot
  · have hOdd : Odd (E B.root) :=
      Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k + 1 := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_odd E k hk hRoot hNonroot hPos

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
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent <;> simp [h]
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
