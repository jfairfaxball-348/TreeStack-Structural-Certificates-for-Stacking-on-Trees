import Mathlib
import TreeStack.Boundary

namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The oriented branch on the u-side of an edge u-r, viewed toward target r. -/
def incidentBranch (T : FiniteTree V) (r u : V)
    (h : T.graph.Adj u r) : OrientedBranch T where
  root := u
  parent := r
  adj := h

@[simp] theorem incidentBranch_root (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).root = u := rfl

@[simp] theorem incidentBranch_parent (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).parent = r := rfl

/-- Distinct incident branches at one target have disjoint interiors. -/
theorem incidentBranch_vertices_disjoint
    (r : V) {u v : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v) :
    Disjoint
      (incidentBranch T r u hu).vertices
      (incidentBranch T r v hv).vertices := by
  classical
  let A : OrientedBranch T := incidentBranch T r u hu
  let B : OrientedBranch T := incidentBranch T r v hv
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hvOutside : v ∉ A.vertices := by
    intro hvA
    have heq :=
      A.eq_root_of_mem_vertices_adj_parent
        hvA (by simpa [A, incidentBranch] using hv)
    have heq' : v = u := by
      simpa [A, incidentBranch] using heq
    exact huv heq'.symm
  have hvComp : v ∈ B.component.supp := by
    simpa [B, incidentBranch] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem :
        B.root ∈ B.component.supp)
  have hxComp : x ∈ B.component.supp := by
    simpa [OrientedBranch.vertices] using hxB
  have hreach : B.deletedGraph.Reachable v x := by
    have :=
      B.component.reachable_of_mem_supp hvComp hxComp
    simpa [B, incidentBranch] using this
  have hreach' :
      (T.graph.deleteEdges {s(v, r)}).Reachable v x := by
    simpa [B, incidentBranch, OrientedBranch.deletedGraph] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidB⟩
  have hxASet : x ∈ (A.vertices : Set V) := by
    simpa using hxA
  have hvOutsideSet : v ∉ (A.vertices : Set V) := by
    simpa using hvOutside
  rcases p.reverse.exists_boundary_dart
      (A.vertices : Set V) hxASet hvOutsideSet with
    ⟨⟨⟨a, b⟩, hab⟩, hdart, haSet, hbSet⟩
  have haFin : a ∈ A.vertices := by simpa using haSet
  have hbFin : b ∉ A.vertices := by simpa using hbSet
  have hedge :=
    A.edge_leaving_vertices_eq_boundary haFin hbFin hab
  have hbRoot : b = r := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · have : b = A.parent := h.2
      simpa [A, incidentBranch] using this
    · have haParent : a = A.parent := h.1
      have : a = r := by simpa [A, incidentBranch] using haParent
      subst a
      have hrNot : r ∉ A.vertices := by
        simpa [A, incidentBranch] using A.parent_not_mem_vertices
      exact (hrNot haFin).elim
  have hrRev : r ∈ p.reverse.support := by
    rw [← hbRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hr : r ∈ p.support := by simpa using hrRev
  let q : T.graph.Walk v r := p.takeUntil r hr
  have hqAvoid : s(v, r) ∉ q.edges := by
    intro hq
    exact havoidB (p.edges_takeUntil_subset_edges hr hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(v, r)}).Reachable v r :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(v, r) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) hv
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot

/-- A vertex inside one incident branch is outside every distinct incident
branch carrier.  The only shared carrier point is the target itself. -/
theorem mem_incidentBranch_vertices_not_mem_sibling_carrier
    (r : V) {u v w : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v)
    (hw : w ∈ (incidentBranch T r u hu).vertices) :
    w ∉ (incidentBranch T r v hv).carrier := by
  classical
  intro hwCarrier
  have hwCases :
      w = r ∨ w ∈ (incidentBranch T r v hv).vertices := by
    simpa [OrientedBranch.carrier, incidentBranch] using hwCarrier
  rcases hwCases with hroot | hwv
  · subst w
    exact (incidentBranch T r u hu).parent_not_mem_vertices hw
  · exact
      (Finset.disjoint_left.mp
        (incidentBranch_vertices_disjoint (T := T) r hu hv huv)) hw hwv

/-- Every vertex other than the target lies in a genuine incident branch. -/
theorem exists_incidentBranch_mem_of_ne_root
    (r : V) {x : V} (hxr : x ≠ r) :
    ∃ u : V, ∃ h : T.graph.Adj u r,
      x ∈ (incidentBranch T r u h).vertices := by
  classical
  obtain ⟨p, hp⟩ :=
    T.isTree.connected.preconnected.exists_isPath r x
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p with
    ⟨u, hru, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hru p').mp hp
  have hrNot : r ∉ p'.support := hpData.2
  have hur : T.graph.Adj u r := hru.symm
  have havoid : s(u, r) ∉ p'.edges := by
    intro he
    exact hrNot (p'.snd_mem_support_of_mem_edges he)
  let q :
      (T.graph.deleteEdges {s(u, r)}).Walk u x :=
    p'.toDeleteEdges {s(u, r)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreach :
      (incidentBranch T r u hur).deletedGraph.Reachable u x := by
    change (T.graph.deleteEdges {s(u, r)}).Reachable u x
    exact ⟨q⟩
  refine ⟨u, hur, ?_⟩
  rw [OrientedBranch.vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff,
    OrientedBranch.component]
  exact (SimpleGraph.ConnectedComponent.sound hreach).symm

/-- Integer contribution of one possible neighbor to the rooted score. -/
noncomputable def rootMessageTerm
    (T : FiniteTree V) (C : Configuration V) (r u : V) : ℤ :=
  if h : T.graph.Adj u r then
    OrientedBranch.messageContribution
      (OrientedBranch.branchMessage C (incidentBranch T r u h))
  else
    0

/-- Sum of all non-EMPTY incident branch messages toward a target root. -/
noncomputable def rootMessageSum
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  ∑ u : V, rootMessageTerm T C r u

/-- Rooted stackability score from the audited branch-message theorem. -/
noncomputable def score
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  (C r : ℤ) + rootMessageSum T C r

/-- Predicate saying that u indexes an occupied incident branch toward r. -/
def IsOccupiedRootNeighbor
    (T : FiniteTree V) (C : Configuration V) (r u : V) : Prop :=
  ∃ h : T.graph.Adj u r, (incidentBranch T r u h).Occupied C

/-- Executable rooted task: an occupied genuine incident branch. -/
def RootTask
    (T : FiniteTree V) (C : Configuration V) (r : V) :=
  {u : V // IsOccupiedRootNeighbor T C r u}

noncomputable instance RootTask.instFintype
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    Fintype (RootTask T C r) :=
  Fintype.ofInjective
    (fun t : RootTask T C r => (t.1 : V))
    Subtype.val_injective

/-- Incident branch represented by a rooted executable task. -/
noncomputable def RootTask.branch
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : OrientedBranch T :=
  incidentBranch T r t.1 (Classical.choose t.2)

theorem RootTask.occupied
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.Occupied C := by
  exact Classical.choose_spec t.2

@[simp] theorem RootTask.branch_root
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.root = t.1 := rfl

@[simp] theorem RootTask.branch_parent
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.parent = r := rfl

/-- Recursive gain attached to a rooted executable task. -/
noncomputable def RootTask.gain
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : ℤ :=
  OrientedBranch.messageContribution
    (OrientedBranch.branchMessage C t.branch)

theorem RootTask.gain_eq_F
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = F (OrientedBranch.effectiveInput C t.branch) := by
  rw [RootTask.gain,
    OrientedBranch.branchMessage_eq_some_of_occupied C t.branch t.occupied]
  rfl

theorem rootMessageTerm_eq_zero_of_not_occupied
    (T : FiniteTree V) (C : Configuration V) (r : V) {u : V}
    (hu : ¬ IsOccupiedRootNeighbor T C r u) :
    rootMessageTerm T C r u = 0 := by
  by_cases h : T.graph.Adj u r
  · have hEmpty : ¬ (incidentBranch T r u h).Occupied C := by
      intro hOcc
      exact hu ⟨h, hOcc⟩
    simp [rootMessageTerm, h,
      OrientedBranch.branchMessage_eq_empty_of_not_occupied
        C (incidentBranch T r u h) hEmpty]
  · simp [rootMessageTerm, h]

theorem RootTask.gain_eq_term
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = rootMessageTerm T C r t.1 := by
  have h : T.graph.Adj t.1 r := Classical.choose t.2
  simp [RootTask.gain, RootTask.branch, rootMessageTerm, h]

/-- Unscheduled rooted task list: every occupied incident branch exactly once. -/
noncomputable def rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    List (RootTask T C r) := by
  classical
  exact (Finset.univ : Finset (RootTask T C r)).toList

theorem rootTasks_nodup
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    (rootTasks T C r).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (RootTask T C r))

@[simp] theorem mem_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (t : RootTask T C r) :
    t ∈ rootTasks T C r := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

/-- Rooted executable task gains sum to the full rooted message sum.
Configuration-empty branches contribute zero to the mathematical sum but
never appear as tasks. -/
theorem taskGainSum_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
      rootMessageSum T C r := by
  classical
  calc
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
        ∑ t : RootTask T C r, t.gain := by
          rw [rootTasks, taskGainSum_toList]
    _ = ∑ t : RootTask T C r,
          rootMessageTerm T C r t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ u ∈
          (Finset.univ.filter fun u : V =>
            IsOccupiedRootNeighbor T C r u),
          rootMessageTerm T C r u := by
          symm
          simpa [RootTask] using
            (Finset.sum_subtype
              (Finset.univ.filter fun u : V =>
                IsOccupiedRootNeighbor T C r u)
              (fun u => by simp)
              (fun u => rootMessageTerm T C r u))
    _ = ∑ u : V, rootMessageTerm T C r u := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro u huUniv huNot
          have huNotOcc : ¬ IsOccupiedRootNeighbor T C r u := by
            intro huOcc
            exact huNot (Finset.mem_filter.mpr ⟨huUniv, huOcc⟩)
          exact rootMessageTerm_eq_zero_of_not_occupied T C r huNotOcc
    _ = rootMessageSum T C r := rfl

end TreeStack
