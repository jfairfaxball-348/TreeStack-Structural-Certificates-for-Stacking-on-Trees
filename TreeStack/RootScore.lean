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
  have hvComp0 : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvComp : v ∈ B.component.supp := by
    simpa [B, incidentBranch] using hvComp0
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

theorem RootTask.branch_eq_incident
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) (h : T.graph.Adj t.1 r) :
    t.branch = incidentBranch T r t.1 h := by
  have hp :
      Classical.choose t.2 = h :=
    Subsingleton.elim _ _
  simp [RootTask.branch, hp]

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



/-- Execute a safe list of occupied incident branches toward one target root.
Every task attains its exact branch message gain; distinct incident interiors
are preserved by locality. -/
theorem executeRootTaskSchedule
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    ∀ (tasks : List (RootTask T C r)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ t.branch.vertices, E v = C v) →
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (E r : ℤ) tasks →
      ∃ D : Configuration V,
        Reach T.graph E D ∧
        (D r : ℤ) =
          (E r : ℤ) +
            taskGainSum (fun t : RootTask T C r => t.gain) tasks ∧
        (∀ t ∈ tasks, t.branch.Cleared D) ∧
        (∀ (u : V) (h : T.graph.Adj u r),
          (∀ t ∈ tasks, t.1 ≠ u) →
          ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro u h hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E r : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            ((E r : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ t.branch.vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ t.branch.vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE : t.branch.Occupied E :=
        (t.branch.occupied_congr_vertices C E hCE).mp t.occupied
      have hMsgC :
          OrientedBranch.branchMessage C t.branch = some t.gain := by
        rw [OrientedBranch.branchMessage_eq_some_of_occupied
          C t.branch t.occupied, t.gain_eq_F]
      have hMsgE :
          OrientedBranch.branchMessage E t.branch = some t.gain := by
        calc
          OrientedBranch.branchMessage E t.branch =
              OrientedBranch.branchMessage C t.branch :=
            (t.branchMessage_congr_vertices C E hCE).symm
          _ = some t.gain := hMsgC
      rcases OrientedBranch.boundary_attainment
          E t.branch hOccE t.gain hMsgE (E r) hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart : t.branch.withBoundary E (E r) = E := by
        have hSelf := t.branch.withBoundary_self E
        simpa using hSelf
      have hReachBranch : t.branch.BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachGlobal : Reach T.graph E E₁ :=
        hReachBranch.toReach t.branch
      have hRoot₁' :
          (E₁ r : ℤ) = (E r : ℤ) + t.gain := by
        simpa using hRoot₁
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ s.branch.vertices, E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hOutside : v ∉ t.branch.carrier := by
          have h :=
            mem_incidentBranch_vertices_not_mem_sibling_carrier
              (T := T) r s.branch.adj t.branch.adj hst hv
          simpa [s.branch_eq_incident s.branch.adj,
            t.branch_eq_incident t.branch.adj] using h
        have hEqStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            (E₁ r : ℤ) ts := by
        rw [hRoot₁']
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hClearedTail, hUntouchedTail⟩
      have hReachAll : Reach T.graph E D :=
        Relation.ReflTransGen.trans hReachGlobal hReachTail
      have hRootAll :
          (D r : ℤ) =
            (E r : ℤ) +
              taskGainSum
                (fun s : RootTask T C r => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁']
        simp only [taskGainSum]
        ring
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.1 := by
        intro s hs hEq
        have hObj : s = t := Subtype.ext hEq
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ t.branch.vertices, D v = E₁ v := by
        intro v hv
        have h :=
          hUntouchedTail t.1 t.branch.adj hHeadNotTail v
        simpa [t.branch_eq_incident t.branch.adj] using h
      have hClearedHead : t.branch.Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, s.branch.Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ (u : V) (h : T.graph.Adj u r),
            (∀ s ∈ t :: ts, s.1 ≠ u) →
            ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v := by
        intro u h hnot v hv
        have hnotHead : t.1 ≠ u :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ u := by
          intro s hs
          exact hnot s (by simp [hs])
        have hOutside : v ∉ t.branch.carrier := by
          have hOut :=
            mem_incidentBranch_vertices_not_mem_sibling_carrier
              (T := T) r h t.branch.adj hnotHead.symm hv
          simpa [t.branch_eq_incident t.branch.adj] using hOut
        have hStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          D v = E₁ v := hUntouchedTail u h hnotTail v hv
          _ = E v := hStep
      exact ⟨D, hReachAll, hRootAll, hClearedAll, hUntouchedAll⟩

/-- Execute every occupied incident branch in the audited order.  The result
clears every non-root vertex and leaves exactly the rooted score at r. -/
theorem executeAllRootTasks
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r))) :
    ∃ D : Configuration V,
      Reach T.graph C D ∧
      (D r : ℤ) = score T C r ∧
      (∀ v : V, v ≠ r → D v = 0) := by
  classical
  let gain : RootTask T C r → ℤ := fun t => t.gain
  let baseTasks : List (RootTask T C r) := rootTasks T C r
  let scheduled : List (RootTask T C r) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using rootTasks_nodup T C r
  have hNodupScheduled : scheduled.Nodup :=
    orderedTasks_nodup gain hNodupBase
  have hSame :
      ∀ t ∈ scheduled, ∀ v ∈ t.branch.vertices, C v = C v := by
    intro t ht v hv
    rfl
  have hSafe' :
      TaskScheduleSafe gain (C r : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeRootTaskSchedule T C r
      scheduled C hNodupScheduled hSame hSafe' with
    ⟨D, hReach, hRoot, hCleared, hUntouched⟩
  have hRootScore : (D r : ℤ) = score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + taskGainSum gain scheduled := hRoot
      _ = (C r : ℤ) + taskGainSum gain baseTasks := by
            change
              (C r : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (C r : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (C r : ℤ) + rootMessageSum T C r := by
            change
              (C r : ℤ) +
                  taskGainSum
                    (fun t : RootTask T C r => t.gain)
                    (rootTasks T C r) =
                (C r : ℤ) + rootMessageSum T C r
            rw [taskGainSum_rootTasks]
      _ = score T C r := rfl
  have hOffRoot : ∀ v : V, v ≠ r → D v = 0 := by
    intro v hvr
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hvr with
      ⟨u, h, hv⟩
    by_cases hOcc : (incidentBranch T r u h).Occupied C
    · let t : RootTask T C r := ⟨u, ⟨h, hOcc⟩⟩
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using mem_rootTasks T C r t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htBranch :
          t.branch = incidentBranch T r u h := by
        exact t.branch_eq_incident h
      have htClear := hCleared t htScheduled
      rw [htBranch] at htClear
      exact htClear v hv
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ u := by
        intro t ht hEq
        have htOcc := t.occupied
        have htBranch :
            t.branch = incidentBranch T r u h := by
          subst u
          exact t.branch_eq_incident h
        rw [htBranch] at htOcc
        exact hOcc htOcc
      have hPres : D v = C v :=
        hUntouched u h hNoTask v hv
      have hC0 : C v = 0 := by
        exact
          ((incidentBranch T r u h).not_occupied_iff_zero_on_vertices C).1
            hOcc v hv
      exact hPres.trans hC0
  exact ⟨D, hReach, hRootScore, hOffRoot⟩

/-- Positive rooted score gives an explicit legal stack at the chosen root. -/
theorem stackableAt_of_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hScore : 0 < score T C r) :
    StackableAt T.graph C r := by
  classical
  have hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r)) := by
    apply orderedTasks_safe
    · positivity
    · rw [taskGainSum_rootTasks]
      simpa [score] using hScore
  rcases executeAllRootTasks T C r hSafe with
    ⟨D, hReach, hRoot, hOffRoot⟩
  refine ⟨D, hReach, ?_⟩
  constructor
  · have hPosZ : 0 < (D r : ℤ) := by
      rw [hRoot]
      exact hScore
    exact_mod_cast hPosZ
  · exact hOffRoot

/-- A branch-local legal reach is in particular a global legal reach. -/
theorem OrientedBranch.BranchReach.toReach
    [DecidableEq V] (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    Reach T.graph C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      exact ⟨u, v, huv, hlegal, rfl⟩

/-- A global legal reach has an exact move-count signature.  Moreover, if an
oriented branch starts occupied and its outward boundary count is zero, then
that branch remains occupied. -/
theorem Reach.exists_moveSignature
    [DecidableEq V] {C D : Configuration V}
    (hreach : Reach T.graph C D) :
    ∃ m : MoveSignature T,
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, ?_, ?_⟩
      · intro w
        simp
      · intro A hOcc hzero
        exact hOcc
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, rfl⟩
      rcases ih with ⟨m, hmBal, hmPersist⟩
      let m' : MoveSignature T := m.extend u v huv
      refine ⟨m', ?_, ?_⟩
      · intro w
        rw [OrientedBranch.move_balance_int _ huv.ne hlegal w, hmBal w]
        simp [m', MoveSignature.incoming_extend, MoveSignature.outgoing_extend]
        by_cases hwu : w = u <;> simp [hwu] <;> ring
      · intro A hOcc hzero
        have hmzero : m.count A.root A.parent = 0 := by
          have hle :
              m.count A.root A.parent ≤ m'.count A.root A.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        rcases hmPersist A hOcc hmzero with ⟨w, hwA, hwpos⟩
        by_cases hvA : v ∈ A.vertices
        · refine ⟨v, hvA, ?_⟩
          simp [move]
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


/-- Net signature flux into a candidate target, summed over all possible
neighbors. Nonedges contribute zero because every positive signature count is
supported on an actual tree edge. -/
noncomputable def rootSignatureFluxSum
    (m : MoveSignature T) (r : V) : ℤ :=
  ∑ u : V,
    (m.count u r : ℤ) - 2 * (m.count r u : ℤ)

theorem rootSignatureFluxSum_eq
    (m : MoveSignature T) (r : V) :
    rootSignatureFluxSum m r =
      (m.incoming r : ℤ) - 2 * (m.outgoing r : ℤ) := by
  rw [rootSignatureFluxSum, MoveSignature.incoming, MoveSignature.outgoing]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Any legal stack at r forces the rooted score to be positive. -/
theorem score_pos_of_stackableAt
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hStackable : StackableAt T.graph C r) :
    0 < score T C r := by
  classical
  rcases hStackable with ⟨D, hReach, hStack⟩
  rcases Reach.exists_moveSignature hReach with
    ⟨m, hmBal, hmPersist⟩
  have hTerm :
      ∀ u : V,
        (m.count u r : ℤ) - 2 * (m.count r u : ℤ) ≤
          rootMessageTerm T C r u := by
    intro u
    by_cases hAdj : T.graph.Adj u r
    · let B : OrientedBranch T := incidentBranch T r u hAdj
      have hClears : MoveSignature.Clears m C B := by
        intro w hw
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hw
        have hzero : D w = 0 := hStack.2 w hwr
        have hbal := hmBal w
        rw [hzero] at hbal
        simpa [MoveSignature.BalancesAt] using hbal.symm
      have hCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ B.vertices →
            A.Occupied C →
            MoveSignature.CausalOutward m A := by
        intro A hAB hOcc
        apply Nat.pos_of_ne_zero
        intro hzero
        rcases hmPersist A hOcc hzero with ⟨w, hwA, hwpos⟩
        have hwB : w ∈ B.vertices := hAB hwA
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hwB
        have hz : D w = 0 := hStack.2 w hwr
        rw [hz] at hwpos
        omega
      have hBounds :=
        OrientedBranch.signature_branchFlux_bounds
          m C B hClears hCausal
      have hFlux :
          (m.count u r : ℤ) - 2 * (m.count r u : ℤ) =
            OrientedBranch.MoveSignature.boundaryFlux m B := by
        rfl
      rw [hFlux]
      by_cases hOcc : B.Occupied C
      · have hBound := (hBounds.1 hOcc).1
        have hMsg :=
          OrientedBranch.branchMessage_eq_some_of_occupied C B hOcc
        have hTermEq :
            rootMessageTerm T C r u =
              F (OrientedBranch.effectiveInput C B) := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          simpa [B, incidentBranch, hMsg]
        rw [hTermEq]
        exact hBound
      · rcases hBounds.2 hOcc with ⟨k, hk⟩
        have hMsg :=
          OrientedBranch.branchMessage_eq_empty_of_not_occupied C B hOcc
        have hTermZero : rootMessageTerm T C r u = 0 := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          simpa [B, incidentBranch, hMsg]
        rw [hTermZero, hk]
        positivity
    · have hIn : m.count u r = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos)
      have hOut : m.count r u = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos).symm
      simp [rootMessageTerm, hAdj, hIn, hOut]
  have hFluxLe :
      rootSignatureFluxSum m r ≤ rootMessageSum T C r := by
    rw [rootSignatureFluxSum, rootMessageSum]
    exact Finset.sum_le_sum fun u _ => hTerm u
  have hRootBal := hmBal r
  have hDle : (D r : ℤ) ≤ score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + (m.incoming r : ℤ) -
            2 * (m.outgoing r : ℤ) := hRootBal
      _ = (C r : ℤ) + rootSignatureFluxSum m r := by
            rw [rootSignatureFluxSum_eq]
            ring
      _ ≤ (C r : ℤ) + rootMessageSum T C r := by
            linarith
      _ = score T C r := rfl
  have hDpos : 0 < (D r : ℤ) := by
    exact_mod_cast hStack.1
  omega

/-- Exact rooted characterization: a configuration can be stacked at r
exactly when its recursive rooted score is positive. -/
theorem stackableAt_iff_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    StackableAt T.graph C r ↔ 0 < score T C r := by
  constructor
  · exact score_pos_of_stackableAt T C r
  · exact stackableAt_of_score_pos T C r

/-- Global non-stackability is equivalent to every rooted score being
nonpositive. -/
theorem not_stackable_iff_all_scores_nonpos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) :
    ¬ Stackable T.graph C ↔ ∀ r : V, score T C r ≤ 0 := by
  rw [Stackable]
  push_neg
  constructor
  · intro h r
    have hn : ¬ 0 < score T C r := by
      intro hp
      exact h r ((stackableAt_iff_score_pos T C r).2 hp)
    omega
  · intro h r hs
    have hp := (stackableAt_iff_score_pos T C r).1 hs
    have hn := h r
    omega

end TreeStack
