import Mathlib
import TreeStack.AuxiliaryCharge

namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Every undirected edge has a dart presentation. -/
theorem exists_edgeDart (e : T.graph.edgeFinset) :
    ∃ d : T.graph.Dart, d.edge = e.1 := by
  rcases Sym2.mk_surjective e.1 with ⟨⟨u, v⟩, huv⟩
  have hedge : e.1 ∈ T.graph.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp e.2
  have hadj : T.graph.Adj u v := by
    rw [← huv] at hedge
    simpa using hedge
  refine ⟨⟨(u, v), hadj⟩, ?_⟩
  simpa using huv

/-- A fixed choice of orientation for each ambient undirected edge.  All later
quantities are proved independent of this presentation. -/
noncomputable def edgeDart (e : T.graph.edgeFinset) : T.graph.Dart :=
  Classical.choose (exists_edgeDart (T := T) e)

@[simp] theorem edgeDart_edge (e : T.graph.edgeFinset) :
    (edgeDart (T := T) e).edge = e.1 :=
  Classical.choose_spec (exists_edgeDart (T := T) e)

/-- The chosen oriented-branch presentation of an ambient edge. -/
noncomputable def edgeBranch (e : T.graph.edgeFinset) : OrientedBranch T :=
  incidentBranch T (edgeDart (T := T) e).snd
    (edgeDart (T := T) e).fst (edgeDart (T := T) e).adj

@[simp] theorem edgeBranch_root (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).root = (edgeDart (T := T) e).fst := rfl

@[simp] theorem edgeBranch_parent (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).parent = (edgeDart (T := T) e).snd := rfl

theorem edgeBranch_edge (e : T.graph.edgeFinset) :
    s((edgeBranch (T := T) e).root, (edgeBranch (T := T) e).parent) = e.1 := by
  exact edgeDart_edge (T := T) e

/-- The ambient-root owner, viewed as a function on undirected edge indices. -/
noncomputable def edgeOwner (ambientRoot : V)
    (e : T.graph.edgeFinset) : V :=
  (edgeBranch (T := T) e).rootedOwner ambientRoot

/-- Rooted owners are injective on all ambient tree edges. -/
theorem edgeOwner_injective (ambientRoot : V) :
    Function.Injective (edgeOwner (T := T) ambientRoot) := by
  intro e f hOwner
  apply Subtype.ext
  have hEdge :=
    edge_eq_of_rootedOwner_eq ambientRoot
      (edgeBranch (T := T) e) (edgeBranch (T := T) f) hOwner
  rw [edgeBranch_edge (T := T) e, edgeBranch_edge (T := T) f] at hEdge
  exact hEdge

/-- Integer weighted mass for the auxiliary powers-of-two weights. -/
noncomputable def auxWeightedMass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, auxWeightInt C ambientRoot hScores v * (C v : ℤ)

/-- Total available weighted vertex-defect budget. -/
noncomputable def auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v

/-- Weighted degree potential appearing after defect cancellation. -/
noncomputable def auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, (T.graph.degree v : ℤ) *
    auxWeightInt C ambientRoot hScores v

/-- The owner charges over all ambient edges fit inside the total vertex
defect budget, by injectivity of the rooted-owner assignment. -/
theorem sum_edgeOwner_charge_le_auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e)) ≤
      auxDefectBudget C ambientRoot hScores := by
  let f : V → ℤ := fun v =>
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v
  have hf : ∀ v, 0 ≤ f v := by
    intro v
    exact mul_nonneg
      (auxWeightInt_nonneg C ambientRoot hScores v)
      ((scoreDefect_nonneg_iff T C v).2 (hScores v))
  let owner : T.graph.edgeFinset → V := edgeOwner ambientRoot
  have hOwner : Function.Injective owner :=
    edgeOwner_injective (T := T) ambientRoot
  calc
    (∑ e : T.graph.edgeFinset,
        auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
          scoreDefect T C (edgeOwner ambientRoot e)) =
        ∑ e : T.graph.edgeFinset, f (owner e) := by rfl
    _ = ∑ v ∈ (Finset.univ : Finset T.graph.edgeFinset).image owner, f v := by
      rw [Finset.sum_image]
      intro e _ g _ heg
      exact hOwner heg
    _ ≤ ∑ v : V, f v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun v _ _ => hf v)
    _ = auxDefectBudget C ambientRoot hScores := by
      rfl

/-- The uniform local edge inequality, packaged on the fixed finite edge
index. -/
theorem edgeContribution_le_endpoint_add_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxEdgeContribution C ambientRoot hScores (edgeBranch e) ≤
      auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent +
        auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
          scoreDefect T C (edgeOwner ambientRoot e) := by
  exact auxEdgeContribution_le_endpoint_add_owner_charge
    C ambientRoot hRootPos hScores (edgeBranch e)

/-- The two darts belonging to a chosen undirected edge presentation. -/
noncomputable def dartOfEdgeBool
    (p : T.graph.edgeFinset × Bool) : T.graph.Dart :=
  if p.2 then (edgeDart (T := T) p.1).symm else edgeDart (T := T) p.1

@[simp] theorem dartOfEdgeBool_edge
    (p : T.graph.edgeFinset × Bool) :
    (dartOfEdgeBool (T := T) p).edge = p.1.1 := by
  rcases p with ⟨e, b⟩
  cases b <;> simp [dartOfEdgeBool, edgeDart_edge]

theorem dartOfEdgeBool_injective :
    Function.Injective (dartOfEdgeBool (T := T)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have hEdge : e = f := by
    apply Subtype.ext
    have h' := congrArg SimpleGraph.Dart.edge h
    simpa using h'
  subst f
  cases b <;> cases c
  · rfl
  · have h' : edgeDart (T := T) e =
        (edgeDart (T := T) e).symm := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h'.symm).elim
  · have h' : (edgeDart (T := T) e).symm =
        edgeDart (T := T) e := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h').elim
  · rfl

theorem dartOfEdgeBool_surjective :
    Function.Surjective (dartOfEdgeBool (T := T)) := by
  intro d
  let e : T.graph.edgeFinset :=
    ⟨d.edge, SimpleGraph.mem_edgeFinset.mpr d.edge_mem⟩
  have hSameEdge : (edgeDart (T := T) e).edge = d.edge := by
    exact edgeDart_edge (T := T) e
  rcases (SimpleGraph.dart_edge_eq_iff (edgeDart (T := T) e) d).mp hSameEdge with
    h | h
  · refine ⟨(e, false), ?_⟩
    simpa [dartOfEdgeBool] using h
  · refine ⟨(e, true), ?_⟩
    simp [dartOfEdgeBool, h]

/-- Ambient darts are exactly an undirected edge together with a Boolean
choice of its two orientations. -/
noncomputable def edgeBoolEquivDart :
    T.graph.edgeFinset × Bool ≃ T.graph.Dart :=
  Equiv.ofBijective (dartOfEdgeBool (T := T))
    ⟨dartOfEdgeBool_injective (T := T),
      dartOfEdgeBool_surjective (T := T)⟩

@[simp] theorem edgeBoolEquivDart_apply
    (p : T.graph.edgeFinset × Bool) :
    edgeBoolEquivDart (T := T) p = dartOfEdgeBool (T := T) p :=
  rfl

/-- Sum a dart function by grouping the two orientations of each undirected
edge. -/
theorem sum_dart_eq_sum_edge_pair (f : T.graph.Dart → ℤ) :
    (∑ d : T.graph.Dart, f d) =
      ∑ e : T.graph.edgeFinset,
        (f (edgeDart (T := T) e) + f (edgeDart (T := T) e).symm) := by
  calc
    (∑ d : T.graph.Dart, f d) =
        ∑ p : T.graph.edgeFinset × Bool,
          f (edgeBoolEquivDart (T := T) p) := by
      exact (Equiv.sum_comp (edgeBoolEquivDart (T := T)) f).symm
    _ = ∑ e : T.graph.edgeFinset,
          (f (edgeDart (T := T) e) + f (edgeDart (T := T) e).symm) := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro e
      rw [Fintype.sum_bool]
      simp [edgeBoolEquivDart_apply, dartOfEdgeBool, add_comm]

/-- Reindex a dart by its head vertex and its tail as a neighbor of that
head. -/
def dartEquivHeadNeighbor :
    T.graph.Dart ≃ Σ v : V, T.graph.neighborSet v where
  toFun d := ⟨d.snd, ⟨d.fst, d.adj.symm⟩⟩
  invFun p := ⟨(p.2.1, p.1), p.2.2.symm⟩
  left_inv d := by ext <;> rfl
  right_inv p := by cases p; rfl

/-- A root message sum may be indexed only by genuine neighbors; all
nonneighbors already contribute zero by definition. -/
theorem sum_neighbor_rootMessageTerm_eq
    (C : Configuration V) (v : V) :
    (∑ u : T.graph.neighborSet v, rootMessageTerm T C v u) =
      rootMessageSum T C v := by
  classical
  rw [rootMessageSum]
  calc
    (∑ u : T.graph.neighborSet v, rootMessageTerm T C v u) =
        ∑ u ∈ T.graph.neighborFinset v, rootMessageTerm T C v u := by
      rw [Finset.sum_subtype (T.graph.neighborFinset v)]
      intro u
      simp [SimpleGraph.mem_neighborFinset, T.graph.adj_comm]
    _ = ∑ u : V, rootMessageTerm T C v u := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u _ hu
      have hNotAdj : ¬ T.graph.Adj u v := by
        simpa [SimpleGraph.mem_neighborFinset, T.graph.adj_comm] using hu
      simp [rootMessageTerm, hNotAdj]

/-- One directed half of the weighted root-message sum. -/
noncomputable def auxDartMessageTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (d : T.graph.Dart) : ℤ :=
  auxWeightInt C ambientRoot hScores d.snd *
    rootMessageTerm T C d.snd d.fst

/-- Summing directed message terms by their head recovers the weighted rooted
message sums. -/
theorem sum_auxDartMessageTerm_eq
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ d : T.graph.Dart,
      auxDartMessageTerm C ambientRoot hScores d) =
      ∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
  calc
    (∑ d : T.graph.Dart,
        auxDartMessageTerm C ambientRoot hScores d) =
        ∑ p : Σ v : V, T.graph.neighborSet v,
          auxDartMessageTerm C ambientRoot hScores
            ((dartEquivHeadNeighbor (T := T)).symm p) := by
      exact
        (Equiv.sum_comp (dartEquivHeadNeighbor (T := T)).symm
          (auxDartMessageTerm C ambientRoot hScores)).symm
    _ = ∑ v : V,
          ∑ u : T.graph.neighborSet v,
            auxWeightInt C ambientRoot hScores v *
              rootMessageTerm T C v u := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ v : V,
          auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
      apply Fintype.sum_congr
      intro v
      rw [← Finset.mul_sum, sum_neighbor_rootMessageTerm_eq]

/-- The two dart terms of an edge are exactly the negative of its auxiliary
edge contribution. -/
theorem auxDartMessageTerm_add_symm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxDartMessageTerm C ambientRoot hScores (edgeDart e) +
        auxDartMessageTerm C ambientRoot hScores (edgeDart e).symm =
      -auxEdgeContribution C ambientRoot hScores (edgeBranch e) := by
  have hAdj := (edgeDart (T := T) e).adj
  have hAdjSymm := hAdj.symm
  simp [auxDartMessageTerm, auxEdgeContribution, edgeBranch,
    rootMessageTerm, incidentBranch, reverseBranch, hAdj, hAdjSymm]

/-- The sum of undirected weighted edge contributions is the negative
weighted root-message sum. -/
theorem sum_auxEdgeContribution_eq_neg_messages
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) =
      -(∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v) := by
  have hGroup :=
    sum_dart_eq_sum_edge_pair (T := T)
      (auxDartMessageTerm C ambientRoot hScores)
  simp_rw [auxDartMessageTerm_add_symm C ambientRoot hScores] at hGroup
  rw [sum_auxDartMessageTerm_eq C ambientRoot hScores] at hGroup
  calc
    (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) =
        -∑ e : T.graph.edgeFinset,
          -auxEdgeContribution C ambientRoot hScores (edgeBranch e) := by
      simp
    _ = -(∑ v : V,
          auxWeightInt C ambientRoot hScores v * rootMessageSum T C v) := by
      rw [← hGroup]

/-- Exact weighted score expansion: weighted mass is the edge contribution
sum minus the total weighted defect budget. -/
theorem auxWeightedMass_eq_edges_sub_defect
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores =
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) -
        auxDefectBudget C ambientRoot hScores := by
  rw [sum_auxEdgeContribution_eq_neg_messages]
  unfold auxWeightedMass auxDefectBudget scoreDefect score
  simp only [mul_neg, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  ring

/-- Sum of the two endpoint weights over undirected edges equals the weighted
degree potential. -/
theorem sum_edgeEndpointWeight_eq_auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      (auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent)) =
      auxDegreePotential C ambientRoot hScores := by
  let f : T.graph.Dart → ℤ := fun d =>
    auxWeightInt C ambientRoot hScores d.snd
  have hGroup := sum_dart_eq_sum_edge_pair (T := T) f
  have hPair (e : T.graph.edgeFinset) :
      f (edgeDart e) + f (edgeDart e).symm =
        auxWeightInt C ambientRoot hScores (edgeBranch e).root +
          auxWeightInt C ambientRoot hScores (edgeBranch e).parent := by
    simp [f, edgeBranch, add_comm]
  simp_rw [hPair] at hGroup
  have hDart :
      (∑ d : T.graph.Dart, f d) =
        ∑ v : V, (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v := by
    calc
      (∑ d : T.graph.Dart, f d) =
          ∑ p : Σ v : V, T.graph.neighborSet v,
            f ((dartEquivHeadNeighbor (T := T)).symm p) := by
        exact
          (Equiv.sum_comp (dartEquivHeadNeighbor (T := T)).symm f).symm
      _ = ∑ v : V,
            ∑ _u : T.graph.neighborSet v,
              auxWeightInt C ambientRoot hScores v := by
        rw [Fintype.sum_sigma]
        rfl
      _ = ∑ v : V, (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
        apply Fintype.sum_congr
        intro v
        rw [Finset.sum_const, Finset.card_univ,
          SimpleGraph.card_neighborSet_eq_degree]
        simp [nsmul_eq_mul, mul_comm]
  rw [hDart] at hGroup
  exact hGroup.symm

set_option maxHeartbeats 800000

/-- Global sum of the local owner-paid edge inequalities. -/
theorem sum_auxEdgeContribution_le_degree_add_defect
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
      auxDegreePotential C ambientRoot hScores +
        auxDefectBudget C ambientRoot hScores := by
  have hLocal :
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
        ∑ e : T.graph.edgeFinset,
          ((auxWeightInt C ambientRoot hScores (edgeBranch e).root +
              auxWeightInt C ambientRoot hScores (edgeBranch e).parent) +
            auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
              scoreDefect T C (edgeOwner ambientRoot e)) := by
    exact Finset.sum_le_sum fun e _ =>
      edgeContribution_le_endpoint_add_owner_charge
        C ambientRoot hRootPos hScores e
  rw [Finset.sum_add_distrib,
    sum_edgeEndpointWeight_eq_auxDegreePotential] at hLocal
  exact hLocal.trans (add_le_add (le_refl _)
    (sum_edgeOwner_charge_le_auxDefectBudget C ambientRoot hScores))

set_option maxHeartbeats 200000

/-- Global weighted defect cancellation.  This is the major Stage 1 bound:
the defect budget in the exact score expansion cancels all owner charges. -/
theorem auxWeightedMass_le_auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores ≤
      auxDegreePotential C ambientRoot hScores := by
  rw [auxWeightedMass_eq_edges_sub_defect]
  have h :=
    sum_auxEdgeContribution_le_degree_add_defect
      C ambientRoot hRootPos hScores
  linarith

end OrientedBranch

end TreeStack
