# Upper-bound prose–Lean map

This map concerns `paper/sections/upper.tex`. All Lean names are in namespace
`TreeStack`; names in graph-specific modules below are additionally in
`OrientedBranch`, unless explicitly marked otherwise. The paper works on the
original ambient tree throughout. Its chosen occupied vertex `o` is Lean's
`ambientRoot`; the final estimator root is a separate vertex.

| Paper item | Lean source and declarations | Correspondence |
| --- | --- | --- |
| Numerical contribution of EMPTY | `TreeStack/Message.lean`: `messageContribution`; `TreeStack/Support.lean`: `score_eq_effectiveInput_of_reverse_not_occupied` | EMPTY remains a distinct message; only its contribution to a sum is zero. |
| Lemma `upper-support`, edge-side partition | `TreeStack/Support.lean`: `vertices_disjoint_reverseBranch`, `mem_vertices_or_mem_reverseBranch`, `vertices_union_reverseBranch`, `occupied_or_reverse_occupied` | The fixed positive pile rules out both sides being empty. |
| Lemma `upper-support`, retained paths | `TreeStack/Support.lean`: `SupportEdge`, `reverse_child_occupied_of_supportEdge`, `child_supportEdge_iff_occupied_of_supportEdge`, `supportDescent_of_mem_pos` | Prose's unique-path argument is the graph form of the formal recursive retained descent. |
| Lemma `upper-support`, terminal retained vertex is occupied | `TreeStack/Support.lean`: `exists_child_supportEdge_of_supportEdge_of_root_not_pos`, `root_pos_of_supportEdge_of_no_child_supportEdge` | No graph or configuration is transported to a support subtype. |
| Local effective-input equations | `TreeStack/Defect.lean`: `defect_equations_of_both_occupied` | These equations are used only on retained edges. |
| Lemma `upper-classification` | `TreeStack/Transfer.lean`: `F_neg_iff`, `F_eq_neg_odd_iff`, `F_eq_nonneg_iff`; `TreeStack/Defect.lean`: `defect_left_nonneg`, `defect_not_both_nonneg`, `defect_two_negative`, `defect_edge_classification` (these declarations are directly in `TreeStack`) | The zero target has only preimage 3; the extra tail defect 3 requires a positive forward message. |
| Genuine classified support edges | `TreeStack/Support.lean`: `defectEdgeState_of_supportEdge`, `DefectArrow`, `DefectiveSupportEdge` | The exceptional nondefective oriented state may still have a positive tail defect. |
| Defective-edge forest | `TreeStack/ForestOwner.lean`: `defectiveGraph_le_tree`, `defectiveGraph_isAcyclic` | The formal owner is then fixed on all ambient edges, not independently in each forest component. |
| Lemma `upper-owners` | `TreeStack/ForestOwner.lean`: `rootedOwner`, `rootedOwner_dist_eq_rootedOther_add_one`, `eq_of_adj_owner_of_dist`, `edge_eq_of_rootedOwner_eq`, `rootedOwner_eq_parent_of_mem_vertices`; `TreeStack/GlobalCharge.lean`: `edgeOwner_injective` | All ambient edges have distinct farther-endpoint owners. |
| Auxiliary orientation | `TreeStack/Auxiliary.lean`: `TwoNegativeOwnerArrow`, `AuxArrow`, `auxArrow_supportEdge`, `not_auxArrow_reverse`, `auxArrow_transGen_irrefl` | Every forced oriented edge is included, even with zero excess; only defective two-negative edges are directed. |
| Heights and doubling | `TreeStack/Auxiliary.lean`: `auxHeight`, `auxHeight_succ_le_of_auxArrow`, `auxHeight_eq_zero_of_no_incoming`, `auxWeight`, `two_mul_auxWeight_le_of_auxArrow` | Formal height is the well-founded maximum of predecessor heights plus one. |
| Empty-side endpoint has weight one | `TreeStack/Auxiliary.lean`: `no_auxArrow_to_root_of_not_occupied`, `auxWeightInt_eq_one_of_not_occupied` | The last claim of the support-separation lemma supplies the corresponding elementary graph argument. |
| Lemma `upper-retained-charge`, oriented case | `TreeStack/DefectCharge.lean`: `oriented_edge_excess_bound`, `oriented_excess_le_tail_budget`, `oriented_excess_le_head_budget` (directly in `TreeStack`); `TreeStack/AuxiliaryCharge.lean`: `defectArrow_auxEdgeContribution_le_tail_charge`, `defectArrow_auxEdgeContribution_le_head_charge` | Either endpoint budget can pay oriented excess, so fixed rooted ownership is valid. |
| Lemma `upper-retained-charge`, two-negative case | `TreeStack/DefectCharge.lean`: `two_negative_edge_excess_eq`, `two_negative_excess_le_owner_budget` (directly in `TreeStack`); `TreeStack/AuxiliaryCharge.lean`: `twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge` | The directed head is the owner, and doubling pays its two-negative excess. |
| Nondefective retained edges | `TreeStack/AuxiliaryCharge.lean`: `defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero`, `nondefectiveSupportEdge_auxEdgeContribution_le_baseline`, `supportEdge_auxEdgeContribution_le` | No charge is incurred for neutral or zero-head-defect oriented edges. |
| Lemma `upper-empty-charge` | `TreeStack/AuxiliaryCharge.lean`: `auxEdgeContribution_eq_emptySide_charge`, `rootedOwner_eq_emptySide_of_root_pos` | Exact cancellation by the empty-side endpoint defect, distinct from retained-state classification. |
| Two distinct charge definitions | `TreeStack/AuxiliaryCharge.lean`: `retainedDefectCharge`, `emptyBoundaryCharge`, `auxEdgeContribution_le_endpoint_add_separated_charges` | The two charges cannot apply simultaneously to one edge. |
| Proposition `upper-weighted`, score identity | `TreeStack/GlobalCharge.lean`: `auxWeightedMass_eq_edges_sub_defect`, `sum_edgeEndpointWeight_eq_auxDegreePotential` | Darts and finite-edge indexing implement grouping messages into unordered edge contributions. |
| Proposition `upper-weighted`, injective sum | `TreeStack/GlobalCharge.lean`: `sum_edgeOwner_charge_le_auxDefectBudget`, `sum_edgeSeparatedCharge_le_auxDefectBudget`, `auxWeightedMass_le_auxDegreePotential` | The omitted owner budget at the occupied ambient root is nonnegative. |
| Lemma `upper-leaf-slack` | `TreeStack/LeafSlack.lean`: `leaf_pos_of_auxWeightInt_ne_one`, `leafWeightSlackTerm_le_configurationSlackTerm`, `auxLeafSlack_le_auxConfigurationSlack`, `mass_le_auxCompactPotential` | Only ambient leaves of nonunit weight must be occupied. |
| Lemma `upper-source-partition` | `TreeStack/HeightSource.lean`: `exists_auxHeight_predecessor_of_pos`, `auxParent`, `auxSourceWalk_isPath`, `auxSourceWalk_length`, `auxHeight_eq_dist_auxSource`, `auxSource_eq_of_mem_auxSourceWalk_support`; `TreeStack/Consolidation.lean`: `auxSourceFiber_treePathConnected`, `auxSourceFiber_heightDominated_of_nonempty` | Fixed height-realizing predecessor choices give connected source fibres and exact local distance heights. |
| Lemma `upper-merge` | `TreeStack/Consolidation.lean`: `dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers`, `treePathConnected_union_of_adj`, `exists_heightDominatingRoot_union_of_adj` | Boundary-depth comparison preserves domination pointwise, not merely a weighted sum. |
| Proposition `upper-consolidation` | `TreeStack/Consolidation.lean`: `exists_adj_mem_not_mem_of_nonempty_ne_univ`, `exists_global_heightDominatingRoot_from_sourceCarrier`, `exists_root_auxHeight_le_dist` | Prose merges two adjacent parts successively; Lean grows one connected union by adjoining an entire source fibre. Both apply the same domination lemma and terminate by decreasing a finite number of parts/sources. |
| Root-independent estimator decomposition | `TreeStack/LeafSlack.lean`: `rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential` | Includes the degree-one root case. |
| Theorem `mass-bound` | `TreeStack/UpperBound.lean`: `exists_root_auxCompactPotential_le_rootEstimate_sub_one`; `mass_add_one_le_estim_of_all_scores_nonpos`, `mass_le_estim_sub_one_of_all_scores_nonpos` (last two directly in `TreeStack`) | Positive mass chooses an occupied ambient root; zero mass is separate. |
| Non-stackability and threshold consequences | `TreeStack/UpperBound.lean`: `nonstackable_mass_le_estim_sub_one`, `universalStackable_estim` (directly in `TreeStack`) | Uses the previously established exact rooted-score criterion. |

`TreeStack/Boundary.lean` proves the branch-message boundary invariant used
upstream by that score criterion. It is not the file implementing the
upper-bound EMPTY-boundary cancellation: that cancellation is in
`AuxiliaryCharge.lean`. The upper section therefore does not import an
unstated pruning or estimator-monotonicity argument from the older prose
notes.
