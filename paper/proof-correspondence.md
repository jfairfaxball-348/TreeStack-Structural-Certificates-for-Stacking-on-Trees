# Paper-to-Lean correspondence

This is an adversarial cross-check of the central mathematical claims in the
paper against the checked declarations in the current Lean development. The
paper's `EMPTY` is `Option.none`; an occupied branch always has a `some d`
message, and `messageContribution` is used only when a numerical sum is
formed.

| Paper statement | Checked declarations |
| --- | --- |
| Configurations, legal moves, positive stacks, reachability, exact-size universality | `Configuration`, `mass`, `support`, `FiniteTree` in `TreeStack/Basic.lean`; `move`, `PebbleStep`, `Reach`, `StackedAt`, `StackableAt`, `Stackable`, `UniversalStackable`, `mass_move_add_one` in `TreeStack/PebblingMove.lean` |
| Source estimator and the lower bound `E_T(r) >= card V + 1` | `leafVertices`, `sigmaVertices`, `leafCount`, `sigma`, `rootEstimate`, `estim`, `sigma_corrected_expansion`, `rootEstimate_corrected_expansion`, `card_add_one_le_rootEstimate`, `rootEstimate_le_estim`, `card_add_one_le_estim` in `TreeStack/Estimator.lean` |
| Root-independent leaf-count form of the estimator (`eq:compact-estimator`) | `rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential` in `TreeStack/LeafSlack.lean`; the paper's two-case proof separately retains a degree-one root |
| The transfer function and the one-vertex flux inequality | `TreeStack.F`, `F_of_le_one`, `F_sub_three_le`, `one_vertex_flux_le`, `one_vertex_flux_mod_three`, `F_sub_three_mul_le`, `F_sub_three_mul_mod_three` in `TreeStack/Transfer.lean` and `TreeStack/Boundary.lean` |
| `EMPTY` versus integer zero | `Message`, `EMPTY`, `empty_ne_integer_zero` in `TreeStack/Transfer.lean`; `Occupied`, `messageContribution`, `branchMessage`, `branchMessage_eq_empty_iff`, `branchMessage_eq_some_of_occupied` in `TreeStack/Message.lean` |
| Exact boundary invariant, including arbitrary legal order and empty excursions | `MoveSignature.CausalOutward`, `MoveSignature.EmptyExcursion`, `signature_branchFlux_bounds`, `ClearOutcome.boundary_le_message`, `ClearOutcome.no_positive_boundary_of_message_nonpos`, `boundary_attainment`, `exactBoundaryInvariant` in `TreeStack/Boundary.lean` |
| Safe constructive order of occupied branches | `orderedTasks_safe`, `executeAllOccupiedChildren`, `attainRootTransfer_even`, `attainRootTransfer_odd`, `boundary_attainment` in `TreeStack/Boundary.lean`; `executeAllRootTasks` in `TreeStack/RootScore.lean` |
| Rooted score and exact stackability | `score`, `stackableAt_of_score_pos`, `score_pos_of_stackableAt`, `stackableAt_iff_score_pos`, `not_stackable_iff_all_scores_nonpos` in `TreeStack/RootScore.lean` |
| Explicit obstruction | `obstruction`, `mass_obstruction`, `obstructionHeight`, `obstructionHeight_pos`, `obstructionHeight_eq_one_add_two_mul_internalPotential`, `sum_root_obstructionHeight_eq_sigma_sub_one`, `obstruction_branchMessage`, `obstruction_score_root_of_parent_score_zero`, `obstruction_score_selected_root`, `obstruction_scores_zero_on_vertices`, `obstruction_score_eq_zero`, `obstruction_not_stackable`, `exists_rootEstimate_eq_estim`, `exists_nonstackable_mass_estim_sub_one` in `TreeStack/Obstruction.lean` |
| Retained support and the fact that integer edge equations are used only when both sides are occupied | `SupportEdge`, `reverse_child_occupied_of_supportEdge`, `child_supportEdge_iff_occupied_of_supportEdge`, `defectEdgeState_of_supportEdge`, `exists_other_occupied_of_all_scores_nonpos` in `TreeStack/Support.lean` |
| Defect equations and oriented/two-negative classification | `defect_left_nonneg`, `defect_right_nonneg`, `defect_not_both_nonneg`, `defect_two_negative`, `defect_edge_classification`, `defect_left_budget`, `defect_right_budget` in `TreeStack/Defect.lean` |
| Ownership and acyclicity | `rootedOwner`, `rootedOwner_dist_eq_rootedOther_add_one`, `edge_eq_of_rootedOwner_eq`, `defectiveGraph_isAcyclic`, `edgeOwner_injective` in `TreeStack/ForestOwner.lean` and `TreeStack/GlobalCharge.lean` |
| Auxiliary directions, heights and powers-of-two doubling | `AuxArrow`, `auxArrow_supportEdge`, `not_auxArrow_reverse`, `auxArrow_transGen_irrefl`, `auxHeight`, `auxHeight_succ_le_of_auxArrow`, `auxWeightInt`, `two_mul_auxWeightInt_le_of_auxArrow` in `TreeStack/Auxiliary.lean` |
| Retained and empty-boundary charge cancellation | `oriented_edge_excess_bound`, `oriented_excess_le_tail_budget`, `oriented_excess_le_head_budget`, `two_negative_edge_excess_eq`, `two_negative_excess_le_owner_budget` in `TreeStack/DefectCharge.lean`; `auxiliaryState_auxEdgeContribution_le_rootedOwner_charge`, `auxEdgeContribution_eq_emptySide_charge`, `auxEdgeContribution_le_endpoint_add_separated_charges` in `TreeStack/AuxiliaryCharge.lean` |
| Weighted identity, injective cancellation and ambient leaf slack | `auxWeightedMass_eq_edges_sub_defect`, `sum_edgeSeparatedCharge_le_auxDefectBudget`, `auxWeightedMass_le_auxDegreePotential`, `auxWeightedMass_sub_configurationSlack_eq_mass`, `auxLeafSlack_le_auxConfigurationSlack`, `mass_le_auxCompactPotential` in `TreeStack/GlobalCharge.lean` and `TreeStack/LeafSlack.lean` |
| Consolidation to one ambient root | `auxSourceFiber_treePathConnected`, `auxSourceFiber_heightDominated_of_nonempty`, `exists_heightDominatingRoot_union_of_adj`, `exists_global_heightDominatingRoot_from_sourceCarrier`, `exists_root_auxHeight_le_dist` in `TreeStack/HeightSource.lean` and `TreeStack/Consolidation.lean` |
| Conversion to the source estimator, exact-size universality and final equality | `rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential`, `mass_add_one_le_estim_of_all_scores_nonpos`, `mass_le_estim_sub_one_of_all_scores_nonpos`, `nonstackable_mass_le_estim_sub_one`, `universalStackable_estim`, `universal_stackable_mono`, `estim_le_of_stackingCandidate`, `stack_eq_estim_of_two_le_card` in `TreeStack/LeafSlack.lean`, `TreeStack/UpperBound.lean` and `TreeStack/Stacking.lean` |
| Exact-size upward closure on a connected graph (`lem:upward`) | `not_stackable_oneOn_of_two_le_card`, `universal_stackable_gt_card`, `exists_two_le_of_card_lt_mass`, `universal_stackable_succ` in `TreeStack/PebblingMove.lean`; `universal_stackable_mono` in `TreeStack/Stacking.lean` |
| Extremal zero-score equality (`cor:zero-extremal`) | A stated consequence, not a separately named Lean theorem: combine `obstruction_score_eq_zero`, `mass_obstruction`, `exists_rootEstimate_eq_estim`, `not_stackable_iff_all_scores_nonpos` and `nonstackable_mass_le_estim_sub_one` |

The cross-check specifically confirms the following semantic points. Scores and
defects use strict positivity and nonpositivity exactly as stated. The
stacking predicate is exact-size, and its threshold has the source lower cut
off `t >= 2`. The singleton tree is excluded from the headline theorem. The
upper-bound argument remains on the ambient tree: nonretained edges are not
converted into integer zero-message edges, their empty-side charge is handled
separately, and occupied-leaf slack is applied only where the auxiliary weight
is greater than one. The auxiliary arrow points from the lower-height endpoint
to the higher-height endpoint, so the paper's inequality is
`A_v >= 2 A_u` on an arrow `u -> v`. The final estimator identity includes
the degree-one-root case.

The independent first-half audit also checked the following details against
the declaration statements and their proofs:

- The boundary theorem is a theorem on the induced subtree consisting of the
  branch and its boundary vertex. Its flux lemma permits arbitrary moves
  elsewhere. Causality supplies at least one outward move from each initially
  occupied cleared subbranch; balance equations alone would not suffice.
- For an initially empty branch the paper sums its balance equations and uses
  alternating signs to obtain a nonpositive multiple of three. This is a
  direct alternative derivation of the empty-branch conclusion in
  `signature_branchFlux_bounds`. It does not assume the branch stays empty
  throughout the sequence.
- The three input ranges in the constructive boundary proof agree with
  `boundary_attainment`. Every task requires a strictly positive final
  boundary pile. An occupied branch with zero integer message is therefore
  processed only with a positive boundary pile; empty branches may be left
  alone.
- The recursive obstruction height concerns a nonroot descendant branch.
  Its leaves are degree-one vertices in the ambient tree, and its closed form
  uses ambient degrees and distances. The opposite side is occupied because
  the selected root has a positive pile on a nontrivial tree.
- Natural subtraction in `sigma - 1` and `estim - 1` is legitimate in the
  paper's ordinary integer equalities: `sigma >= 1` directly, and on a
  nontrivial tree `estim >= card V + 1 >= 3`.
- The zero configuration is covered by the rooted equivalence: it has score
  zero and is not stackable. The rooted theorem itself also holds for a
  singleton tree. The estimator lower bound and headline equality require
  nontriviality. The separately stated singleton convention follows directly
  from the definitions; it is not attributed to the headline Lean theorem.
- The obstruction alone does not prove the lower bound for an exact-size
  threshold. The paper includes and uses `lem:upward` before concluding the
  equality, matching the formal dependency through
  `estim_le_of_stackingCandidate`.

The citations in the introduction match the verified records in
`literature-and-submission-audit.md`: the conjecture and computational range
are attributed to Csernák--Soukup, and the cover-pebbling comparison concerns
an extremal initial distribution rather than the paper's final-support
condition. No mathematical defect was found in the first-half review; its
only source amendment clarified the domain of the boundary theorem.

The formal theorem is checked with no project axioms or proof holes. The
theorem-level audit permits only Lean's standard `propext`, `Quot.sound`, and
`Classical.choice`, as recorded by `Audit.lean` and `formalization.yaml`.
