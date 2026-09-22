# Lean formalization progress

Status: **the complete Lean proof through the exact Csernák–Soukup stacking
equality is merged on `main`.** PR #17, “Lean: global defect cancellation to
exact stacking equality,” merged as
`2bffb748a3d56147e2561a6a026b497c99e15686`. The complete ready-PR workflow
passed as run #232 and the post-merge `main` workflow passed as run #233.
External human mathematical review of the completed result has also been
reported complete by the maintainer. The remaining project stages are Palomar
packaging/verification and publication preparation, not Lean proof repair.

## Pinned environment

- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- Namespace: `TreeStack`

The source semantics remain unchanged.  In particular,
`UniversalStackable G t` means exact-size universality and
`EMPTY = none` remains categorically different from `some 0`.
Python computations are regression/falsification evidence only.

## Merged exact-boundary milestone

PR #8, “Lean: exact boundary attainment,” merged as

`2d7911c28e31eef1e1e35f4221bd6c342ef93834`.

The complete PR workflow passed before merge, and the post-merge `main` push
workflow also passed completely.

`TreeStack/Boundary.lean` now proves

```text
OrientedBranch.boundary_attainment
OrientedBranch.exactBoundaryInvariant :
  ExactBoundaryInvariant C B
```

for every finite-tree configuration and oriented branch.

For an occupied branch with recursive message `some d`, the checked theorem
contains all three audited clauses:

1. if `0 < q + d`, there is a legal branch-local clearing whose final
   external boundary pile is exactly `q + d`;
2. every legal clearing leaves at most `q + d` at the boundary;
3. if `q + d ≤ 0`, no legal clearing can leave a positive boundary pile.

The construction enumerates only occupied genuine child branches.  Empty
children are omitted from the executable task list; they are never represented
as zero-gain tasks.  Supporting checked declarations include

```text
exists_childBranch_mem_of_mem_vertices_ne_root
parent_not_mem_childBranch_carrier
BranchReach.repeat_move
taskGainSum_occupiedChildTasks
executeOccupiedTaskSchedule
executeAllOccupiedChildren
attainRootTransfer_even
attainRootTransfer_odd
attainRootTransfer_ge_two
```

together with the earlier locality, separation, signature, and necessity
lemmas.  The low-input construction explicitly preloads the root from the
external boundary; the high-input construction uses explicit legal repeated
moves.  No balance-only phantom sequence is used.

## Merged rooted score milestone

PR #9, “Lean: rooted score characterization,” merged as

`fd6f7a90111f0a6424510792fa7c0b8dcdfcbfab`.

The complete PR workflow passed before merge, and the post-merge `main` full
workflow also passed completely.

A new file `TreeStack/RootScore.lean` defines the exact rooted score from
incident oriented branch messages:

```text
incidentBranch
rootMessageTerm
rootMessageSum
score
```

with configuration-empty incident branches contributing no integer summand
while remaining message-level `EMPTY`.

Occupied incident branches are represented by a task subtype, so an empty
branch cannot become an executable zero-gain task:

```text
RootTask
rootTasks
taskGainSum_rootTasks
```

The constructive direction is checked through

```text
executeRootTaskSchedule
executeAllRootTasks
stackableAt_of_score_pos
```

using the same audited positive/zero/negative scheduler and the merged exact
branch-boundary attainment theorem.  Incident branch disjointness/locality
proves that clearing one branch does not alter a later branch's message.

For necessity, `Reach.exists_moveSignature` extracts a global oriented
move-count signature from an arbitrary legal reach.  The proof applies
`OrientedBranch.signature_branchFlux_bounds` independently to every incident
branch.  Occupied branch flux is bounded by its recursive integer message;
an initially empty incident branch has nonpositive flux `-3k`.  Summing these
bounds at the target root gives the rooted upper bound without projecting an
interleaved global move sequence into separate branch sequences.

The main checked rooted statements are

```text
score_pos_of_stackableAt
stackableAt_iff_score_pos :
  StackableAt T.graph C r ↔ 0 < score T C r

not_stackable_iff_all_scores_nonpos :
  ¬ Stackable T.graph C ↔ ∀ r, score T C r ≤ 0
```

The rooted proof, its `Audit.lean` axiom checks, the complete repository
workflow, and the post-merge `main` workflow are all green.

## Explicit estimator obstruction milestone

`TreeStack/Obstruction.lean` now defines the explicit rooted obstruction

```text
obstruction T r
```

with `sigma T r - 1` pebbles at the selected root, one pebble at every other
leaf, and zero elsewhere.  Its mass is checked exactly:

```text
mass_obstruction :
  mass (obstruction T r) = rootEstimate T r - 1
```

For an oriented branch lying away from the selected root, the development
defines a well-founded recursive obstruction height and proves both its closed
form and its exact recursive message:

```text
OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential
OrientedBranch.obstruction_branchMessage
```

The incident branches at the selected root are partitioned explicitly, their
closed-form heights sum to `sigma T r - 1`, and the root score therefore
cancels exactly.  A reverse-edge score decomposition then propagates score zero
recursively through every descendant branch.  The main checked statements are

```text
sum_root_obstructionHeight_eq_sigma_sub_one
obstruction_score_selected_root
OrientedBranch.obstruction_scores_zero_on_vertices
obstruction_score_eq_zero :
  score T (obstruction T r) v = 0

obstruction_not_stackable :
  ¬ Stackable T.graph (obstruction T r)
```

Finally, the finite maximum defining `estim` is shown to be attained and,
for a nontrivial finite vertex type, the formal lower-bound witness is:

```text
exists_nonstackable_mass_estim_sub_one :
  ∃ C : Configuration V,
    mass C = estim T - 1 ∧
      ¬ Stackable T.graph C
```

This closes the explicit-obstruction/lower-bound layer without conflating
`EMPTY` with integer zero.

## Arbitrary-defect edge classification milestone

`TreeStack/Defect.lean` formalizes the local edge algebra used in the
arbitrary-defect upper-bound proof.  For nonnegative endpoint defects satisfying

```text
a = F (-δu - b)
b = F (-δv - a)
```

the development proves the two oriented cases and the two-negative case are
exhaustive:

```text
defect_left_nonneg
defect_right_nonneg
defect_not_both_nonneg
defect_two_negative
defect_edge_classification
```

The oriented cases also expose the endpoint budget inequalities needed later
for edge-excess charging:

```text
defect_left_budget  : 2 * δv ≤ δu
defect_right_budget : 2 * δu ≤ δv
```

The abstract classification is connected back to the actual TreeStack
recursion rather than left as standalone arithmetic.  The new score defect is

```text
scoreDefect T C v = - score T C v
```

and, whenever both sides of an oriented tree edge are occupied,
`OrientedBranch.defect_equations_of_both_occupied` derives the two defect
equations directly from the exact branch messages and the reverse-edge score
decomposition.  Consequently

```text
OrientedBranch.defectEdgeState_of_scores_nonpos
```

classifies the actual pair of recursive messages whenever both edge sides are
occupied and both endpoint scores are nonpositive.

This closes the local arbitrary-defect edge-classification obligation.  It
does **not** yet prove the global estimator upper bound: support pruning must
first ensure that the surviving edge sides are occupied, after which the
owner assignment, auxiliary orientation/height, weighted defect cancellation,
occupied-leaf slack, and connected-partition consolidation remain to be
formalized.

## In-place support-reduction core

PR #14 introduces `TreeStack/Support.lean`.  Rather than transporting
configurations, recursive messages, rooted scores, and estimators to a subtype
of vertices, the development keeps the original finite vertex type and
characterizes the retained support core directly by occupied edge sides.

For every oriented tree edge, the two deleted-edge components are now proved to
be disjoint and exhaustive:

```text
OrientedBranch.vertices_disjoint_reverseBranch
OrientedBranch.mem_vertices_or_mem_reverseBranch
OrientedBranch.vertices_union_reverseBranch
```

The symmetric retained-edge predicate is

```text
OrientedBranch.SupportEdge C B :=
  B.Occupied C ∧ B.reverseBranch.Occupied C

OrientedBranch.supportEdge_reverse_iff
```

so every retained edge satisfies exactly the two-sided occupation hypothesis
needed by the merged defect classification.  The direct bridge is

```text
OrientedBranch.defectEdgeState_of_supportEdge
```

under all-nonpositive rooted scores.

Empty exterior support retains the message-level EMPTY semantics.  In
particular,

```text
OrientedBranch.score_eq_effectiveInput_of_reverse_not_occupied
```

uses `branchMessage = EMPTY`; no `some 0` surrogate is introduced.

Two further pruning facts are machine-checked.  A configuration whose positive
support is contained in one vertex has rooted score equal to the pile at that
vertex,

```text
score_eq_of_support_subset_singleton
```

and therefore an all-nonpositive-score configuration with a positive pile has
a second distinct occupied vertex:

```text
exists_other_occupied_of_all_scores_nonpos
```

Finally, a retained support edge whose root has no retained child edge must
have an occupied root:

```text
OrientedBranch.root_pos_of_supportEdge_of_no_child_supportEdge
```

This is the in-place leaf-occupancy statement needed for the later leaf-slack
argument.  It gives the key pruning semantics without introducing subtype
transport obligations.  A remaining structural packaging step is to organize
the retained `SupportEdge` edges as the connected support core (or prove the
equivalent path/forest facts directly) before the global defect-flow argument.

## Retained path closure, forced orientations, and rooted owners

PR #15 packages the retained `SupportEdge` predicate into the path/edge facts
needed by the global defect-flow proof while continuing to avoid subtype
transport.

Below a retained edge, its occupied reverse side supplies exterior support for
every genuine child edge.  Consequently child retention is characterized
exactly by child-side occupation:

```text
OrientedBranch.reverse_child_occupied_of_supportEdge
OrientedBranch.child_supportEdge_iff_occupied_of_supportEdge
```

The new inductive certificate

```text
OrientedBranch.SupportDescent
```

records a descent from an oriented-branch root through retained child edges.
The recursive theorem

```text
OrientedBranch.supportDescent_of_mem_pos
```

shows that every positive-support vertex on the retained side of an edge is
joined to the edge root entirely through retained support edges.  Together with

```text
OrientedBranch.exists_child_supportEdge_of_supportEdge_of_root_not_pos
OrientedBranch.root_pos_of_supportEdge_of_no_child_supportEdge
```

this gives the in-place connected/path-closure and leaf-occupancy interface
needed from the minimal subtree spanning the positive support.

The first global orientation interface is also now formalized.  A forced
oriented-type edge is represented by

```text
OrientedBranch.DefectArrow
```

meaning a retained edge whose displayed recursive message is nonnegative.
Under all-nonpositive scores the reverse message is strictly negative, the
reverse orientation cannot also be a `DefectArrow`, and the tail defect has
the required factor-two budget:

```text
OrientedBranch.reverse_message_neg_of_defectArrow
OrientedBranch.not_defectArrow_reverse
OrientedBranch.defectArrow_tail_budget
OrientedBranch.supportEdge_defectArrow_or_reverse_or_both_neg
```

PR #15 also adds `TreeStack/ForestOwner.lean`.  Instead of separately rooting
each defective-forest component, it fixes one ambient tree root and assigns
every tree edge to its endpoint farther from that root:

```text
OrientedBranch.rootedOwner
OrientedBranch.rootedOther
OrientedBranch.rootedOther_adj_rootedOwner
OrientedBranch.rootedOwner_dist_eq_rootedOther_add_one
OrientedBranch.rootedOwner_other_edge
OrientedBranch.eq_of_adj_owner_of_dist
OrientedBranch.edge_eq_of_rootedOwner_eq
OrientedBranch.rootedOwner_reverse
```

The key theorem `edge_eq_of_rootedOwner_eq` proves injectivity on underlying
undirected tree edges.  Therefore its restriction to any defective-edge subset
is the required injective incident-owner assignment; no separate
forest-component rooting theorem is needed.

The defective subset is now explicit and orientation invariant:

```text
OrientedBranch.DefectiveSupportEdge
OrientedBranch.defectiveSupportEdge_reverse_iff
OrientedBranch.defectiveGraph
OrientedBranch.defectiveGraph_le_tree
OrientedBranch.defectiveGraph_isAcyclic
```

`defectiveGraph_isAcyclic` proves the defective retained edges form a forest
simply because their graph is a spanning subgraph of the ambient tree.

A new file `TreeStack/DefectCharge.lean` also formalizes the local weighted
edge estimates that the future auxiliary-height construction will feed:

```text
oriented_edge_excess_bound
oriented_excess_le_tail_budget
oriented_excess_le_head_budget
two_negative_edge_excess_eq
two_negative_excess_le_owner_budget
```

Thus, once a directed auxiliary edge supplies the doubling relation between
endpoint weights, oriented-type excess can be paid by either endpoint and a
two-negative edge oriented toward its owner can be paid by that owner's defect.

This in-place architecture removes the need to transport configurations,
messages, scores, and defect states to a subtype-valued support tree.

The preferred remaining route is now **ambient-tree throughout**.  The
auxiliary height is defined on every ambient vertex and is zero off the
directed defective structure, hence its weight there is exactly one.  This
makes a separate estimator-monotonicity theorem for a subtype support core
unnecessary provided the next global summation proves the baseline edge bound
for nondefective/nonretained ambient edges and performs leaf slack only where
the auxiliary weight exceeds one.  An ambient leaf with weight greater than
one lies on a directed defective retained edge, so the existing retained-leaf
occupancy machinery is the relevant source of slack.  The next session should
therefore pursue this ambient-tree summation first; only revive a separate
support-core estimator comparison if a concrete Lean obstruction forces it.


## Auxiliary orientation and height milestone (PR #16)

PR #16 builds the global directed layer directly on the ambient tree.

The two-negative state is now connected to the fixed rooted owner in precisely
the orientation required by the charging algebra:

```text
OrientedBranch.two_negative_parameters_toward_rootedOwner
OrientedBranch.TwoNegativeOwnerArrow
```

The combined defective-edge relation is

```text
OrientedBranch.AuxArrow
OrientedBranch.auxArrow_or_reverse_of_defectiveSupportEdge
OrientedBranch.auxArrow_defectiveGraph
OrientedBranch.not_auxArrow_reverse
```

A direct deleted-edge cut argument proves that an auxiliary arrow cannot have a
directed return path across the same ambient tree edge.  Consequently:

```text
OrientedBranch.auxArrow_no_reflTransGen_reverse
OrientedBranch.auxArrow_transGen_irrefl
```

No separate defective-forest component rooting is used.

Finite strict-predecessor sets give a topological recursion measure:

```text
OrientedBranch.auxPred
OrientedBranch.auxPred_ssubset_of_auxArrow
OrientedBranch.auxRank
OrientedBranch.auxRank_lt_of_auxArrow
```

The actual longest-directed-path height and powers-of-two weights are then
defined by well-founded recursion:

```text
OrientedBranch.auxHeight
OrientedBranch.auxHeight_succ_le_of_auxArrow
OrientedBranch.auxWeight
OrientedBranch.two_mul_auxWeight_le_of_auxArrow
OrientedBranch.auxWeightInt
OrientedBranch.two_mul_auxWeightInt_le_of_auxArrow
```

Thus every auxiliary edge `u → v` has the checked doubling inequality
`2 * A_u ≤ A_v`.

`TreeStack/AuxiliaryCharge.lean` instantiates the abstract inequalities from
`DefectCharge.lean` with these actual weights:

```text
OrientedBranch.auxEdgeContribution
OrientedBranch.defectArrow_auxEdgeContribution_le_tail_charge
OrientedBranch.defectArrow_auxEdgeContribution_le_head_charge
OrientedBranch.twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
OrientedBranch.auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
```

The last theorem is the local owner-paid form needed before summing globally:
for either a forced oriented-type edge or a two-negative owner arrow, the
weighted edge contribution is bounded by the two neutral endpoint weights plus
the defect charge at the fixed rooted owner.  The remaining global step must
sum these charges using `edge_eq_of_rootedOwner_eq` and handle neutral and
nonretained ambient edges.

## Validation and trust

There are no permitted `sorry`, `admit`, project axioms, weakened
definitions, or hidden computational assumptions.  The development workflow
rejects proof-hole tokens.

The authoritative complete validation path remains:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

All Lean layers through PR #17 are complete on `main`, including the
lower-bound obstruction, auxiliary orientation and charging machinery, global
weighted cancellation, arbitrary-defect upper bound, and final exact equality.

## PR #17 global upper bound and exact equality

The ambient-tree global proof is now implemented without subtype transport.
The critical charging architecture is:

```text
OrientedBranch.AuxArrow
OrientedBranch.retainedDefectCharge
OrientedBranch.emptyBoundaryCharge
OrientedBranch.sum_edgeSeparatedCharge_le_auxDefectBudget
OrientedBranch.auxWeightedMass_le_auxDegreePotential
```

Every forced `DefectArrow` participates in `AuxArrow`, including oriented
states with zero positive excess.  Only genuinely defective retained edges
receive `retainedDefectCharge`.  Nonretained edges are handled separately by
`emptyBoundaryCharge`, which is derived from the literal message-level
`EMPTY = none` case; it is never replaced by `some 0`.

The ordinary-mass conversion and ambient leaf slack are checked through:

```text
OrientedBranch.auxWeightedMass_sub_configurationSlack_eq_mass
OrientedBranch.auxLeafSlack_le_auxConfigurationSlack
OrientedBranch.mass_le_auxCompactPotential
OrientedBranch.rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
```

The last theorem explicitly separates the degree-one-root and internal-root
cases, so the source root convention is preserved.

Connected-partition consolidation remains entirely on the ambient vertex type.
Canonical height-zero source fibres are path connected; adjacent carriers can
be merged while preserving pointwise height domination.  The main declarations
are:

```text
OrientedBranch.exists_heightDominatingRoot_union_of_adj
OrientedBranch.exists_global_heightDominatingRoot_from_sourceCarrier
OrientedBranch.exists_root_auxHeight_le_dist
OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
```

These feed the global estimator upper bound and exact-size universality:

```text
mass_add_one_le_estim_of_all_scores_nonpos
mass_le_estim_sub_one_of_all_scores_nonpos
nonstackable_mass_le_estim_sub_one
universalStackable_estim
```

Finally, `TreeStack/Stacking.lean` defines the exact-size source stacking
number as the least `t >= 2` satisfying `UniversalStackable T.graph t`, proves
upward exact-size closure, combines the upper bound with the already-checked
`estim T - 1` obstruction, and proves:

```text
universal_stackable_mono
estim_stackingCandidate
stack_stackingCandidate
estim_le_of_stackingCandidate
stack_eq_estim
stack_eq_estim_of_two_le_card
```

The headline theorem is

```text
stack_eq_estim_of_two_le_card
    (T : FiniteTree V)
    (hcard : 2 <= Fintype.card V) :
    stack T = estim T
```

which explicitly excludes the one-vertex source-convention exception.

The final equality was introduced in commit
`16ad6a26b717346c759e5bdbd923f32542eb3772`; global theorem audits were
expanded through commit `274f17bc061b5c5e46441177a4e809f845f90925`;
the final draft compile repair is
`482eff2eff834edb27a51e058aa88723c7cac0b5`.  Draft workflow run #228 passed
the proof-hole guard and `lake build`.

## Remaining work

No mathematical Lean proof obligation remains. PR #17 and its post-merge
`main` validation are complete, and external human mathematical review has
been reported complete by the maintainer.

The active stage is Palomar packaging and mechanical verification. The
statement surface and preflight workflow are being prepared without changing
the mathematical source. A repository licence is still a maintainer legal
decision and must be selected before Palomar can pass its required root-licence
check. After a preflight-green immutable commit is frozen, the remaining stages
are the separate Palomar registration decision and research-paper/publication
work. No unsupported priority claim is made by the Lean development itself.
