# Lean formalization progress

Status: **the exact branch-boundary invariant, rooted score characterization,
explicit estimator obstruction, local arbitrary-defect edge classification,
and the in-place support-reduction core are merged on `main`.  PR #15 extends
that core with retained path closure, forced defect-edge orientations, and an
injective incident-owner assignment for arbitrary tree-edge subsets.**  The
authoritative baseline for PR #15 is the PR #14 merge commit
`53a57b2b21a9e2a8c714a9574587382b07c2d620`.

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
undirected tree edges.  Therefore its restriction to any later-defined
defective-edge subset is already the required injective incident-owner
assignment; no separate forest-component rooting theorem is needed.

This in-place architecture removes the need to transport configurations,
messages, scores, and defect states to a subtype-valued support tree.  It does
**not by itself remove every estimator comparison obligation**.  The current
mass/leaf-slack proof from `notes/defect-flow.md` still compares the potential
of the minimal support core with the estimator of the ambient tree.  Unless the
remaining upper-bound argument is reformulated wholly with ambient-tree
degrees/leaves, an explicit monotonicity/comparison lemma for the embedded
connected support core is still needed.  That comparison should be kept purely
combinatorial and independent of message transport.

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

The lower-bound obstruction, local arbitrary-defect classification, and PR #14
support-reduction core are complete on `main`.  PR #15 adds the machine-checked
retained-path closure, forced-orientation interface, and injective ambient-root
edge-owner mechanism needed for the next charging layer.

## Next formal frontier

The explicit estimator obstruction supplies the machine-checked lower bound,
the local arbitrary-defect edge states are classified, and retained
`SupportEdge` edges now have an in-place connected/path-closure interface.
Forced oriented-type edges and an injective incident-owner assignment are also
available.

The remaining Lean work is the global upper-bound layer: define the exact
defective retained-edge subset and connect its two-negative states to the owner
choice; establish the support-core estimator comparison still required by the
current proof architecture (or replace it with an equivalent ambient-tree
bound); orient owner-charged two-negative edges; define longest-directed-path
heights and prove the powers-of-two doubling inequality; formalize weighted
defect cancellation; prove occupied-leaf slack; formalize connected-partition
consolidation; and finally derive `mass C ≤ estim T - 1` for every non-stackable
configuration.

The Csernák–Soukup tree-stacking conjecture is therefore **not yet fully
formalized in Lean**, but the lower-bound obstruction is no longer an open
formal obligation.
