# Lean formalization progress

Status: **Phase 1 exact branch-boundary invariant proved in Lean on PR #8.**
The recursive message necessity layer, occupied-child scheduling, constructive
attainment, universal boundary upper bound, and nonpositive impossibility are
all machine-checked.  The next unproved layer is the rooted score
characterization
`StackableAt T.graph C r ↔ 0 < score T C r`.

## Pinned environment and baseline

This slice started from `main` at merge commit
`04e6bd9653ed35e320e99e2d104ca659845ab11a`, the merge of PR #7,
“Lean: exact boundary necessity, scheduling, and child separation.”

- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- Namespace: `TreeStack`

The source semantics are unchanged.  In particular,
`UniversalStackable G t` still means exact-size universality, and
`EMPTY = none` remains categorically different from `some 0`.

## Exact boundary theorem

`TreeStack/Boundary.lean` retains the target proposition

```text
ExactBoundaryInvariant C B
```

and now proves it as

```text
OrientedBranch.exactBoundaryInvariant :
  ExactBoundaryInvariant C B
```

for every finite-tree configuration and oriented branch.

For an occupied branch with recursive message `some d`, this theorem
machine-checks all three audited clauses:

1. if `0 < q + d`, a legal branch-local clearing exists whose final external
   boundary pile is exactly `q + d`;
2. every legal clearing has final boundary pile at most `q + d`;
3. if `q + d ≤ 0`, no legal clearing can leave a positive boundary pile.

The upper-bound and nonpositive clauses continue to come from the previously
proved move-signature necessity layer:

```text
ClearOutcome.boundary_le_message
ClearOutcome.no_positive_boundary_of_message_nonpos
```

The new constructive half is

```text
OrientedBranch.boundary_attainment
```

and is well-founded by the existing strict child-cardinality theorem
`childBranch_card_lt`.

## Constructive child scheduler

The construction enumerates only occupied genuine child branches.  The task
type itself contains an occupancy proof, so a configuration-empty child cannot
be represented as an executable zero-gain task.

New supporting declarations include:

```text
OccupiedChild
occupiedChildTasks
taskGainSum_occupiedChildTasks
executeOccupiedTaskSchedule
executeAllOccupiedChildren
```

The sum of executable task gains is proved equal to `childMessageSum`.
The existing `orderedTasks_safe` theorem is then applied to the occupied
task list.

Sibling independence is formal rather than implicit.  The construction uses
and extends the checked locality/separation layer, including:

```text
branchMessage_congr_vertices
BranchReach.eq_of_not_mem_carrier
childBranch_carrier_subset
childBranch_vertices_disjoint
exists_childBranch_mem_of_mem_vertices_ne_root
parent_not_mem_childBranch_carrier
BranchReach.of_child
```

Thus clearing an earlier sibling cannot change a later sibling's interior or
recursive message.

## Explicit root/boundary attainment

After all occupied children have been cleared, every non-root branch vertex is
zero and the construction reduces to the branch root and its external
boundary.

`BranchReach.repeat_move` supplies exact legal repeated moves along one
oriented edge.  The endpoint construction is split into explicit audited
cases:

```text
attainRootTransfer_even
attainRootTransfer_odd
attainRootTransfer_ge_two
```

For effective input at least two, the proof performs the exact outward/inward
sequence realizing `F`.  The odd case explicitly handles whether the
external boundary initially has a pebble.

For effective input at most one, `boundary_attainment` first preloads

```text
b = 2 - effectiveInput C B
```

pebbles at the root using exactly `b` inward boundary moves.  Positivity of
the requested final boundary value proves that these moves are affordable.
The occupied children are then executed in the audited task order, leaving
exactly two pebbles at the root; one final outward move realizes

```text
F x = 2*x - 3.
```

No balance-only or phantom sequence is used.

## Trust and validation status

There are no `sorry`, `admit`, or project-specific axioms in the project
Lean source.  The draft PR workflow rejects proof-hole tokens.

Draft Lean CI is green for commit
`0f9e5f7aeddd58a61b18a85fab70334a2822a2b1`, which includes the complete
constructive proof and `OrientedBranch.exactBoundaryInvariant`.
`Audit.lean` now prints axiom dependencies for the new construction and
checks the final theorem.

Before this slice is considered merged and complete, PR #8 must pass the full
repository validation path and the post-merge `main` workflow:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

Python computation remains regression/falsification evidence only and is not
used to discharge Lean obligations.

## Next formal frontier

Only after the exact-boundary PR is fully validated and merged should Phase 1
continue with the rooted score layer:

```text
StackableAt T.graph C r ↔ 0 < score T C r
```

The Csernák–Soukup tree-stacking conjecture is **not yet formally proved**.
The machine-checked milestone reached here is the complete recursive exact
boundary invariant on oriented branches.
