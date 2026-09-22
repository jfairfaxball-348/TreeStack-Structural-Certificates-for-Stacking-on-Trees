# Lean formalization progress

Status: **the exact branch-boundary invariant is merged on `main`, and the
rooted score characterization is machine-checked on draft PR #9.**  The rooted
slice still requires the complete PR workflow, merge, and post-merge `main`
validation before it is treated as the next authoritative baseline.

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

## Rooted score layer on PR #9

The focused branch is

`chatgpt/root-score-characterization`

and draft PR #9 is “Lean: rooted score characterization.”

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

Draft Lean CI passed for commit
`016bbba3c002cb60f567f7e8392bd8aebb62f289`, containing the complete rooted
proof.  `Audit.lean` is being extended to print axiom dependencies for this
layer before the PR is promoted to the complete workflow.

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

PR #9 is not considered complete until that full workflow is green, it is
merged into `main`, and the post-merge `main` workflow is also green.

## Next formal frontier

After PR #9 is fully validated and merged, the next proof layer from the
roadmap is the explicit estimator obstruction, followed by support pruning and
the arbitrary-defect estimator bound.

The Csernák–Soukup tree-stacking conjecture is **not yet formally proved**.
The strongest merged milestone at present is the complete exact branch-boundary
invariant; the rooted score theorem is the current integration milestone.
