# Lean formalization progress

Status: **the exact branch-boundary invariant and rooted score characterization
are merged on `main`; the explicit estimator obstruction and exact Lean
lower-bound witness are now formalized in PR #12.**  The merged rooted-score
baseline is `bea4d6dde1b75322b3db1ca8bee0813930d32ece`.

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

The rooted-score milestone is complete on `main`; future work should branch
from the authoritative merge commit above.

## Next formal frontier

The explicit estimator obstruction now supplies the machine-checked lower
bound.  The remaining Lean work is the global upper-bound layer: support
pruning and the arbitrary-defect estimator bound, followed by the final theorem
that every configuration of size `estim T` is stackable for every nontrivial
finite tree.

The Csernák–Soukup tree-stacking conjecture is therefore **not yet fully
formalized in Lean**, but the lower-bound obstruction is no longer an open
formal obligation.
