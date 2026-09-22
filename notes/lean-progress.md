# Lean formalization progress

Status: **the exact branch-boundary invariant, rooted score characterization,
and explicit estimator obstruction are merged on `main`; the local
arbitrary-defect edge classification for the upper bound is now machine-checked
in PR #13.**  The authoritative pre-PR #13 baseline is merge commit
`525e4568017856bd3db87128bd0039de22ae68f3`.

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

The lower-bound obstruction is complete on `main`.  PR #13 adds the
machine-checked local arbitrary-defect classification needed by the upper
bound.

## Next formal frontier

The explicit estimator obstruction supplies the machine-checked lower bound,
and the local arbitrary-defect edge states are now classified.  The remaining
Lean work is the global upper-bound layer: support pruning and estimator
monotonicity under adjoining leaves; defective-edge owner assignment;
auxiliary orientations and heights; weighted defect cancellation;
occupied-leaf slack; connected-partition consolidation; and finally the
global bound `mass C ≤ estim T - 1` for every non-stackable configuration.

The Csernák–Soukup tree-stacking conjecture is therefore **not yet fully
formalized in Lean**, but the lower-bound obstruction is no longer an open
formal obligation.
