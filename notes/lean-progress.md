# Lean formalization progress

Status: **Phase 1 partial, sound and compiling through the recursive
move-signature upper bound, the necessity half of the exact boundary
invariant, audited child-task scheduling, configuration locality, and sibling
child-branch separation.**  The equality-attainment construction in the exact
boundary theorem and the rooted score characterization remain unproved in Lean.

## Session baseline and pinned environment

This phase extension started from `main` at merge commit
`ad37ae4f31de008cc5fff03d626a1405b4e268ff`, the merge of PR #5.

- Lean: `v4.34.0`
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`
- Lake manifest: committed at repository root
- Namespace: `TreeStack`

No existing semantics were weakened.  In particular,
`UniversalStackable G t` still quantifies over configurations of exactly
`t` pebbles, and `EMPTY : Option Int = none` remains a message state
categorically different from `some 0`.

## Definitions and theorem layer now available

The pre-existing files retain finite-tree/configuration semantics, legal
pebbling moves and finite reachability, the audited transfer function `F`,
the exact estimator, and deleted-edge oriented branches.

### Strict recursive branch geometry

For `B : OrientedBranch T` and `c : B.Child`, `TreeStack/Branch.lean`
now proves

```text
(B.childBranch c).vertices ⊆ B.vertices
(B.childBranch c).vertices ⊂ B.vertices
(B.childBranch c).card < B.card
```

via Mathlib reachability and bridge deletion in the acyclic tree.  The
cardinality decrease is relative to the parent branch, not merely relative to
the whole tree, and therefore supplies an honest well-founded recursion
measure.

Reusable boundary-separation lemmas are also proved:

- `edge_leaving_vertices_eq_boundary`: every tree edge leaving
  `B.vertices` is exactly the deleted boundary edge;
- `eq_root_of_mem_vertices_adj_parent`: the exterior parent has no neighbor
  in the branch other than `B.root`.

### Recursive branch message

`TreeStack/Message.lean` defines

- `OrientedBranch.Occupied C B`, meaning the configuration restriction to
  the branch has a positive pebble somewhere;
- `messageContribution : Message → Int`, used only when aggregating child
  messages;
- `branchMessage C B : Message`;
- `childMessageSum C B : Int`;
- `effectiveInput C B : Int`.

The recursive definition uses

```text
termination_by B.card
decreasing_by B.childBranch_card_lt ...
```

and therefore recurses only on strict child branches.  For occupied branches
Lean proves the audited equation

```text
branchMessage C B = some (F (effectiveInput C B)).
```

For configuration-empty branches Lean proves exactly

```text
branchMessage C B = EMPTY ↔ ¬ B.Occupied C.
```

Thus `EMPTY` has not been replaced by integer zero.  Its contribution to a
parent sum is zero only after explicitly applying `messageContribution`.

### Exact boundary-invariant statement layer

`TreeStack/Boundary.lean` introduces the static and legal-sequence objects
needed to state the next theorem without conflating balance feasibility with
legal scheduling:

- `MoveSignature`, `incoming`, `outgoing`, and `BalancesAt`;
- branch `carrier`;
- signature predicates `SupportedOn`, `Clears`, `CausalOutward`,
  `FeasibleClearing`, and `EmptyExcursion`;
- `boundaryFlux`;
- legal branch-local `BranchPebbleStep` and `BranchReach`;
- `Cleared`, `withBoundary`, and `ClearOutcome`;
- `ExactBoundaryInvariant C B`.

`ExactBoundaryInvariant` is currently a **target proposition**, not a proved
theorem.  It encodes all three audited claims for an occupied branch of message
`d`: exact attainment when `q+d>0`, the universal upper bound
`D(parent) ≤ q+d`, and impossibility of a positive cleared boundary pile when
`q+d≤0`.

## Dependency graph reached

```text
legal pebbling semantics
        |
        +--------------------------+
        |                          |
        v                          v
exact-size universality        transfer F
        |                          |
        v                          +--> F(z-3) <= F(z)
upward closure                    +--> flux upper bound / mod 3
                                   +--> equality attainment

tree bridge deletion / components
        |
        v
OrientedBranch
        |
        +--> child side containment
        +--> strict child subset
        +--> childBranch.card < parent.card
        +--> unique boundary edge
        |
        v
well-founded branchMessage : Option Int
        |
        +--> occupied recursive equation
        +--> EMPTY iff branch restriction unoccupied
        |
        v
move signatures + branch-local legal reachability
        |
        v
ExactBoundaryInvariant  [STATEMENT PRESENT; PROOF NEXT]
        |
        v
rooted score theorem
        |
        v
downstream obstruction / defect-flow formalization
```

The exact estimator branch remains available in parallel:

```text
leafCount / sigma / rootEstimate / estim
        |
        +--> corrected root-sensitive expansion
        +--> |V| + 1 <= rootEstimate(T,r)
        +--> |V| + 1 <= estim(T)
```

## Strongest new machine-checked results

The key new structural theorem is the strict recursive decrease

```text
OrientedBranch.childBranch_card_lt :
  (B.childBranch c).card < B.card
```

together with the corresponding strict finite-set containment.  This removes
the previous well-founded-recursion blocker.

The strongest new boundary theorem on the current branch is

```text
OrientedBranch.ClearOutcome.boundary_le_message :
  B.Occupied C →
  branchMessage C B = some d →
  B.ClearOutcome C q D →
  (D B.parent : ℤ) ≤ (q : ℤ) + d
```

derived from the recursive signature theorem
`OrientedBranch.signature_branchFlux_bounds`.  The recursive message theorem
remains

```text
OrientedBranch.branchMessage_eq_some_of_occupied :
  B.Occupied C →
  branchMessage C B = some (F (effectiveInput C B))
```

with the separate empty-state classification

```text
OrientedBranch.branchMessage_eq_empty_iff :
  branchMessage C B = EMPTY ↔ ¬ B.Occupied C.
```

The complete Csernák–Soukup stacking theorem is **not** yet formalized in
Lean, and neither `ExactBoundaryInvariant` nor the rooted score equivalence is
claimed as proved.

## Exact remaining Phase 1 frontier

Dependencies 1–5 from the earlier boundary plan are now substantially
machine-checked:

- `BranchReach.exists_moveSignature` extracts exact move counts and
  per-vertex balances from a legal branch-local sequence.
- Occupied clearings force causal outward boundary crossing.
- Empty excursions have nonpositive boundary gain and exact gain `-3k`.
- `signature_branchFlux_bounds` proves the recursive occupied-branch upper
  bound together with the modulo-three residue statement, while empty children
  contribute only nonnegative three-step losses.
- `ClearOutcome.boundary_le_message` and
  `ClearOutcome.no_positive_boundary_of_message_nonpos` establish the
  necessity half of the target boundary theorem.
- `orderedTasks_safe` proves the audited positive/zero/negative task order.
  Empty branches are omitted rather than converted into executable zero tasks.
- Message locality, branch-local outside-state preservation, child-carrier
  containment, and sibling child-branch disjointness are available for the
  constructive induction.

The immediate blocker is now **sufficiency / exact attainment**:

1. Instantiate the generic task scheduler with the occupied genuine child
   branches and their recursive message gains.
2. Compose the inductively supplied child clearing sequences while proving
   earlier child clearings do not alter later child interiors or messages.
3. After the child tasks, prove the root/boundary one-vertex construction
   attains exactly `q + F (effectiveInput C B)`; keep the audited
   `x ≥ 2` and `x ≤ 1` cases explicit.
4. Package this construction with the already-proved upper and nonpositive
   halves to prove `ExactBoundaryInvariant C B`.
5. Only then define the rooted score and prove
   `StackableAt T.graph C r ↔ 0 < score T C r`.

The exact branch boundary theorem remains the Phase 1 blocker, but its
necessity half and scheduling arithmetic are no longer open obligations.

## Current branch checkpoint

PR #7 (`chatgpt/exact-boundary-invariant`) contains the first full
move-signature/necessity layer for the exact boundary theorem.  The latest
substantive code also proves configuration locality and geometric separation
needed by the constructive half.  Before merge, the draft PR must be marked
ready so that the repository's **full** workflow runs the Python regression
suite, verifier, complete Lean build, and `Audit.lean`.

## Small-case and regression coverage

The Python regression suite remains falsification/specification evidence only.
Its message-vs-reachability test enumerates every unlabeled tree in its stated
orders and every root, so the bounded coverage includes `K₂`, paths, stars,
leaf roots, and zero-total configurations.  A separate test checks the
stronger exact boundary-gain identity on small branches for multiple exterior
boundary piles.  None of these computations is used to discharge a Lean proof
obligation.

## Verification

The required full CI path remains

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

Two substantive checkpoints in this session have already passed Lean:

- commit `3f4b2749b4a3709b3e38cfe6b83992901c3f8229`, proving strict child
  nesting, passed the complete then-current workflow in run `35634489385`;
- commit `7b93bdd79f657c98110e3dc20310daf5156d2ebb`, including the recursive
  message definition, passed the complete then-current workflow in run
  `35635336057`.

At those full runs the Python regression suite had **23 passing tests**, and
the verifier checked **131,958 rooted cases from 23,079 configurations on 13
unlabeled trees**.  The later boundary-layer development uses a draft-PR
Lean-only checkpoint to avoid repeatedly rerunning unchanged Python tests;
before merge PR #6 must be marked ready and the complete workflow above must
pass again on the final head.

## Trust statement

There are no `sorry`, `admit`, or project-specific axioms in the
`TreeStack` Lean source.  The workflow rejects proof-hole tokens in project
Lean files.  `Audit.lean` prints the axiom dependencies of the strongest
proved branch and message theorems; only standard Lean/Mathlib logical axioms
are permitted.  Python and bounded computation remain regression and
specification checks only.
