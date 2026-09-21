# Lean formalization progress

Status: **Phase 1 partial, sound and compiling through the exact-size threshold,
transfer-arithmetic, exact estimator, and initial oriented-branch layers.**
The recursive branch message, exact branch boundary invariant, and rooted score
theorem are not yet formalized.

## Session baseline and pinned environment

This phase extension started from `main` at merge commit
`578089fb4f8a3d02105a83b404e4786a2b2f7c63`, the merge of PR #4.

- Lean: `v4.34.0`
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`
- Lake manifest: committed at repository root
- Namespace: `TreeStack`

The project uses Mathlib's `SimpleGraph`, graph distance, graph degree,
connected components, bridge deletion, and `SimpleGraph.IsTree`.

## Definitions adopted

The existing pebbling layer retains `Configuration V := V → Nat`, legal
`PebbleStep`, finite `Reach`, `StackableAt`, exact-size
`UniversalStackable`, `Message := Option Int`, the distinct marker
`EMPTY := none`, and the audited five-case transfer `F : Int → Int`.
No semantics were weakened or replaced.

### Exact estimator

`TreeStack/Estimator.lean` formalizes the source definitions:

- `leafVertices T r`: vertices `v ≠ r` of Mathlib degree one;
- `sigmaVertices T r`: the root together with vertices of degree greater
  than one;
- `nonRootInternalVertices T r`: non-root vertices of degree greater than
  one;
- `leafCount T r := (leafVertices T r).card`;
- `sigma T r := 1 + ∑ v ∈ sigmaVertices T r,
    degree(v) * 2^(dist(r,v))`;
- `rootEstimate T r := sigma T r + leafCount T r`;
- `estim T := sup_{r ∈ V(T)} rootEstimate T r`.

The implementation uses Mathlib's `SimpleGraph.degree` and
`SimpleGraph.dist`.

### Oriented branches

`TreeStack/Branch.lean` defines `OrientedBranch T` by a root vertex,
parent boundary vertex, and proof that the two are adjacent. For a branch
`B : v → p`:

- `deletedGraph B` is `T.graph.deleteEdges {vp}`;
- `component B` is the connected component containing `v`;
- `vertices B` is the finite support of that component;
- `card B` is its cardinality;
- `Child B` records a neighbor of `v` different from `p`;
- `childBranch B c` orients that child edge back toward `v`.

## Dependency graph reached

```text
finite tree / configuration
        |
        v
legal pebbling move --> finite reachability --> stackability
        |                                      |
        v                                      v
one-step mass drop                    exact-size universality
                                               |
                                               v
                              universal_stackable_gt_card
                                               |
                                               v
                                universal_stackable_succ

transfer F
   |
   +--> exact case lemmas
   +--> F(z - 3) <= F(z)
   +--> transfer preimage classifications
   +--> one-vertex flux upper bound
   +--> modulo-three flux congruence
   +--> equality-attainment constructions

Mathlib degree + distance
   |
   v
leafCount / sigma / rootEstimate / estim
   |
   +--> corrected root-sensitive expansion
   +--> |V| + 1 <= rootEstimate(T,r)
   +--> |V| + 1 <= estim(T)

tree adjacency + bridge deletion + connected components
   |
   v
OrientedBranch(v -> p)
   |
   +--> root belongs to branch
   +--> parent lies outside branch
   +--> 0 < branch.card < |V|
   +--> childBranch objects
   |
   v
NEXT: child branch strict containment/cardinality decrease
   |
   v
well-founded recursive branch message
   |
   v
exact boundary invariant
   |
   v
rooted score theorem
```

## New theorems in this session

### Exact estimator

- `sigmaVertices_eq_insert`
- `sigma_corrected_expansion`
- `rootEstimate_corrected_expansion`
- `erase_root_eq_leaf_union_internal`
- `leafVertices_disjoint_internal`
- `card_erase_root_eq_leafCount_add_internal`
- `card_internal_le_weighted_sum`
- `card_add_one_le_rootEstimate_of_degree_pos`
- `card_add_one_le_rootEstimate`
- `rootEstimate_le_estim`
- `card_add_one_le_estim`

The strongest estimator consequence currently machine checked is

```text
[Nontrivial V] -> Fintype.card V + 1 <= estim T.
```

The rooted form is also proved for every root:

```text
[Nontrivial V] -> Fintype.card V + 1 <= rootEstimate T r.
```

### Oriented branches

- `OrientedBranch.root_ne_parent`
- `OrientedBranch.root_mem_vertices`
- `OrientedBranch.parent_not_mem_vertices`
- `OrientedBranch.vertices_nonempty`
- `OrientedBranch.card_pos`
- `OrientedBranch.vertices_ssubset_univ`
- `OrientedBranch.card_lt_total`
- `OrientedBranch.childBranch_root`
- `OrientedBranch.childBranch_parent`

The parent-exclusion theorem is derived from Mathlib's bridge characterization
for edges in an acyclic graph; it is not a project-specific axiom.

All previously listed basic, pebbling, exact-size, and transfer theorems from
PR #4 remain available unchanged.

## Root-leaf correction retained

The proposed helper identity

```text
rootEstimate(T,r) - 1
  = L + sum_{deg(v)>1} deg(v) * 2^(d(r,v))
```

is false when the root itself has degree one. For `K2`, either root has
`sigma = 2` and one other leaf, so `rootEstimate - 1 = 2`, whereas the
displayed right-hand side is `1`.

Lean does not encode that false statement. Instead it proves the corrected
root-sensitive expansion

```text
rootEstimate(T,r)
  = 1 + leafCount(T,r) + degree(r)
      + sum_{v != r, degree(v)>1} degree(v) * 2^(d(r,v)).
```

Thus the root contribution remains explicit even for a leaf root.

## Strongest machine-checked status

The complete Csernák–Soukup stacking theorem is **not** yet Lean-formalized.
Phase 1 remains partial.

The strongest independently useful additions beyond PR #4 are the exact
source estimator and its lower bound, plus a deleted-edge component model of
oriented branches proving that the branch contains its root, excludes its
parent, is nonempty, and has cardinality strictly smaller than the whole tree.

No recursive branch message, exact branch boundary invariant, or rooted score
characterization is claimed yet.

## Remaining Phase 1 obligations

1. Prove that every genuine child branch is a strict subset of its parent
   branch, hence `card (childBranch B c) < card B`. This is the immediate
   well-founded-recursion frontier.
2. Define branch restriction/nonemptiness and the audited recursive message,
   preserving `EMPTY : Option Int` as distinct from integer zero.
3. Formalize move signatures and boundary flux.
4. Prove the causal outward-crossing lemma.
5. Prove empty-branch excursions have nonpositive boundary gain divisible by
   three.
6. Formalize positive/zero/negative child-task scheduling.
7. Prove the exact branch boundary invariant, including equality attainment.
8. Define root score and prove
   `StackableAt T C r ↔ 0 < S_r(C)`.
9. Only after that exact theorem is secure, continue downstream to the
   generalized-flow formalization.

The immediate blocker is therefore the tree-specific child-branch strict
nesting lemma needed to justify recursion on branch cardinality.

## Verification

The CI path is:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

PR #5 head `57512bebc079f24b23443928dad01aec242bf910` passed combined
GitHub Actions run `35631979218` on 2026-09-21:

- `python3 -m pip install -e '.[test]'`: success;
- `python3 -m pytest -q`: **23 passed in 8.36s**;
- verifier: **131,958 rooted cases from 23,079 configurations on 13 trees**;
- `python3 -m compileall -q treestack`: success;
- Lean proof-hole scan: success;
- `lake build`: **Build completed successfully (8930 jobs)**;
- `lake env lean Audit.lean`: success.

`Audit.lean` includes the strongest estimator results and
`OrientedBranch.parent_not_mem_vertices` and
`OrientedBranch.card_lt_total`. Their axiom reports contain only standard
Lean/Mathlib logical axioms: `propext`, `Classical.choice`, and
`Quot.sound`. No project-specific axiom or `sorryAx` was reported.

## Trust statement

There are no `sorry`, `admit`, or project-specific axioms in the current
`TreeStack` Lean source. Python and bounded computation remain regression and
specification checks only; no universal Lean theorem is derived from them.
