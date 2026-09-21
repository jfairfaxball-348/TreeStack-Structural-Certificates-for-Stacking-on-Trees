# Lean formalization progress

Status: **Phase 1 partial, sound and compiling through the exact-size threshold
and transfer-arithmetic layer.** The exact branch boundary invariant and rooted
score theorem are not yet formalized.

## Pinned environment

- Lean: `v4.34.0`
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`
- Lake manifest: committed at repository root
- Namespace: `TreeStack`

The project uses Mathlib's `SimpleGraph` and `SimpleGraph.IsTree` rather
than introducing a separate graph theory.

## Definitions adopted

- `Configuration V := V → Nat`.
- `mass C := ∑ v, C v`.
- `support C := {v | 0 < C v}`.
- `FiniteTree V` stores a `SimpleGraph V` and a proof of
  `SimpleGraph.IsTree`.
- `move C u v` uses natural-number subtraction at `u`; legality is not
  encoded in the raw update but in `PebbleStep`, which requires both
  adjacency and `2 ≤ C u`.
- `Reach` is `Relation.ReflTransGen (PebbleStep G)`.
- `StackedAt`, `StackableAt`, and `Stackable` follow the source
  reachability semantics.
- `UniversalStackable G t` quantifies over configurations of **exactly**
  `t` pebbles.
- `Message := Option Int`; `none` is `EMPTY`, while `some 0` is the
  genuine integer message zero.
- `F : Int → Int` is the five-case transfer function from the audited proof.

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
   +--> negative / zero / nonnegative preimages
   +--> one-vertex flux upper bound
   +--> modulo-three flux congruence
   +--> equality-attainment constructions
```

The next dependency edge is the oriented-branch representation and
well-founded recursive message definition. The exact boundary invariant and
root-score theorem remain downstream of that work.

## Theorems proved

### Basic/configuration layer

- `mem_support_iff`

### Pebbling and exact-size semantics

- `mass_move_add_one`
- `stackableAt_of_stackedAt`
- `stackable_of_step`
- `oneOn_apply`
- `mass_oneOn`
- `no_step_oneOn`
- `not_stackable_oneOn_of_two_le_card`
- `universal_stackable_gt_card`
- `exists_two_le_of_card_lt_mass`
- `universal_stackable_succ`

The two `universal_stackable_*` theorems formalize the independent-audit
repair required by the source's exact-size convention.

### Transfer arithmetic

- `empty_ne_integer_zero`
- `F_of_le_one`
- `F_two`
- `F_three`
- `F_of_ge_four_even`
- `F_of_ge_five_odd`
- `F_sub_three_le`
- `F_neg_iff`
- `F_eq_zero_iff`
- `F_eq_neg_odd_iff`
- `F_eq_nonneg_iff`
- `one_vertex_flux_le`
- `one_vertex_flux_mod_three`
- `one_vertex_flux_attained_le_one`
- `one_vertex_flux_attained_even`
- `one_vertex_flux_attained_odd`

## Estimator correction discovered during formalization

The requested helper identity

```text
rootEstimate(T,r) - 1
  = L + sum_{deg(v)>1} deg(v) * 2^(d(r,v))
```

is not valid when the root itself has degree one. For `K2`, either root has
`sigma = 2` and one other leaf, so `rootEstimate - 1 = 2`, while the
displayed right-hand side is `1`.

This is an issue with that proposed intermediate identity, not with the source
definition of the estimator. The source definition includes the root in
`sigma_T(r)` regardless of its degree. The Lean development therefore has
not encoded the false helper identity. The estimator module should next prove
the corrected expansion with the root contribution retained explicitly.

## Remaining Phase 1 obligations

1. Formalize source-exact distance, degree, leaf count, `sigma`,
   `rootEstimate`, and `estim`, including the corrected root-leaf algebra.
2. Prove the estimator lower bound needed later.
3. Define oriented deleted-edge branches.
4. Define branch messages with explicit `EMPTY` and prove recursion
   well-founded by branch/subtree cardinality.
5. Formalize move signatures and boundary flux.
6. Prove the causal outward-crossing lemma.
7. Prove empty-branch excursions have nonpositive gain divisible by three.
8. Formalize positive/zero/negative child-task scheduling.
9. Prove the exact branch boundary invariant.
10. Define root score and prove
    `StackableAt T C r ↔ 0 < S_r(C)`.

## Verification

The repository CI follows the same pattern used in the completed Fischer
formalization project:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the axioms of the strongest exact-size and transfer
theorems. The CI also rejects occurrences of `sorry`, `admit`, or
project-specific `axiom` declarations in the `TreeStack/*.lean` source
tree.

PR #4 combined CI run 35624780508 passed on 2026-09-21 with the following
results:

- `python3 -m pip install -e '.[test]'`: success;
- `python3 -m pytest -q`: **23 passed in 4.40s**;
- `python3 -m treestack.src.verify --max-order 6 --max-total 8`:
  **verified 131,958 rooted cases from 23,079 configurations on 13 trees**;
- `python3 -m compileall -q treestack`: success;
- Lean proof-hole scan: success;
- `lake build`: **Build completed successfully (8928 jobs)**;
- `lake env lean Audit.lean`: success.

The axiom audit reported only Mathlib/Lean standard logical axioms among the
audited theorems: `propext`, `Classical.choice`, and `Quot.sound`.
No project-specific axiom or `sorryAx` was reported.

## Trust statement

There are no `sorry`, `admit`, or project-specific axioms in the current
`TreeStack` Lean source. Python and bounded computation remain regression and
specification checks only; no universal Lean theorem is derived from them.
