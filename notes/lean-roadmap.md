# Lean formalization roadmap

Date: 2026-09-21  
Status: proof survived the independent audit. Formalize the corrected theorem; do not import bounded Python computations as logical evidence.

## Headline theorem

For every finite simple tree `T` with at least two vertices,

\[
\operatorname{stack}(T)=\operatorname{estim}(T).
\]

The formal statement must explicitly assume `2 <= Fintype.card V`; `K_1` is excluded because the source defines `stack` using `t>=2` while the displayed estimator is 1 there.

## 1. Core objects

Use Mathlib's finite simple graph API with a finite vertex type, decidable equality, connectedness, and acyclicity. Isolate a small project API for degree, unique tree paths/distance, edge-side components, connected subtrees, and leaves.

Define:

```text
Configuration V := V -> Nat
mass C := sum_v C v
support C := {v | C v > 0}
PebbleStep T C D : Prop
Reach T := Relation.ReflTransGen (PebbleStep T)
StackedAt C r
StackableAt T C r
Stackable T C
```

Implement `PebbleStep` with explicit witnesses `u v`, adjacency, `2 <= C u`, and a pointwise update so no truncated-subtraction ambiguity enters the proof.

## 2. Exact-size stacking number

Mirror the source definition, not an “at least” variant:

```text
UniversalStackable T t := forall C, mass C = t -> Stackable T C
stack T := minimum t >= 2 with UniversalStackable T t
```

Prove existence from a concrete finite-tree upper bound or define the minimum over a nonempty finite set once the main upper bound is available.

Formalize early:

```text
universal_stackable_gt_card :
  UniversalStackable T t -> 2 <= t -> Fintype.card V < t

universal_stackable_succ :
  UniversalStackable T t -> UniversalStackable T (t+1)
```

The first uses a configuration with one pebble on each of `t` distinct vertices when `t <= card V`. The second makes one legal move from a duplicated vertex and invokes universality at size `t`.

## 3. Estimator

Define `leafCount T r`, `sigma T r`, `rootEstimate T r`, and `estim T`. Prove for nontrivial trees the useful identity

\[
\operatorname{rootEstimate}(r)-1
=L+\sum_{\deg(v)>1}\deg(v)2^{d(r,v)}.
\]

Also prove estimator monotonicity under adjoining one leaf, then under enlarging a connected subtree by repeated leaf attachments.

## 4. Transfer and branch messages

Use a genuine sum type, preferably `Option Int`, for messages; `none` is `EMPTY` and must never be identified with integer zero.

Define `F : Int -> Int` by the five cases from the proof. Prove the arithmetic helpers first:

- `F (z-3) <= F z`;
- negative values of `F` are exactly negative odd integers with the stated inverse;
- preimages of `k>=0`, including the exceptional `k=0` case;
- the one-vertex flux maximum and congruence modulo three.

Represent an oriented branch as one side of a deleted tree edge. Define the message recursively by branch size.

## 5. Exact branch theorem

Formalize the stronger boundary invariant before the root corollary. For a nonempty branch `B` with exterior boundary vertex initially holding `q` pebbles, prove:

- if `q+d(B)>0`, there is a legal sequence clearing `B` and leaving exactly `q+d(B)` at the boundary;
- every legal sequence that clears `B` leaves at most `q+d(B)` there;
- if `q+d(B)<=0`, no positive boundary stack after clearing `B` is reachable.

Break the proof into:

1. move-count balance extraction;
2. causal outward-crossing lemma for a nonempty cleared branch;
3. empty-branch excursion gain `=-3k`;
4. one-vertex arithmetic upper bound;
5. positive/zero/negative child scheduling;
6. constructive cases `x>=2` and `x<=1`.

Then prove

```text
stackableAt_iff_score_pos : StackableAt T C r <-> 0 < score T C r
nonstackable_iff_all_scores_nonpos : not (Stackable T C) <-> forall v, score T C v <= 0
```

## 6. Explicit obstruction

For a root `r`, define the configuration with `sigma r - 1` pebbles at `r`, one pebble at every other leaf, and zero elsewhere. Define recursive obstruction heights away from `r` and prove the closed form. Then prove all scores are zero and

```text
mass_extremal : mass (C_r) = rootEstimate T r - 1
```

At an estimator-maximizing root this yields a non-stackable state of mass `estim T - 1`. Combine it later with `universal_stackable_succ` to obtain the exact-size lower bound.

## 7. Support pruning

For a nonzero configuration with all scores nonpositive, define the minimal connected subtree spanning its support, preferably as the union of unique tree paths between support vertices rather than an executable pruning loop.

Prove:

- singleton nonzero support contradicts all scores nonpositive;
- every leaf of the support subtree is occupied;
- both sides of every support-tree edge contain support;
- every support-tree branch message is an integer, not `EMPTY`;
- surviving scores are unchanged;
- `estim H <= estim T`.

## 8. Defect-edge classification

Set `delta_v=-score_v` as a natural number using the nonpositivity hypothesis. For each genuine edge derive

\[
a=F(-\delta_u-b),\qquad b=F(-\delta_v-a).
\]

Use an inductive structure for the exhaustive states:

```text
DefectEdgeState.oriented tail head k ...
DefectEdgeState.twoNegative r q ...
```

with neutral state represented separately or as `twoNegative 0 0`. Record as theorems:

- oriented: reverse message `-2(k+delta_head)-3` and `delta_tail in {2delta_head,2delta_head+3}`;
- two-negative: messages `-(2r+1),-(2q+1)` and endpoint defects `r+2q`, `q+2r`.

## 9. Injective owners and orientations

Define defective edges as in the paper proof. Since they form a forest, prove a finite-forest lemma assigning every defective edge injectively to an incident vertex. A constructive rooted-component proof is appropriate.

Keep forced orientations; orient defective two-negative edges toward their owners; neutral edges remain unoriented. Prove acyclicity from the underlying tree.

Define longest incoming-path height `h(v)` and `A_v=2^{h(v)}`. Prove every oriented `u->v` satisfies `A_v>=2A_u`.

## 10. Weighted defect cancellation

Formalize the weighted score identity before any inequality:

\[
\sum_vA_vC(v)
=-\sum_vA_v\delta_v
-\sum_{uv\in E}(A_vd_{u\to v}+A_ud_{v\to u}).
\]

Prove separate edge lemmas for neutral, oriented, and two-negative states. For oriented type expose `k(2A_u-A_v)<=0`; for two-negative type orient parameters consistently with owner/head.

Show each positive edge excess is bounded by its distinct owner's budget `A_v delta_v`, then sum using owner injectivity to get

\[
\sum_vA_vC(v)\le\sum_v\deg(v)A_v.
\]

## 11. Leaf slack

Use the exact identity

\[
|C|=\sum_vA_vC(v)-\sum_v(A_v-1)C(v).
\]

Every support-tree leaf is occupied, hence the slack term pays at least `sum_leaves(A_v-1)`. Conclude

\[
|C|\le L+\sum_{\deg(v)>1}\deg(v)2^{h(v)}.
\]

Do not import the zero-score lemma “leaf height is zero”; it is unnecessary here.

## 12. Connected-partition consolidation

Formalize independently of pebbling:

\[
\sum_i\sum_{v\in P_i}w_v2^{d(r_i,v)}
\le\max_r\sum_vw_v2^{d(r,v)}
\]

for a finite tree partitioned into connected parts with nonnegative weights. Prove the two-part merge lemma first: for adjacent parts, the two rerooting exponent shifts sum to two, so one rerooting preserves or increases combined potential. Induct on the number of parts.

Build the selected-predecessor partition from the height function and apply the lemma with `w_v=deg(v)` on internal vertices and zero on leaves. This yields

```text
all_scores_nonpos_mass_le : mass C <= estim T - 1
```

## 13. Final theorem order

Recommended proof order:

1. basic tree/pebbling definitions;
2. exact-size upward-closure lemmas;
3. estimator identities;
4. transfer arithmetic;
5. branch boundary theorem;
6. root score theorem;
7. explicit obstruction;
8. support pruning and estimator monotonicity;
9. defect-edge classification;
10. forest owners;
11. orientation heights;
12. weighted cancellation;
13. leaf slack;
14. connected-partition consolidation;
15. arbitrary-defect estimator bound;
16. lower and upper bounds for `stack`;
17. equality.

A plausible file layout is `Basic.lean`, `Estimator.lean`, `PebblingMove.lean`, `Transfer.lean`, `Branch.lean`, `RootScore.lean`, `Obstruction.lean`, `Support.lean`, `EdgeClassification.lean`, `ForestOwners.lean`, `OrientationHeight.lean`, `Consolidation.lean`, `DefectFlow.lean`, and `Main.lean`.

## 14. Executable versus logical layers

Python enumeration, certificate code, and any Lean `#eval` checks are regression/oracle material only. The trusted theorem must depend solely on definitions and proved lemmas. Small executable cases may be retained as tests but must not discharge universal proof obligations.

## Proposed future Palomar headline theorem

No Palomar action should occur in this stage. If the formalization is later reviewed and registered, use the corrected theorem:

> **Tree Stacking Formula.** For every finite simple tree `T` with at least two vertices,
> \[
> \operatorname{stack}(T)=\max_{r\in V(T)}\left(1+\operatorname{leaf}_T(r)+\sum_{v=r\text{ or }\deg_T(v)>1}\deg_T(v)2^{d_T(r,v)}\right).
> \]
