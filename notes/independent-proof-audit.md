# Independent proof audit

Date: 2026-09-21  
Audited baseline: `main` at `06c019aacd2b4269864b17d12867a1a4eda4d2f1`  
Decision: **GO for Lean formalization after the exact-size threshold lemma below is inserted into the written proof.** No surviving internal mathematical gap was found. Novelty/priority remains subject to external literature review.

## Canonical theorem statement

Let `T=(V,E)` be a finite simple undirected tree with `|V|>=2`. A configuration is `C:V->N`. A legal pebbling move along an oriented edge `u->v` removes two pebbles from `u` and adds one to `v`. A configuration is stacked if its support has size one, and stackable if a stacked configuration is reachable by finitely many legal moves. Define

\[
\operatorname{stack}(T)=\min\{t\ge2:\text{ every configuration of exactly }t\text{ pebbles is stackable}\}.
\]

For `r in V`, define

\[
\operatorname{leaf}_T(r)=|\{v\ne r:\deg_T(v)=1\}|,
\]

\[
\sigma_T(r)=1+\sum_{v=r\text{ or }\deg_T(v)>1}\deg_T(v)2^{d_T(r,v)},
\]

and

\[
\operatorname{estim}(T)=\max_r(\sigma_T(r)+\operatorname{leaf}_T(r)).
\]

**Theorem.** For every finite simple tree `T` with at least two vertices,

\[
\boxed{\operatorname{stack}(T)=\operatorname{estim}(T).}
\]

The restriction `|V|>=2` is necessary under the source convention `t>=2`: `stack(K_1)=2` while the estimator equals `1`.

For a nonempty oriented branch, the proof uses the integer transfer

\[
F(x)=\begin{cases}
2x-3,&x\le1,\\
1,&x=2,\\
0,&x=3,\\
x/2,&x\ge4\text{ even},\\
(x-3)/2,&x\ge5\text{ odd}.
\end{cases}
\]

An empty branch is a separate state `EMPTY`, not the integer zero. If `d_{u->r}` is the message from the nonempty `u`-side branch toward `r`, define

\[
S_r(C)=C(r)+\sum_{u\sim r,\ d_{u\to r}\ne EMPTY}d_{u\to r}.
\]

The exact rooted theorem is

\[
\operatorname{StackableAt}(C,r)\iff S_r(C)>0.
\]

Hence `C` is non-stackable iff `S_v(C)<=0` for every vertex.

## Dependency graph

```text
legal pebbling semantics
  -> exact branch boundary invariant
  -> rooted score theorem
  -> non-stackable iff all scores <= 0

explicit zero-score obstruction ------------------------------+
                                                               |
support pruning -> defect edge classification                  |
  -> injective defective-edge owners                           |
  -> forced/auxiliary orientations and exponential weights     |
  -> edge-excess cancellation                                  |
  -> occupied-leaf slack                                       |
  -> connected-partition consolidation                         |
  -> |C| <= estim(T)-1 for all all-nonpositive-score C --------+
                                                               |
                  maximum non-stackable mass = estim(T)-1      |
                                                               v
                   exact-size upward-closure lemma
                                                               |
                                                               v
                         stack(T)=estim(T)
```

The zero-score generalized-flow theorem is a clean intermediate result but is not logically needed once the arbitrary-defect theorem is available.

## Adversarial proof audit

### Branch messages

I checked the proof against legal sequences, not only balance equations. The causal requirement that a nonempty cleared branch uses at least one outward boundary move is essential and repairs otherwise unschedulable balance solutions. The one-vertex arithmetic then gives the stated `F`, with all lower fluxes differing by multiples of three.

The distinction `EMPTY != 0` is essential. An initially empty branch that begins and ends empty has boundary gain `-3k` for some `k>=0`; therefore such excursions never improve the maximum boundary pile and may be omitted in the maximizing construction, but they cannot be represented by integer message zero.

The inductive upper bound, the positive/zero/negative task scheduling, and the odd cleanup move `p->v->p` all have the required legality budgets. A survivor inside a branch is not lost because stackability is tested separately at every possible target. I found no gap in

\[
\operatorname{StackableAt}(C,r)\iff S_r(C)>0.
\]

### Zero-score generalized flow

For a nonzero all-zero-score configuration, no edge side can be empty. The edge equations

\[
a=F(-b),\qquad b=F(-a)
\]

have exactly the neutral state `(-1,-1)` and the two oriented families `(k,-2k-3)` and its reversal for `k>=0`. Longest-directed-path heights are well defined because an orientation of a subgraph of a tree is acyclic. In the zero-score case no oriented edge can point into a leaf, so leaf height is zero.

For an oriented edge `u->v`, `A_v>=2A_u` with `A_x=2^{h(x)}`, and

\[
A_u(2k+3)-A_vk\le A_u+A_v.
\]

The connected-partition consolidation lemma is valid independently of pebbling: when two adjacent connected parts are rerooted across their joining edge, the two exponent shifts sum to two, so at least one rerooting does not decrease the combined potential.

### Arbitrary-defect generalized flow

Pruning to the minimal connected subtree spanning the support preserves surviving scores, makes every remaining edge side nonempty, and makes every support-tree leaf occupied. A nonzero one-vertex support cannot have all scores nonpositive. The estimator is monotone when leaves are adjoined, so proving the bound on the support subtree suffices.

Put `delta_v=-S_v(C)>=0`. For a genuine edge with messages `a=d_{u->v}` and `b=d_{v->u}`, the endpoint equations are

\[
a=F(-\delta_u-b),\qquad b=F(-\delta_v-a).
\]

The exhaustive solutions are:

- oriented type: if `a=k>=0`, then `b=-2(k+delta_v)-3` and `delta_u in {2delta_v,2delta_v+3}`, with the second option unavailable for `k=0`;
- two-negative type: `a=-(2r+1)`, `b=-(2q+1)`, with `delta_u=r+2q` and `delta_v=q+2r`.

Defective edges form a forest and therefore admit injective incident owners. Keep forced orientations and orient defective two-negative edges toward their owners. The resulting directed graph is acyclic.

For an oriented edge `u->v`, the positive excess is

\[
X_{uv}=2A_u\delta_v,
\]

and either endpoint can pay it because `A_v>=2A_u` and `delta_u>=2delta_v`. For a two-negative edge oriented toward owner `v`,

\[
X_{uv}=2(A_vr+A_uq)\le A_v(2r+q)=A_v\delta_v.
\]

Owner injectivity prevents double charging. Substitution into the weighted score identity gives

\[
\sum_v A_v C(v)\le\sum_v\deg(v)A_v.
\]

Returning to ordinary mass subtracts `sum_v(A_v-1)C(v)`. Occupied support leaves pay at least the unwanted weighted leaf terms, yielding

\[
|C|\le L+\sum_{\deg(v)>1}\deg(v)2^{h(v)}.
\]

Connected-partition consolidation then produces

\[
|C|\le\operatorname{estim}(T)-1.
\]

I found no endpoint mismatch, reversed inequality, uncancelled excess, circular lemma dependence, or counterexample.

## Exact-size threshold repair

The repository's structural arguments determine the maximum non-stackable mass, but the source definition of `stack` quantifies over configurations of exactly one size. The following lemma must be explicit.

**Lemma.** Let `G` be a finite connected graph on `n>=2` vertices and `t>=2`. If every configuration of exactly `t` pebbles is stackable, then `t>n`, and every configuration of exactly `t+1` pebbles is stackable.

**Proof.** If `t<=n`, place one pebble on each of `t` distinct vertices. The configuration is not stacked and has no legal move. Thus `t>n`. For a size-`t+1` configuration, either it is already stacked or pigeonhole gives a vertex with at least two pebbles. Make one legal move to a neighbour; the new configuration has size `t`, hence is stackable. Prepending that move proves the original configuration stackable. `square`

Therefore universal stackability is upward closed. The explicit non-stackable obstruction of mass `estim(T)-1` gives `stack(T)>=estim(T)`, and the arbitrary-defect theorem gives the reverse inequality.

## Resolved concerns and remaining issues

Resolved concerns include: phantom balance solutions; `EMPTY` versus integer zero; empty-branch excursions; odd-residue reverse moves; no-empty-edge-side in the zero-score model; support pruning; one-vertex support; exhaustive defect-edge classification; owner existence/injectivity; orientation acyclicity; endpoint conventions in the weighted identity; oriented and two-negative edge charging; multiple defective edges at one vertex; leaf-slack direction; consolidation; and circularity.

Editorial repairs required before merging this audit: add the exact-size lemma to `notes/estimator.md`, and remove its stale statement that the global upper bound remains open. This audit branch performs both repairs.

No unresolved internal proof step remains. The unresolved external issue is priority/novelty: negative searches are not a proof that the theorem or architecture is new.

## Independent computational attack

Baseline reproduction:

```text
python3 -m pytest -q
22 passed in 5.80s

python3 -m treestack.src.verify --max-order 6 --max-total 8
verified 131958 rooted cases from 23079 configurations on 13 trees

python3 -m compileall -q treestack
exit status 0
```

`pip install -e '.[test]'` could not complete because this sandbox could not resolve the package index while pip attempted to fetch the PEP-517 build dependency `setuptools>=68`; this was an environment/network failure, not a test failure.

`tests/test_independent_audit.py` imports none of TreeStack's message, reachability, estimator, or certificate modules. It independently implements the estimator formula and exhaustive legal-move stackability. Through order five, it checked all 66,508 configurations on the complete `estim(T)` layers of all seven unlabeled trees and found all stackable; every corresponding `estim(T)-1` layer contained a non-stackable state.

A separate targeted census inspected 31,389 nonzero all-nonpositive-score configurations over every unlabeled tree of orders 2 through 6 and total mass at most 12. It found no state that the independent legal-move solver could stack. The scan included empty exterior branches, mixed zero/negative defects, multiple defective edges incident to one vertex, height-three orientations, vertices with incoming and outgoing forced orientations, positive-height support leaves, and tight equality cases.

These finite checks are falsification evidence only, not proof.

## Final assessment

**Mathematical confidence:** high, approximately 0.90. The corrected theorem has a coherent non-circular proof once the short exact-size threshold lemma is made explicit.

**Research decision:** proceed to Lean formalization. Keep novelty language conservative until a human citation audit using comprehensive mathematical databases has been completed.
