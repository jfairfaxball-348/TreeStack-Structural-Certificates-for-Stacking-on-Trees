# Zero-score generalized flow

Status: proved within the project, pending external review and prior-art audit.

This note proves the exact optimization problem that remains after imposing
zero score at every vertex.  It also corrects an important formulation issue:
the abstract integer edge equations are equivalent to genuine zero-score
configurations only after empty branches have been ruled out.

Throughout, `T` is a finite tree with at least two vertices and `C` is a
configuration satisfying

\[
S_v(C)=0\qquad(v\in V(T)).
\]

The all-zero configuration is trivial, so assume below that `C` is nonzero.

## 1. Empty branches cannot occur

For every edge `uv`, both components of `T-uv` contain a pebble.

Indeed, suppose the component on the `u`-side is empty.  Then the branch message
`d_{u->v}` is the empty symbol, not the integer zero.  Since `S_v(C)=0`, the
effective input on the `v`-side that defines `d_{v->u}` is exactly zero.  Hence

\[
d_{v\to u}=F(0)=-3.
\]

But `C(u)=0` and every other branch incident with `u` lies inside the empty
`u`-side, so all those branch messages are empty.  Thus `S_u(C)=-3`, a
contradiction.

Consequently every directed branch message is an integer.  This is the missing
hypothesis behind the edge-state model: integer message zero must never be
substituted for an empty branch.

## 2. Classification on one edge

For an edge `uv`, write

\[
a=d_{u\to v},\qquad b=d_{v\to u}.
\]

Because both branch sides are nonempty and both endpoint scores are zero,

\[
a=F(-b),\qquad b=F(-a). \tag{1}
\]

The integer solutions of (1) are exactly

\[
(-1,-1),\qquad (k,-2k-3),\qquad (-2k-3,k),\qquad k\ge0. \tag{2}
\]

To prove this, first suppose both entries are negative.  If `a<=-2`, then
`-a>=2`, and the definition of `F` gives `F(-a)>=0`, contradicting `b<0`.
Hence `a=-1`, and symmetrically `b=-1`.  Otherwise one entry is nonnegative;
say `a=k>=0`.  Then

\[
b=F(-k)=-2k-3,
\]

and `F(2k+3)=k`, including `k=0` through the exceptional value `F(3)=0`.
The other orientation is symmetric.

Call `(-1,-1)` a **neutral edge**.  In the second family orient the edge from
`u` to `v`, so that the positive message `k` travels from tail to head.  At the
tail the incoming endpoint contribution to the score is `-2k-3`; at the head
it is `k`.

Since every score is zero,

\[
C(v)=-\sum_{u\sim v}d_{u\to v}. \tag{3}
\]

Thus a neutral edge contributes total mass `2`, while an oriented edge of
parameter `k` contributes total mass `k+3`.  At a vertex `v`, if `N(v)` is the
number of neutral incident edges, then nonnegativity of `C(v)` is exactly

\[
\sum_{e\text{ enters }v}k_e
\le
N(v)+\sum_{e\text{ leaves }v}(2k_e+3). \tag{4}
\]

This is the exact generalized-flow model for nonzero genuine zero-score
configurations.

## 3. A dual weighting from orientation heights

Ignore the parameters for a moment and let `h(v)` be the length of a longest
directed path ending at `v`.  Because the underlying graph is a tree, the
oriented subgraph is acyclic.  For every oriented edge `u->v`,

\[
h(v)\ge h(u)+1.
\]

Set

\[
A_v=2^{h(v)}.
\]

Then `A_v>=2A_u` on every oriented edge `u->v`.

Every leaf has `h=0`.  Indeed, the singleton branch at a leaf is nonempty by
Section 1, so the leaf contains a positive number of pebbles.  If its incident
edge were oriented into the leaf, equation (3) would give `C(leaf)=-k<=0`, a
contradiction.

Let `M=|C|`.  Since every `A_v>=1`,

\[
M\le\sum_v A_v C(v). \tag{5}
\]

Expand the right side edge by edge using (3).  A neutral edge `uv` contributes
`A_u+A_v`.  An oriented edge `u->v` of parameter `k` contributes

\[
A_u(2k+3)-A_vk
=3A_u+k(2A_u-A_v)
\le3A_u
\le A_u+A_v. \tag{6}
\]

Summing (6) and the neutral contributions gives

\[
M\le\sum_v \deg(v)2^{h(v)}. \tag{7}
\]

If `L` is the number of leaves, their heights are zero, so

\[
M\le L+
\sum_{\deg(v)>1}\deg(v)2^{h(v)}. \tag{8}
\]

It remains to replace the many orientation sources implicit in `h` by one
root.

## 4. Connected-partition consolidation lemma

We use the following purely metric lemma.

**Lemma.** Let a tree be partitioned into connected parts `P_i`.  Choose a root
`r_i` in each part and nonnegative vertex weights `w_v`.  Then

\[
\sum_i\sum_{v\in P_i}w_v2^{d(r_i,v)}
\le
\max_{r\in V(T)}\sum_vw_v2^{d(r,v)}. \tag{9}
\]

**Proof.** It is enough to show that two adjacent parts can be merged without
lowering their combined potential.  Let `A,B` meet across the edge `xy`, with
`x in A`, `y in B`, and roots `a in A`, `b in B`.  Write

\[
X=\sum_{v\in A}w_v2^{d(a,v)},\qquad
Y=\sum_{v\in B}w_v2^{d(b,v)}.
\]

Let `alpha=d(a,x)` and `beta=d(b,y)`.  If `P` is the contribution of the
vertices of `B` when the union is rooted at `a`, then for every `v in B`,

\[
d(a,v)=\alpha+1+d(y,v)
\ge d(b,v)+\alpha+1-\beta,
\]

so

\[
P\ge2^{\alpha+1-\beta}Y. \tag{10}
\]

Similarly, if `Q` is the contribution of `A` when the union is rooted at `b`,

\[
Q\ge2^{\beta+1-\alpha}X. \tag{11}
\]

The two integer exponents in (10)--(11) sum to `2`; hence at least one is at
least `1`.  Therefore either `P>=Y` or `Q>=X`.  Rooting the union at `a` in the
first case, or at `b` in the second, gives potential at least `X+Y`.
Repeatedly merge adjacent parts in the quotient tree.  The final single root
has potential at least the original sum, proving (9).  \(\square\)

## 5. Applying the lemma to the height function

For each vertex with `h(v)>0`, select one incoming oriented edge `u->v` with

\[
h(v)=h(u)+1.
\]

The selected edges form a forest.  Every component has exactly one vertex of
height zero, and if that vertex is `r_i`, then for every vertex `v` in the
component,

\[
h(v)=d(r_i,v). \tag{12}
\]

Apply the consolidation lemma with

\[
w_v=\begin{cases}
\deg(v),&\deg(v)>1,\\
0,&\deg(v)=1.
\end{cases}
\]

Equations (9) and (12) give

\[
\sum_{\deg(v)>1}\deg(v)2^{h(v)}
\le
\max_r\sum_{\deg(v)>1}\deg(v)2^{d(r,v)}. \tag{13}
\]

Combining (8) and (13),

\[
|C|\le
L+\max_r\sum_{\deg(v)>1}\deg(v)2^{d(r,v)}. \tag{14}
\]

For every root `r`, the definition of the estimator gives the uniform identity

\[
\operatorname{root\_estimate}(r)-1
=
L+\sum_{\deg(v)>1}\deg(v)2^{d(r,v)}. \tag{15}
\]

When `r` is a leaf, its degree-one root term in `sigma_T(r)` exactly replaces
the leaf omitted by `leaf(r)`; when `r` is internal, all `L` leaves are counted
by `leaf(r)`.  Therefore (14)--(15) prove

\[
\boxed{|C|\le\operatorname{estim}(T)-1}. \tag{16}
\]

The explicit obstruction `C_r` from `estimator.md`, for an
estimator-maximizing root, has every score zero and has size
`estim(T)-1`.  Hence

\[
\boxed{\max\{|C|:S_v(C)=0\text{ for all }v\}
=\operatorname{estim}(T)-1}. \tag{17}
\]

This proves the zero-score generalized-flow subproblem completely.  The later
arbitrary-defect argument in `defect-flow.md` proves that every configuration
with all scores nonpositive satisfies the same estimator bound.

## 6. Computational regression checks

`treestack/src/generalized_flow.py` implements the edge classification, height
certificate, selected predecessor partition, and constructive consolidation
lemma.  `tests/test_zero_score_flow.py` checks:

- the integer edge classification on a wide finite interval;
- the empty-branch/integer-zero distinction on `K_2`;
- all zero-score configurations within the documented small bounded search;
- the explicit obstruction family through order 10;
- the non-unique three-leaf-star extremizer `(0,3,3,3)`;
- every neutral/oriented edge pattern on every unlabeled tree through order 8
  for the parameter-free height/consolidation inequality.

These checks are regression support only; the proof above is independent of
their finite bounds.
