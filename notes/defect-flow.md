# Arbitrary-defect generalized flow

Status: proved within the project, pending external mathematical review and a
complete prior-art audit.

This note proves the remaining global inequality.  Let `T` be a finite tree
with at least two vertices, let `C` be a configuration, and suppose

\[
S_v(C)\le 0\qquad(v\in V(T)).
\]

Then

\[
\boxed{|C|\le \operatorname{estim}(T)-1.} \tag{G}
\]

The all-zero configuration is immediate, so assume throughout that `C` is
nonzero.  Put

\[
\delta_v=-S_v(C)\ge0.
\]

The proof enlarges the zero-score generalized-flow argument.  The new point is
that every edge contribution beyond the zero-score potential can be charged
injectively to an endpoint defect.

## 1. Removing empty exterior branches

Let `H` be the minimal connected subtree of `T` containing the support of `C`.
It has at least two vertices: a nonzero configuration supported at one vertex
has positive score at that vertex.  Every component of every edge deletion in
`H` contains a pebble, so every directed branch message in `H` is a genuine
integer.

The scores at vertices of `H` are unchanged when passing from `T` to `H`.
Indeed, every deleted component is empty, its branch message is the separate
EMPTY symbol, and EMPTY branches are omitted from both the message recursion
and the score.  Every leaf of `H` contains at least one pebble.

We will prove

\[
|C|\le\operatorname{estim}(H)-1. \tag{1}
\]

The estimator is monotone under adjoining leaves.  For a nontrivial tree `R`,
write

\[
P_R(r)=L_R+
\sum_{\deg_R(v)>1}\deg_R(v)2^{d_R(r,v)}
=\operatorname{root\_estimate}_R(r)-1, \tag{2}
\]

where `L_R` is the number of leaves.  If a new leaf is attached at `p`, then
for every old root `r`, `P_R(r)` does not decrease.  If `p` was a leaf, the old
leaf is replaced by the new one and the new internal term at `p` is positive.
If `p` was internal, the leaf term increases by one and the coefficient at `p`
also increases by one.  Any connected subtree can be enlarged to `T` one leaf
at a time.  Thus

\[
\operatorname{estim}(H)\le\operatorname{estim}(T), \tag{3}
\]

so (1) implies (G).  We may therefore replace `T` by `H` and assume below that
both sides of every edge are nonempty and every tree leaf is occupied.

## 2. Exact edge classification with defects

For an edge `uv`, put

\[
a=d_{u\to v},\qquad b=d_{v\to u}.
\]

Both are integers.  Removing the contribution from the opposite branch at
each endpoint gives

\[
a=F(-\delta_u-b),\qquad b=F(-\delta_v-a). \tag{4}
\]

We use two elementary inverse facts about `F`:

- a negative value of `F` has the unique form `-(2r+1)`, with unique preimage
  `1-r`;
- the preimages of `k>=0` are `2k` and `2k+3`, except that zero has only the
  preimage `3`.

The solutions of (4) have exactly the following forms.

### Oriented type

One message is nonnegative and the other is negative.  If `a=k>=0`, orient
the edge `u->v`.  Then

\[
b=-2(k+\delta_v)-3, \tag{5}
\]

and

\[
\delta_u\in\{2\delta_v,\ 2\delta_v+3\}. \tag{6}
\]

The second possibility in (6) requires `k>=1`.  The case with `b>=0` is
symmetric.  Both messages cannot be nonnegative, since the input defining
either one would then be at most zero.

### Two-negative type

There are unique `r,q>=0` such that

\[
a=-(2r+1),\qquad b=-(2q+1), \tag{7}
\]

and (4) is equivalent to

\[
\delta_u=r+2q,\qquad \delta_v=q+2r. \tag{8}
\]

When `r=q=0`, this is the zero-score neutral state `(-1,-1)`.  Otherwise call
the edge a defective two-negative edge.

These formulas follow directly by substituting the inverse facts into (4), so
the classification is exhaustive.

## 3. Injective owners and an auxiliary orientation

For an oriented-type edge `u->v`, its later excess term is zero when
`delta_v=0`; call it defective when `delta_v>0`.  Also call every nonneutral
two-negative edge defective.  The defective edges form a forest because they
are a subset of the edges of `T`.

Every edge of a forest can be assigned injectively to an incident vertex:
root each component and assign each edge to its child endpoint.  Fix such an
**owner** for every defective edge.

Keep the forced orientation on every oriented-type edge.  Orient every
defective two-negative edge toward its owner.  Leave neutral edges unoriented.
Any orientation of a subgraph of a tree is acyclic.  Let `h(v)` be the length
of a longest directed path ending at `v`, and put

\[
A_v=2^{h(v)}. \tag{9}
\]

For every auxiliary oriented edge `u->v`,

\[
A_v\ge2A_u. \tag{10}
\]

## 4. Every edge excess is paid by its owner

The score identity gives

\[
C(v)=-\delta_v-\sum_{u\sim v}d_{u\to v}.
\]

After multiplying by `A_v` and summing,

\[
W:=\sum_vA_vC(v)
=-\sum_vA_v\delta_v
-\sum_{uv\in E(T)}\bigl(A_vd_{u\to v}+A_ud_{v\to u}\bigr). \tag{11}
\]

Consider one edge.

For an oriented-type edge `u->v` with nonnegative message `k`, equations
(5) and (10) give the edge contribution

\[
\begin{aligned}
E_{uv}
&=A_u\bigl(2(k+\delta_v)+3\bigr)-A_vk\\
&=3A_u+k(2A_u-A_v)+2A_u\delta_v\\
&\le A_u+A_v+X_{uv}, \tag{12}
\end{aligned}
\]

where

\[
X_{uv}=2A_u\delta_v. \tag{13}
\]

If `X_uv>0`, either endpoint can pay it.  At the tail, (6) gives

\[
A_u\delta_u\ge2A_u\delta_v=X_{uv}; \tag{14}
\]

at the head, (10) gives

\[
A_v\delta_v\ge2A_u\delta_v=X_{uv}. \tag{15}
\]

Thus the chosen owner can pay the excess.

For a two-negative edge oriented `u->v` toward its owner `v`, relabel `r,q`
so that the message from `u` to `v` is `-(2r+1)`.  Its contribution is

\[
E_{uv}=A_u+A_v+2(A_vr+A_uq)
=A_u+A_v+X_{uv}. \tag{16}
\]

By (8), (10), and the fact that `v` is the owner,

\[
X_{uv}=2A_vr+2A_uq
\le A_v(2r+q)=A_v\delta_v. \tag{17}
\]

A neutral edge contributes exactly `A_u+A_v` and has zero excess.

Owners are distinct, so (14)--(17) imply

\[
\sum_eX_e\le\sum_vA_v\delta_v. \tag{18}
\]

Substituting the edge bounds into (11), all defect excesses cancel:

\[
W\le\sum_{uv\in E(T)}(A_u+A_v)
=\sum_v\deg(v)A_v. \tag{19}
\]

## 5. Occupied leaves remove the unwanted leaf weights

Using `A_v>=1`, write the unweighted mass exactly as

\[
|C|=W-\sum_v(A_v-1)C(v). \tag{20}
\]

Every leaf of the minimal support tree is occupied, hence its pebble count is
at least one.  If `L` is the number of leaves, (19)--(20) give

\[
\begin{aligned}
|C|
&\le \sum_v\deg(v)A_v-
      \sum_{\deg(v)=1}(A_v-1)\\
&=L+\sum_{\deg(v)>1}\deg(v)2^{h(v)}. \tag{21}
\end{aligned}
\]

This leaf-slack step is why the auxiliary orientation is allowed to point into
a leaf; unlike the zero-score proof, leaf height zero is not needed.

## 6. Consolidation to one root

For completeness, select for every vertex of positive height one incoming edge
that realizes its height.  The selected edges form connected parts, each with
a unique height-zero root `r_i`, and

\[
h(v)=d(r_i,v)
\]

inside its part.

The connected-partition consolidation lemma says that for nonnegative weights
`w_v`,

\[
\sum_i\sum_{v\in P_i}w_v2^{d(r_i,v)}
\le\max_r\sum_vw_v2^{d(r,v)}. \tag{22}
\]

Here is the short merge proof.  If adjacent parts `A,B` meet across `xy` and
have roots `a,b`, put `alpha=d(a,x)` and `beta=d(b,y)`.  Rerooting the `B`
contribution at `a` multiplies its lower bound by
`2^(alpha+1-beta)`; rerooting the `A` contribution at `b` multiplies its lower
bound by `2^(beta+1-alpha)`.  The exponents sum to two, so at least one is
positive.  Choosing the corresponding root merges the two parts without
decreasing their total potential.  Repeating proves (22).

Apply (22) with

\[
w_v=\begin{cases}
\deg(v),&\deg(v)>1,\\
0,&\deg(v)=1.
\end{cases}
\]

Equation (21) becomes

\[
|C|\le
L+\max_r\sum_{\deg(v)>1}\deg(v)2^{d(r,v)}
=\operatorname{estim}(T)-1 \tag{23}
\]

by (2).  Together with the support reduction and (3), this proves (G) on the
original tree.

## 7. Normalization and the stacking formula

For an estimator-maximizing root `r`, the explicit configuration `C_r` from
`estimator.md` has

\[
|C_r|=\operatorname{estim}(T)-1,
\qquad S_v(C_r)=0\quad\text{for every }v. \tag{24}
\]

Thus the requested normalization statement follows in a stronger form: for
**every** configuration `C` with all scores nonpositive, not only a maximum
one, the fixed zero-score extremizer `C_r` satisfies

\[
|C_r|\ge|C|. \tag{25}
\]

Finally, the branch-message theorem applies to arbitrary configurations and
states

\[
C\text{ is non-stackable}
\iff S_v(C)\le0\quad\text{for every }v.
\]

Hence every non-stackable configuration has at most
`estim(T)-1` pebbles, while (24) is a non-stackable configuration of exactly
that size.  Therefore, for every finite tree with at least two vertices,

\[
\boxed{\operatorname{stack}(T)=\operatorname{estim}(T).} \tag{26}
\]

This is a proof within the project.  It has not yet received external
mathematical review, and no claim of novelty is made here.

## 8. Computational checks

`treestack/src/defect_flow.py` implements the exact edge classification,
support pruning, injective owner assignment, auxiliary heights, defect
cancellation, leaf slack, and consolidation certificate.

The regression suite checks:

- all abstract edge solutions in a broad finite message/defect window;
- every nonzero configuration of total at most 12 on every unlabeled tree of
  orders 2 through 5 that has all scores nonpositive (2,917 configurations);
- pruning an empty exterior branch before applying the integer edge model;
- the smallest coordinatewise-saturation counterexample described in
  `main-inequality.md`.

These computations support the proof but are not used as proof.
