# The explicit estimator obstruction

Status: proved, conditional on the branch-message theorem for the final
non-stackability conclusion.  Together with the exact-size threshold lemma
below, this gives the lower bound `stack(T)>=estim(T)` for every nontrivial
finite tree.  The later arbitrary-defect theorem supplies the matching upper
bound.

Fix a root `r`.  Let `C_r(r)=\sigma_T(r)-1`, put one pebble on every leaf
different from `r`, and put zero elsewhere.  Root the tree at `r`.  For a
non-root vertex `v`, define

\[
h_v=\begin{cases}
1,&v\text{ has no children},\\
3+2\sum_{u\text{ child of }v}h_u,&\text{otherwise}.
\end{cases}
\]

## Closed form

If `T_v` is the descendant subtree at `v`, then

\[
\boxed{h_v=1+2\sum_{\substack{w\in T_v\\\deg_T(w)>1}}
\deg_T(w)2^{d_T(v,w)}}. \tag{1}
\]

For a leaf the sum is empty.  If `v` is not a leaf, use
`#children(v)=\deg_T(v)-1` and the induction hypothesis:

\[
\begin{aligned}
1+2\deg_T(v)+4\sum_u\sum_{\substack{w\in T_u\\\deg_T(w)>1}}
 \deg_T(w)2^{d_T(u,w)}
&=1+2\deg_T(v)+2\sum_u(h_u-1)\\
&=3+2\sum_u h_u.
\end{aligned}
\]

Summing (1) over the children of `r` gives

\[
\sum_{u\text{ child of }r}h_u
=\deg_T(r)+\sum_{\substack{w\ne r\\\deg_T(w)>1}}
 \deg_T(w)2^{d_T(r,w)}
=\sigma_T(r)-1. \tag{2}
\]

The first term is one from each root branch; the factor two in (1) turns
`2^{d_T(u,w)}` into `2^{d_T(r,w)}`.

## Messages

For a leaf `v\ne r`, the upward message is `F(1)=-1=-h_v`.  At a non-leaf
non-root vertex the effective input is

\[
x=C_r(v)+\sum_u d_{u\to v}=-\sum_u h_u\le-1,
\]

so

\[
d_{v\to p}=F(x)=2x-3=-\left(3+2\sum_u h_u\right)=-h_v.
\]

Equations (2) and `C_r(r)=\sigma_T(r)-1` now give `S_r(C_r)=0`.

In fact every score is zero.  Propagate away from `r`.  Suppose the score at a
parent `p` is zero.  Removing the child-branch contribution
`d_{v\to p}=-h_v` shows that the effective input from the `p`-side is `h_v`,
hence `d_{p\to v}=F(h_v)`.  If `v` is a leaf, its other-side input is `1` and
`1+F(1)=0`.  Otherwise write `H=\sum_u h_u\ge1`.  Then `h_v=3+2H`, so

\[
F(h_v)=\frac{h_v-3}{2}=H,
\qquad
S_v(C_r)=-H+H=0.
\]

Thus

\[
\boxed{S_v(C_r)=0\quad\text{for every }v\in V(T).}
\]

Also

\[
|C_r|=(\sigma_T(r)-1)+\operatorname{leaf}(r)
=\sigma_T(r)+\operatorname{leaf}(r)-1.
\]

By the branch-message theorem `C_r` is non-stackable.  Choosing `r` to
maximize the estimator therefore gives a non-stackable configuration of size
`estim(T)-1`.

## Exact-size threshold lemma

The source definition of `stack(T)` quantifies over configurations of exactly
`t` pebbles, so the preceding obstruction needs a short upward-closure lemma.

**Lemma.** Let `G` be a finite connected graph on `n>=2` vertices and let
`t>=2`.  If every configuration of exactly `t` pebbles is stackable, then
`t>n`, and every configuration of exactly `t+1` pebbles is stackable.

**Proof.** If `t<=n`, place one pebble on each of `t` distinct vertices.  The
configuration has support size greater than one and admits no legal move, so it
is not stackable.  Hence `t>n`.

Now let `C` have size `t+1`.  If `C` is already stacked there is nothing to
prove.  Otherwise, since `t+1>n`, some vertex `u` contains at least two pebbles.
Because `G` is connected and nontrivial, `u` has a neighbour `v`.  Make one
legal move `u->v`; the resulting configuration has exactly `t` pebbles and is
stackable by hypothesis.  Prepending the one move shows that `C` is stackable.
`\square`

Consequently the set of universal stackable sizes (above the source lower
cutoff `2`) is upward closed.  Since the estimator-maximizing obstruction has
size `estim(T)-1`, no universal size can be smaller than `estim(T)`.  Therefore

\[
\boxed{\operatorname{stack}(T)\ge\operatorname{estim}(T)}
\]

for every finite tree with at least two vertices.

The arbitrary-defect theorem in `defect-flow.md` gives the reverse inequality,
so this lower bound is one half of the completed proof of the tree formula.
