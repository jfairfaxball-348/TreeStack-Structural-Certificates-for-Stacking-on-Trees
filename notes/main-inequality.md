# Main estimator inequality: current attack

Status: open.  This note records reductions and falsified stronger claims.

The target is

\[
S_v(C)\le0\ (v\in V(T))\quad\Longrightarrow\quad
|C|\le\operatorname{estim}(T)-1.
\]

## A useful reparameterization

Root the tree temporarily.  For every non-root (v), let

\[
x_v=C(v)+\sum_{u\text{ child of }v}d_{u\to v},
\qquad d_{v\to p}=F(x_v),
\]

and put (x_r=S_r(C)).  Telescoping gives the exact identity

\[
|C|=x_r+\sum_{v\ne r}\bigl(x_v-F(x_v)\bigr). \tag{1}
\]

If (s_v=S_v(C)) and (v) has parent (p), the message from the parent side
and the score satisfy

\[
d_{p\to v}=F(s_p-d_{v\to p}),
\qquad
s_v=x_v+F(s_p-F(x_v)). \tag{2}
\]

Equations (1)--(2) turn the problem into an integer optimization on a tree,
but (F) is not monotone at every adjacent pair, so a naive convexity argument
does not suffice.

## Complete description when all scores are zero

Suppose (S_v(C)=0) for every vertex.  For an edge (uv), write
(a=d_{u\to v}) and (b=d_{v\to u}).  Then

\[
a=F(-b),\qquad b=F(-a).
\]

The integer solutions are exactly

\[
(a,b)=(-1,-1),
\quad (k,-2k-3),
\quad (-2k-3,k)
\qquad(k\ge0). \tag{3}
\]

Indeed, a nonnegative entry (k) forces the other entry to be
(F(-k)=-2k-3), and (F(2k+3)=k); the only solution with neither entry
nonnegative is ((-1,-1)).

Moreover,

\[
C(v)=-\sum_{u\sim v}d_{u\to v}. \tag{4}
\]

Thus zero-score configurations are equivalent to the following edge-state
model:

- a neutral edge contributes message (-1) at each endpoint and total mass 2;
- an oriented edge with parameter (k\ge0) contributes (-2k-3) at its tail,
  (k) at its head, and total mass (k+3);
- at each vertex the sum of incoming endpoint contributions is nonpositive.

This is an exact generalized-flow formulation on the tree.  Proving that its
maximum is

\[
\max_r\bigl(\sigma_T(r)+\operatorname{leaf}(r)-1\bigr)
\]

is a concrete subproblem.  A second required step is to show that an arbitrary
maximum-mass non-stackable configuration can be replaced, without losing mass,
by a zero-score one.

## Stronger statements already falsified

The maximum obstruction need not be unique and need not equal one of the
explicit (C_r).  On the three-leaf star, the configuration with zero at the
center and three pebbles at every leaf has total mass 9, all scores zero, and is
extremal; it is not any (C_r).  Similar extra extremizers occur already on
(P_3) and the four-vertex star.

Nor is every coordinatewise-maximal non-stackable configuration zero-score.
Small exhaustive searches find maximal configurations with some score (-3).
The more plausible statement, consistent with all current tests, is only that a
*maximum-total-mass* obstruction can be chosen with every score zero.

These examples rule out a proof based on uniqueness of the (C_r), while
leaving open a mass-preserving normalization to an explicit or zero-score
extremizer.

