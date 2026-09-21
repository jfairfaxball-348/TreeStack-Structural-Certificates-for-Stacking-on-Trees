# Main estimator inequality: current attack

Status: open in full.  The zero-score case is now proved exactly; the remaining
bottleneck is normalization from arbitrary nonpositive scores.

The target is

\[
S_v(C)\le0\ (v\in V(T))\quad\Longrightarrow\quad
|C|\le\operatorname{estim}(T)-1. \tag{G}
\]

## What is now proved

The branch-message theorem reduces non-stackability to the simultaneous score
inequalities `S_v(C)<=0`.  The explicit estimator obstruction proves
`stack(T)>=estim(T)` for every nontrivial tree.

The new zero-score theorem, proved in `zero-score-flow.md`, is

\[
\boxed{S_v(C)=0\ \forall v
\quad\Longrightarrow\quad
|C|\le\operatorname{estim}(T)-1.} \tag{Z}
\]

Moreover the bound in (Z) is sharp: the explicit estimator obstruction at an
estimator-maximizing root has all scores zero and size `estim(T)-1`.

The proof of (Z) has four ingredients:

1. a nonzero genuine zero-score configuration has no empty side of any edge;
2. the integer edge states are exactly neutral `(-1,-1)` or oriented
   `(k,-2k-3)` states;
3. longest directed-path heights give a dual exponential weighting that bounds
   mass by a multi-root degree potential;
4. a connected-partition merge lemma consolidates that potential to one root,
   where it is exactly the estimator minus one.

An earlier version of this note described the integer edge-state model as an
unqualified equivalence.  That was too strong because an empty branch is not an
integer message zero.  The no-empty-side lemma in `zero-score-flow.md` repairs
the equivalence for every nonzero genuine zero-score configuration.

## Useful reparameterization for the remaining problem

Root the tree temporarily.  For every non-root `v`, let

\[
x_v=C(v)+\sum_{u\text{ child of }v}d_{u\to v},
\qquad d_{v\to p}=F(x_v),
\]

and put `x_r=S_r(C)`.  Telescoping gives

\[
|C|=x_r+\sum_{v\ne r}\bigl(x_v-F(x_v)\bigr). \tag{1}
\]

If `s_v=S_v(C)` and `v` has parent `p`, then

\[
d_{p\to v}=F(s_p-F(x_v)),
\qquad
s_v=x_v+F(s_p-F(x_v)). \tag{2}
\]

The transfer map is not monotone at every adjacent pair, so simply increasing a
negative score toward zero is not automatically safe.

## Remaining normalization problem

It would now suffice to prove:

> For every maximum-total-size configuration `C` with `S_v(C)<=0` for all
> vertices, there exists a configuration `C'` with `|C'|>=|C|` and
> `S_v(C')=0` for every vertex.

This statement is still open in the project.  Coordinatewise saturation is not
valid: bounded searches already contain coordinatewise-maximal non-stackable
configurations with negative scores.  Also maximum obstructions are not unique;
on the three-leaf star, `(0,3,3,3)` is a tight zero-score obstruction but is not
one of the explicit root configurations.

Therefore a proof of (G) still needs a genuinely global argument, for example a
mass-preserving normalization, induction deleting negative-score defects, or a
dual certificate that works directly for all nonpositive scores.

Do not claim the tree conjecture is solved until this remaining step is proved
for arbitrary configurations.
