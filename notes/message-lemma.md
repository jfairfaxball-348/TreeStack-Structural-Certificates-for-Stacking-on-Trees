# Branch-message theorem

Status: proof obtained; independently checked computationally on bounded
instances.  It has not yet passed a prior-art audit or external review.

## Statement

Let (B) be the component on the (v)-side of an oriented edge (v\to p),
and assume that the restriction of (C) to (B) is nonempty.  Define its
message recursively by

\[
d(B)=F\left(C(v)+\sum_i d(B_i)\right),
\]

where the sum is over the nonempty child branches and

\[
F(x)=\begin{cases}
2x-3,&x\le1,\\
1,&x=2,\\
0,&x=3,\\
x/2,&x\ge4\text{ even},\\
(x-3)/2,&x\ge5\text{ odd}.
\end{cases}
\]

An empty branch has a separate symbol ​(\varnothing), not integer message
zero.

**Exact boundary invariant.** If the boundary vertex (p) initially has
(q\ge0) pebbles and no moves outside (B\cup\{p\}) are allowed, the largest
number of pebbles that can remain at (p) after clearing all of (B) is
(q+d(B)), provided this number is positive.  If (q+d(B)\le0), clearing (B)
to a positive stack at (p) is impossible.

Taking the child branches of a proposed target (r) gives

\[
\operatorname{StackableAt}(C,r)\iff
S_r(C):=C(r)+\sum_{u\sim r}d_{u\to r}>0.
\]

## Move-count upper bound

A clearing sequence has a **signature** (m_{a\to b}\in\mathbb N), the number
of times each oriented edge is used.  For every (w\in B), clearing imposes

\[
C(w)+\sum_{z\sim w}m_{z\to w}
-2\sum_{z\sim w}m_{w\to z}=0. \tag{1}
\]

Its boundary flux is

\[
\phi=m_{v\to p}-2m_{p\to v};
\]

the final pile at (p) is (q+\phi).  Because (B) is initially nonempty and
ends empty, at least one move (v\to p) occurs: the last move that removes the
last pebble from (B) must cross its only boundary.  This causal condition is
essential.  Balance equations without it admit unschedulable phantom
solutions when the effective pile is nonpositive.

An initially empty child branch needs a separate observation, because a legal
sequence may use it temporarily even though the recursive algorithm omits it.
If such a branch starts and ends empty, let $M$ be the number of moves whose
edge lies in the branch or is its boundary edge.  Summing pebble counts over the
branch shows that its net boundary flux is $-M\le0$.  Pebbling preserves the
bipartite imbalance modulo three; since both endpoint configurations are
supported outside the branch, this flux is also zero modulo three.  Hence every
empty-branch excursion has flux $-3k$ for some $k\ge0$, while doing nothing has
flux zero.  Empty branches can therefore lower, but never raise, the upper
bound below.

The following arithmetic lemma is the core.  For an integer (y), suppose
(A\ge1), (B\ge0), and

\[
y+B-2A=0.
\]

Then

\[
A-2B\le F(y),\qquad A-2B\equiv F(y)\pmod 3. \tag{2}
\]

Equality is attained at (A=\max(1,\lceil y/2\rceil)).  For (y\le1), this
gives (A=1,B=2-y) and flux (2y-3).  For (y=2k\ge2), it gives
(A=k,B=0) and flux (k).  For (y=2k+1\ge3), it gives
(A=k+1,B=1) and flux (k-1).  Increasing (A) by one forces (B) to
increase by two and lowers flux by three.

Induct on the branch.  Restrict a signature to each child branch.  By induction
the flux of a nonempty child has the form

\[
\phi_i=d_i-3k_i\quad(k_i\ge0).
\]

An empty child has flux $-3k_i$ by the preceding observation, so it may be
included with formal gain zero for this upper-bound calculation only.

At (v), put (x=C(v)+\sum_i d_i) and (K=\sum_i k_i).  Equation (1) at
(v) is the one-vertex equation (2) with effective value (y=x-3K).  Hence

\[
\phi\le F(x-3K)\le F(x).
\]

The last inequality follows by checking that (F(z-3)\le F(z)) for every
integer (z).  Congruence in (2) also gives
(\phi\equiv F(x)\pmod3), completing the induction.  Therefore every legal
clearing sequence finishes with at most (q+d(B)) pebbles at the boundary.

## Legal construction attaining the bound

We prove attainability simultaneously by induction.  First use this scheduling
fact: starting with (a\ge0) pebbles at a vertex and child tasks of integer
gains (d_i), if (a+\sum_i d_i>0), all tasks can be legally completed with
that final pile.  Process positive gains first, then zero gains, then negative
gains.  A positive task is legal even from zero.  If any nonpositive task
remains, positivity of the final total makes the pile after the positive tasks
strictly positive.  During the negative tasks every intermediate pile is at
least the final positive pile.  The induction hypothesis realizes each task
legally and changes the pile by exactly its gain.  Empty branches are omitted;
including them as zero tasks would make this statement false at pile zero.

Let (x=C(v)+\sum_i d_i).

- If (x\ge2), the scheduling fact clears the children and leaves (x)
  pebbles at (v).  If (x) is even, perform (x/2) moves (v\to p).  If
  (x\ge3) is odd, first perform ((x-1)/2) moves (v\to p), leaving one at
  (v); then perform (p\to v\to p).  The hypothesis
  (q+F(x)>0) supplies the two boundary pebbles needed for the middle move.
  The final boundary pile is (q+F(x)).  This includes (x=2) and (x=3).

- If (x\le1), set (j=2-x).  The condition (q+F(x)>0) is exactly
  (q\ge2j).  Make (j) moves (p\to v), use the scheduling fact on the
  children (now the effective pile is (x+j=2)), and finish with one move
  (v\to p).  The final boundary pile is
  (q-2j+1=q+2x-3=q+F(x)).

This proves sufficiency and equality in the exact boundary invariant.  Combined
with the signature upper bound, it proves necessity.

## Target-root theorem and the “survivor inside a branch” issue

For a fixed target (r), its nonempty incident branches are disjoint tasks with
initial pile (C(r)).  The scheduling fact says that they can all be cleared
exactly when (S_r(C)>0).  Necessity follows by applying the signature bound to
each nonempty branch, the nonpositive $-3k$ bound to any used empty branch,
and the balance at (r).

The branch invariant deliberately assumes that the final survivor is at its
external boundary.  A sequence whose survivor is inside that branch is instead
tested by choosing that interior vertex as the target.  Thus stackability
without a prescribed target is equivalent to (S_r(C)>0) for at least one
vertex (r); no survivor location is discarded.
