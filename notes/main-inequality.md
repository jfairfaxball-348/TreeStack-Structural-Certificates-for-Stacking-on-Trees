# Main estimator inequality

Status: proved within the project, pending external mathematical review and a
complete prior-art audit.

The global inequality is now

\[
\boxed{
S_v(C)\le0\ (v\in V(T))
\quad\Longrightarrow\quad
|C|\le\operatorname{estim}(T)-1.
} \tag{G}
\]

A self-contained proof is in `defect-flow.md`; an executable certificate is in
`treestack/src/defect_flow.py`.

## Proof architecture

1. Prune empty exterior branches to the minimal subtree spanning the support.
   Scores on the support do not change, every remaining directed message is an
   integer, every remaining edge has nonempty support on both sides, and every
   leaf is occupied.  The estimator cannot decrease when a connected subtree
   is enlarged by adjoining leaves.

2. Put `delta_v=-S_v(C)`.  Across a genuine edge, the two messages are either:

   - an oriented state with nonnegative message `k` from `u` to `v`, reverse
     message `-2(k+delta_v)-3`, and
     `delta_u in {2 delta_v, 2 delta_v+3}`; or
   - two negative messages `-(2r+1), -(2q+1)`, with
     `delta_u=r+2q` and `delta_v=q+2r`.

3. The edges whose defect excess is positive form a forest.  Assign them
   injectively to incident owner vertices.  Keep the forced orientations on
   one-nonnegative-message edges and orient each defective two-negative edge
   toward its owner.  With longest-directed-path weights `A_v=2^h(v)`, each
   edge excess is at most `A_v delta_v` at its distinct owner.

4. The score identity then gives

   \[
   \sum_vA_vC(v)\le\sum_v\deg(v)A_v.
   \]

   Passing back to unweighted mass subtracts
   `sum_v (A_v-1)C(v)`.  Because every support-tree leaf is occupied, this
   pays exactly the unwanted weighted leaf terms and leaves

   \[
   |C|\le L+\sum_{\deg(v)>1}\deg(v)2^{h(v)}.
   \]

5. The connected-partition consolidation lemma replaces the many height-zero
   sources by one root.  The final potential is exactly the estimator minus
   one.

The explicit estimator obstruction at an estimator-maximizing root has this
same mass and has score zero everywhere.  Consequently normalization holds in
the stronger form that every all-nonpositive-score configuration, not merely a
maximum one, can be replaced by a fixed zero-score extremizer without losing
mass.

Combining (G) with the exact branch-message characterization and the explicit
obstruction proves within this project

\[
\operatorname{stack}(T)=\operatorname{estim}(T)
\]

for every finite tree with at least two vertices.  This conclusion is pending
external review; no novelty claim is made.

## Failed stronger local statements

Coordinatewise saturation is false.  On the path with edges
`1-0`, `1-2`, and `0-3`, the configuration

\[
C=(1,3,0,1)
\]

has score vector `(0,0,-3,0)`.  It is non-stackable, but adding one pebble at
any single vertex makes it stackable.  Exhaustive minimization found no such
example on a smaller tree; this one has total mass five and total defect three.

A naive edgewise conversion to zero-score states also fails to preserve
nonnegative vertex counts.  On the same path, `C=(0,0,1,2)` has score vector
`(-4,-2,-4,-11)`.  Replacing each oriented defect state

\[
(k,-2(k+\delta)-3)
\]

by its zero-score state `(k+delta,-2(k+delta)-3)` and each two-negative state
by `(-1,-1)` produces formal vertex counts `(-4,2,1,13)`.  The negative first
coordinate shows why defect cancellation must be global rather than a local
normalization of each edge.

These are counterexamples only to the indicated stronger local methods, not to
normalization or the estimator formula.
