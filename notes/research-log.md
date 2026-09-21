# Research log

## Proved (pending external review)

- Exact branch-boundary invariant and the branch-message characterization; see
  `message-lemma.md`.
- Explicit estimator obstruction with all scores zero, giving
  `stack(T)>=estim(T)` for every nontrivial finite tree; see `estimator.md`.
- Zero-score generalized-flow theorem:

  \[
  \max\{|C|:S_v(C)=0\ \forall v\}=\operatorname{estim}(T)-1.
  \]

  See `zero-score-flow.md`.
- Connected-partition exponential-potential consolidation lemma used in the
  zero-score proof.
- Arbitrary-defect generalized-flow theorem:

  \[
  S_v(C)\le0\ \forall v
  \quad\Longrightarrow\quad
  |C|\le\operatorname{estim}(T)-1.
  \]

  The proof prunes empty exterior branches, classifies every genuine defect
  edge, injectively assigns defective edges to endpoint owners, cancels every
  edge excess with its owner's defect budget under exponential height weights,
  uses occupied-leaf slack, and applies the existing consolidation lemma.  See
  `defect-flow.md`.
- Global normalization, in the stronger form that every configuration with all
  scores nonpositive can be replaced without mass loss by the fixed explicit
  zero-score obstruction at an estimator-maximizing root.
- Combining the global inequality with the exact branch theorem and explicit
  obstruction proves within the project

  \[
  \operatorname{stack}(T)=\operatorname{estim}(T)
  \]

  for every finite tree with at least two vertices.  This conclusion is
  pending external mathematical review and a complete prior-art audit.

## Correction made during the zero-score audit

The raw integer equations

\[
a=F(-b),\qquad b=F(-a)
\]

are not by themselves equivalent to a genuine configured-tree edge state,
because an empty branch is a separate symbol from integer zero.  For example,
on `K_2` the configuration `(3,0)` has one integer message zero and one empty
message; its scores are `(3,0)`, not `(0,0)`.

For every **nonzero all-zero-score** configuration the problem disappears: no
side of any edge can be empty.  If one side were empty, the opposite endpoint's
zero score would make the return message `F(0)=-3`, forcing score `-3` on the
empty side.  The repaired edge-state equivalence is now stated with this lemma.

## Computationally verified

- Independent legal-move reachability and message solvers agree on all roots in
  the bounded test suite.  The larger historical run covered 1,839,827 rooted
  cases from 273,339 configurations on all 24 unlabeled trees of orders 2
  through 7, with total size at most 10.
- Current regression command
  `python -m treestack.src.verify --max-order 6 --max-total 8` verifies 131,958
  rooted cases from 23,079 configurations on 13 trees.
- The arbitrary-defect certificate was checked during development on 31,389
  nonzero configurations with all scores nonpositive, over every unlabeled
  tree of orders 2 through 6 and total size at most 12.  The permanent bounded
  regression covers the analogous 2,917 configurations through order 5.
- The current pytest suite has 22 tests.  It includes the earlier zero-score
  checks plus the exact defect-edge classification on defects 0 through 12 and
  messages -50 through 20, support pruning, the minimized
  coordinatewise-saturation counterexample, and the failed naive edgewise
  zero-state replacement.
- For every root of every unlabeled tree of orders 2 through 10, the proposed
  explicit obstruction has the claimed size and all message scores zero.
- The authors' 40 tests passed in the earlier source audit, and their
  reverse-state atlas program reproduced equality on the 24 nontrivial trees
  through order 7.  A Python 3.9 compatibility shim for `typing.TypeAlias` was
  needed; their source was not modified.

## Pending review / not yet completed

- External mathematical review of the branch theorem, zero-score proof, and
  arbitrary-defect proof.
- Originality of the branch theorem and the two generalized-flow arguments.
- Lean formalization.
- Independent reproduction in this repository of the pilot census rows for
  orders 8 through 10.

## Failed or dangerous approaches

- Plain nonnegative move-count balance equations are insufficient: for
  effective pile zero they admit a zero-boundary-flow solution that cannot be
  legally scheduled.  Requiring at least one outward boundary move for a
  nonempty cleared branch repairs the upper-bound argument.
- A no-cycle lemma cannot simply be imposed.  Clearing an odd residue may
  require both directions of the same edge, for example the final
  `p->v->p` cleanup.
- Coordinatewise saturation cannot prove normalization: coordinatewise-maximal
  non-stackable configurations can have negative scores.  A minimized example
  is `(1,3,0,1)` on the four-vertex path with edges `1-0, 1-2, 0-3`; its scores
  are `(0,0,-3,0)`, yet adding one pebble at any vertex makes it stackable.
- Naively replacing each defect edge by its corresponding zero-score edge
  state need not produce nonnegative vertex counts.  On the same path,
  `(0,0,1,2)` has scores `(-4,-2,-4,-11)`, while the formal edgewise
  replacement produces counts `(-4,2,1,13)`.
- Uniqueness of the explicit obstruction is false.  The three-leaf star has the
  distinct tight zero-score obstruction `(0,3,3,3)`.
- Treating an empty branch as message zero creates spurious edge states.  The
  generalized-flow proof must first establish that zero-score nonzero
  configurations have no empty edge side.
