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
- The current pytest suite has 17 tests.  It includes bounded exhaustive
  zero-score certificate checks, explicit obstruction checks through order 10,
  and the parameter-free height/consolidation inequality for every
  neutral/oriented edge pattern on every unlabeled tree through order 8.
- For every root of every unlabeled tree of orders 2 through 10, the proposed
  explicit obstruction has the claimed size and all message scores zero.
- The authors' 40 tests passed in the earlier source audit, and their
  reverse-state atlas program reproduced equality on the 24 nontrivial trees
  through order 7.  A Python 3.9 compatibility shim for `typing.TypeAlias` was
  needed; their source was not modified.

## Conjectural / not yet completed

- Zero-score normalization for arbitrary maximum-mass non-stackable
  configurations.
- The full global estimator inequality for arbitrary configurations with all
  scores nonpositive.
- Originality of the branch theorem and zero-score proof.
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
  non-stackable configurations can have negative scores.
- Uniqueness of the explicit obstruction is false.  The three-leaf star has the
  distinct tight zero-score obstruction `(0,3,3,3)`.
- Treating an empty branch as message zero creates spurious edge states.  The
  generalized-flow proof must first establish that zero-score nonzero
  configurations have no empty edge side.
