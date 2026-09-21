# Research log

## Proved (pending external review)

- Exact branch-boundary invariant and the branch-message characterization;
  see `message-lemma.md`.

## Computationally verified

- Independent legal-move reachability and message solvers agree on all roots
  in the bounded test suite.  The largest explicit falsification run so far
  covered 1,839,827 rooted cases from 273,339 configurations on all 24
  unlabeled trees of orders 2 through 7, with total size at most 10.
- For every root of every unlabeled tree of orders 2 through 10, the proposed
  extremal configuration has the claimed size and all message scores zero.
- The authors' 40 tests pass and their reverse-state atlas program reproduces
  equality on the 24 nontrivial trees through order 7.  A Python 3.9 runtime
  compatibility shim for `typing.TypeAlias` was needed; their source was not
  modified.

## Conjectural / not yet completed

- The global estimator inequality for arbitrary non-stackable configurations.
- Originality of the branch theorem.
- Lean formalization.
- Independent reproduction in this repository of the pilot census rows for
  orders 8 through 10.

## Failed or dangerous approaches

- Plain nonnegative move-count balance equations are insufficient: for
  effective pile zero they admit a zero-boundary-flow solution that cannot be
  legally scheduled.  Requiring at least one outward boundary move for a
  nonempty cleared branch repairs the upper-bound argument.
- A no-cycle lemma cannot simply be imposed.  Clearing an odd residue may
  require both directions of the same edge (for example, the final
  (p\to v\to p) cleanup).
