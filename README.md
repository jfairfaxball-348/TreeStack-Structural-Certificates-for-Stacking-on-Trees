# TreeStack — Structural Certificates for Stacking on Trees

This repository studies the corrected nontrivial-tree form of the
Csernák–Soukup conjecture

\[
|V(T)|\ge2\implies \operatorname{stack}(T)=\operatorname{estim}(T).
\]

The project has three principal structural results. The completed mathematical
argument has now received external human review; the prior-art/originality audit
remains deliberately conservative and no unsupported priority claim is made:

1. an exact rooted branch-message theorem characterizing stackability at a
   prescribed vertex by the sign of one integer score;
2. an exact solution of the resulting **zero-score generalized-flow problem**,
   proving

   \[
   \max\{|C|:S_v(C)=0\text{ for every }v\}
   =\operatorname{estim}(T)-1.
   \]

3. an arbitrary-defect generalized-flow certificate proving

   \[
   S_v(C)\le0\text{ for every }v
   \implies |C|\le\operatorname{estim}(T)-1.
   \]

Together with the explicit zero-score obstruction, these results prove within
the project that

\[
\operatorname{stack}(T)=\operatorname{estim}(T)
\]

for every finite tree with at least two vertices. External human mathematical
review of the completed result has been completed. The originality/prior-art
audit remains preliminary, so the repository does not infer a priority claim
from mechanization or review alone.

## Reproduce the bounded checks

Use Python 3.9 or later in a virtual environment:

```bash
python -m pip install -e '.[test]'
python -m pytest -q
python -m treestack.src.verify --max-order 6 --max-total 8
```

At the current revision, the pytest suite contains 23 tests.  The verifier
command above checks 131,958 rooted cases from 23,079 configurations on 13
unlabeled trees and stops at the first message/reachability disagreement.

The direct legal-move solver is in `treestack/src/reachability.py`.  The
independent branch-message implementation is in `treestack/src/messages.py`.
The zero-score certificate and consolidation implementation is in
`treestack/src/generalized_flow.py`; the arbitrary-defect certificate is in
`treestack/src/defect_flow.py`.

Proof notes:

- `notes/message-lemma.md` — exact branch theorem;
- `notes/estimator.md` — explicit estimator obstruction and lower bound;
- `notes/zero-score-flow.md` — zero-score generalized-flow theorem;
- `notes/defect-flow.md` — arbitrary-defect generalized-flow theorem;
- `notes/main-inequality.md` — summary of the now-proved global inequality and
  failed stronger local normalization statements;
- `notes/literature.md` — preliminary prior-art audit.

The reproduced published atlas baseline through order 7 is in
`data/published_baseline_through_7.csv`.  No order-11 census is part of this
project stage.


## Lean formalization

The Lean development now machine-checks the corrected nontrivial-tree formula
end to end.  It includes the exact rooted branch-message theorem and score
characterization

\[
\operatorname{StackableAt}(T,C,r) \iff 0 < S_r(C),
\]

the explicit zero-score obstruction of mass
\(\operatorname{estim}(T)-1\), and the arbitrary-defect upper bound

\[
S_v(C)\le0\text{ for every }v
\quad\Longrightarrow\quad
|C|\le\operatorname{estim}(T)-1.
\]

The upper-bound proof stays on the ambient tree throughout.  It combines
weighted defect cancellation, occupied-leaf slack, canonical height-zero
source fibres, and connected-partition consolidation to obtain one root whose
distance profile dominates the auxiliary height profile.

The final Lean layer proves exact-size universality at the estimator and
formalizes the source stacking number as the least exact size \(t\ge2\) for
which every configuration is stackable.  For every finite tree with at least
two vertices, the headline checked theorem is

```text
TreeStack.stack_eq_estim_of_two_le_card :
  2 ≤ Fintype.card V → TreeStack.stack T = TreeStack.estim T
```

The one-vertex case is intentionally excluded because of the source convention
that the stacking threshold is at least two. External human mathematical review
of the completed result has been completed. The prior-art/originality audit
remains conservative; the repository does not claim priority merely from
mechanization or review.

The Lean environment is pinned by `lean-toolchain` and
`lake-manifest.json`. To reproduce the complete validation path:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

See `notes/lean-progress.md` for the exact proved theorem list, dependency
boundary, trust statement, and validation status.


## Palomar packaging status

The protected Palomar statement surface, Solution surface, Comparator
configuration, v0.4 metadata draft, verification documentation, and pinned full
preflight workflow are prepared on the Palomar packaging branch. Registration
has **not** been performed.

The repository now uses the Apache-2.0 licence, with a single root `LICENSE`
file and matching `project.license` metadata. The remaining Palomar gate is
purely mechanical: the full preflight must pass at the exact candidate commit.
See `docs/PALOMAR_PLAN.md` for the freeze protocol.
