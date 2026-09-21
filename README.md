# TreeStack — Structural Certificates for Stacking on Trees

This repository studies the corrected nontrivial-tree form of the
Csernák–Soukup conjecture

\[
|V(T)|\ge2\implies \operatorname{stack}(T)=\operatorname{estim}(T).
\]

The project currently has three structural results, all pending external review
and a complete prior-art audit:

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

for every finite tree with at least two vertices.  The proof has not yet
received external mathematical review, and the originality audit is still
preliminary.  The repository therefore does not claim a new theorem of record.

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

Lean Phase 1 is underway. The current formal development has machine-checked
the exact-size stacking semantics, the audit repair proving upward closure of
universal exact sizes, the arithmetic core of the branch transfer function,
the source-exact estimator with its elementary lower bound, strict child-branch
containment/cardinality decrease, and the well-founded recursive branch
message with `EMPTY` kept separate from integer zero. Move-signature and
branch-local legal-reachability structures now state the exact boundary
invariant precisely. The immediate formal frontier is proving that invariant;
the rooted score theorem remains downstream.

The Lean environment is pinned by `lean-toolchain` and
`lake-manifest.json`. To reproduce the full CI path:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

See `notes/lean-progress.md` for the exact proved theorem list, dependency
boundary, trust statement, and remaining obligations.
