# TreeStack — Structural Certificates for Stacking on Trees

This repository studies the corrected nontrivial-tree form of the
Csernák–Soukup conjecture

\[
|V(T)|\ge2\implies \operatorname{stack}(T)=\operatorname{estim}(T).
\]

The project currently has two structural results, both pending external review
and a complete prior-art audit:

1. an exact rooted branch-message theorem characterizing stackability at a
   prescribed vertex by the sign of one integer score;
2. an exact solution of the resulting **zero-score generalized-flow problem**,
   proving

   \[
   \max\{|C|:S_v(C)=0\text{ for every }v\}
   =\operatorname{estim}(T)-1.
   \]

The full conjecture is **not yet proved**.  The remaining gap is global
normalization: configurations with all scores nonpositive but some scores
strictly negative still have to be bounded by the same estimator, or reduced to
zero-score configurations without losing mass.

## Reproduce the bounded checks

Use Python 3.9 or later in a virtual environment:

```bash
python -m pip install -e '.[test]'
python -m pytest -q
python -m treestack.src.verify --max-order 6 --max-total 8
```

At the current revision, the pytest suite contains 17 tests.  The verifier
command above checks 131,958 rooted cases from 23,079 configurations on 13
unlabeled trees and stops at the first message/reachability disagreement.

The direct legal-move solver is in `treestack/src/reachability.py`.  The
independent branch-message implementation is in `treestack/src/messages.py`.
The zero-score certificate and consolidation implementation is in
`treestack/src/generalized_flow.py`.

Proof notes:

- `notes/message-lemma.md` — exact branch theorem;
- `notes/estimator.md` — explicit estimator obstruction and lower bound;
- `notes/zero-score-flow.md` — zero-score generalized-flow theorem;
- `notes/main-inequality.md` — the remaining global inequality and
  normalization gap;
- `notes/literature.md` — preliminary prior-art audit.

The reproduced published atlas baseline through order 7 is in
`data/published_baseline_through_7.csv`.  No order-11 census is part of this
project stage.
