# TreeStack — Structural Certificates for Stacking on Trees

This repository studies the corrected nontrivial-tree form of the
Csernák–Soukup conjecture

\[
|V(T)|\ge2\implies \operatorname{stack}(T)=\operatorname{estim}(T).
\]

The current main result is a proof candidate for an exact rooted-tree branch
message theorem.  It is separated from the still-open global estimator
inequality and from the unfinished literature/novelty audit.

## Reproduce the bounded checks

Use Python 3.9 or later in a virtual environment:

```bash
python -m pip install -e '.[test]'
python -m pytest -q
python -m treestack.src.verify --max-order 6 --max-total 8
```

The direct solver in `treestack/src/reachability.py` enumerates only legal
moves.  The independent structural implementation is in
`treestack/src/messages.py`.  Tests stop immediately at the first disagreement.

The proof and its exact invariant are in `notes/message-lemma.md`; source
definitions and the (K_1) domain correction are in `notes/definitions.md`.
The reproduced published atlas baseline is in
`data/published_baseline_through_7.csv`.  The pilot's order 8--10 equality
claims have not yet been independently regenerated in this clean repository;
the order counts and extremal-message identities are tested through order 10.

