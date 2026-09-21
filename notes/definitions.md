# Definitions and source audit

Status: source-verified on 2026-09-21 against arXiv:2604.22341v1 and commit
`701cdd93dd19869a9b90947edd6361efd81cfc1f` of the authors' public repository.

A configuration on a finite graph is a function (C:V(G)\to\mathbb N).  A
move along (uv) removes two pebbles at (u) and adds one at (v).  A
configuration is stacked when its support has size one, and is stackable when a
stacked configuration is reachable by finitely many moves.

The paper's prose defines `stack(G)` as the least integer (t) for which every
configuration of size (t) is stackable.  Its formal convention elsewhere is
that the minimization starts at (t\ge2).  Thus the printed tree conjecture must
either exclude (K_1) or change that convention: under the convention in the
project brief, `stack(K1)=2` while `estim(K1)=1`.  The authors' `Pebbling`
constructor also rejects graphs with fewer than two vertices.  All work here
uses the corrected domain ​(|V(T)|\ge2).

For a tree (T) and (r\in V(T)), the source defines

\[
\operatorname{leaf}(r)=|\{v\ne r:\deg_T(v)=1\}|,
\]

\[
\sigma_T(r)=1+\sum_{v=r\text{ or }\deg_T(v)>1}
  \deg_T(v)2^{d_T(r,v)},
\qquad
\operatorname{estim}(T)=\max_r(\sigma_T(r)+\operatorname{leaf}(r)).
\]

Code/source detail: the authors' `sigma(r)` method omits the displayed (+1),
and their `tree_estimation()` adds it after maximizing.  The final estimator is
the same; the helper method alone is not the paper's named (\sigma_T(r)).

Sources:

- T. Csernák and L. Soukup, *Stacking and clearing in graph pebbling*,
  arXiv:2604.22341v1, especially Sections 1 and 10.
- `lajossoukup/pebbling`, files `pebbling.py` and
  `atlas_tree_estimation.py`, commit recorded above.

