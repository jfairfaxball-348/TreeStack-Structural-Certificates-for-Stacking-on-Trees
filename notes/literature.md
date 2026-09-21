# Literature and novelty audit

Status: preliminary, not sufficient for an originality claim.

## Direct source

Csernák and Soukup, *Stacking and clearing in graph pebbling*,
arXiv:2604.22341v1, introduces the stacking parameter, proves general results,
and states the tree estimator as Conjecture 10.3.  Section 10 gives an
almost-stacked sufficient condition and obtains the upper bound only under the
Almost Stacked Hypothesis.  It does not state the branch recursion in this
repository.  As of 2026-09-21 arXiv lists only v1 (24 April 2026).

The associated public repository `lajossoukup/pebbling` uses a reverse-state
enumeration over whole configurations.  Inspection at commit
`701cdd93dd19869a9b90947edd6361efd81cfc1f` found no rooted integer-message
solver.  The repository and its Zenodo record are essential provenance for the
order-at-most-seven census, but they do not presently overlap the proposed
linear-time characterization.

## Closest recent work

Adauto, Bardenova, Bidav, and Hurlbert, *Target Pebbling in Trees*,
arXiv:2504.10460v2 (later published in *Discrete Mathematics*), gives polynomial
algorithms and extremal descriptions for satisfying a fixed demand (D) on a
tree.  Its main machinery is path partitions, greedy minimal solutions, and
superstack extremal configurations.  A source-level search of v2 found no
piecewise recurrence matching (F), no signed branch surplus, and no exact
branch-clearing invariant.

The distinction is substantive: target pebbling asks that the final
configuration dominate (D) and allows arbitrary leftovers.  Stackability at
(r) requires every non-(r) vertex to be empty.  Odd residues therefore force
non-greedy cleanup moves (p\to v\to p), which standard target reachability can
discard.  Thus the new theorem is not an immediate instance of their target
algorithm, although their extremal-configuration transformations may be useful
for the global estimator inequality.

## Classical mechanisms checked so far

- Chung's rooted-tree path partitions and (t)-fold pebbling formulas optimize
  delivery to a fixed target, not exact clearing of all other vertices.
- The cover pebbling/stacking theorem (Sjöstrand; independently Vuong and
  Wyckoff) concerns positive target demands and extremal initial stacks.
- Squishing/squashing lemmas reduce the location of obstructions on threads;
  they do not provide the signed exact-clearing transfer used here.
- No-cycle/transition-digraph lemmas certify ordinary target reachability after
  deleting cycles.  They cannot be applied verbatim here: exact clearing of an
  odd branch can require both orientations of one edge.
- Existing tree and outerplanar reachability algorithms prune branches by
  moving as many pebbles as possible toward a fixed target.  That state is
  nonnegative and does not encode the cost of removing a residual singleton.

## Searches still required

- Citation-index checks for every work citing arXiv:2604.22341 and later journal
  metadata.
- Full-text inspection of the tree/outerplanar reachability algorithms and
  weighted-graph pebbling algorithms, not only abstracts and keyword searches.
- Broader GitHub and arXiv formula searches using equivalent normalizations of
  (F), especially a threshold/cost rather than signed-gain convention.
- Direct comparison with demand-pebbling and exact-transformation variants in
  which unwanted leftover pebbles must be eliminated.

No novelty claim should be made until these items are complete.

