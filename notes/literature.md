# Literature and novelty audit

Status: preliminary, not sufficient for an originality claim.  Last updated
2026-09-21.

## Direct source

Csernák and Soukup, *Stacking and clearing in graph pebbling*,
arXiv:2604.22341v1, introduces the stacking parameter, proves general results,
and states the tree estimator as Conjecture 10.3.  Section 10 gives an
almost-stacked sufficient condition and obtains the upper bound only under the
Almost Stacked Hypothesis.  The arXiv record still describes the tree formula
as conjectural and computationally motivated.

The associated public repository `lajossoukup/pebbling` uses a reverse-state
enumeration over whole configurations.  Inspection at commit
`701cdd93dd19869a9b90947edd6361efd81cfc1f` found no rooted integer-message
solver.  The repository and its Zenodo record are essential provenance for the
order-at-most-seven census, but they do not presently overlap the proposed
linear-time characterization.

## Closest recent work

Adauto, Bardenova, Bidav, and Hurlbert, *Target Pebbling in Trees*,
arXiv:2504.10460, gives polynomial algorithms and extremal descriptions for
satisfying a fixed demand `D` on a tree.  Its main machinery is path partitions,
greedy minimal solutions, and superstack extremal configurations.

The distinction is substantive: target pebbling asks that the final
configuration dominate `D` and allows arbitrary leftovers.  Stackability at a
vertex requires every other vertex to be empty.  Odd residues can therefore
force non-greedy cleanup moves such as `p->v->p`, which ordinary target
reachability may discard.  The branch theorem and zero-score flow argument are
not immediate instances of the target-pebbling algorithm.

A September 2026 search also finds the later Csernák–Soukup paper *Stacking and
Clearing in Directed Graph Pebbling* (arXiv:2606.04659).  Its advertised main
results concern directed graphs and directed cycles; the search did not locate
a resolution of the undirected tree estimator conjecture there.

## Relation of the new zero-score proof to searched machinery

The project now proves the zero-score optimization by an oriented integer
edge-state model, longest-directed-path exponential weights, and a
connected-partition consolidation lemma.  No inspected source has yet been
identified as stating this exact combination.  That observation is **not** a
novelty claim: a full citation-index and terminology audit is still required.

The empty-branch correction is also specific to exact clearing.  An empty
branch is a separate state from integer message zero; replacing it by zero can
create spurious algebraic edge states.  This issue is not automatically visible
in target-reachability formulations that allow leftovers.

## Classical mechanisms checked so far

- Chung's rooted-tree path partitions and `t`-fold pebbling formulas optimize
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
- Broader formula searches using equivalent normalizations of `F`, especially
  threshold/cost rather than signed-gain conventions.
- Direct comparison with demand-pebbling and exact-transformation variants in
  which unwanted leftover pebbles must be eliminated.
- Search for generalized-flow or exponential-potential consolidation lemmas
  equivalent to the new zero-score proof.

No novelty claim should be made until these items are complete.
