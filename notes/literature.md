# Literature and novelty audit

Status: preliminary, not sufficient for an originality claim.  Last updated
2026-09-21 after the arbitrary-defect proof was obtained.

## Direct source

Csernák and Soukup, *Stacking and clearing in graph pebbling*,
arXiv:2604.22341v1, introduces the stacking parameter, proves general results,
and states the tree estimator as Conjecture 10.3.  Section 10 gives an
almost-stacked sufficient condition and obtains the upper bound only under the
Almost Stacked Hypothesis.  The arXiv record still describes the tree formula
as conjectural and computationally motivated.  As of 2026-09-21, its submission
history still lists only v1 (2026-04-24).

Source: <https://arxiv.org/abs/2604.22341>.

The associated public repository `lajossoukup/pebbling` uses a reverse-state
enumeration over whole configurations.  Inspection at commit
`701cdd93dd19869a9b90947edd6361efd81cfc1f` found no rooted integer-message
solver.  The repository and its Zenodo record are essential provenance for the
order-at-most-seven census, but they do not presently overlap the proposed
linear-time characterization.

## Closest recent work

Adauto, Bardenova, Bidav, and Hurlbert, *Target Pebbling in Trees*,
arXiv:2504.10460v2, gives polynomial algorithms and extremal descriptions for
satisfying a fixed demand `D` on a tree.  Its main machinery is path partitions,
greedy minimal solutions, and superstack extremal configurations.  The paper's
definition says explicitly that a configuration is `D`-solvable if a sequence
places **at least** `D(v)` pebbles at each vertex.  It neither requires nor
tracks the removal of pebbles outside the demand support.

The distinction is substantive: target pebbling asks that the final
configuration dominate `D` and allows arbitrary leftovers.  Stackability at a
vertex requires every other vertex to be empty.  Odd residues can therefore
force non-greedy cleanup moves such as `p->v->p`, which ordinary target
reachability may discard.  The branch theorem and zero-score flow argument are
not immediate instances of the target-pebbling algorithm.

Source: <https://arxiv.org/abs/2504.10460> (v2 dated 2026-01-22; definition in
Section 1.2).

A September 2026 search also finds the later Csernák–Soukup paper *Stacking and
Clearing in Directed Graph Pebbling* (arXiv:2606.04659).  Its advertised main
results concern existence on strongly connected digraphs and an exact formula
for directed cycles.  Inspection did not locate a resolution of the undirected
tree estimator conjecture there.

Source: <https://arxiv.org/abs/2606.04659>.

Exact-title, arXiv-ID, author, and formula searches on 2026-09-21 found this
directed follow-up and secondary summaries, but no later paper claiming a proof
of the undirected tree formula.  This is evidence about the searches performed,
not a complete citation-index audit and not a novelty claim.

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

## Audit after the arbitrary-defect proof

The proof in `defect-flow.md` uses an exact classification of the two directed
messages on an edge with endpoint defects, an injective assignment of defective
forest edges to endpoints, and exponential longest-path weights.  A targeted
search was made for this combination and for equivalent terminology: exact
configuration transformation, demand pebbling, tree pruning,
squishing/squashing, transition digraphs, no-cycle lemmas, generalized and
integer flows on trees, discrete convex optimization on trees, and pebbling
weight-function duality.

The closest inspected mechanisms remain different:

- Bunde–Chambers–Cranston–Milans–West, *Pebbling and Optimal Pebbling in
  Graphs*, defines ordinary root reachability, uses the no-cycle lemma, gives a
  tree pebbling algorithm, and proves a squishing lemma for root-unsolvable
  distributions.  Its target condition is reaching a root, so unused pebbles
  may remain.  Its no-cycle reduction is not valid verbatim for exact clearing,
  where an odd residual pebble can require moves in both directions on an edge.
  Source: <https://arxiv.org/abs/math/0510621>.
- Hurlbert, *A Linear Optimization Technique for Graph Pebbling*, develops the
  Weight Function Lemma and dual certificates from rooted subtree strategies.
  It concerns ordinary root solvability.  The exponential weights are related
  in spirit, but no inspected statement supplies the defect-edge equations,
  injective owner cancellation, or exact-clearing conclusion used here.
  Source: <https://arxiv.org/abs/1101.5641>.
- General discrete-convex and submodular-flow searches found broad integer
  optimization frameworks, but no source identified the transfer map or the
  tree-specific defect-owner inequality in this project.  Because terminology
  may differ, this negative search result is not sufficient for originality.

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

- A reliable citation-index check for every work citing arXiv:2604.22341 and
  later journal metadata.  Web search found only the same authors' directed
  follow-up, but that is not a complete citation graph.
- Full-text inspection of the tree/outerplanar reachability algorithms and
  weighted-graph pebbling algorithms, not only abstracts and keyword searches.
- Broader formula searches using equivalent normalizations of `F`, especially
  threshold/cost rather than signed-gain conventions.
- Direct comparison with demand-pebbling and exact-transformation variants in
  which unwanted leftover pebbles must be eliminated.
- Search for generalized-flow, endpoint-charging, or exponential-potential
  consolidation lemmas equivalent to either generalized-flow proof.
- Expert comparison of the arbitrary-defect owner argument with pebbling
  weight-function duality and integer generalized-flow duality.

No novelty claim should be made until these items are complete.
