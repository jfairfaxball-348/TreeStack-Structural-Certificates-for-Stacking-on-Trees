# Literature and originality audit

**Status:** comprehensive public-record audit completed 2026-09-23.

## Conclusion

No prior published or publicly accessible proof was located of the
Csernák--Soukup tree-stacking estimator conjecture

[
|V(T)|\ge 2 \Longrightarrow \operatorname{stack}(T)=\operatorname{estim}(T),
]

and no equivalent theorem was located under the alternative formulations and
terminology searched below.

Accordingly, as of 2026-09-23, the strongest defensible originality statement
from this audit is:

> The present project appears to contain the first publicly available proof of
> the Csernák--Soukup tree-stacking estimator conjecture identified by a
> comprehensive public-record search.

This is a negative literature-search conclusion, not an absolute priority
guarantee. Unpublished manuscripts, private communications, work not indexed by
the searched public systems, or earlier work using terminology too remote to be
retrieved cannot be ruled out. The conclusion should be corrected if earlier
work is subsequently identified.

## Advertised result checked

The audit was keyed to the exact advertised theorem in the repository:

`TreeStack.stack_eq_estim_of_two_le_card`, asserting that for every finite
simple connected acyclic graph on at least two vertices, the source
Csernák--Soukup stacking number equals their explicit tree estimator.

The one-vertex convention correction is not treated as an originality claim.

## Direct source and current status of the conjecture

Tamás Csernák and Lajos Soukup, *Stacking and clearing in graph pebbling*,
arXiv:2604.22341v1, introduces the stacking and clearing parameters. Section 10
defines the tree estimator, proves the estimator upper bound under the Almost
Stacked Hypothesis, and then states the unconditional equality as Conjecture
10.3. The paper reports computational verification for all trees with at most
seven vertices.

Source: <https://arxiv.org/abs/2604.22341>.

The arXiv record was checked through 2026-09-23. No later version resolving
Conjecture 10.3 was located.

The associated public computation repository was also inspected at commit
`701cdd93dd19869a9b90947edd6361efd81cfc1f`:

<https://github.com/lajossoukup/pebbling>

Its tree-estimation code computes the stacking number by whole-configuration
enumeration and compares it with the estimator on the NetworkX atlas trees. The
generated report records equality on the 24 nontrivial atlas trees through
order seven. No proof of the general tree formula, rooted integer-message
characterization, or generalized-flow certificate was found in that repository.

## Forward and later-work checks

Exact-title, author, arXiv-identifier, formula, and conjecture-number searches
were run through public web and scholarly-index surfaces. Searches included
`2604.22341`, the exact paper title, `Conjecture 10.3`,
`stack(T)=estim(T)`, `sigma_T(r)`, `Almost Stacked Hypothesis`, and
equivalent textual descriptions of moving all pebbles to one vertex.

The later paper by the same authors,

Tamás Csernák and Lajos Soukup, *Stacking and Clearing in Directed Graph
Pebbling*, arXiv:2606.04659v1,

studies the directed analogue and proves an exact formula for directed cycles.
It cites the undirected work but does not resolve the undirected tree estimator
conjecture.

Source: <https://arxiv.org/abs/2606.04659>.

Public arXiv/graph-pebbling listings and exact-title/identifier searches through
2026-09-23 located no later independent paper claiming a proof of the tree
formula. Public searches aimed at Semantic Scholar, OpenAlex, zbMATH,
MathSciNet, Google Scholar, Crossref, and general web indexing likewise located
no independent resolution. Some of those services expose only partial public
index data, so this is recorded as search coverage rather than a claim of
complete database access.

## Closest recent tree work

Matheus Adauto, Viktoriya Bardenova, Yunus Bidav, and Glenn Hurlbert,
*Target Pebbling in Trees*, arXiv:2504.10460v2, later published in
*Discrete Mathematics* 349 (2026), article 115029, gives a polynomial-time
algorithm for the target-pebbling number of a tree and characterizes extremal
configurations.

Source: <https://arxiv.org/abs/2504.10460>.

This is the closest recent tree-pebbling result found, but its target condition
is different. A configuration is (D)-solvable when pebbling moves can leave
**at least** (D(v)) pebbles at each demanded vertex. Extra pebbles elsewhere
may remain. TreeStack stackability instead requires the final configuration to
be supported at a single vertex: every other vertex must be empty.

That distinction is mathematically substantive. Exact clearing can require
moves whose purpose is to eliminate an odd residual pebble, including local
backtracking that ordinary root/target reachability can discard. The
TreeStack branch-message theorem and defect-flow argument therefore do not
follow from the target-pebbling algorithm.

## Classical and adjacent pebbling mechanisms checked

The audit compared the advertised theorem and its proof mechanisms with the
main nearby strands of graph-pebbling literature.

- **Classical rooted and tree pebbling.** Chung's tree formulas and later tree
  algorithms optimize delivery to a prescribed root. They permit unused
  pebbles away from the target.
- **Bunde--Chambers--Cranston--Milans--West, _Pebbling and Optimal Pebbling in
  Graphs_.** This develops ordinary root solvability, a no-cycle lemma,
  squishing/smoothing tools, and a linear-time tree pebbling algorithm. Its
  reachability target is not exact clearing.
  Source: <https://arxiv.org/abs/math/0510621>.
- **Hurlbert, _A Linear Optimization Technique for Graph Pebbling_.** The
  Weight Function Lemma and rooted subtree strategies provide dual upper-bound
  certificates for ordinary root solvability. Related exponential weights do
  not supply the exact-clearing message equations, defect ownership, or
  connected-partition consolidation used here.
  Source: <https://arxiv.org/abs/1101.5641>.
- **Cover pebbling and the Cover Pebbling/Stacking Theorem.** Sjöstrand, and
  independently Vuong--Wyckoff, show that for positive cover demands an
  extremal obstruction may be taken to have its *initial* pebbles stacked at
  one vertex. Older literature therefore uses words such as "stacking" and
  "concentrate all pebbles", but this is an extremal reduction of starting
  configurations, not the Csernák--Soukup operation of legally transforming an
  arbitrary configuration into a stack.
- **Cover rubbling and stacking.** Haynes--Keaton (2020) proves a rubbling
  analogue of the cover-pebbling stacking theorem. Its meaning of stacking is
  the same extremal-initial-distribution notion, not the 2026 stacking number.
  DOI: <https://doi.org/10.1016/j.disc.2020.112080>.
- **Cup stacking.** Fay--Hurlbert--Tennant, *Cup Stacking in Graphs*,
  arXiv:2310.06192, uses "stackable" for a different token-moving game with
  different moves and initial conditions. It is not graph pebbling in the
  Csernák--Soukup sense.
  Source: <https://arxiv.org/abs/2310.06192>.
- **Directed/oriented pebbling.** Older oriented-pebbling work was searched for
  "simple configuration", "concentrate", and all-pebbles-at-one-vertex
  terminology. The matching passages found were again descriptions of
  cover-pebbling extremal reductions or different directed move systems, not
  the undirected tree theorem here.

## Equivalent-terminology and formula searches

To reduce the risk of missing an equivalent result under different language,
the audit searched combinations including:

- stacking number / stackable configuration / stacked configuration;
- concentrate, collect, gather, aggregate, or move all pebbles to one vertex;
- exact reachability, exact transformation, exact clearing, and no leftovers;
- target pebbling, demand pebbling, cover pebbling, rubbling, and cup stacking;
- tree pruning, squishing/squashing, no-cycle and transition-digraph methods;
- integer/generalized flow on trees, gain flow, defect charging, endpoint
  charging, exponential potentials, and weight-function duality;
- direct formula fragments and normalizations involving `stack(T)`,
  `estim(T)`, rooted distance sums, degrees, leaf terms, and
  `sigma_T(r)`.

No searched formulation produced a prior theorem equivalent to
`stack(T)=estim(T)` for all finite nontrivial trees.

## Comparison with the TreeStack proof architecture

The repository's proof has three structural layers that were separately checked
against the searched literature:

1. an exact rooted branch-message theorem characterizing stackability at a
   prescribed root by the sign of a single recursively defined integer score;
2. an explicit zero-score obstruction of mass (operatorname{estim}(T)-1);
3. an arbitrary-defect generalized-flow certificate, using edge-message
   classification, defect ownership/cancellation, exponential height weights,
   source fibres, and connected-partition consolidation to prove the global
   upper bound.

Related ideas occur individually in ordinary pebbling, flow optimization, and
weight-function methods, but no inspected public source was found stating the
same theorem or a result that subsumes these exact-clearing arguments.

## Public-code and repository checks

The source authors' public computation repository was inspected directly as
described above. Web searches for the exact conjecture number, source formula,
and theorem language on public code-hosting surfaces found no separate proof
repository or formalization predating this project.

A global authenticated code-index search across every hosting service was not
available, so this item should be read as a public web/repository search rather
than an exhaustive scan of all private or unindexed code.

## Audit limitations

This audit is intended to be comprehensive for **publicly discoverable prior
work**, not metaphysically exhaustive. In particular:

- no search can exclude unpublished or private work;
- subscription bibliographic databases may expose less information to public
  search than to institutional subscribers;
- terminology can in principle be so different that keyword retrieval misses an
  equivalent theorem;
- no claim is made that the source authors or other domain experts have
  certified priority for this project;
- external human mathematical review of the proof is a separate fact and is not
  treated as an originality certification.

Within those limits, the audit found no prior published or publicly accessible
proof and therefore closes the repository's previously recorded
prior-art/originality gap as of 2026-09-23.

## Re-audit trigger

Before journal submission or if substantial time passes before publication,
rerun the exact-title/arXiv-ID forward search and the graph-pebbling arXiv search
to catch work posted after 2026-09-23. Any earlier proof subsequently located
should be added here and the originality wording in the README and
`formalization.yaml` revised promptly.
