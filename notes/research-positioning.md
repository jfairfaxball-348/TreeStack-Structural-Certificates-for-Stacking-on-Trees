# Research positioning

Date: 2026-09-21  
Scope: positioning after an independent adversarial proof audit of the corrected tree-stacking theorem.

## Recommendation

The paper should lead with the **resolution of the corrected Csernák--Soukup tree-stacking conjecture**, not with the computational work and not with the zero-score theorem alone. The exact branch certificate and the arbitrary-defect owner/cancellation theorem should be presented as the structural mechanisms that make the resolution possible.

The most defensible hierarchy is:

1. headline theorem: for every finite tree with at least two vertices, `stack(T)=estim(T)`;
2. exact rooted branch-message certificate for exact clearing on trees;
3. arbitrary-defect generalized-flow / endpoint-owner theorem bounding every all-nonpositive-score configuration by `estim(T)-1`;
4. zero-score generalized-flow theorem as a clean special case and conceptual bridge;
5. algorithmic corollary: the branch messages give a linear-size / linear-time dynamic certificate for stackability on a configured tree, subject to routine implementation-model qualifications.

The theorem is mathematically defensible from the present proof after inserting the universal-size upward-closure lemma identified in `independent-proof-audit.md`. Novelty is not yet defensible as a categorical statement of “first proof”; negative searches do not establish priority.

## Proposed title

**Stacking on Trees: Exact Branch Certificates and the Csernák--Soukup Formula**

A more conservative title, if priority remains uncertain, is **Structural Certificates for Exact Stacking on Trees**.

## Proposed abstract

We study the stacking number introduced by Csernák and Soukup: the least `t>=2` such that every configuration of `t` pebbles on a graph can be transformed by pebbling moves into a configuration supported on a single vertex. For a finite tree with at least two vertices, we prove the estimator formula conjectured by Csernák and Soukup. The proof has two structural ingredients. First, we associate a signed integer message to every nonempty oriented branch and prove an exact boundary invariant; this gives a root-by-root characterization of stackability by the sign of a single score, while treating an empty branch as a separate state. Second, we solve the resulting extremal problem for configurations whose scores are all nonpositive. After pruning empty exterior branches, every edge falls into an explicit defect state. Defective edges admit injective endpoint owners; exponential longest-path weights then charge each edge excess to its owner's vertex defect. Occupied-leaf slack converts the weighted bound to ordinary mass, and a connected-partition consolidation lemma reduces the resulting multi-source potential to the tree estimator. An explicit zero-score obstruction attains the bound. The same branch certificate also yields a direct algorithm for deciding stackability of a configuration on a tree. The proof architecture is compared with target pebbling, cover pebbling, tree reachability algorithms, and weight-function methods.

This abstract intentionally does not claim priority or novelty beyond saying what the manuscript proves.

## Intended audience

Primary audience: researchers in graph pebbling, extremal graph theory, and algorithmic graph theory. Secondary audience: combinatorial optimization researchers interested in discrete generalized-flow or potential arguments, and formalization researchers because the proof decomposes into local arithmetic, finite-tree combinatorics, and explicit potential inequalities.

## Why the contribution matters beyond one conjecture

The branch theorem is an exact-clearing analogue of tree dynamic programming: it records not merely how many pebbles can be delivered to a root while allowing leftovers, but the signed gain or cost of eliminating an entire branch. The distinction is structural; odd residual pebbles may force moves in both directions along an edge.

The arbitrary-defect proof is also potentially reusable. Its pattern is:

```text
local nonlinear transfer law
 -> exact edge-state classification
 -> sparse set of positive excesses
 -> injective endpoint owners
 -> acyclic exponential weights
 -> cancellation against vertex defect budgets
 -> boundary/leaf slack
 -> consolidation to one global potential.
```

That pattern is recognizable as a combinatorial dual-certificate argument even though no inspected source was found with this exact tree-stacking formulation.

## Prior-art comparison matrix

| Work / area | What is known there | Relation to this project | Present assessment |
|---|---|---|---|
| Csernák--Soukup, *Stacking and clearing in graph pebbling*, arXiv:2604.22341v1 (2026) | Introduces `stack` and `clear`; states the tree estimator as Conjecture 10.3; proves the tree upper bound only under the Almost Stacked Hypothesis; reports computation through order 7 | Direct source of the problem and estimator | The source still presents the tree formula as conjectural; its arXiv record has only v1 as of 2026-09-21 |
| Csernák--Soukup, *Stacking and Clearing in Directed Graph Pebbling*, arXiv:2606.04659 (2026) | Directed analogue; strong connectivity criteria and directed-cycle formula | Same authors and new parameter, but different graph model | No undirected-tree resolution located |
| Hurlbert, *General graph pebbling*, Discrete Appl. Math. 161 (2013) | Common framework using families of target configurations | Conceptual umbrella broad enough to describe many pebbling variants | Does not by itself supply the exact tree formula or branch/defect proof |
| Adauto--Bardenova--Bidav--Hurlbert, *Target Pebbling in Trees*, Discrete Math. 349 (2026), 115029 / arXiv:2504.10460 | Polynomial algorithms and extremal configurations for arbitrary fixed demand `D` on a tree | Closest recent tree extremal/algorithmic work | Semantics differ: `D`-solvability requires a final configuration **at least** `D`, so leftover pebbles are allowed; exact clearing to one support vertex is stricter |
| Chung's tree `t`-pebbling/path-partition theory | Exact formulas for delivering prescribed pebbles to a fixed root on trees | Classical tree machinery | Ordinary target delivery, not elimination of all exterior pebbles |
| Bunde--Chambers--Cranston--Milans--West, *Pebbling and Optimal Pebbling in Graphs*, JGT 57 (2008) | Tree pebbling algorithm, smoothing/squishing, ordinary root reachability | Algorithmic and structural precedent | Target reachability permits leftovers; no-cycle/squishing tools do not directly encode odd exact-cleanup costs |
| Hurlbert, *A Linear Optimization Technique for Graph Pebbling*, arXiv:1101.5641 | Weight Function Lemma and LP-style upper-bound certificates | Closest dual/potential precedent | Exponential weights are related in spirit; no inspected statement gives the signed defect equations plus injective owner cancellation used here |
| Sjöstrand, *The Cover Pebbling Theorem* (2005); Vuong--Wyckoff, *Conditions for Weighted Cover Pebbling of Graphs* | For positive demands, worst obstructions can be stacked; weighted cover formula | Motivates “stacking” extremal phenomena and ASH | Cover/target feasibility asks for lower bounds on final occupancy and permits extra pebbles; it does not impose exact one-support cleanup |
| Jones--Laison--McLeman--Nyman, *Weighted Pebbling Numbers on Graphs*; Sieben, weighted-graph pebbling algorithm | Weighted-edge pebbling and target reachability | Relevant terminology/search neighborhood | Different weights live on edges and change move cost; no overlap found with the branch signed-gain transfer `F` |
| Haynes--Keaton, *Cover rubbling and stacking* (2020) | “Stacking” terminology in cover rubbling context | Terminological collision worth citing/searching | Different parameter and move system; no theorem overlap found |

## Citation and novelty audit performed

Searches on 2026-09-21 included the exact arXiv identifier, exact title, authors, “stacking number”, exact clearing, target pebbling, demand/cover pebbling, weighted pebbling, tree reachability algorithms, Weight Function Lemma / pebbling duality, generalized flow, endpoint charging, and exponential potentials.

The arXiv record for `2604.22341` links to citation tools but still lists only v1. SciRate's current search page displayed zero “scites” for the paper. Exact-title and arXiv-ID web searches located the authors' directed follow-up and secondary mirrors/summaries, but no later paper claiming the undirected-tree formula. Searches also located the 2026 journal publication of *Target Pebbling in Trees*, classical cover-pebbling work, ordinary tree reachability algorithms, and weight-function methods.

### Limitations

This is not a complete proof of novelty. In this environment:

- direct Semantic Scholar citation-page retrieval redirected to a page the web tool could not access;
- Google Scholar results were not directly inspectable as a reliable exhaustive citation list;
- no subscription citation database such as MathSciNet, Web of Science, or Scopus was available as a complete graph of forward citations;
- terminology may differ, especially for signed dynamic programs, exact configuration transformation, integer generalized flows, or potential charging;
- recent manuscripts not indexed by the searched services could be missed.

Therefore the correct language is “we found no prior source proving this formula or using this exact proof architecture in the searches described,” not “this is the first proof.”

## What appears known versus what appears new

### Known / directly sourced

- The stacking parameter and tree estimator are due to Csernák and Soukup.
- The formula was explicitly conjectured and computationally verified by them through seven vertices.
- General target-family frameworks, target/demand pebbling on trees, cover-pebbling stacking theorems, tree reachability algorithms, and weight-function dual certificates predate this project.

### Not found in inspected prior work

- the exact signed branch transfer `F` as a necessary-and-sufficient certificate for clearing every pebble outside a chosen tree root;
- the explicit defect-edge pair classification induced by negative rooted scores;
- injective ownership of defective tree edges combined with longest-directed-path weights to cancel all positive edge excess against vertex defects;
- the occupied-leaf slack plus connected-partition exponential-potential consolidation in this exact role;
- an unconditional proof of the Csernák--Soukup undirected tree estimator formula.

These are observations from the performed search, not priority claims.

## Recommended contribution hierarchy in the paper

The theorem resolution should be the title/abstract-level result. The branch score should be elevated to a named theorem early in the paper because it is independently useful and explains why the later optimization problem is the right one. The arbitrary-defect owner/cancellation theorem should be presented as the central technical theorem. The zero-score argument can be retained as a warm-up that reveals the potential method before the full defect bookkeeping.

A paper led only by the zero-score result would undersell the work. A paper led only by the owner/cancellation lemma would obscure the motivating graph-pebbling theorem. Conversely, claiming a broad new generalized-flow theory would overstate what has been established.

## Most serious remaining weakness

The most serious remaining weakness is **external validation and priority**, not an identified internal mathematical gap. This proof was developed and audited in a computational research workflow and has not yet been checked by an independent human expert or a proof assistant. The literature search also cannot establish novelty conclusively.

Before public submission, the written proof should additionally repair the missing universal-size upward-closure lemma and the stale last paragraph of `notes/estimator.md`.

## Proceed / do not proceed

Proceed to formalization and manuscript preparation. Treat “resolution of the corrected tree-stacking conjecture” as the mathematical claim, but use conservative priority language until a human citation audit has checked MathSciNet/zbMATH/Google Scholar/Semantic Scholar or equivalent databases and compared the proof with the full text of the closest tree target-pebbling and pebbling-duality papers.
