# Publication literature and submission audit

Checked on **2026-09-23**, independently refreshed for the publication stage.
This supplements [the research audit](../notes/literature.md); it does not
claim access to private manuscripts or exhaustive subscription databases.

## Forward literature search

The public web search was rerun using the following queries, including exact
identifier, conjecture, formula, title, author, and alternative terminology:

```text
"2604.22341"
"Conjecture 10.3" "stacking"
"stacking number" trees pebbling proof
"estim" "sigma" "stacking" tree Soukup
"stack(T)" "estim(T)"
"sigma_T(r)" pebbling
"sigma" "deg(v)" "estim(T)"
"Stacking and clearing in graph pebbling" proof conjecture
"Soukup" "tree" "stacking" estimator proof
"Csernák" "Soukup" stacking tree proof estimator 2026
"stacking" "tree" "exact reachability" pebbling
"graph pebbling" "tree" "stacking" conjecture 2026 proof
"2604.22341" proof -site:researchgate.net -site:papers.cool
```

The formula queries were checked against the displayed estimator itself,
not merely against the phrase “stacking number.” In the notation of the
source, this is

\[
\sigma_T(r)=1+\sum_{\substack{v\in V(T)\\v=r\text{ or }\deg(v)>1}}
\deg(v)2^{d(r,v)},\qquad
\operatorname{estim}(T)=\max_r\bigl(\sigma_T(r)+\operatorname{leaf}(r)\bigr).
\]

**Result:** no earlier public proof or competing resolution of the
nontrivial-tree equality was located by this refresh. This is a bounded
negative search result, not a guarantee of priority. The manuscript should
say that it proves the conjecture; it need not make a “first proof” claim.
Searches may miss unindexed work, differently named equivalent results,
private work, and recent items awaiting indexing.

### Source and subsequent work inspected

- Csernák–Soukup,
  [*Stacking and clearing in graph pebbling*](https://arxiv.org/abs/2604.22341),
  including the [introduction, definitions and §10](https://arxiv.org/html/2604.22341v1).
  The record lists only v1, posted 24 April 2026. The tree section states
  Conjecture 10.3 and reports computation through order seven. Its preceding
  upper bound assumes the Almost Stacked Hypothesis. The exact-size threshold
  is restricted to integers at least two; a stack has nonempty singleton
  support. These conventions are retained in the manuscript, with the
  singleton-tree exception stated explicitly.
- Csernák–Soukup,
  [*Stacking and Clearing in Directed Graph Pebbling*](https://arxiv.org/abs/2606.04659),
  v1, posted 3 June 2026. The [full text](https://arxiv.org/html/2606.04659v1)
  concerns directed pebbling, including directed cycles and existence
  criteria. It supplies no proof of the undirected tree estimator equality.
- Adauto–Bardenova–Bidav–Hurlbert,
  [*Target Pebbling in Trees*](https://arxiv.org/abs/2504.10460),
  v2, revised 22 January 2026; published in *Discrete Mathematics* 349 (2026),
  no. 7, article 115029,
  [DOI 10.1016/j.disc.2026.115029](https://doi.org/10.1016/j.disc.2026.115029).
  Its [definition of target solvability](https://arxiv.org/html/2504.10460v2)
  requires at least the demanded number of pebbles at each vertex. Additional
  pebbles can remain elsewhere. Thus its tree algorithm does not by itself
  characterize exact clearing to a single stack. This comparison is an
  inference from the differing target conditions, not an assertion made by
  those authors about TreeStack.
- Sjöstrand's
  [cover pebbling theorem](https://arxiv.org/abs/math/0410129)
  concerns satisfying positive demands from arbitrary initial configurations.
  The extremal reduction places the initial supply at one vertex. This is a
  different use of “stacking” from requiring a final configuration supported
  at one vertex.

Search hits for stacking in eternal domination and cover rubbling were
excluded after checking their move systems and target conditions. The older
survey and classical pebbling sources are background for the distinction
between delivery to a prescribed target and the exact final-support condition.
Only works actually cited in the paper belong in its bibliography; the
additional forward-search checks above are recorded here rather than padding
the article's reference list.

## Bibliographic verification

All entries in `references.bib` were checked against primary sources:

| Key | Verified record | Use |
| --- | --- | --- |
| `cs2026` | [arXiv:2604.22341](https://arxiv.org/abs/2604.22341): Tamás Csernák and Lajos Soukup, 2026; no journal publication claimed | Definitions, estimator, conjecture and order-seven computation |
| `chung1989` | [SIAM publisher record](https://epubs.siam.org/doi/10.1137/0402041): Fan R. K. Chung, *Pebbling in hypercubes*, **2** (1989), no. 4, 467–472 | Classical graph pebbling |
| `hurlbert1999` | [arXiv:math/0406024](https://arxiv.org/abs/math/0406024) and [author's publication list](https://glennhurlbert.github.io/pubs.html): *Congressus Numerantium* **139** (1999), 41–64 | Classical pebbling background; 2004 is the arXiv posting year, not the journal year |
| `sjostrand2005` | [Electronic Journal of Combinatorics](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v12i1n22): Jonas Sjöstrand, **12** (2005), no. 1, N22; DOI 10.37236/1989; [arXiv:math/0410129](https://arxiv.org/abs/math/0410129) | Cover-pebbling comparison; 2004 is the preprint year |

No arXiv identifier was invented for Chung's 1989 paper. Accent commands in
the BibTeX author fields preserve the names under PDFLaTeX/BibTeX. The
bibliography uses ordinary BibTeX, without a Biber-format dependency.

## Classification

The [official MSC2020 list, maintained by Mathematical Reviews and zbMATH](https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf)
was checked. The selected classifications are:

- Primary **05C57**: Games on graphs (graph-theoretic aspects).
- Secondary **05C05**: Trees.

The source paper also uses 05C38, Paths and cycles. The present article's
principal result concerns arbitrary trees, so that extra classification is
not needed. The proposed arXiv category is **math.CO (Combinatorics)**, without
a cross-list. Formal verification is part of reproducibility, not the main
subject of the paper.

## Official arXiv requirements checked

The following are current documentation checks, not a claim that the paper
has been uploaded to or processed by arXiv.

1. [Submission overview](https://info.arxiv.org/help/submit/index.html).
   TeX is the preferred archival input for a TeX-authored paper. The generated
   inspection PDF is excluded from the source archive. Filenames use only
   letters, digits, underscore, plus, hyphen, period, comma and equals; all
   input names must match case. ZIP or tar.gz may carry the source package.
2. [TeX submissions](https://info.arxiv.org/help/submit_tex.html).
   Compile from the archive root. Include every required input, but omit
   unused figures, logs, auxiliary build files, backups, Git metadata and
   other unrelated material. Include custom packages if absent from the
   supported installation. Avoid referee mode and a variable `\today` date.
   Include both `references.bib` and the generated `main.bbl`; the system uses
   an uploaded `.bbl`, whose basename must match the main source. Inspect the
   PDF generated by arXiv during the actual submission process.
3. [TeX Live at arXiv](https://info.arxiv.org/help/faq/texlive.html).
   The official page lists **TeX Live 2025 as default**, with 2023 also
   available, and supports PDFLaTeX. Standard AMS/LaTeX packages and
   PDFLaTeX are appropriate for this article. The page records a `cleveref`
   naming issue on TeX Live 2025; ordinary theorem labels and `\ref` avoid
   this dependency. No external fonts or shell-escape processing are needed.
4. [Metadata fields](https://info.arxiv.org/help/prep.html).
   The abstract limit remains **1920 characters**. Metadata should be ASCII
   with supported TeX accents/math, without unexplained local macros.
   Comments should give the final page and figure counts. Optional
   report-number, journal-reference and DOI fields remain empty when
   inapplicable; no prospective publication is claimed. Author names must be
   accurate, and AI tools must not be listed as authors.
5. [Common processing mistakes](https://info.arxiv.org/help/faq/mistakes.html).
   Use relative, case-correct paths and portable filenames. Do not make
   untested changes after the final local build. Figures, if any are later
   added, must already be in a format supported by the chosen engine.

## Final handoff conditions

The build/preflight result and actual artifact counts belong in
`paper/README.md` and the generated build report. The submission bundle must
be regenerated from the canonical source after replacing the Palomar record
placeholder. The author must select an arXiv license and complete personal
account/endorsement information as required by arXiv, then inspect the PDF
produced by arXiv before submitting. No submission is performed by this
publication workflow.
