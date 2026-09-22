# Source, scope, and provenance

## Mathematical source

Tamás Csernák and Lajos Soukup, *Stacking and clearing in graph pebbling*,
arXiv:2604.22341v1 (2026), introduces the stacking number and states the
tree-estimator formula as a conjecture.

The source uses exact-size configurations in the definition of the stacking
threshold. TreeStack preserves that convention in
`UniversalStackable G t`: every configuration of exactly mass `t` must be
stackable.

## Formalized result

The principal checked declaration is:

```text
TreeStack.stack_eq_estim_of_two_le_card
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T
```

Thus the submitted statement is explicitly the nontrivial-tree form. The
one-vertex case is not silently folded into the theorem: the source stacking
candidate convention requires `t ≥ 2`, while the displayed estimator is
`1` on the one-vertex tree.

The Lean proof also formalizes the structural machinery used to obtain the
equality, including exact branch messages, the rooted score characterization,
the explicit estimator-minus-one obstruction, arbitrary-defect charging,
weighted cancellation, occupied-leaf slack, and ambient-tree consolidation.

## EMPTY semantics

Internally, a branch with no pebbles is represented by `Option.none`. This is
categorically different from an occupied branch whose integer message is
`some 0`. The proof development and its audits preserve this distinction.

The Palomar Challenge does not expose the branch-message implementation because
it is not a definitional dependency of the advertised theorem. It therefore
does not introduce any alternate encoding of EMPTY.

## Review and automation

Development was extensively AI-assisted under direction of the human
maintainer, with repeated Lean builds, theorem-level axiom auditing, Python
regression checks, and adversarial review stages.

The maintainer has reported that an external human mathematical review of the
completed result has been completed. No reviewer name, affiliation, date, or
quotation is recorded in this repository, so none is asserted here.

## Novelty and priority

The source paper is credited as the origin of the stacking parameter and the
tree-estimator conjecture. This repository supplies a machine-checked proof of
the corrected nontrivial-tree statement. The metadata does not assert priority
over every possible independent proof, and Palomar registration should not be
described as journal publication or as an independent human-referee
endorsement.
