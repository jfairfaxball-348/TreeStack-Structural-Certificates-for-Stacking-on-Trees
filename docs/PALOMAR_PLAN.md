# Palomar packaging plan

This repository is being prepared for Palomar, but this document does not
perform or authorize registration. Registration remains a separate maintainer
action against one immutable 40-character commit after all mechanical gates
pass.

## Advertised result

The single Comparator theorem is:

`TreeStack.stack_eq_estim_of_two_le_card`

Its exact statement is the corrected nontrivial-tree form

`2 ≤ Fintype.card V → stack T = estim T`.

The one-vertex case is deliberately excluded because the source definition of
the stacking number restricts candidate thresholds to `t ≥ 2`, whereas the
displayed estimator is `1` on the one-vertex tree.

## Protected statement surface

`Challenge.lean` imports only Mathlib and reproduces the public definitions
needed by the theorem: configurations and mass, legal pebbling moves and
reachability, stackability, exact-size `UniversalStackable`, finite trees,
the rooted estimator and `estim`, `StackingCandidate`, and `stack`.

The proof development's internal recursive message state distinguishes
`Option.none` (EMPTY) from `some 0`. That state is not in the definitional
surface of the advertised theorem, so the Challenge neither imports it nor
replaces it by an integer surrogate.

`Solution.lean` imports `TreeStack.Stacking`, where the completed project
already proves the same fully qualified declaration.

## Comparator and trust boundary

`comparator.json` selects only
`TreeStack.stack_eq_estim_of_two_le_card`. The permitted standard axioms are
`propext`, `Quot.sound`, and `Classical.choice`. The project proof
contains no `sorry`, `admit`, or project axiom; the sole deliberate
`sorry` is the advertised Challenge theorem.

The ordinary TreeStack workflow remains authoritative for the complete Python
regression suite, bounded verifier, Lean build, and `Audit.lean`. The
additional statement-surface workflow compiles `Challenge.lean`,
`Solution.lean`, and `PalomarAudit.lean`.

## Palomar pipeline pin

The live PalomarSubmission repository was audited at

`a09f5c38ee58bf92c459b974b174ff4063ebea5f`.

The current intake contract requires a 12-character lowercase alphanumeric
preflight request id; this repository uses `treestackpf1`.

`.github/workflows/palomar-preflight.yml` pins both the reusable workflow
reference and `pipeline_commit` to that exact SHA and requests `mode: full`.

The project pins Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The canonical Mathlib revision's
own `lean-toolchain` is exactly `leanprover/lean4:v4.34.0`, matching the
project toolchain. Palomar's current minimum is v4.28.0.

## Metadata and human review

`formalization.yaml` uses the current v0.4 shape, describes the
Csernák--Soukup conjecture source without making a priority claim, records the
explicit one-vertex convention correction, and discloses extensive AI-assisted
development.

The maintainer has stated during this packaging handoff that external human
mathematical review of the completed result is complete. No reviewer identity,
affiliation, date, or quotation is recorded in the repository, so the metadata
records only the fact of completed external human review and explicitly avoids
inventing those details.

## Legal gate

TreeStack currently has no recorded root licence decision. Palomar requires
exactly one mechanically detectable root licence and an identical SPDX value in
`project.license`.

No licence is asserted by this packaging branch until the maintainer makes that
legal choice. This is intentionally expected to block the official Palomar
preflight at the licence/metadata gate. Once a licence is selected, add exactly
one accepted root licence file, set `project.license` to the matching SPDX
identifier, rerun the full preflight, and only then freeze the submission
candidate commit.

## Final freeze checklist

1. ordinary TreeStack CI green;
2. statement-surface workflow green;
3. exact root licence chosen and metadata synchronized;
4. official Palomar full preflight green, including Comparator, protected
   Challenge compilation, Lean kernel export, and NanoDa replay;
5. packaging PR merged;
6. post-merge `main` validation and Palomar preflight green;
7. record the final immutable `main` SHA and only then use the Palomar
   submission form.
