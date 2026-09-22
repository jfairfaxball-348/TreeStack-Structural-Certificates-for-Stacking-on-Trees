# Verification protocol

A Palomar candidate is acceptable only when the ordinary project checks and the
protected statement/comparator checks both succeed at the exact candidate
commit.

## Ordinary TreeStack validation

Run from a fresh checkout:

```bash
python3 -m pip install -e '.[test]'
python3 -m pytest -q
python3 -m treestack.src.verify --max-order 6 --max-total 8
python3 -m compileall -q treestack
lake build
lake env lean Audit.lean
```

The repository GitHub Actions workflow runs this same substantive path for a
ready pull request and for `main`.

## Statement-surface validation

The Palomar Challenge is intentionally separate from the implementation-heavy
project modules. It must have a Mathlib-only transitive import boundary and only
one deliberate `sorry`, at
`TreeStack.stack_eq_estim_of_two_le_card`.

The repository statement-surface workflow additionally runs:

```bash
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean PalomarAudit.lean
```

`PalomarAudit.lean` prints the theorem-level axioms of the actual proved
Solution declaration.

## Official full Palomar preflight

`.github/workflows/palomar-preflight.yml` calls the current audited
PalomarSubmission reusable workflow in `mode: full`. This is predictive
mechanical verification only; it does not register the result.

The full preflight is expected to exercise repository preparation, dependency
and toolchain checks, licence and metadata validation, the protected Challenge
boundary, Comparator, Lean kernel export, and independent NanoDa replay.

The pinned pipeline SHA for this packaging revision is:

`a09f5c38ee58bf92c459b974b174ff4063ebea5f`.

A green ordinary Lean build is not a substitute for a green Palomar full
preflight.

## Current legal prerequisite

Before Palomar can pass, the maintainer must select the TreeStack repository
licence. The final candidate must contain exactly one accepted root licence
file, and its SPDX identifier must equal `project.license` in
`formalization.yaml`. No legal choice is inferred from another repository.
