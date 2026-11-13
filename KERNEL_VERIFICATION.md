# Kernel verification record

## Result

The corrected complete project passed its full build and both endpoint audits
on 2026-11-13:

```text
Lean 4.20.0, x86_64-unknown-linux-gnu
commit 77cfc4d1a4f6, Release
Lake 5.0.0-77cfc4d
Mathlib v4.20.0
Build completed successfully.
```

Commands:

```sh
lake build
lake env lean KernelAudit.lean
lake env lean FoundationFreeKernelAudit.lean
```

The original uploaded Foundation-free candidate did not compile. The repaired
version does. No principal theorem statement or mathematical hypothesis was
changed, and no axiom, `sorry`, or `admit` was added.

## Foundation-free checked theorem types

```lean
bounded_envelope_with_roots_nf
  (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
  (n : Nat) (φ : DeltaZero (n + 1))
  (A : V) (params : Fin n → V) :
  ∃ E, ...

bounded_separation_from_nine_no_foundation
  (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
  BoundedSeparation B.mem

nine_axioms_imply_bounded_zermelo_no_foundation
  (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
  BoundedZermeloCore B

bounded_zermelo_iff_nine_no_foundation
  (B : BackgroundNoFoundation V) :
  BoundedZermeloCore B ↔ Nonempty (NineAxioms B.mem)

bounded_zermelo_iff_bzminus_plus_nine_no_foundation
  (B : BackgroundNoFoundation V) :
  BoundedZermeloCore B ↔
    (BZMinusNoFoundation B ∧ Nonempty (NineAxioms B.mem))
```

`BackgroundNoFoundation` has only membership, Extensionality, and Power Set.
In particular, the theorem parameters contain no Foundation, acyclicity,
`NoUniversal`, Separation, Infinity, Replacement, or Choice field.

## Axiom audit

For every Foundation-free theorem above, `#print axioms` returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` and no project-declared axiom. These three entries are
Lean's standard metatheoretic principles. `Classical.choice` is not an
assumption that the object-level membership structure satisfies Choice.

The original Foundation-based theorems in `KernelAudit.lean` return the same
three-item list.

## Compilation repairs

The necessary repairs were proof-preserving implementation corrections:

- register all flat sibling modules in `lakefile.lean`;
- make the induction-hypothesis application in the external finite-object
  injection explicit and import the standard `Infinite` API;
- repair a branch variable eliminated by an equality pattern;
- expose beta-reduced and locally abbreviated membership expressions before
  rewriting;
- replace an expensive propositional automation step by a direct proof;
- normalize the Frege-one construction's `m := B.mem` specifications;
- simplify a malformed existential unpacking;
- remove a duplicate universe declaration;
- add `FoundationFreeKernelAudit.lean` and update the GitHub workflow.

None of these changes modifies `BackgroundNoFoundation`, `NineAxioms`,
`DeltaZero`, `BoundedSeparation`, `BoundedZermeloCore`, or either endpoint
statement.

## Scope

The checked result is a semantic theorem over arbitrary one-sorted membership
structures. It is not a formalization of a syntactic first-order proof
calculus. Passing from semantic consequence to a displayed syntactic
derivability statement uses the usual soundness/completeness metatheory, which
is not formalized in this project.
