# Kernel verification record

## Result

The corrected project passed a clean full build on 2026-11-12:

```text
Lean (version 4.20.0, x86_64-unknown-linux-gnu,
      commit 77cfc4d1a4f6, Release)
Lake version 5.0.0-77cfc4d (Lean version 4.20.0)
Mathlib tag v4.20.0

Build completed successfully. 571 targets.
```

Commands:

```sh
lake clean
lake build
lake env lean KernelAudit.lean
```

The SHA-256 digest of the original submitted archive was:

```text
f22b79b50a5c7e5b2fc4a73d66f8f275d88b621e7ea8785f866e48ee5f63bfa5
```

That original archive did not compile as submitted. The corrected version in
this package does. No principal theorem statement or mathematical hypothesis
was changed during repair.

## Checked theorem types

```lean
nine_axioms_imply_delta_zero_separation
  (B : Background V) (H : NineAxioms B.mem) :
  BoundedSeparation B.mem

bounded_zermelo_implies_nine_axioms
  (B : Background V) (h : BoundedZermeloCore B) :
  NineAxioms B.mem

nine_axioms_imply_bounded_zermelo
  (B : Background V) (H : NineAxioms B.mem) :
  BoundedZermeloCore B

bounded_zermelo_iff_nine_axioms (B : Background V) :
  BoundedZermeloCore B ↔ HasNineAxioms B

bounded_zermelo_iff_bzminus_plus_nine (B : Background V) :
  BoundedZermeloCore B ↔
    (BoundedZermeloMinus B ∧ HasNineAxioms B)

bounded_zermelo_iff_nine_with_extra
  (B : Background V) (Extra : Prop) :
  (BoundedZermeloCore B ∧ Extra) ↔
    (HasNineAxioms B ∧ Extra)
```

## Axiom audit

For every theorem above, `#print axioms` returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, there is no `sorryAx`, no project-declared axiom, no assumed
separation theorem in the forward implication, and no assumed nine-axiom
field in the reverse implication.

These are metatheoretic Lean dependencies. `Classical.choice` is not an
assumption that the object membership structure satisfies the set-theoretic
Axiom of Choice.

## Repairs required for compilation

The submitted sources required the following implementation repairs:

- imports were moved before module documentation and narrowed to the used
  Mathlib modules;
- the Lake library was given explicit roots for the flat module layout;
- reserved/shadowed identifiers and implicit induction arities were made
  explicit;
- several proof terms were restated to expose definitional equalities to Lean;
- the final reverse unordered-composition proof was rewritten to apply its
  `DeltaZero` correctness lemma with an explicit environment.

These repairs changed elaboration/proof plumbing only. They did not change
the definitions of `Background`, `NineAxioms`, `DeltaZero`,
`BoundedSeparation`, `BoundedZermeloCore`, or the endpoint theorem types.

## Scope of the conclusion

The checked result is a semantic theorem over arbitrary one-sorted membership
structures. It is not a formalization of a syntactic first-order deduction
calculus. Accordingly, the Lean project itself establishes semantic
equivalence; conversion to a statement with the symbol `⊢` additionally uses
the usual metatheoretic soundness/completeness connection for first-order
logic, which is not formalized here.
