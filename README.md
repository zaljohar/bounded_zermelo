# Nine axioms ⇔ Bounded Zermelo (Lean 4, kernel verified)

## Exact endpoint

`EquivalenceMain.lean` proves:

```lean
theorem bounded_zermelo_iff_bzminus_plus_nine (B : Background V) :
    BoundedZermeloCore B ↔
      (BoundedZermeloMinus B ∧ HasNineAxioms B)
```

Here `Background V` supplies Extensionality, Power Set, and Foundation;
`BoundedZermeloCore B` additionally supplies Empty Set, Pairing, Union, and
the full `DeltaZero` Separation schema; and `HasNineAxioms B` is the
conjunction of the nine unrestricted existence principles in
`NineAxiomCore.lean`.

Thus, relative to the shared background, the checked endpoint is

    BZ core  ⇔  (BZ core without Δ₀-Separation) + T₉.

The stronger checked theorem `bounded_zermelo_iff_nine_axioms` shows that
Empty Set, Pairing, and Union are already consequences of `T₉`, so the
`BoundedZermeloMinus` conjunct is redundant.

`BoundedZermeloCore` intentionally does not contain Infinity or Choice. The
checked theorem `bounded_zermelo_iff_nine_with_extra B Extra` permits any
common additional proposition—for example a chosen formulation of Infinity—to
be conjoined to both sides.

## What kind of formal result this is

This is a semantic Lean theorem about every one-sorted membership structure
`B` satisfying the displayed hypotheses. It directly proves the required
model-theoretic implication and equivalence. It is not an encoding of a
first-order proof calculus, and Lean does not formalize the completeness step
from semantic consequence to syntactic derivability in this project.

The internal syntax `DeltaZero n` contains equality, membership, falsity,
negation, conjunction, and bounded existential quantification. Consequently
`BoundedSeparation` covers arbitrary bounded formulas, including arbitrary
finite parameters and nonstratified formulas.

## Reverse direction

`BoundedZermeloReverse.lean` derives all nine fields from the ordinary BZ-core
axioms:

- Empty Set, singleton, set union, and common superset use Empty Set, Pairing,
  and Union.
- Difference and intersection are direct Δ₀-Separation instances.
- The unordered-intersection and unordered-membership operations are bounded
  filters of their input sets.
- Unordered composition is obtained by separation inside `P(D)`, where
  `D = (⋃q) ∪ (⋃r)`.

No field of `NineAxioms` is used as a premise in this reverse proof.

## Kernel-verification status

Verified on 2026-11-12 with:

```text
Lean 4.20.0, commit 77cfc4d1a4f6, Release
Lake 5.0.0-77cfc4d
Mathlib v4.20.0
```

A clean `lake build` completed all 571 targets successfully. Running
`lake env lean KernelAudit.lean` after that clean build showed that each of
the six principal forward, reverse, and equivalence theorems depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, no project-declared axiom, and no extra mathematical
hypothesis hidden in the endpoint. `Classical.choice` here is Lean's
metatheoretic choice principle used to extract witnesses; it is not the
object-theoretic Axiom of Choice for `B`.

## Reproducing the check

```sh
lake update
lake build
lake env lean KernelAudit.lean
```

For GitHub, the included `.github/workflows/lean-kernel-check.yml` performs
the same build and axiom audit on every push and pull request. See
`GITHUB_CHECKING.md` for upload and verification instructions.

The submitted unverified archive required source repairs before Lean accepted
it. Those repairs resolved import placement, module-root configuration,
reserved identifiers, implicit constructor arities, and local definitional
equalities. They did not alter the statements of the principal theorems, the
definitions of `Background`, `NineAxioms`, `DeltaZero`, or
`BoundedSeparation`, and they added no assumptions.
