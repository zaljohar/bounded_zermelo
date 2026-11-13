# Foundation-free bounded Zermelo — kernel-verified Lean development

**Status: VERIFIED.** The Foundation-free endpoint was elaborated and checked
by the Lean 4.20.0 kernel on 2026-11-13.

The principal theorem in `FoundationFreeEquivalenceCandidate.lean` is:

```lean
theorem bounded_zermelo_iff_bzminus_plus_nine_no_foundation
    (B : BackgroundNoFoundation V) :
    BoundedZermeloCore B ↔
      (BZMinusNoFoundation B ∧ Nonempty (NineAxioms B.mem))
```

`BackgroundNoFoundation` contains only membership, Extensionality, and Power
Set. It has no Foundation, acyclicity, `NoUniversal`, Separation, Infinity,
Replacement, or object-theoretic Choice field.

The stronger forward theorem is:

```lean
theorem bounded_separation_from_nine_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    BoundedSeparation B.mem
```

Thus the nine unrestricted existence principles imply every bounded
Separation instance, with arbitrary finite parameters, over Extensionality and
Power Set alone.

## Foundation-free method

The construction replaces finite-cycle exclusion by explicit devices derived
from the nine principles:

- an external injection `Nat → V` made from the empty object and iterated
  singletons;
- a Frege-one construction that rules out a universal set;
- relative Russell sets producing fresh irreflexive markers at every fixed
  finite membership depth;
- tagged finite assignment frames with directed atomic equality and membership
  relations, including the self-membership case;
- exact cylindrification, bounded truth compilation, finite localization, and
  coordinate extraction.

No Separation instance is assumed in the forward direction.

## Reproducing the kernel check

```bash
lake update
lake build
lake env lean FoundationFreeKernelAudit.lean
```

The complete build succeeds. `FoundationFreeKernelAudit.lean` checks the five
principal Foundation-free declarations and reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project-declared axiom, or Foundation dependency.
`Classical.choice` is a metatheoretic Lean principle used to select witnesses;
it is not object-theoretic Choice in the membership structure.

The older Foundation-based endpoint remains available in
`EquivalenceMain.lean` and is checked separately by `KernelAudit.lean`.
