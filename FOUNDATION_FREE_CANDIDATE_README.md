# Foundation-free bounded Zermelo — kernel-verified Lean development

**Status: VERIFIED.** The flat assignment-frame construction and the
Foundation-free endpoint were checked with Lean 4.20.0.

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
- a relative Russell set supplying fresh local coordinate markers;
- flat tagged assignment frames with directed atomic equality and membership
  relations, including self-membership;
- exact cylindrification, bounded truth compilation, finite localization, and
  coordinate extraction.

No Separation instance is assumed in the forward direction.

## Flat assignment codes

The code follows [Al-Johar's Hausdorff-style tuple](https://mathoverflow.net/q/518204/95347)
with a fixed marker `m_i` for each coordinate throughout a frame. An
assignment with values `a_i` is the set of tags `{a_i,m_i}`. For each
domain `D_i ⊆ E`, the tags constitute a sort `U_i`. The sorts are pairwise
disjoint. Each marker contains the empty object and is outside the
depth-two envelope of `E`.

For positive arity, the candidates are nonempty subsets of the finite
union of the sorts. The marker conditions make the candidate sort
disjoint from each `U_i` and rule out a candidate belonging to a tag.
Thus the unordered membership filter on the candidate-to-tag product
gives exactly the edges from candidates to tags they contain.

For each coordinate, take the candidate endpoints of this incidence graph
to locate candidates with at least one tag. To locate candidates with two
distinct tags, compose the graph with the inequality graph on `U_i` and
intersect with the incidence graph again. The inequality graph exists
by removing singleton edges from `U_i * U_i`. Difference and finite
intersection yield the set of candidates with exactly one tag in every
sort. Applying the membership filter to the resulting tuple-to-tag
products gives the coordinate projection graphs.

`FoundationFreeFlatTupleFilters.lean` implements the filters.
`flat_assignment_frame_exists_nf` in `FoundationFreeFiniteAssignmentFrame.lean`
certifies the exact code and projection specifications. The zero-coordinate
frame consists of the empty tuple.

## Reproducing the kernel check

```bash
lake update
lake build
lake env lean FoundationFreeKernelAudit.lean
```

The complete build succeeds. `FoundationFreeKernelAudit.lean` checks the flat
frame theorem and the five principal Foundation-free declarations. It reports:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project-declared axiom, or Foundation dependency.
`Classical.choice` is a metatheoretic Lean principle used to select witnesses;
it is not object-theoretic Choice in the membership structure.

The older Foundation-based endpoint remains available in
`EquivalenceMain.lean` and is checked separately by `KernelAudit.lean`.
