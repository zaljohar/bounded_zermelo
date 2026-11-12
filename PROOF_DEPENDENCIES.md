# Mathematical dependency chain for the fixed-frame Lean proof

**Scope and status.** This is an exposition of the argument represented by
the attached source files. The entire import chain has been compiled from a
clean build directory and checked by the Lean 4.20.0 kernel.

## 1. Ambient assumptions

We work with an extensional one-sorted membership structure satisfying
Foundation and Power Set, with the following nine global existence
principles: empty, singletons, differences, intersections, unions,
unordered composition, unordered intersection filter, unordered membership
filter, and common supersets. No instance of Separation is assumed.

A formula of `DeltaZero n` has equality, membership, negation, conjunction,
and bounded existential quantification; it is interpreted by the original
membership relation, without stratification conditions.

## 2. Building finite tagged assignment frames

The source `NineAxiomCore.lean` derives Pairing, finite unions, fresh markers
and unordered products. `TaggingGraph.lean` constructs singleton images.
The files `FreshTag.lean`, `FiniteTaggedDomains.lean`,
`FreshTupleDisjoint.lean`, `FiniteAssignmentFrame.lean` then construct a
*single* set of finite assignment codes for any specified finite family
of bounded coordinate domains. Each coordinate has a disjoint tagged copy
`U_i = {{x,m_i}: x∈D_i}` and a represented coordinate projection graph
`P_i ⊆ T*U_i`. Every tuple has uniquely decodable raw values, and every
admissible raw valuation has a representing tuple code.

The disjointness and realization properties are the exact object-level
existence obligations. They are not additional axioms: the corresponding
Lean proofs have been elaborated and kernel-checked.

## 3. Atomic truth sets

The tagged membership relation can be oriented as follows. With a marker
`m_i` outside the bounded domain and outside the members of its elements,

    {x,m_i} ∩ y ≠ ∅   iff   x∈y.

The unordered intersection filter detects the left side. Typed composition
transports this to the tagged copy of `y`; disjoint sorts remove reverse
orientations. Equality uses a common raw value and the two tagging graphs.
Combining these atomic relations with the actual coordinate projection
graphs, and extracting only diagonal tuple matches, gives sets of tuples
satisfying each atomic equality and membership condition. The proof includes
repeated variables, including `x∈x`, which is false under Foundation.

See `FiniteFrameAllAtomic.lean`.

## 4. Agreement on all but one coordinate

For a fixed tuple sort `T`, define the symmetric matching graph

    G_j = { {s,t} : s,t∈T and coord_j(s)=coord_j(t) }.

It is represented by composing the j-th coordinate projection graph with
its reverse, filtering to `T*T`. Since the tag sort is disjoint from T,
there are no spurious paths. Any finite conjunction of these graphs exists
by finite intersection, yielding

    G_{≠k} = { {s,t}: s,t∈T and s_j=t_j for all j≠k }.

Given an actual `S⊆T`, define

    C_k(S) = T ∩ ⋃ (G_{≠k} ∩ (S*T)).

Then

    t∈C_k(S)  iff  t∈T and there exists s∈S such that
                      coord_j(s)=coord_j(t) for all j≠k.

Although the union of an unordered edge also exposes its source s, this
causes no false positives: s itself is a valid target witness (choose s),
and coordinate agreement is reflexive. The exact construction is formalized
in `FixedFrameCylindrification.lean`.

## 5. One fixed frame is enough for the entire formula

Suppose a subformula has `m` in-scope de Bruijn variables. Give variable i
the physical coordinate `m - 1 - i`. In the body of a new bounded quantifier,
variable 0 is physical coordinate m, while each prior variable i shifts to
position i+1 and therefore still denotes physical coordinate m-1-i.

For a formula with m initial free variables and maximum bounded nesting
depth d, one assignment frame of N=m+d coordinates therefore suffices.
Freshly bound coordinates are slots m, m+1, ... and can all use the same
chosen local envelope E as their raw domain.

Induct on the formula:

* equality and membership: the represented atomic truth sets;
* false: empty set;
* negation and conjunction: difference and intersection;
* `∃y∈z ψ`: intersect the truth set for ψ with the already constructed
  atomic membership truth set for `y∈z`, then apply C_m.

This is the actual bounded-quantifier step in
`UniformBoundedTruth.lean`, not an assumed `FiniteFrameObligation`.

## 6. Uniform quantifier bounds and final extraction

Take a set A to be separated, finitely many parameters p_i and a fixed
Δ₀ formula φ of depth d. Form a seed containing A and each p_i. By d
iterations of `X ↦ X∪⋃X`, form E containing all objects any bounded
quantifier may reach. For x∈A, the original truth of φ(x,p) agrees with
truth where every quantified variable is additionally restricted to E.

Use a frame of N=(n+1)+d coordinates. Assign raw domain A to physical slot n
(the distinguished free variable), singleton {p_i} to slot n-1-i, and E
to every later slot. The formula truth set on that frame is an actual set.
The coordinate-n image of this set, using the represented projection and
raw-to-tag matching graph, is precisely

    { x∈A : φ(x,p) }.

If A is empty, return the existing empty set. If A is nonempty, any a0∈A
is a filler for unused E-coordinates when realizing a prescribed valuation.
This last argument is in `BoundedSeparationFinalDraft.lean`, and
`MainProof.lean` names the intended unconditional endpoint.

## 7. Formal-verification status

The complete codebase is kernel verified with Lean 4.20.0. A clean
`lake build` completed successfully. `KernelAudit.lean` reports only
`propext`, `Classical.choice`, and `Quot.sound` for every principal endpoint;
there is no `sorryAx` or project-declared axiom.
