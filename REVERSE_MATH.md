# Formalization rationale for BZ ⇒ T₉

Work in an extensional membership structure with full Power Set and Foundation,
as well as Empty Set, Pairing, Union, and Δ₀-Separation.

1. **Empty, singletons, set union.** Empty and union are background axioms.
   Singleton `{a}` is the degenerate unordered pair `{a,a}`.
2. **Difference, intersection.** These are Δ₀ separation instances with
   atomic predicates `x ∉ b` and `x ∈ b`.
3. **Common supersets.** Let `p={a,b}` and `c=⋃p=a∪b`. Then a,b⊆c.
4. **Intersection and membership filters.** For an arbitrary candidate `t`,
   the formula asserting `t={a,b}` is bounded:

       a∈t ∧ b∈t ∧ ∀z∈t (z=a ∨ z=b).

   Therefore the conditions

       ∃a∈t ∃b∈t [t={a,b} ∧ ∃z∈a (z∈b)]
       ∃a∈t ∃b∈t [t={a,b} ∧ (a∈b ∨ b∈a)]

   are Δ₀. Separating them from the given input `X` gives operations 7 and 8.
5. **Unordered composition.** For input relations `q,r`, define

       D=(⋃q)∪(⋃r),   P=℘(D).

   Every output `{a,c}` with `{a,b}∈q` and `{b,c}∈r` lies in P. Inside P
   its membership is equivalent to the bounded formula

       ∃a∈D ∃b∈D ∃c∈D
         [t={a,c} ∧
          ∃p∈q (p={a,b}) ∧ ∃p∈r (p={b,c})].

   Thus Δ₀ separation constructs exactly the unordered composition.

The reverse proof uses no existence operation from T₉ as a premise.
The forward proof comes from `MainProof.lean` in the original archive.

**Formal status:** compiled and checked by the Lean 4.20.0 kernel as part of
the clean full-project build. The reverse theorem has no hypothesis of type
`NineAxioms`; its only object-theoretic premise is `BoundedZermeloCore B`.
