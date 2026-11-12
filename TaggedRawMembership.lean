import NineAxiomCore
/-!
# Directed membership edges using unordered intersection

This module derives, directly from the unrestricted unordered-intersection
operation, the graph of *directed* membership between a fresh tagged copy of
one domain and another bounded domain.  It does not postulate Separation,
Gödel's membership operation, or any truth-set compiler.

The essential hypothesis is freshness of the marker `m` from every member of
`D`: then `{a,m} ∩ d ≠ ∅` is equivalent to `a ∈ d`.

NOT YET ELABORATED: the runtime has no Lean toolchain.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- If `U` consists of the unordered tagged copies `{a,m}` of `a ∈ X`, and
`m` belongs to none of the sets in `D`, the unordered intersection filter
constructs *directed* membership from the tagged sort `U` to `D`.

`H` is the exact edge set:

  H = { {u,d} | u∈U, d∈D, ∃a∈X (u={a,m} ∧ a∈d) }.

The predicate is a proof-level specification, not a use of Separation.
-/
theorem tagged_raw_membership_edges_exists
    (B : Background V) (H : NineAxioms B.mem)
    (X U D m : V)
    (hU : ∀ u : V, B.mem u U ↔
      ∃ a : V, B.mem a X ∧ IsUPair B.mem u a m)
    (hmD : ∀ d : V, B.mem d D → ¬ B.mem m d) :
    HasMembers B.mem (fun t : V =>
      ∃ u d a : V,
        B.mem u U ∧ B.mem d D ∧ B.mem a X ∧
        IsUPair B.mem u a m ∧ B.mem a d ∧
        IsUPair B.mem t u d) := by
  obtain ⟨Q, hQ⟩ := unordered_product_exists B H U D
  obtain ⟨I, hI⟩ := H.unorderedIntersection Q
  refine ⟨I, ?_⟩
  intro t
  constructor
  · intro htI
    obtain ⟨htQ, v, w, htvw, ⟨z, hzv, hzw⟩⟩ := (hI t).1 htI
    obtain ⟨u, d, huU, hdD, htud⟩ := (hQ t).1 htQ
    have hInt : ∃ z : V, B.mem z u ∧ B.mem z d := by
      rcases unordered_pair_endpoints B htvw htud with h | h
      · rcases h with ⟨hvu, hwd⟩
        exact ⟨z, by simpa [hvu] using hzv, by simpa [hwd] using hzw⟩
      · rcases h with ⟨hvd, hwu⟩
        exact ⟨z, by simpa [hwu] using hzw, by simpa [hvd] using hzv⟩
    obtain ⟨a, haX, huam⟩ := (hU u).1 huU
    obtain ⟨z, hzu, hzd⟩ := hInt
    have hz : z = a ∨ z = m := (huam z).1 hzu
    have had : B.mem a d := by
      rcases hz with hza | hzm
      · simpa [hza] using hzd
      · exact False.elim ((hmD d hdD) (by simpa [hzm] using hzd))
    exact ⟨u, d, a, huU, hdD, haX, huam, had, htud⟩
  · rintro ⟨u, d, a, huU, hdD, haX, huam, had, htud⟩
    have htQ : B.mem t Q := (hQ t).2 ⟨u, d, huU, hdD, htud⟩
    have hau : B.mem a u := (huam a).2 (Or.inl rfl)
    exact (hI t).2 ⟨htQ, u, d, htud, ⟨a, hau, had⟩⟩

end NineAxiomBZ
