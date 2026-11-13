import FoundationFreeFrameMatching
/-!
# Directed membership edges using unordered intersection

This module derives, directly from the unrestricted unordered-intersection
operation, the graph of *directed* membership between a fresh tagged copy of
one domain and another bounded domain.  It does not postulate Separation,
Gödel's membership operation, or any truth-set compiler.

The essential hypothesis is freshness of the marker `m` from every member of
`D`: then `{a,m} ∩ d ≠ ∅` is equivalent to `a ∈ d`.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- If `U` consists of the unordered tagged copies `{a,m}` of `a ∈ X`, and
`m` belongs to none of the sets in `D`, the unordered intersection filter
constructs *directed* membership from the tagged sort `U` to `D`.

`H` is the exact edge set:

  H = { {u,d} | u∈U, d∈D, ∃a∈X (u={a,m} ∧ a∈d) }.

The predicate is a proof-level specification, not a use of Separation.
-/
theorem tagged_raw_membership_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (X U D m : V)
    (hU : ∀ u : V, B.mem u U ↔
      ∃ a : V, B.mem a X ∧ IsUPair B.mem u a m)
    (hmD : ∀ d : V, B.mem d D → ¬ B.mem m d) :
    HasMembers B.mem (fun t : V =>
      ∃ u d a : V,
        B.mem u U ∧ B.mem d D ∧ B.mem a X ∧
        IsUPair B.mem u a m ∧ B.mem a d ∧
        IsUPair B.mem t u d) := by
  obtain ⟨Q, hQ⟩ := unordered_product_without_foundation B H U D
  obtain ⟨I, hI⟩ := H.unorderedIntersection Q
  refine ⟨I, ?_⟩
  intro t
  constructor
  · intro htI
    obtain ⟨htQ, v, w, htvw, ⟨z, hzv, hzw⟩⟩ := (hI t).1 htI
    obtain ⟨u, d, huU, hdD, htud⟩ := (hQ t).1 htQ
    have hInt : ∃ z : V, B.mem z u ∧ B.mem z d := by
      rcases unordered_pair_endpoints_nf B htvw htud with h | h
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

end NineAxiomBZ.NoFoundation

namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Directed membership edges from the ith tagged coordinate into the
common raw envelope E; no Foundation premise. -/
theorem frame_member_to_raw_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D) (i : Fin n) :
    ∃ G : V, TypedEdges B.mem (F.tagSort i) E
      (fun u b => ∃ a : V, B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i) ∧ B.mem a b) G := by
  obtain ⟨G, hG⟩ := tagged_raw_membership_edges_exists_nf
    B H (D i) (F.tagSort i) E (F.marker i)
    (F.tagSpec i) (F.markerFresh i)
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨u, b, a, hu, hb, ha, hua, hab, hp'⟩ := (hG p).mp hp
    exact ⟨u, b, hu, hb, hp', a, ha, hua, hab⟩
  · rintro ⟨u, b, hu, hb, hp', a, ha, hua, hab⟩
    exact (hG p).mpr ⟨u, b, a, hu, hb, ha, hua, hab, hp'⟩

/-- Two distinct tagged coordinates admit an exact directed membership
relation even for nonstratified membership. -/
theorem frame_membership_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun p : V =>
      ∃ u v : V, B.mem u (F.tagSort i) ∧
        B.mem v (F.tagSort j) ∧ IsUPair B.mem p u v ∧
        ∃ b : V, B.mem b E ∧
          (∃ a : V, B.mem a (D i) ∧
            IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
          (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) := by
  obtain ⟨Gi, hGi⟩ := frame_member_to_raw_edges_exists_nf
    B H E n D F i
  obtain ⟨Gj, hGj⟩ := frame_matching_edges_exists_nf
    B H E n D F j
  have hUE : DisjointSortNF B.mem (F.tagSort i) E := by
    intro u a hu ha heq
    exact F.rawDisjoint i a u ha hu heq.symm
  exact typed_composition_exists_nf B H
    (F.tagSort i) E (F.tagSort j) Gi Gj
    (fun u b => ∃ a : V, B.mem a (D i) ∧
      IsUPair B.mem u a (F.marker i) ∧ B.mem a b)
    (fun b v => B.mem b (D j) ∧
      IsUPair B.mem v b (F.marker j))
    hUE (F.tagPairwiseDisjoint i j hij) (F.rawDisjoint j)
    hGi hGj

end NineAxiomBZ.NoFoundation
