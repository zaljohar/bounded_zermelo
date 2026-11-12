import NineAxiomCore
/-!
Projection graphs for unordered products of *disjoint* sorts.  The hypotheses
are explicit and will be furnished by the later fresh-marker construction.
No extra existence axiom and no bounded-Separation theorem is assumed.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- If `T` is the unordered product of disjoint sorts `U` and `V`, and
no product code belongs to a member of `U`, the first-coordinate projection
is a set of unordered pairs. -/
theorem first_coordinate_graph_exists
    (B : Background V) (H : NineAxioms B.mem)
    (U Vset T : V)
    (hT : ∀ t : V, B.mem t T ↔
      ∃ u v : V, B.mem u U ∧ B.mem v Vset ∧ IsUPair B.mem t u v)
    (hUV : ∀ u v : V, B.mem u U → B.mem v Vset → u ≠ v)
    (hreverse : ∀ t u : V, B.mem t T → B.mem u U → ¬ B.mem t u) :
    HasMembers B.mem (fun p : V =>
      ∃ t u v : V, B.mem t T ∧ B.mem u U ∧ B.mem v Vset ∧
        IsUPair B.mem t u v ∧ IsUPair B.mem p t u) := by
  obtain ⟨Q, hQ⟩ := unordered_product_exists B H T U
  obtain ⟨E, hE⟩ := H.unorderedMembership Q
  refine ⟨E, ?_⟩
  intro p
  constructor
  · intro hpE
    obtain ⟨hpQ, a, b, hpab, hab⟩ := (hE p).1 hpE
    obtain ⟨t, u, htT, huU, hptu⟩ := (hQ p).1 hpQ
    have htu_or_hut : B.mem t u ∨ B.mem u t := by
      rcases unordered_pair_endpoints B hpab hptu with h | h
      · rcases h with ⟨hat, hbu⟩
        rcases hab with hab | hba
        · exact Or.inl (by simpa [hat, hbu] using hab)
        · exact Or.inr (by simpa [hat, hbu] using hba)
      · rcases h with ⟨hau, hbt⟩
        rcases hab with hab | hba
        · exact Or.inr (by simpa [hau, hbt] using hab)
        · exact Or.inl (by simpa [hau, hbt] using hba)
    have hut : B.mem u t := htu_or_hut.resolve_left (hreverse t u htT huU)
    obtain ⟨u0, v0, hu0, hv0, ht⟩ := (hT t).1 htT
    rcases (ht u).1 hut with huEq | hvEq
    · subst u0
      exact ⟨t, u, v0, htT, huU, hv0, ht, hptu⟩
    · have huu0 : u = v0 := hvEq
      exact False.elim (hUV u v0 huU hv0 huu0)
  · rintro ⟨t, u, v, htT, huU, hvV, ht, hp⟩
    have hpQ : B.mem p Q := (hQ p).2 ⟨t, u, htT, huU, hp⟩
    have hut : B.mem u t := (ht u).2 (Or.inl rfl)
    apply (hE p).2
    refine ⟨hpQ, u, t, ?_, Or.inl hut⟩
    · intro x
      constructor
      · intro hx
        rcases (hp x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (hp x).2 (Or.inr h)
        · exact (hp x).2 (Or.inl h)

end NineAxiomBZ
