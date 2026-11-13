import FoundationFreeTaggedTuple

/-!
# Foundation-free prefix and final-coordinate graphs

Construct the two projection graphs for T * F using only T9, Extensionality,
and Power Set, without any instance of Foundation or bounded Separation.
The necessary disjointness and exclusion of reverse membership are
proved in `FoundationFreeTaggedTuple`, with fresh two-cycle-free markers.

This is a replacement for the Foundation-dependent use of
`FreshPrefixStep` / `FreshTupleDisjoint` in the original green proof.
Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

private theorem upair_flip (m : V → V → Prop) {p a b : V}
    (h : IsUPair m p a b) : IsUPair m p b a := by
  intro z
  rw [h z]
  tauto

/-- An entirely Foundation-free version of the abstract two-sort
coordinate-projection lemma. -/
theorem first_coordinate_graph_exists_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U Vset T : V)
    (hT : ∀ t : V, B.mem t T ↔
      ∃ u v : V, B.mem u U ∧ B.mem v Vset ∧ IsUPair B.mem t u v)
    (hUV : DisjointSortNF B.mem U Vset)
    (hreverse : ∀ t u : V, B.mem t T → B.mem u U → ¬ B.mem t u) :
    HasMembers B.mem (fun p : V =>
      ∃ t u v : V, B.mem t T ∧ B.mem u U ∧ B.mem v Vset ∧
        IsUPair B.mem t u v ∧ IsUPair B.mem p t u) := by
  let m := B.mem
  obtain ⟨Q, hQ⟩ := unordered_product_without_foundation B H T U
  obtain ⟨E, hE⟩ := H.unorderedMembership Q
  refine ⟨E, ?_⟩
  intro p
  constructor
  · intro hpE
    obtain ⟨hpQ, a, b, hpab, hab⟩ := (hE p).mp hpE
    obtain ⟨t, u, htT, huU, hptu⟩ := (hQ p).mp hpQ
    have hor : m t u ∨ m u t := by
      rcases unordered_pair_endpoints_nf B hpab hptu with h | h
      · obtain ⟨hat, hbu⟩ := h
        rcases hab with h | h
        · exact Or.inl (by simpa [hat, hbu] using h)
        · exact Or.inr (by simpa [hat, hbu] using h)
      · obtain ⟨hau, hbt⟩ := h
        rcases hab with h | h
        · exact Or.inr (by simpa [hau, hbt] using h)
        · exact Or.inl (by simpa [hau, hbt] using h)
    have hut : m u t := hor.resolve_left (hreverse t u htT huU)
    obtain ⟨u0, v0, hu0, hv0, ht⟩ := (hT t).mp htT
    rcases (ht u).mp hut with huu0 | huv0
    · have huEq : u0 = u := huu0.symm
      subst u0
      exact ⟨t, u, v0, htT, huU, hv0, ht, hptu⟩
    · exact False.elim (hUV u v0 huU hv0 huv0)
  · rintro ⟨t, u, v, htT, huU, hvV, ht, hp⟩
    have hpQ : m p Q := (hQ p).mpr ⟨t, u, htT, huU, hp⟩
    have hut : m u t := (ht u).mpr (Or.inl rfl)
    exact (hE p).mpr ⟨hpQ, u, t, upair_flip m hp, Or.inl hut⟩

/-- The old Foundation-dependent prefix and last-coordinate graph
construction, now obtained from the nine axioms without Foundation.
No assumed graph constructor appears among its premises. -/
theorem fresh_two_projections_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (X T W : V) (hXW : B.mem X W) (hTW : B.mem T W) :
    ∃ (marker F N Gamma Lambda : V),
      (∀ f : V, B.mem f F ↔
        ∃ x : V, B.mem x X ∧ IsUPair B.mem f x marker) ∧
      (∀ n : V, B.mem n N ↔
        ∃ t f : V, B.mem t T ∧ B.mem f F ∧ IsUPair B.mem n t f) ∧
      (∀ p : V, B.mem p Gamma ↔
        ∃ n t f : V, B.mem n N ∧ B.mem t T ∧ B.mem f F ∧
          IsUPair B.mem n t f ∧ IsUPair B.mem p n t) ∧
      (∀ p : V, B.mem p Lambda ↔
        ∃ n t f : V, B.mem n N ∧ B.mem t T ∧ B.mem f F ∧
          IsUPair B.mem n t f ∧ IsUPair B.mem p n f) ∧
      DisjointSortNF B.mem T F ∧
      DisjointSortNF B.mem N T ∧
      DisjointSortNF B.mem N F ∧
      (∀ Y : V, B.mem Y W →
        DisjointSortNF B.mem F Y ∧ DisjointSortNF B.mem N Y) ∧
      (∀ Y z : V, B.mem Y W → B.mem z Y →
        ¬ B.mem marker z) ∧
      (∀ Y : V, B.mem Y W → ¬ B.mem marker Y) ∧
      (∀ Y z v : V, B.mem Y W → B.mem z Y → B.mem v z →
        ¬ B.mem marker v) := by
  let m := B.mem
  obtain ⟨marker, F, N, _hNo2, hF, hN,
    hTF, hNT, hNF, hrevNT, hrevNF, hFreshOld, hMarkerFreshOld, hMarkerOutside, hMarkerDeep⟩ :=
    fresh_three_sorts_without_foundation B H X T W hXW hTW

  obtain ⟨Gamma, hGamma⟩ :=
    first_coordinate_graph_exists_no_foundation B H T F N hN hTF hrevNT

  have hNswap (n : V) : m n N ↔
      ∃ f t : V, m f F ∧ m t T ∧ IsUPair m n f t := by
    have hN' : m n N ↔
        ∃ t f : V, m t T ∧ m f F ∧ IsUPair m n t f := by
      simpa only [m] using hN n
    rw [hN']
    constructor
    · rintro ⟨t, f, ht, hf, hn⟩
      exact ⟨f, t, hf, ht, upair_flip m hn⟩
    · rintro ⟨f, t, hf, ht, hn⟩
      exact ⟨t, f, ht, hf, upair_flip m hn⟩

  have hFT : DisjointSortNF m F T := by
    intro f t hf ht hEq
    exact hTF t f ht hf hEq.symm

  obtain ⟨Lambda, hLambda⟩ :=
    first_coordinate_graph_exists_no_foundation B H F T N
      hNswap hFT hrevNF

  refine ⟨marker, F, N, Gamma, Lambda,
    hF, hN, ?_, ?_, hTF, hNT, hNF, hFreshOld,
    hMarkerFreshOld, hMarkerOutside, hMarkerDeep⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨n, t, f, hnN, htT, hfF, hnPair, hpPair⟩ :=
        (hGamma p).mp hp
      exact ⟨n, t, f, hnN, htT, hfF, hnPair, hpPair⟩
    · rintro ⟨n, t, f, hnN, htT, hfF, hnPair, hpPair⟩
      exact (hGamma p).mpr ⟨n, t, f, hnN, htT, hfF, hnPair, hpPair⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨n, f, t, hnN, hfF, htT, hnPair, hpPair⟩ :=
        (hLambda p).mp hp
      exact ⟨n, t, f, hnN, htT, hfF,
        upair_flip m hnPair, hpPair⟩
    · rintro ⟨n, t, f, hnN, htT, hfF, hnPair, hpPair⟩
      exact (hLambda p).mpr ⟨n, f, t, hnN, hfF, htT,
        upair_flip m hnPair, hpPair⟩

end NineAxiomBZ.NoFoundation
