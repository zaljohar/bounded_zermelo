import FoundationFreeUnorderedProduct
/-!
An unconditional Δ₀-Separation instance without Foundation:
  {x∈A | x∩B ≠ ∅}
This uses the marker-free unordered product, the unordered intersection
relation, set union, and intersection. It never uses singleton images.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- The overlap selector exists without Foundation or any auxiliary
hypothesis, including `NoUniversal`.
A key detail is that the endpoint B entering ∪H is harmless: when H is
nonempty, B is nonempty, and therefore B∩B is nonempty. -/
theorem intersecting_elements_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (A D : V) :
    HasMembers B.mem (fun x : V =>
      B.mem x A ∧ ∃ z : V, B.mem z x ∧ B.mem z D) := by
  let m := B.mem
  obtain ⟨sD, hsD⟩ := H.singleton D
  obtain ⟨R, hR⟩ := unordered_product_without_foundation B H A sD
  obtain ⟨J, hJ⟩ := H.unorderedIntersection R
  obtain ⟨U, hU⟩ := H.setUnion J
  obtain ⟨I, hI⟩ := H.intersection A U
  refine ⟨I, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxA, hxU⟩ := (hI x).1 hx
    obtain ⟨t, htJ, hxt⟩ := (hU x).1 hxU
    obtain ⟨htR, a, b, hp, ⟨z, hza, hzb⟩⟩ := (hJ t).1 htJ
    obtain ⟨v, w, hvA, hwSD, htvw⟩ := (hR t).1 htR
    have hw : w = D := (hsD w).1 hwSD
    subst w
    have hxv : x = v ∨ x = D := (htvw x).1 hxt
    have hpair := unordered_pair_endpoints_nf B hp htvw
    have hover : ∃ z : V, m z v ∧ m z D := by
      rcases hpair with ⟨hav, hbD⟩ | ⟨haD, hbv⟩
      · exact ⟨z, by simpa [hav] using hza,
          by simpa [hbD] using hzb⟩
      · exact ⟨z, by simpa [hbv] using hzb,
          by simpa [haD] using hza⟩
    refine ⟨hxA, ?_⟩
    rcases hxv with h | h
    · simpa [h] using hover
    · obtain ⟨z, _, hzD⟩ := hover
      exact ⟨z, by simpa [h] using hzD, hzD⟩
  · rintro ⟨hxA, ⟨z, hzx, hzD⟩⟩
    obtain ⟨t, ht⟩ := unordered_pair_exists m H x D
    have htR : m t R :=
      (hR t).2 ⟨x, D, hxA, (hsD D).2 rfl, ht⟩
    have htJ : m t J :=
      (hJ t).2 ⟨htR, x, D, ht, ⟨z, hzx, hzD⟩⟩
    have hxU : m x U :=
      (hU x).2 ⟨t, htJ, (ht x).2 (Or.inl rfl)⟩
    exact (hI x).2 ⟨hxA, hxU⟩

/-- The nonstratified-looking direction `c ∈ x` is already available
as a Δ₀ unary separation instance. -/
theorem contains_element_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (A c : V) :
    HasMembers B.mem (fun x : V => B.mem x A ∧ B.mem c x) := by
  obtain ⟨sc, hsc⟩ := H.singleton c
  obtain ⟨K, hK⟩ := intersecting_elements_without_foundation B H A sc
  refine ⟨K, ?_⟩
  intro x
  rw [hK x]
  constructor
  · rintro ⟨hxA, z, hzx, hzsc⟩
    have hzc : z = c := (hsc z).1 hzsc
    exact ⟨hxA, by simpa [hzc] using hzx⟩
  · rintro ⟨hxA, hcx⟩
    exact ⟨hxA, c, hcx, (hsc c).2 rfl⟩

end NineAxiomBZ.NoFoundation
