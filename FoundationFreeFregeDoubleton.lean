import FoundationFreeNonPairWitness

/-!
# Finite Frege-1 test without Foundation

For an unordered pair p, being a *doubleton* is equivalent to existence
of two disjoint non-pair sets n,k, each intersecting p.

This precise equivalence is the mathematical core of the 2020 Frege-1
construction, but it works in non-well-founded membership structures.

The set-closure construction which collects all such doubletons is addressed
in `FoundationFreeFregeOne.lean`.

Kernel-checked with Lean 4.20.0. No Separation or Foundation is assumed.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

def IsUnorderedPair (m : V → V → Prop) (p : V) : Prop :=
  ∃ a b : V, IsUPair m p a b

def Intersects (m : V → V → Prop) (a b : V) : Prop :=
  ∃ z : V, m z a ∧ m z b

def DisjointSets (m : V → V → Prop) (a b : V) : Prop :=
  ∀ z : V, ¬(m z a ∧ m z b)

def Doubleton (m : V → V → Prop) (p : V) : Prop :=
  ∃ a b : V, IsUPair m p a b ∧ a ≠ b

def DisjointNonpairWitness (m : V → V → Prop) (p : V) : Prop :=
  ∃ n k : V,
    (¬ IsUnorderedPair m n) ∧ (¬ IsUnorderedPair m k) ∧
    DisjointSets m n k ∧ Intersects m n p ∧ Intersects m k p

private theorem pair_singleton_if_same (m : V → V → Prop)
    {p a b : V} (hp : IsUPair m p a b) (hab : a = b) :
    ∀ z : V, m z p ↔ z = a := by
  intro z
  rw [hp z, hab]
  tauto

/-- A pair is a genuine doubleton exactly if two disjoint nonpairs
can intersect it. No Foundation and no singleton-image set is used. -/
theorem doubleton_iff_disjoint_nonpair_witnesses
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (p : V) (hPair : IsUnorderedPair B.mem p) :
    Doubleton B.mem p ↔ DisjointNonpairWitness B.mem p := by
  let m := B.mem
  constructor
  · rintro ⟨a, b, hp, hab⟩
    obtain ⟨n, k, hnNP, hkNP, hnkd, han, hbk⟩ :=
      disjoint_nonpair_witnesses B H a b hab
    refine ⟨n, k, hnNP, hkNP, hnkd, ?_, ?_⟩
    · exact ⟨a, han, (hp a).2 (Or.inl rfl)⟩
    · exact ⟨b, hbk, (hp b).2 (Or.inr rfl)⟩
  · rintro ⟨n, k, _, _, hdisj, ⟨u, hun, hup⟩, ⟨v, hvk, hvp⟩⟩
    obtain ⟨a, b, hp⟩ := hPair
    refine ⟨a, b, hp, ?_⟩
    intro hab
    have hsing := pair_singleton_if_same m hp hab
    have hua : u = a := (hsing u).1 hup
    have hva : v = a := (hsing v).1 hvp
    have han : m a n := by simpa [hua] using hun
    have hak : m a k := by simpa [hva] using hvk
    exact hdisj a ⟨han, hak⟩

end NineAxiomBZ.NoFoundation
