import FoundationFreeNoUniverseReduction

/-!
# Universal-set bridge (Foundation-free)
A Frege-one set is a set of ALL singleton objects. If it exists, the
unordered membership filter constructs the Russell class as a set.
This file does not postulate a universal set or Foundation.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

def IsUniversal (B : BackgroundNoFoundation V) (U : V) : Prop :=
  ∀ x : V, B.mem x U

def FregeOne (B : BackgroundNoFoundation V) : Prop :=
  HasMembers B.mem (fun s : V =>
    ∃ x : V, ∀ y : V, B.mem y s ↔ y = x)

/-- Under a hypothetical universal set, unordered composition of U with U
is the set of all unordered pairs (including singleton degenerate pairs). -/
theorem all_unordered_pairs_if_universal
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U : V) (hU : IsUniversal B U) :
    HasMembers B.mem (fun t : V =>
      ∃ a b : V, IsUPair B.mem t a b) := by
  obtain ⟨P, hP⟩ := H.unorderedComposition U U
  refine ⟨P, ?_⟩
  intro t
  constructor
  · intro ht
    obtain ⟨a, b, c, hac, _, _⟩ := (hP t).mp ht
    exact ⟨a, c, hac⟩
  · rintro ⟨a, c, hac⟩
    obtain ⟨aa, haa⟩ := unordered_pair_exists B.mem H a a
    obtain ⟨ac, hac'⟩ := unordered_pair_exists B.mem H a c
    exact (hP t).mpr ⟨a, a, c, hac,
      ⟨aa, hU aa, haa⟩, ⟨ac, hU ac, hac'⟩⟩

/-- A global singleton-set family immediately excludes a universal set;
this is just the T9 unordered-membership/diagonal Russell construction. -/
theorem no_universal_if_frege_one
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hOne : FregeOne B) : NoUniversal B := by
  obtain ⟨one, hOneMem⟩ := hOne
  apply no_universal_from_global_singletons B H
  intro U hUniv
  refine ⟨one, ?_⟩
  intro t
  constructor
  · intro hton
    obtain ⟨a, hsingle⟩ := (hOneMem t).mp hton
    exact ⟨a, hUniv a, hsingle⟩
  · rintro ⟨a, _, hsingle⟩
    exact (hOneMem t).mpr ⟨a, hsingle⟩

end NineAxiomBZ.NoFoundation
