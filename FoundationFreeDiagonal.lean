import FoundationFreeCore
/-!
# Replacing the invalid Foundation-based self-membership shortcut

A non-well-founded membership structure can contain x∈x, so the original
`TagUniqueness.no_self_membership_for_tags` and the diagonal case in
`FiniteFrameAllAtomic` are UNAVAILABLE in the desired theorem.

The following theorem gives a Foundation-free replacement *conditional on*
singleton-image existence for the bounded input set.  The missing task is
to derive the singleton-image existence uniformly from T₉ without using
Foundation.  This condition is NOT added to any final theorem as an axiom.

This source has not been compiled in the current environment.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- A bounded singleton-image family. -/
def SingletonImageOn (m : V → V → Prop) (A : V) : Prop :=
  HasMembers m (fun t : V =>
    ∃ x : V, m x A ∧ (∀ y : V, m y t ↔ y = x))

/-- The old proof used Foundation to declare all self-membership atoms false.
This replacement constructs their *actual* truth set, including possible
Quine atoms and other non-well-founded objects, provided singleton images
are available.  The construction is exactly: ∪(unorderedMembership(A^ι)). -/
theorem diagonal_membership_from_singleton_image
    (m : V → V → Prop) (H : NineAxioms m)
    (A : V) (hImage : SingletonImageOn m A) :
    HasMembers m (fun x : V => m x A ∧ m x x) := by
  obtain ⟨I, hI⟩ := hImage
  obtain ⟨J, hJ⟩ := H.unorderedMembership I
  obtain ⟨U, hU⟩ := H.setUnion J
  refine ⟨U, ?_⟩
  intro x
  rw [hU x]
  constructor
  · rintro ⟨t, htJ, hxt⟩
    obtain ⟨htI, a, b, hp, hab⟩ := (hJ t).mp htJ
    obtain ⟨y, hyA, hySingle⟩ := (hI t).mp htI
    have hxy : x = y := (hySingle x).mp hxt
    have hay : a = y := (hySingle a).mp ((hp a).mpr (Or.inl rfl))
    have hby : b = y := (hySingle b).mp ((hp b).mpr (Or.inr rfl))
    have hyy : m y y := by
      rcases hab with hab | hba
      · simpa [hay, hby] using hab
      · simpa [hay, hby] using hba
    exact ⟨by simpa [hxy] using hyA, by simpa [hxy] using hyy⟩
  · rintro ⟨hxA, hxx⟩
    obtain ⟨sx, hsx⟩ := H.singleton x
    have hsxI : m sx I := (hI sx).mpr ⟨x, hxA, hsx⟩
    have hsxPair : IsUPair m sx x x := by
      intro y
      simpa [or_self] using (hsx y)
    have hsxJ : m sx J :=
      (hJ sx).mpr ⟨hsxI, x, x, hsxPair, Or.inl hxx⟩
    exact ⟨sx, hsxJ, (hsx x).mpr rfl⟩

end NineAxiomBZ.NoFoundation
