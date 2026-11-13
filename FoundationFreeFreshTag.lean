import FoundationFreeFan
/-!
A Foundation-free replacement for `fresh_marker_for_two`, conditional on
**properness of every set** (NoUniversal).  This conditional is not assumed
in the final target; whether it follows from T₉ is an open subgoal.
No cycle exclusion or Foundation is invoked here.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Every set omits at least one object. This is *not* assumed by T₉. -/
def NoUniversal (B : BackgroundNoFoundation V) : Prop :=
  ∀ D : V, ∃ marker : V, ¬ B.mem marker D

/-- A marker outside U, outside every element of U, and outside every element
of an element of U. Requires only finite Union and `NoUniversal`.
The construction itself does not use membership acyclicity. -/
theorem fresh_marker_three_levels
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hn : NoUniversal B) (U : V) :
    ∃ marker : V,
      (¬ B.mem marker U) ∧
      (∀ u : V, B.mem u U → ¬ B.mem marker u) ∧
      (∀ u v : V, B.mem u U → B.mem v u → ¬ B.mem marker v) := by
  let m := B.mem
  obtain ⟨U1, hU1⟩ := H.setUnion U
  obtain ⟨U2, hU2⟩ := H.setUnion U1
  obtain ⟨D1, hD1⟩ := binary_union_exists m H U U1
  obtain ⟨D, hD⟩ := binary_union_exists m H D1 U2
  obtain ⟨marker, hmarker⟩ := hn D
  have hnotU : ¬ m marker U := by
    intro hmU
    exact hmarker ((hD marker).2 (Or.inl ((hD1 marker).2 (Or.inl hmU))))
  have hnotU1 : ¬ m marker U1 := by
    intro hmU1
    exact hmarker ((hD marker).2 (Or.inl ((hD1 marker).2 (Or.inr hmU1))))
  have hnotU2 : ¬ m marker U2 := by
    intro hmU2
    exact hmarker ((hD marker).2 (Or.inr hmU2))
  refine ⟨marker, hnotU, ?_, ?_⟩
  · intro u hu hmu
    exact hnotU1 ((hU1 marker).2 ⟨u, hu, hmu⟩)
  · intro u v hu hv hmv
    have hvU1 : m v U1 := (hU1 v).2 ⟨u, hu, hv⟩
    exact hnotU2 ((hU2 marker).2 ⟨v, hvU1, hmv⟩)

end NineAxiomBZ.NoFoundation
