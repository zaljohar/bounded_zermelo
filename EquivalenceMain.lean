import BoundedZermeloReverse
/-!
# Final endpoint: finite axiomatization of Bounded Zermelo

The equivalence is relative to `Background` (Extensionality, Power Set,
Foundation). `BoundedZermeloCore` includes Empty Set, Pairing, Union, and
full Δ₀-Separation; `NineAxioms` contains exactly the nine proposed axioms.
There is no Separation hypothesis in the nine-axiom-to-BZ direction.

The complete project was elaborated and kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ

variable {V : Type u}

/-- Bounded Zermelo with the Δ₀-Separation schema removed, over the
shared Background. This keeps the usual Empty Set, Pairing, and Union. -/
structure BoundedZermeloMinus (B : Background V) : Prop where
  empty : HasMembers B.mem (fun _ : V => False)
  pairing : ∀ a b : V, HasMembers B.mem (fun x : V => x = a ∨ x = b)
  union : ∀ a : V, HasMembers B.mem (fun x : V =>
    ∃ y : V, B.mem y a ∧ B.mem x y)

/-- The nine axioms as a single proposition (the record itself is a Type). -/
def HasNineAxioms (B : Background V) : Prop :=
  Nonempty (NineAxioms B.mem)

/-- The nine axioms imply the ordinary BZ axioms, including Δ₀-Separation. -/
theorem nine_axioms_imply_bounded_zermelo
    (B : Background V) (H : NineAxioms B.mem) :
    BoundedZermeloCore B := by
  refine {
    empty := H.empty,
    pairing := unordered_pair_exists B.mem H,
    union := H.setUnion,
    separation := nine_axioms_imply_delta_zero_separation B H
  }

/-- The final equivalence: Bounded Zermelo ↔ separation-free background
plus the nine unrestricted operations. -/
theorem bounded_zermelo_iff_nine_axioms (B : Background V) :
    BoundedZermeloCore B ↔ HasNineAxioms B := by
  constructor
  · intro h
    exact ⟨bounded_zermelo_implies_nine_axioms B h⟩
  · rintro ⟨H⟩
    exact nine_axioms_imply_bounded_zermelo B H


/-- **Exact requested endpoint**:
    BZ ↔ (BZ without Δ₀-Separation) + T₉.

The stronger statement above also shows the elementary existence fields in
`BoundedZermeloMinus` are redundant on the nine-axiom side. -/
theorem bounded_zermelo_iff_bzminus_plus_nine (B : Background V) :
    BoundedZermeloCore B ↔ (BoundedZermeloMinus B ∧ HasNineAxioms B) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ⟨h.empty, h.pairing, h.union⟩
    · exact ⟨bounded_zermelo_implies_nine_axioms B h⟩
  · rintro ⟨_, hNine⟩
    exact (bounded_zermelo_iff_nine_axioms B).mpr hNine

/-- Any additional common axioms, such as Infinity or Choice, can be
conjoined to *both* formulations without changing the equivalence. -/
theorem bounded_zermelo_iff_nine_with_extra
    (B : Background V) (Extra : Prop) :
    (BoundedZermeloCore B ∧ Extra) ↔ (HasNineAxioms B ∧ Extra) := by
  constructor
  · rintro ⟨hBZ, hExtra⟩
    exact ⟨(bounded_zermelo_iff_nine_axioms B).mp hBZ, hExtra⟩
  · rintro ⟨hNine, hExtra⟩
    exact ⟨(bounded_zermelo_iff_nine_axioms B).mpr hNine, hExtra⟩

end NineAxiomBZ

#print axioms NineAxiomBZ.bounded_zermelo_iff_bzminus_plus_nine
