import DeltaZeroSyntax
/-!
# Foundation-free background
The original verified project builds Foundation into `Background`.  The
replacement below is genuinely weaker: Extensionality + Power Set only.
These declarations add NO Foundation, no acyclicity, and no Separation.
-/
universe u
namespace NineAxiomBZ.NoFoundation

/-- Extensionality and Power Set, with no restriction on membership cycles. -/
structure BackgroundNoFoundation (V : Type u) where
  mem : V → V → Prop
  extensionality : ∀ a b : V, (∀ x : V, mem x a ↔ mem x b) → a = b
  powerset : ∀ a : V,
    HasMembers mem (fun x : V => ∀ y : V, mem y x → mem y a)

variable {V : Type u}

/-- The usual elementary existence axioms, without Separation or Foundation. -/
structure BZMinusNoFoundation (B : BackgroundNoFoundation V) : Prop where
  empty : HasMembers B.mem (fun _ : V => False)
  pairing : ∀ a b : V, HasMembers B.mem (fun x : V => x = a ∨ x = b)
  union : ∀ a : V, HasMembers B.mem (fun x : V =>
    ∃ y : V, B.mem y a ∧ B.mem x y)

/-- This direction uses no regularity or cycle-exclusion assumption. -/
theorem nine_axioms_imply_bzminus
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    BZMinusNoFoundation B := by
  exact ⟨H.empty, unordered_pair_exists B.mem H, H.setUnion⟩

end NineAxiomBZ.NoFoundation
