import Mathlib.Data.Fin.VecNotation

/-! Frozen statement and definitions from adaptive snapshot e462dec.
No project proof imports. The four sorries are intentional challenge holes only. -/

universe u

namespace NineAxiomBZ

variable {V : Type u}

/-- Membership-only interpretation of a set in a one-sorted first-order model. -/
def HasMembers (mem : V → V → Prop) (P : V → Prop) : Prop :=
  ∃ s : V, ∀ x : V, mem x s ↔ P x

/-- An unordered pair, including the degenerate case `a = b`. -/
def IsUPair (mem : V → V → Prop) (p a b : V) : Prop :=
  ∀ x : V, mem x p ↔ x = a ∨ x = b

/-- The eight unrestricted operations from the first MathOverflow post plus
(9) the common-superset principle.  These assert existence, not the existence
of a global universal set or a bounded relational milieu. -/
structure NineAxioms (mem : V → V → Prop) where
  empty : HasMembers mem (fun _ : V => False)
  singleton : ∀ a : V, HasMembers mem (fun x : V => x = a)
  difference : ∀ a b : V,
    HasMembers mem (fun x : V => mem x a ∧ ¬ mem x b)
  intersection : ∀ a b : V,
    HasMembers mem (fun x : V => mem x a ∧ mem x b)
  setUnion : ∀ a : V,
    HasMembers mem (fun x : V => ∃ y : V, mem y a ∧ mem x y)
  unorderedComposition : ∀ q r : V,
    HasMembers mem (fun t : V =>
      ∃ a b c : V,
        IsUPair mem t a c ∧
        (∃ p : V, mem p q ∧ IsUPair mem p a b) ∧
        (∃ p : V, mem p r ∧ IsUPair mem p b c))
  unorderedIntersection : ∀ x : V,
    HasMembers mem (fun t : V =>
      mem t x ∧ ∃ a b : V,
        IsUPair mem t a b ∧
        ∃ z : V, mem z a ∧ mem z b)
  unorderedMembership : ∀ x : V,
    HasMembers mem (fun t : V =>
      mem t x ∧ ∃ a b : V,
        IsUPair mem t a b ∧ (mem a b ∨ mem b a))
  commonSuperset : ∀ a b : V,
    ∃ c : V, ∀ x : V, mem x a ∨ mem x b → mem x c

/-- Syntax of Δ₀ first-order formulas, with n variables represented by
Fin n. Every quantifier is bounded by an existing variable. -/
inductive DeltaZero : Nat → Type where
  | equal {n : Nat} (i j : Fin n) : DeltaZero n
  | member {n : Nat} (i j : Fin n) : DeltaZero n
  | falsum {n : Nat} : DeltaZero n
  | neg {n : Nat} (φ : DeltaZero n) : DeltaZero n
  | conj {n : Nat} (φ ψ : DeltaZero n) : DeltaZero n
  | bex {n : Nat} (bound : Fin n) (body : DeltaZero (n + 1)) : DeltaZero n

/-- Full original-membership semantics, including bounded quantification.
`Fin.cases y ρ` adds the new de Bruijn variable in position zero. -/
def DeltaZero.holds (mem : V → V → Prop) :
    {n : Nat} → DeltaZero n → (Fin n → V) → Prop
  | _, .equal i j, ρ => ρ i = ρ j
  | _, .member i j, ρ => mem (ρ i) (ρ j)
  | _, .falsum, _ => False
  | _, .neg φ, ρ => ¬ φ.holds mem ρ
  | _, .conj φ ψ, ρ => φ.holds mem ρ ∧ ψ.holds mem ρ
  | _, .bex i φ, ρ =>
      ∃ y : V, mem y (ρ i) ∧ φ.holds mem (Fin.cases y ρ)

/-- The fully parameterized, *nonstratified* Δ₀-Separation schema.
No proof or Separation axiom is silently assumed. -/
def BoundedSeparation (mem : V → V → Prop) : Prop :=
  ∀ (n : Nat) (φ : DeltaZero (n + 1))
    (a : V) (parameters : Fin n → V),
    HasMembers mem (fun x : V =>
      mem x a ∧ φ.holds mem (Fin.cases x parameters))

end NineAxiomBZ

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

/-- Bounded Zermelo over the common Extensionality/Power Set background.
Any optional additional axiom (e.g., Infinity) may be added to both sides of
our equivalence without changing the proof. -/
structure BoundedZermeloCore (B : BackgroundNoFoundation V) : Prop where
  empty : HasMembers B.mem (fun _ : V => False)
  pairing : ∀ a b : V, HasMembers B.mem (fun x : V => x = a ∨ x = b)
  union : ∀ a : V, HasMembers B.mem (fun x : V =>
    ∃ y : V, B.mem y a ∧ B.mem x y)
  separation : BoundedSeparation B.mem

theorem bounded_separation_from_nine_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    BoundedSeparation B.mem := sorry

theorem nine_axioms_imply_bounded_zermelo_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    BoundedZermeloCore B := sorry

theorem bounded_zermelo_iff_nine_no_foundation
    (B : BackgroundNoFoundation V) :
    BoundedZermeloCore B ↔ Nonempty (NineAxioms B.mem) := sorry

theorem bounded_zermelo_iff_bzminus_plus_nine_no_foundation
    (B : BackgroundNoFoundation V) :
    BoundedZermeloCore B ↔
      (BZMinusNoFoundation B ∧ Nonempty (NineAxioms B.mem)) := sorry

end NineAxiomBZ.NoFoundation
