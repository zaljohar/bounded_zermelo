import NineAxiomCore
/-!
# Bounded first-order formulas and the exact endpoint

This module isolates the Δ₀ object-language syntax from the large old
research draft. There is no Separation premise in this definition, and
`holds` uses the original membership relation of the given BZ model.

The endpoint is intentionally a DEFINITION, not an assumed axiom or
an unproved theorem.  Its proof still requires the finite tuple compiler.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

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
