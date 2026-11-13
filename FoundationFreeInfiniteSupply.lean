import FoundationFreeCore
import Mathlib.Data.Fintype.EquivFin

/-!
# Infinitely many distinct objects without Foundation

The existence of an empty set and of singletons is enough to exhibit an
injective meta-level map Nat → V, even if the model contains membership cycles.

This is NOT an Infinity axiom: the range of the external map is not asserted
 to be represented by a set in the membership structure.

This file uses no Foundation and no Separation.
-/

universe u
namespace NineAxiomBZ.NoFoundation

variable {V : Type u}

noncomputable def zeroObject (m : V → V → Prop) (H : NineAxioms m) : V :=
  Classical.choose H.empty

noncomputable def singletonObject (m : V → V → Prop)
    (H : NineAxioms m) (a : V) : V :=
  Classical.choose (H.singleton a)

private theorem zeroObject_empty (m : V → V → Prop) (H : NineAxioms m) (x : V) :
    ¬ m x (zeroObject m H) := by
  exact ((Classical.choose_spec H.empty) x).mp

private theorem singletonObject_mem (m : V → V → Prop) (H : NineAxioms m)
    (a x : V) :
    m x (singletonObject m H a) ↔ x = a :=
  (Classical.choose_spec (H.singleton a)) x

noncomputable def pureFiniteObjects (m : V → V → Prop)
    (H : NineAxioms m) : Nat → V
  | 0 => zeroObject m H
  | n + 1 => singletonObject m H (pureFiniteObjects m H n)

/-- Distinct indices give distinct objects, with no cycle exclusions. -/
theorem pureFiniteObjects_injective (m : V → V → Prop) (H : NineAxioms m) :
    Function.Injective (pureFiniteObjects m H) := by
  intro i
  induction i with
  | zero =>
      intro j hij
      cases j with
      | zero => rfl
      | succ j =>
          have hm : m (pureFiniteObjects m H j)
              (pureFiniteObjects m H (j + 1)) := by
            change m (pureFiniteObjects m H j)
              (singletonObject m H (pureFiniteObjects m H j))
            exact (singletonObject_mem m H _ _).2 rfl
          have hm0 : m (pureFiniteObjects m H j)
              (pureFiniteObjects m H 0) := by
            rw [hij]
            exact hm
          exact False.elim (zeroObject_empty m H _ hm0)
  | succ i ih =>
      intro j hij
      cases j with
      | zero =>
          have hm : m (pureFiniteObjects m H i)
              (pureFiniteObjects m H (i + 1)) := by
            change m (pureFiniteObjects m H i)
              (singletonObject m H (pureFiniteObjects m H i))
            exact (singletonObject_mem m H _ _).2 rfl
          have hm0 : m (pureFiniteObjects m H i)
              (pureFiniteObjects m H 0) := by
            rw [← hij]
            exact hm
          exact False.elim (zeroObject_empty m H _ hm0)
      | succ j =>
          have hprev : pureFiniteObjects m H i = pureFiniteObjects m H j := by
            have hmem : m (pureFiniteObjects m H i)
                (pureFiniteObjects m H (j + 1)) := by
              rw [← hij]
              change m (pureFiniteObjects m H i)
                (singletonObject m H (pureFiniteObjects m H i))
              exact (singletonObject_mem m H _ _).2 rfl
            exact (singletonObject_mem m H _ _).1 hmem
          exact congrArg Nat.succ (ih hprev)

/-- The carrier is infinite in the metatheory, not necessarily internally
Dedekind-infinite. -/
theorem infinite_carrier_from_nine (m : V → V → Prop) (H : NineAxioms m) :
    Infinite V := by
  exact Infinite.of_injective (pureFiniteObjects m H)
    (pureFiniteObjects_injective m H)

end NineAxiomBZ.NoFoundation
