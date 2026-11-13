import FoundationFreeFregeOne
import FoundationFreeFiniteEnvelope

/-!
# Russell markers without Foundation

The original proof uses Foundation to obtain fresh, irreflexive tags.
Under the nine axioms this is unnecessary.  The localized Russell set

    R(D) = {x in D : x notin x}

exists, because the preceding Frege-one construction gives singleton
images and hence the bounded self-membership selector.  Russell's
argument proves BOTH `R(D) notin D` and `R(D) notin R(D)`.

Applying the construction to a finite membership-depth envelope gives
irreflexive markers fresh at any prescribed finite depth.  It does not
postulate Foundation, `NoUniversal`, or bounded Separation.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Bounded Russell separation follows from the nine operations once the
Frege-one argument has established local singleton images.  This does NOT
assume any other separation instance. -/
theorem relative_russell_set_exists
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (D : V) :
    HasMembers B.mem (fun x : V => B.mem x D ∧ ¬ B.mem x x) := by
  obtain ⟨Self, hSelf⟩ :=
    diagonal_membership_from_singleton_image B.mem H D
      (singleton_images_from_nine_no_foundation B H D)
  obtain ⟨R, hR⟩ := H.difference D Self
  refine ⟨R, ?_⟩
  intro x
  rw [hR x]
  change (B.mem x D ∧ ¬ B.mem x Self) ↔ _
  rw [hSelf x]
  tauto

/-- The relative Russell set is outside D and does not belong to itself.
Neither statement uses Foundation or the assumption `NoUniversal`. -/
theorem relative_russell_fresh_irreflexive
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (D : V) :
    ∃ R : V,
      (∀ x : V, B.mem x R ↔ B.mem x D ∧ ¬ B.mem x x) ∧
      ¬ B.mem R D ∧ ¬ B.mem R R := by
  obtain ⟨R, hR⟩ := relative_russell_set_exists B H D
  have hNoSelf : ¬ B.mem R R := by
    intro h
    exact ((hR R).mp h).2 h
  have hOutside : ¬ B.mem R D := by
    intro h
    exact hNoSelf ((hR R).mpr ⟨h, hNoSelf⟩)
  exact ⟨R, hR, hOutside, hNoSelf⟩

/-- A structural monotonicity fact: an object reachable at depth k is
also reachable at depth k+1.  Cyclic membership poses no difficulty. -/
theorem reachableWithin_step
    (m : V → V → Prop) (D : V) (k : Nat) (x : V)
    (h : ReachableWithin m D k x) :
    ReachableWithin m D (k + 1) x :=
  Or.inl h

/-- Monotonicity of the bounded reachability predicate. -/
theorem reachableWithin_mono
    (m : V → V → Prop) (D : V)
    {k n : Nat} (hkn : k ≤ n) {x : V}
    (hx : ReachableWithin m D k x) :
    ReachableWithin m D n x := by
  induction n, hkn using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact Or.inl ih

/-- Freshness at every fixed finite depth, WITH irreflexivity, follows
unconditionally from T9 plus Extensionality and Power Set. -/
theorem irreflexive_fresh_marker_at_depth
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (D : V) (n : Nat) :
    ∃ marker : V,
      ¬ B.mem marker marker ∧
      (∀ x : V, ReachableWithin B.mem D n x →
        ¬ B.mem marker x) ∧
      ¬ ReachableWithin B.mem D n marker := by
  obtain ⟨E, hE⟩ := finite_envelope_exists B H D (n + 1)
  obtain ⟨marker, _hmarker, hOutside, hIrrefl⟩ :=
    relative_russell_fresh_irreflexive B H E
  refine ⟨marker, hIrrefl, ?_, ?_⟩
  · intro x hx hmx
    have hReach : ReachableWithin B.mem D (n + 1) marker :=
      Or.inr ⟨x, hx, hmx⟩
    exact hOutside ((hE marker).mpr hReach)
  · intro hReach
    have hNext : ReachableWithin B.mem D (n + 1) marker :=
      Or.inl hReach
    exact hOutside ((hE marker).mpr hNext)

/-- Avoiding every member of a finite support, and itself, is now an
unconditional theorem.  In particular this replaces the irreflexivity
part of Foundation in the old fresh-tagging modules. -/
theorem irreflexive_marker_avoids_finite_support
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (D : V) (n : Nat) :
    ∃ marker : V,
      ¬ B.mem marker marker ∧
      (∀ x : V, ReachableWithin B.mem D n x →
        ¬ B.mem marker x) := by
  obtain ⟨marker, hIr, hFresh, _⟩ :=
    irreflexive_fresh_marker_at_depth B H D n
  exact ⟨marker, hIr, hFresh⟩

end NineAxiomBZ.NoFoundation
