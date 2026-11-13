import FoundationFreeFreshTag
/-!
# Finite reachability envelopes, without Foundation
For any fixed natural number n, the first n membership-depth layers below
an arbitrary input set U form an actual set, using ONLY Union and Pairing.
If no set is universal, a marker can be selected outside that envelope.
No choice over an infinite family of model sets and no Replacement is needed:
Nat.rec operates externally for a single fixed n.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- The elements of U, or objects reached by following at most n further
membership edges downwards from an element of U. This definition permits
arbitrary membership cycles. -/
def ReachableWithin (m : V → V → Prop) (U : V) : Nat → V → Prop
  | 0, x => m x U
  | n + 1, x => ReachableWithin m U n x ∨
      ∃ y : V, ReachableWithin m U n y ∧ m x y

/-- A concrete set exists for each finite membership-depth envelope.
This is NOT an instance of Δ₀-Separation: it is built by iterated Union
and binary union directly from the nine axioms. -/
theorem finite_envelope_exists
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U : V) (n : Nat) :
    HasMembers B.mem (ReachableWithin B.mem U n) := by
  induction n with
  | zero =>
      exact ⟨U, fun _ => Iff.rfl⟩
  | succ n ih =>
      obtain ⟨D, hD⟩ := ih
      obtain ⟨UD, hUD⟩ := H.setUnion D
      obtain ⟨N, hN⟩ := binary_union_exists B.mem H D UD
      refine ⟨N, ?_⟩
      intro x
      rw [hN x]
      change (B.mem x D ∨ B.mem x UD) ↔ _
      rw [hUD x]
      change
        (B.mem x D ∨
          (∃ y : V, B.mem y D ∧ B.mem x y)) ↔
        (ReachableWithin B.mem U n x ∨
          ∃ y : V, ReachableWithin B.mem U n y ∧ B.mem x y)
      constructor
      · intro hx
        rcases hx with hx | ⟨y, hy, hxy⟩
        · exact Or.inl ((hD x).mp hx)
        · exact Or.inr ⟨y, (hD y).mp hy, hxy⟩
      · intro hx
        rcases hx with hx | ⟨y, hy, hxy⟩
        · exact Or.inl ((hD x).mpr hx)
        · exact Or.inr ⟨y, (hD y).mpr hy, hxy⟩


/-- If every set is proper, for every *finite* number of membership steps
there is a fresh marker outside all objects reachable within that depth.
This replaces the use of finite membership-cycle exclusion in tag proofs.
It still has the separate premise `NoUniversal`, which must ultimately
be derived from T₉ rather than introduced into the final theorem. -/
theorem fresh_marker_at_finite_depth
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hn : NoUniversal B) (U : V) (n : Nat) :
    ∃ marker : V, ∀ x : V,
      ReachableWithin B.mem U n x → ¬ B.mem marker x := by
  -- To avoid membership in each reachable object, choose the marker outside
  -- the (n+1)-depth envelope, not merely outside the n-depth envelope.
  obtain ⟨D, hD⟩ := finite_envelope_exists B H U (n + 1)
  obtain ⟨marker, hmarker⟩ := hn D
  refine ⟨marker, ?_⟩
  intro x hx hmx
  have hdeep : ReachableWithin B.mem U (n + 1) marker :=
    Or.inr ⟨x, hx, hmx⟩
  exact hmarker ((hD marker).2 hdeep)

end NineAxiomBZ.NoFoundation
