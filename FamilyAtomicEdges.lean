import FamilyMatchingEdges
import TaggedRawMembership
import TypedComposition
/-!
# Equality and directional membership edges on finite tagged domains

For DISTINCT coordinate indices i and j this file produces represented
cross-sort atomic relations. The same-coordinate cases are handled
separately: equality is automatic, while self-membership is excluded
by first-order Foundation.

These constructions are independent of a truth-set compiler or of
any Separation schema. NOT ELABORATED: no Lean executable is installed.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The graph of equality between two different tagged coordinate sorts.
The witness `a` is in both original raw domains. -/
theorem family_equality_edges_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (hDE : ∀ (i : Fin n) (x : V),
      B.mem x (D i) → B.mem x E)
    (F : FiniteTaggedDomains B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun p : V =>
      ∃ u v : V,
        B.mem u (F.U i) ∧ B.mem v (F.U j) ∧
        IsUPair B.mem p u v ∧
        ∃ a : V, B.mem a E ∧
          (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
          (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) := by
  obtain ⟨Gi, hGi⟩ := family_matching_edges_exists B H E n D hDE F i
  obtain ⟨Gj, hGj⟩ := family_matching_edges_exists B H E n D hDE F j
  have hGiReverse :
      TypedEdges B.mem (F.U i) E
        (fun u a => B.mem a (D i) ∧
          IsUPair B.mem u a (F.marker i)) Gi :=
    typedEdges_reverse B.mem E (F.U i)
      (fun a u => B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i)) Gi hGi
  obtain ⟨C, hC⟩ := typed_composition_exists B H
    (F.U i) E (F.U j) Gi Gj
    (fun u a => B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i))
    (fun a v => B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))
    (disjointSort_symm B.mem (F.rawDisjoint i))
    (F.pairwise i j hij) (F.rawDisjoint j)
    hGiReverse hGj
  exact ⟨C, hC⟩

/-- Construct a directed raw membership relation from Ui to E.
The symmetric membership filter becomes directed because the marker
has no members in common with a raw target b∈E. -/
theorem family_member_to_raw_edges_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteTaggedDomains B E n D) (i : Fin n) :
    ∃ G : V, TypedEdges B.mem (F.U i) E
      (fun u b => ∃ a : V,
        B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i) ∧ B.mem a b) G := by
  obtain ⟨G, hG⟩ := tagged_raw_membership_edges_exists
    B H (D i) (F.U i) E (F.marker i)
    (F.spec i) (F.markerFresh i)
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨u, b, a, hu, hb, ha, hua, hab, hp'⟩ := (hG p).mp hp
    exact ⟨u, b, hu, hb, hp', a, ha, hua, hab⟩
  · rintro ⟨u, b, hu, hb, hp', a, ha, hua, hab⟩
    exact (hG p).mpr ⟨u, b, a, hu, hb, ha, hua, hab, hp'⟩

/-- Directed (nonstratified) membership between distinct tagged domains.
This is the bounded atomic analogue of Gödel's ordered membership filter,
constructed without assuming it as a primitive. -/
theorem family_membership_edges_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (hDE : ∀ (i : Fin n) (x : V),
      B.mem x (D i) → B.mem x E)
    (F : FiniteTaggedDomains B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun p : V =>
      ∃ u v : V,
        B.mem u (F.U i) ∧ B.mem v (F.U j) ∧
        IsUPair B.mem p u v ∧
        ∃ b : V, B.mem b E ∧
          (∃ a : V, B.mem a (D i) ∧
            IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
          (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) := by
  obtain ⟨Gi, hGi⟩ := family_member_to_raw_edges_exists B H E n D F i
  obtain ⟨Gj, hGj⟩ := family_matching_edges_exists B H E n D hDE F j
  obtain ⟨C, hC⟩ := typed_composition_exists B H
    (F.U i) E (F.U j) Gi Gj
    (fun u b => ∃ a : V,
      B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i) ∧ B.mem a b)
    (fun b v => B.mem b (D j) ∧
      IsUPair B.mem v b (F.marker j))
    (disjointSort_symm B.mem (F.rawDisjoint i))
    (F.pairwise i j hij) (F.rawDisjoint j)
    hGi hGj
  exact ⟨C, hC⟩

end NineAxiomBZ
