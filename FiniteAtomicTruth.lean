import FamilyAtomicEdges
import AtomicTruthFromRelations
/-!
# Atomic truth sets on a finite represented assignment sort

From an assignment sort T with represented projections to the coordinate
sorts and from the newly constructed equality/membership edge sets,
we construct the exact set of assignments satisfying each binary atomic
predicate on *distinct* coordinates.

The diagonal cases still need to be integrated into the full compiler.
No Separation instance is used. NOT ELABORATED.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- This does NOT assume that the sets of satisfying assignments exist:
only the tuple projections, as actual sets, are given. -/
structure FiniteCoordinateProjections (B : Background V)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteTaggedDomains B E n D) (T : V) where
  P : Fin n → V
  coord : Fin n → V → V → Prop
  disjoint : ∀ i : Fin n, DisjointSort B.mem T (F.U i)
  edges : ∀ i : Fin n,
    TypedEdges B.mem T (F.U i) (coord i) (P i)

/-- The atomic equality truth set for two distinct coordinates. -/
theorem finite_assignment_equality_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (hDE : ∀ (i : Fin n) (x : V),
      B.mem x (D i) → B.mem x E)
    (F : FiniteTaggedDomains B E n D)
    (T : V) (CP : FiniteCoordinateProjections B E n D F T)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t T ∧
      ∃ u v : V,
        B.mem u (F.U i) ∧ B.mem v (F.U j) ∧
        CP.coord i t u ∧ CP.coord j t v ∧
        ∃ a : V, B.mem a E ∧
          (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
          (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) := by
  obtain ⟨G, hG⟩ :=
    family_equality_edges_exists B H E n D hDE F i j hij
  have hTyped : TypedEdges B.mem (F.U i) (F.U j)
      (fun u v => ∃ a : V, B.mem a E ∧
        (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
        (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) G := hG
  obtain ⟨S, hS⟩ := atomic_truth_from_typed_edges B H
    T (F.U i) (F.U j) (CP.P i) (CP.P j) G
    (CP.coord i) (CP.coord j)
    (fun u v => ∃ a : V, B.mem a E ∧
      (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
      (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j)))
    (CP.disjoint i) (CP.disjoint j) (F.pairwise i j hij)
    (CP.edges i) (CP.edges j) hTyped
  refine ⟨S, ?_⟩
  intro t
  rw [hS t]
  constructor
  · rintro ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩
    exact ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
  · rintro ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
    exact ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩

/-- The directed membership truth set for two distinct coordinates. -/
theorem finite_assignment_membership_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (hDE : ∀ (i : Fin n) (x : V),
      B.mem x (D i) → B.mem x E)
    (F : FiniteTaggedDomains B E n D)
    (T : V) (CP : FiniteCoordinateProjections B E n D F T)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t T ∧
      ∃ u v : V,
        B.mem u (F.U i) ∧ B.mem v (F.U j) ∧
        CP.coord i t u ∧ CP.coord j t v ∧
        ∃ b : V, B.mem b E ∧
          (∃ a : V, B.mem a (D i) ∧
            IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
          (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) := by
  obtain ⟨G, hG⟩ :=
    family_membership_edges_exists B H E n D hDE F i j hij
  have hTyped : TypedEdges B.mem (F.U i) (F.U j)
      (fun u v => ∃ b : V, B.mem b E ∧
        (∃ a : V, B.mem a (D i) ∧
          IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
        (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) G := hG
  obtain ⟨S, hS⟩ := atomic_truth_from_typed_edges B H
    T (F.U i) (F.U j) (CP.P i) (CP.P j) G
    (CP.coord i) (CP.coord j)
    (fun u v => ∃ b : V, B.mem b E ∧
      (∃ a : V, B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
      (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j)))
    (CP.disjoint i) (CP.disjoint j) (F.pairwise i j hij)
    (CP.edges i) (CP.edges j) hTyped
  refine ⟨S, ?_⟩
  intro t
  rw [hS t]
  constructor
  · rintro ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩
    exact ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
  · rintro ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
    exact ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩

end NineAxiomBZ
