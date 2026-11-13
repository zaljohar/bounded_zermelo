import FoundationFreeFrameDecoding
import FoundationFreeTaggedMatching

/-!
# Raw-to-tag matching graphs for Foundation-free assignment frames

The original kernel-checked code invoked a graph lemma using marker = {support},
and hence implicitly used Foundation.  Here the marker is an arbitrary safe
fresh object with explicit `markerOutsideDomain` and `markerDeep` witnesses.
These are stored in `FiniteAssignmentFrameNF` and proved by its constructor.

No Foundation axiom or Separation instance is used in the statements.
Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Reverse an already represented undirected typed edge relation. -/
theorem typed_edges_reverse_nf
    (m : V → V → Prop) (U W : V) (R : V → V → Prop)
    (G : V) (hG : TypedEdges m U W R G) :
    TypedEdges m W U (fun w u => R u w) G := by
  intro p
  constructor
  · intro hp
    obtain ⟨u, w, hu, hw, hp, hr⟩ := (hG p).mp hp
    refine ⟨w, u, hw, hu, ?_, hr⟩
    intro z
    rw [hp z]
    tauto
  · rintro ⟨w, u, hw, hu, hp, hr⟩
    apply (hG p).mpr
    refine ⟨u, w, hu, hw, ?_, hr⟩
    intro z
    rw [hp z]
    tauto

/-- Each raw domain is related to its actual tagged copy by an object-level
set of unordered matching edges.  The proof does not require that the marker
be a singleton or that membership be well-founded. -/
theorem frame_matching_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D) (i : Fin n) :
    ∃ G : V, TypedEdges B.mem E (F.tagSort i)
      (fun x u => B.mem x (D i) ∧
        IsUPair B.mem u x (F.marker i)) G := by
  let m := B.mem
  obtain ⟨G, hG⟩ := tagged_matching_from_deep_marker
    B H (D i) (F.marker i)
    (F.markerOutsideDomain i)
    (F.markerDeep i)
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨x, f, hxD, hxf, hp⟩ := (hG p).mp hp
    have hxE : m x E := F.rawBound i x hxD
    have hfU : m f (F.tagSort i) :=
      (F.tagSpec i f).mpr ⟨x, hxD, hxf⟩
    exact ⟨x, f, hxE, hfU, hp, hxD, hxf⟩
  · rintro ⟨x, f, hxE, hfU, hp, hxD, hxf⟩
    exact (hG p).mpr ⟨x, f, hxD, hxf, hp⟩

/-- Equality of two DISTINCT coordinate values is represented by an actual
unordered cross-sort relation, via the common raw domain E. -/
theorem frame_equality_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun p : V =>
      ∃ u v : V,
        B.mem u (F.tagSort i) ∧ B.mem v (F.tagSort j) ∧
        IsUPair B.mem p u v ∧
        ∃ a : V, B.mem a E ∧
          (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
          (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) := by
  obtain ⟨Gi, hGi⟩ := frame_matching_edges_exists_nf B H E n D F i
  obtain ⟨Gj, hGj⟩ := frame_matching_edges_exists_nf B H E n D F j
  have hiReverse : TypedEdges B.mem (F.tagSort i) E
      (fun u a => B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i)) Gi :=
    typed_edges_reverse_nf B.mem E (F.tagSort i)
      (fun a u => B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i)) Gi hGi
  have hiE : DisjointSortNF B.mem (F.tagSort i) E := by
    intro u a hu ha heq
    exact F.rawDisjoint i a u ha hu heq.symm
  exact typed_composition_exists_nf B H (F.tagSort i) E
    (F.tagSort j) Gi Gj
    (fun u a => B.mem a (D i) ∧
      IsUPair B.mem u a (F.marker i))
    (fun a v => B.mem a (D j) ∧
      IsUPair B.mem v a (F.marker j))
    hiE (F.tagPairwiseDisjoint i j hij) (F.rawDisjoint j)
    hiReverse hGj

end NineAxiomBZ.NoFoundation
