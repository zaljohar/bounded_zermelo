import FoundationFreeUniformBoundedTruth
import FoundationFreeTypedRelationalImage

/-!
# Extracting a coordinate from a Foundation-free represented frame

This transports an assignment subset through its typed tagged-coordinate
graph, then through the actual raw-to-tag matching relation.  The proof
uses only the nine operations; it does not assume Replacement, Separation,
or a non-founded analogue of Foundation.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Existential image of a subset S of represented tuples under the raw
coordinate decoder.  The output is an object-language set. -/
theorem finite_frame_coordinate_image_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (N : Nat) (D : Fin N → V)
    (hDE : ∀ i x, B.mem x (D i) → B.mem x E)
    (F : FiniteAssignmentFrameNF B E N D)
    (i : Fin N) (S : V)
    (hST : ∀ t, B.mem t S → B.mem t F.sort) :
    HasMembers B.mem (fun x : V =>
      B.mem x (D i) ∧ ∃ t : V, B.mem t S ∧
        F.decodeRaw B H E N D t i = x) := by
  obtain ⟨M, hM⟩ := frame_matching_edges_exists_nf B H E N D F i
  have hMrev : TypedEdges B.mem (F.tagSort i) E
      (fun u x => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i)) M :=
    typed_edges_reverse_nf B.mem E (F.tagSort i)
      (fun x u => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i))
      M hM
  have hUE : DisjointSortNF B.mem (F.tagSort i) E := by
    intro u a hu ha heq
    exact F.rawDisjoint i a u ha hu heq.symm
  obtain ⟨Z, hZ⟩ := two_step_typed_image_exists_nf B H
    F.sort (F.tagSort i) E (F.projectionGraph i) M S
    (F.projectionRel i)
    (fun u x => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i))
    hST (F.tupleTagDisjoint i) hUE
    (F.projectionSpec i) hMrev
  refine ⟨Z, ?_⟩
  intro x
  constructor
  · intro hxZ
    obtain ⟨hxE, t, u, htS, huTag, hProj, hMatch⟩ := (hZ x).mp hxZ
    obtain ⟨hxD, hPair⟩ := hMatch
    have ht : B.mem t F.sort := hST t htS
    have hx : x = F.decodeRaw B H E N D t i :=
      frame_tagged_edge_decodes_nf B H E N D F
        t ht i x u hxD huTag hProj hPair
    exact ⟨hxD, t, htS, hx.symm⟩
  · rintro ⟨hxD, t, htS, hDec⟩
    have ht : B.mem t F.sort := hST t htS
    obtain ⟨_hdi, u, huTag, hProj, hPair⟩ :=
      F.decodeRaw_correct B H E N D t ht i
    have hPairX : IsUPair B.mem u x (F.marker i) := by
      simpa only [hDec] using hPair
    exact (hZ x).mpr
      ⟨hDE i x hxD, t, u, htS, huTag, hProj, hxD, hPairX⟩

end NineAxiomBZ.NoFoundation
