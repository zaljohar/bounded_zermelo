import UniformBoundedTruth
import FrameAtomicBridge
import FamilyMatchingEdges
import TypedRelationalImage
/-!
# Extraction of a decoded coordinate from a represented finite frame

No relation image, replacement or separation existence axiom is assumed.
The image uses the existing tagged matching graphs and composition lemmas.
Draft only: Lean elaboration has not been run.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Extract all raw coordinate-i values of a *given actual subset*
    S of an actual assignment frame. The output exists from the nine axioms,
    even though the decoding function is only specified metatheoretically. -/
theorem finite_frame_coordinate_image_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (N : Nat) (D : Fin N → V)
    (hDE : ∀ i x, B.mem x (D i) → B.mem x E)
    (F : FiniteAssignmentFrame B E N D)
    (i : Fin N) (S : V)
    (hST : ∀ t, B.mem t S → B.mem t F.sort) :
    HasMembers B.mem (fun x : V =>
      B.mem x (D i) ∧ ∃ t : V, B.mem t S ∧
        F.decodeRaw B H E N D t i = x) := by
  let FD := F.asTaggedDomains B E N D
  obtain ⟨M,hM⟩ := family_matching_edges_exists B H E N D hDE FD i
  have hMrev : TypedEdges B.mem (F.tagSort i) E
      (fun u x => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i)) M := by
    have hr := typedEdges_reverse B.mem E (F.tagSort i)
      (fun x u => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i))
      M hM
    exact hr
  obtain ⟨Z,hZ⟩ := two_step_typed_image_exists B H
      F.sort (F.tagSort i) E (F.projectionGraph i) M S
      (F.projectionRel i)
      (fun u x => B.mem x (D i) ∧ IsUPair B.mem u x (F.marker i))
      hST (F.tupleTagDisjoint i)
      (disjointSort_symm B.mem (F.rawDisjoint i))
      (F.projectionSpec i) hMrev
  refine ⟨Z, ?_⟩
  intro x
  constructor
  · intro hxZ
    obtain ⟨hxE,t,u,htS,huTag,hProj,hMatch⟩ := (hZ x).mp hxZ
    obtain ⟨hxD,hPair⟩ := hMatch
    have ht : B.mem t F.sort := hST t htS
    have hx : x = F.decodeRaw B H E N D t i :=
      frame_tagged_edge_decodes B H E N D F
        t ht i x u hxD huTag hProj hPair
    exact ⟨hxD,t,htS,hx.symm⟩
  · rintro ⟨hxD,t,htS,hDec⟩
    have ht : B.mem t F.sort := hST t htS
    obtain ⟨_hdi,u,huTag,hProj,hPair⟩ :=
      F.decodeRaw_correct B H E N D t ht i
    have hPairX : IsUPair B.mem u x (F.marker i) := by
      simpa only [hDec] using hPair
    exact (hZ x).mpr
      ⟨hDE i x hxD,t,u,htS,huTag,hProj,hxD,hPairX⟩

end NineAxiomBZ
