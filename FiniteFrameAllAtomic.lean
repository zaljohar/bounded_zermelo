import FrameAtomicBridge
import FiniteFrameDecoding
import TagUniqueness
/-!
# All atomic truth sets on finite assignment frames

This module fills the diagonal gap in `FrameAtomicBridge.lean` and packages
its two distinct-coordinate constructions as the exact equality and
membership truth-set interfaces required by `BoundedTruthInduction.lean`.

Everything asserted here is a theorem from the given nine axioms and the
residual BZ background, not a new existential axiom.  The existing source
and this addition have NOT been elaborated by Lean in this environment.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- If a represented coordinate edge points to a tag encoding `a`, then
`a` is the uniquely decoded raw coordinate. -/
theorem frame_tagged_edge_decodes
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (t : V) (ht : B.mem t F.sort) (i : Fin n)
    (a u : V)
    (haD : B.mem a (D i))
    (hu : B.mem u (F.tagSort i))
    (hpu : F.projectionRel i t u)
    (hup : IsUPair B.mem u a (F.marker i)) :
    a = F.decodeRaw B H E n D t i := by
  have hUnique := finite_frame_raw_coordinate_unique B E n D F t ht i
  have ha : B.mem a (D i) ∧
      ∃ v : V, B.mem v (F.tagSort i) ∧
        F.projectionRel i t v ∧
        IsUPair B.mem v a (F.marker i) :=
    ⟨haD, u, hu, hpu, hup⟩
  have haChoose : a = Classical.choose hUnique :=
    (Classical.choose_spec hUnique).2 a ha
  have hDecode : F.decodeRaw B H E n D t i =
      Classical.choose hUnique := by
    unfold FiniteAssignmentFrame.decodeRaw
    rw [dif_pos ht]
  exact haChoose.trans hDecode.symm

/-- All equality atom truth sets, INCLUDING the diagonal `i = j`. -/
theorem finite_frame_all_equality_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (i j : Fin n) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      F.decodeRaw B H E n D t i = F.decodeRaw B H E n D t j) := by
  by_cases hij : i = j
  · subst j
    refine ⟨F.sort, ?_⟩
    intro t
    simp
  · obtain ⟨S, hS⟩ :=
      finite_frame_equality_truth_exists B H E n D F i j hij
    refine ⟨S, ?_⟩
    intro t
    constructor
    · intro htS
      obtain ⟨ht, u, v, hu, hv, hpi, hpj, a, haE,
        ⟨haDi, huPair⟩, ⟨haDj, hvPair⟩⟩ := (hS t).mp htS
      have hai := frame_tagged_edge_decodes B H E n D F
        t ht i a u haDi hu hpi huPair
      have haj := frame_tagged_edge_decodes B H E n D F
        t ht j a v haDj hv hpj hvPair
      exact ⟨ht, hai.symm.trans haj⟩
    · rintro ⟨ht, hEq⟩
      obtain ⟨hDi, u, hu, hpi, huPair⟩ :=
        F.decodeRaw_correct B H E n D t ht i
      obtain ⟨hDj, v, hv, hpj, hvPair⟩ :=
        F.decodeRaw_correct B H E n D t ht j
      let a := F.decodeRaw B H E n D t i
      have haE : B.mem a E := F.rawBound i a hDi
      have haDj : B.mem a (D j) := by
        simpa [a, hEq] using hDj
      have hvPairA : IsUPair B.mem v a (F.marker j) := by
        simpa [a, hEq] using hvPair
      exact (hS t).mpr
        ⟨ht, u, v, hu, hv, hpi, hpj, a, haE,
          ⟨hDi, huPair⟩, ⟨haDj, hvPairA⟩⟩

/-- All membership atom truth sets, INCLUDING `i = j`, where
Foundation rules out self-membership. -/
theorem finite_frame_all_membership_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (i j : Fin n) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      B.mem (F.decodeRaw B H E n D t i)
        (F.decodeRaw B H E n D t j)) := by
  by_cases hij : i = j
  · subst j
    obtain ⟨Z, hZ⟩ := H.empty
    refine ⟨Z, ?_⟩
    intro t
    constructor
    · intro htZ
      exact False.elim ((hZ t).mp htZ)
    · rintro ⟨_, hxx⟩
      exact False.elim (no_self_membership_for_tags B H
        (F.decodeRaw B H E n D t i) hxx)
  · obtain ⟨S, hS⟩ :=
      finite_frame_membership_truth_exists B H E n D F i j hij
    refine ⟨S, ?_⟩
    intro t
    constructor
    · intro htS
      obtain ⟨ht, u, v, hu, hv, hpi, hpj, b, hbE,
        ⟨a, haDi, huPair, hab⟩, ⟨hbDj, hvPair⟩⟩ := (hS t).mp htS
      have hai := frame_tagged_edge_decodes B H E n D F
        t ht i a u haDi hu hpi huPair
      have hbj := frame_tagged_edge_decodes B H E n D F
        t ht j b v hbDj hv hpj hvPair
      have hRaw : B.mem (F.decodeRaw B H E n D t i)
          (F.decodeRaw B H E n D t j) := by
        rw [← hai, ← hbj]
        exact hab
      exact ⟨ht, hRaw⟩
    · rintro ⟨ht, hMem⟩
      obtain ⟨hDi, u, hu, hpi, huPair⟩ :=
        F.decodeRaw_correct B H E n D t ht i
      obtain ⟨hDj, v, hv, hpj, hvPair⟩ :=
        F.decodeRaw_correct B H E n D t ht j
      let a := F.decodeRaw B H E n D t i
      let b := F.decodeRaw B H E n D t j
      have hbE : B.mem b E := F.rawBound j b hDj
      exact (hS t).mpr
        ⟨ht, u, v, hu, hv, hpi, hpj, b, hbE,
          ⟨a, hDi, huPair, hMem⟩, ⟨hDj, hvPair⟩⟩

end NineAxiomBZ
