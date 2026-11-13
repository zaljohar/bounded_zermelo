import FoundationFreeAtomicTruthFromRelations
import FoundationFreeTaggedRawMembership

/-!
# Atomic truth sets on Foundation-free assignment frames

There is no appeal to Foundation or to an assumed Separation instance.
Distinct-coordinate membership and equality are translated into typed
relations between disjoint tagged sorts. Diagonal equality is trivial;
diagonal membership must be evaluated rather than assumed false.

This module is an uncompiled proof draft.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Build the truth set of equality between two distinct coordinates. -/
theorem frame_distinct_equality_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      ∃ u v : V,
        B.mem u (F.tagSort i) ∧ B.mem v (F.tagSort j) ∧
        F.projectionRel i t u ∧ F.projectionRel j t v ∧
        ∃ a : V, B.mem a E ∧
          (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
          (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) := by
  obtain ⟨G, hG⟩ := frame_equality_edges_exists_nf B H E n D F i j hij
  obtain ⟨S, hS⟩ := atomic_truth_from_typed_edges_nf B H
    F.sort (F.tagSort i) (F.tagSort j)
    (F.projectionGraph i) (F.projectionGraph j) G
    (F.projectionRel i) (F.projectionRel j)
    (fun u v => ∃ a : V, B.mem a E ∧
      (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
      (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j)))
    (F.tupleTagDisjoint i) (F.tupleTagDisjoint j)
    (F.tagPairwiseDisjoint i j hij)
    (F.projectionSpec i) (F.projectionSpec j) hG
  refine ⟨S, ?_⟩
  intro t
  rw [hS t]
  constructor
  · rintro ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩
    exact ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
  · rintro ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
    exact ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩

/-- Build the truth set of membership between two distinct coordinates. -/
theorem frame_distinct_membership_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      ∃ u v : V,
        B.mem u (F.tagSort i) ∧ B.mem v (F.tagSort j) ∧
        F.projectionRel i t u ∧ F.projectionRel j t v ∧
        ∃ b : V, B.mem b E ∧
          (∃ a : V, B.mem a (D i) ∧
            IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
          (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) := by
  obtain ⟨G, hG⟩ := frame_membership_edges_exists_nf B H E n D F i j hij
  obtain ⟨S, hS⟩ := atomic_truth_from_typed_edges_nf B H
    F.sort (F.tagSort i) (F.tagSort j)
    (F.projectionGraph i) (F.projectionGraph j) G
    (F.projectionRel i) (F.projectionRel j)
    (fun u v => ∃ b : V, B.mem b E ∧
      (∃ a : V, B.mem a (D i) ∧
        IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
      (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j)))
    (F.tupleTagDisjoint i) (F.tupleTagDisjoint j)
    (F.tagPairwiseDisjoint i j hij)
    (F.projectionSpec i) (F.projectionSpec j) hG
  refine ⟨S, ?_⟩
  intro t
  rw [hS t]
  constructor
  · rintro ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩
    exact ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
  · rintro ⟨ht, u, v, hu, hv, hcu, hcv, hrel⟩
    exact ⟨ht, u, v, hu, hv, hcu, hrel, hcv⟩

/-- Decode the raw value of a represented tagged-coordinate edge. -/
theorem frame_tagged_edge_decodes_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (t : V) (ht : B.mem t F.sort) (i : Fin n)
    (a u : V)
    (haD : B.mem a (D i))
    (hu : B.mem u (F.tagSort i))
    (hpu : F.projectionRel i t u)
    (hup : IsUPair B.mem u a (F.marker i)) :
    a = F.decodeRaw B H E n D t i := by
  have hUnique := finite_frame_raw_coordinate_unique_nf B E n D F t ht i
  have ha : B.mem a (D i) ∧
      ∃ v : V, B.mem v (F.tagSort i) ∧
        F.projectionRel i t v ∧ IsUPair B.mem v a (F.marker i) :=
    ⟨haD, u, hu, hpu, hup⟩
  have haChoose : a = Classical.choose hUnique :=
    (Classical.choose_spec hUnique).2 a ha
  have hDecode : F.decodeRaw B H E n D t i =
      Classical.choose hUnique := by
    unfold FiniteAssignmentFrameNF.decodeRaw
    rw [dif_pos ht]
  exact haChoose.trans hDecode.symm

/-- All equality atom truth sets, including the diagonal case. -/
theorem frame_all_equality_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) :
    HasMembers B.mem (fun t : V => B.mem t F.sort ∧
      F.decodeRaw B H E n D t i = F.decodeRaw B H E n D t j) := by
  by_cases hij : i = j
  · subst j
    refine ⟨F.sort, ?_⟩
    intro t
    simp
  · obtain ⟨S, hS⟩ :=
      frame_distinct_equality_truth_exists_nf B H E n D F i j hij
    refine ⟨S, ?_⟩
    intro t
    constructor
    · intro htS
      obtain ⟨ht,u,v,hu,hv,hpi,hpj,a,haE,
        ⟨haDi,huPair⟩,⟨haDj,hvPair⟩⟩ := (hS t).mp htS
      have hai := frame_tagged_edge_decodes_nf B H E n D F
        t ht i a u haDi hu hpi huPair
      have haj := frame_tagged_edge_decodes_nf B H E n D F
        t ht j a v haDj hv hpj hvPair
      exact ⟨ht, hai.symm.trans haj⟩
    · rintro ⟨ht,hEq⟩
      obtain ⟨hDi,u,hu,hpi,huPair⟩ :=
        F.decodeRaw_correct B H E n D t ht i
      obtain ⟨hDj,v,hv,hpj,hvPair⟩ :=
        F.decodeRaw_correct B H E n D t ht j
      let a := F.decodeRaw B H E n D t i
      have haE : B.mem a E := F.rawBound i a hDi
      have haDj : B.mem a (D j) := by
        simpa [a, hEq] using hDj
      have hvPairA : IsUPair B.mem v a (F.marker j) := by
        simpa [a, hEq] using hvPair
      exact (hS t).mpr
        ⟨ht,u,v,hu,hv,hpi,hpj,a,haE,
          ⟨hDi,huPair⟩,⟨haDj,hvPairA⟩⟩


/-- The diagonal membership atom can be TRUE in a non-well-founded model.
Its truth set is constructed through the actual bounded self-membership
selector, rather than through Foundation's `x ∉ x` assertion. -/
theorem frame_diagonal_membership_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i : Fin n) :
    HasMembers B.mem (fun t : V => B.mem t F.sort ∧
      B.mem (F.decodeRaw B H E n D t i)
        (F.decodeRaw B H E n D t i)) := by
  let m := B.mem
  obtain ⟨Self, hSelf⟩ := diagonal_membership_from_singleton_image
    m H (D i) (singleton_images_from_nine_no_foundation B H (D i))
  have hOutside : ¬ m (F.marker i) Self := by
    intro hMark
    have hInDomain : m (F.marker i) (D i) := ((hSelf _).mp hMark).1
    exact F.markerOutsideDomain i hInDomain
  obtain ⟨TaggedSelf, hTaggedSelf⟩ :=
    corrected_fan_no_foundation B H Self (F.marker i) hOutside
  have hSubset : ∀ f : V, m f TaggedSelf → m f (F.tagSort i) := by
    intro f hf
    obtain ⟨x, hxSelf, hPair⟩ := (hTaggedSelf f).mp hf
    have hxD : m x (D i) := ((hSelf x).mp hxSelf).1
    exact (F.tagSpec i f).mpr ⟨x, hxD, hPair⟩
  obtain ⟨Q,hQ⟩ := unordered_product_without_foundation B H
    F.sort TaggedSelf
  obtain ⟨I,hI⟩ := H.intersection (F.projectionGraph i) Q
  obtain ⟨U,hU⟩ := H.setUnion I
  obtain ⟨O,hO⟩ := H.intersection F.sort U
  refine ⟨O, ?_⟩
  intro t
  constructor
  · intro htO
    obtain ⟨htT, htU⟩ := (hO t).mp htO
    obtain ⟨p, hpI, htp⟩ := (hU t).mp htU
    obtain ⟨hpProj, hpQ⟩ := (hI p).mp hpI
    obtain ⟨t0, u0, ht0T, hu0Tag, hpt0u0, hProj⟩ :=
      (F.projectionSpec i p).mp hpProj
    obtain ⟨s,f,hsT,hfSelf,hpsf⟩ := (hQ p).mp hpQ
    have hfTag : m f (F.tagSort i) := hSubset f hfSelf
    have htu : t0 = s ∧ u0 = f := by
      rcases unordered_pair_endpoints_nf B hpt0u0 hpsf with h | h
      · exact h
      · obtain ⟨ht0f, hu0s⟩ := h
        exact False.elim (F.tupleTagDisjoint i t0 f ht0T hfTag ht0f)
    have ht0 : t = t0 := by
      rcases (hpt0u0 t).mp htp with h | h
      · exact h
      · exact False.elim (F.tupleTagDisjoint i t u0 htT hu0Tag h)
    obtain ⟨x,hxSelf,hxf⟩ := (hTaggedSelf f).mp hfSelf
    have hxD : m x (D i) := ((hSelf x).mp hxSelf).1
    have hxMem : m x x := ((hSelf x).mp hxSelf).2
    have hDecode : x = F.decodeRaw B H E n D t i := by
      apply frame_tagged_edge_decodes_nf B H E n D F
        t htT i x u0 hxD hu0Tag
      · simpa [ht0] using hProj
      · simpa [htu.2] using hxf
    refine ⟨htT, ?_⟩
    simpa [← hDecode] using hxMem
  · rintro ⟨htT, hSelfMem⟩
    let x := F.decodeRaw B H E n D t i
    obtain ⟨hxD, u, huTag, hProj, huPair⟩ :=
      F.decodeRaw_correct B H E n D t htT i
    have hxSelf : m x Self := (hSelf x).mpr ⟨hxD, hSelfMem⟩
    have huSelf : m u TaggedSelf :=
      (hTaggedSelf u).mpr ⟨x, hxSelf, huPair⟩
    obtain ⟨p, hpair⟩ := unordered_pair_exists m H t u
    have hpProj : m p (F.projectionGraph i) :=
      (F.projectionSpec i p).mpr
        ⟨t, u, htT, huTag, hpair, hProj⟩
    have hpQ : m p Q := (hQ p).mpr ⟨t, u, htT, huSelf, hpair⟩
    have hpI : m p I := (hI p).mpr ⟨hpProj, hpQ⟩
    have htU : m t U := (hU t).mpr
      ⟨p, hpI, (hpair t).mpr (Or.inl rfl)⟩
    exact (hO t).mpr ⟨htT, htU⟩

/-- All membership atoms, including both diagonal and distinct-coordinate
cases, admit truth sets WITHOUT Foundation. -/
theorem frame_all_membership_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (i j : Fin n) :
    HasMembers B.mem (fun t : V => B.mem t F.sort ∧
      B.mem (F.decodeRaw B H E n D t i)
        (F.decodeRaw B H E n D t j)) := by
  by_cases hij : i = j
  · subst j
    exact frame_diagonal_membership_truth_exists_nf B H E n D F i
  · obtain ⟨S, hS⟩ :=
      frame_distinct_membership_truth_exists_nf B H E n D F i j hij
    refine ⟨S, ?_⟩
    intro t
    constructor
    · intro htS
      obtain ⟨ht,u,v,hu,hv,hpi,hpj,b,hbE,
        ⟨a,haDi,huPair,hab⟩,⟨hbDj,hvPair⟩⟩ := (hS t).mp htS
      have hai := frame_tagged_edge_decodes_nf B H E n D F
        t ht i a u haDi hu hpi huPair
      have hbj := frame_tagged_edge_decodes_nf B H E n D F
        t ht j b v hbDj hv hpj hvPair
      have hRaw : B.mem (F.decodeRaw B H E n D t i)
          (F.decodeRaw B H E n D t j) := by
        rw [← hai, ← hbj]
        exact hab
      exact ⟨ht, hRaw⟩
    · rintro ⟨ht, hMem⟩
      obtain ⟨hDi,u,hu,hpi,huPair⟩ :=
        F.decodeRaw_correct B H E n D t ht i
      obtain ⟨hDj,v,hv,hpj,hvPair⟩ :=
        F.decodeRaw_correct B H E n D t ht j
      let a := F.decodeRaw B H E n D t i
      let b := F.decodeRaw B H E n D t j
      have hbE : B.mem b E := F.rawBound j b hDj
      exact (hS t).mpr
        ⟨ht,u,v,hu,hv,hpi,hpj,b,hbE,
          ⟨a,hDi,huPair,hMem⟩,⟨hDj,hvPair⟩⟩

end NineAxiomBZ.NoFoundation
