import FiniteFrameAllAtomic
import FiniteFrameDecoding
import TypedCompositionFiltered
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
/-!
# Finite-frame agreement and cylindrification

This file advances the missing bounded-quantifier step. It is written entirely
using the `Background` and `NineAxioms` definitions; the old finite-frame
existence and coordinate decoding theorems are imported as PROOFS, not axioms.

IMPORTANT: This is an unelaborated Lean draft. The runtime does not contain
Lean/Mathlib, so no kernel-verification claim is made.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Unordered graph over one object-level sort. -/
def UndirectedGraph (B : Background V) (T : V)
    (R : V → V → Prop) (p : V) : Prop :=
  ∃ s t : V, B.mem s T ∧ B.mem t T ∧
    IsUPair B.mem p s t ∧ R s t

/-- Intersections of undirected graphs compute conjunction when the
    underlying relations are symmetric. -/
theorem undirected_graph_intersection_exists
    (B : Background V) (H : NineAxioms B.mem) (T : V)
    (R S : V → V → Prop)
    (hSsym : ∀ s t, S s t → S t s)
    (hR : HasMembers B.mem (UndirectedGraph B T R))
    (hS : HasMembers B.mem (UndirectedGraph B T S)) :
    HasMembers B.mem (UndirectedGraph B T (fun s t => R s t ∧ S s t)) := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  obtain ⟨c, hc⟩ := H.intersection a b
  refine ⟨c, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨hpa, hpb⟩ := (hc p).mp hp
    obtain ⟨s,t,hs,ht,hpst,hRst⟩ := (ha p).mp hpa
    obtain ⟨u,v,hu,hv,hpuv,hSuv⟩ := (hb p).mp hpb
    have hSt : S s t := by
      rcases unordered_pair_endpoints B hpst hpuv with h | h
      · rcases h with ⟨h1,h2⟩
        simpa only [h1,h2] using hSuv
      · rcases h with ⟨h1,h2⟩
        have hRev := hSsym u v hSuv
        simpa only [h1,h2] using hRev
    exact ⟨s,t,hs,ht,hpst,hRst,hSt⟩
  · rintro ⟨s,t,hs,ht,hpst,hRst,hSst⟩
    exact (hc p).mpr
      ⟨(ha p).mpr ⟨s,t,hs,ht,hpst,hRst⟩,
       (hb p).mpr ⟨s,t,hs,ht,hpst,hSst⟩⟩

/-- The *same* tagged coordinate can be recovered from two represented
    tuples exactly when their decoded coordinate values agree. -/
theorem frame_common_tag_iff_equal
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (i : Fin n) (s t : V)
    (hs : B.mem s F.sort) (ht : B.mem t F.sort) :
    (∃ q : V, B.mem q (F.tagSort i) ∧
        F.projectionRel i s q ∧ F.projectionRel i t q) ↔
      F.decodeRaw B H E n D s i = F.decodeRaw B H E n D t i := by
  obtain ⟨hDs, us, hus, hPus, hPairS⟩ :=
    F.decodeRaw_correct B H E n D s hs i
  obtain ⟨hDt, ut, hut, hPut, hPairT⟩ :=
    F.decodeRaw_correct B H E n D t ht i
  constructor
  · rintro ⟨q,hq,hPsq,hPtq⟩
    obtain ⟨ws, hws, huniqS⟩ := F.coordinateUnique s hs i
    obtain ⟨wt, hwt, huniqT⟩ := F.coordinateUnique t ht i
    have hsu : us = q :=
      (huniqS us ⟨hus,hPus⟩).trans (huniqS q ⟨hq,hPsq⟩).symm
    have htu : ut = q :=
      (huniqT ut ⟨hut,hPut⟩).trans (huniqT q ⟨hq,hPtq⟩).symm
    have hsPair : IsUPair B.mem q
        (F.decodeRaw B H E n D s i) (F.marker i) := by
      simpa only [hsu] using hPairS
    have htPair : IsUPair B.mem q
        (F.decodeRaw B H E n D t i) (F.marker i) := by
      simpa only [htu] using hPairT
    exact tagged_pair_payload_unique B q _ _ (F.marker i) hsPair htPair
  · intro heq
    have hutEq : us = ut := by
      apply B.extensionality
      intro z
      rw [hPairS z, hPairT z]
      simpa only [heq]
    refine ⟨us,hus,hPus,?_⟩
    simpa only [← hutEq] using hPut

/-- Every single-coordinate agreement relation has an actual set of
    unordered edges. Uses only the existing coordinate projection graph
    and the user's unordered composition and product operations. -/
theorem frame_one_coordinate_agreement_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D) (i : Fin n) :
    HasMembers B.mem (UndirectedGraph B F.sort
      (fun s t => F.decodeRaw B H E n D s i =
                  F.decodeRaw B H E n D t i)) := by
  let U := F.tagSort i
  let T := F.sort
  let R : V → V → Prop := F.projectionRel i
  have hrev : TypedEdges B.mem U T (fun u t => R t u)
      (F.projectionGraph i) := by
    intro p
    constructor
    · intro hp
      obtain ⟨t,u,ht,hu,hptu,hR⟩ := (F.projectionSpec i p).mp hp
      refine ⟨u,t,hu,ht,?_,hR⟩
      intro z
      constructor
      · intro hz
        rcases (hptu z).mp hz with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hz
        rcases hz with h | h
        · exact (hptu z).mpr (Or.inr h)
        · exact (hptu z).mpr (Or.inl h)
    · rintro ⟨u,t,hu,ht,hput,hR⟩
      apply (F.projectionSpec i p).mpr
      refine ⟨t,u,ht,hu,?_,hR⟩
      intro z
      constructor
      · intro hz
        rcases (hput z).mp hz with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hz
        rcases hz with h | h
        · exact (hput z).mpr (Or.inr h)
        · exact (hput z).mpr (Or.inl h)
  obtain ⟨G,hG⟩ :=
    typed_composition_filtered_exists B H T U T
      (F.projectionGraph i) (F.projectionGraph i)
      R (fun u t => R t u)
      (F.tupleTagDisjoint i)
      (by
        intro u t hu ht hEq
        exact F.tupleTagDisjoint i t u ht hu hEq.symm)
      (F.projectionSpec i) hrev
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨s,t,hs,ht,hpst,q,hq,hRs,hRt⟩ := (hG p).mp hp
    refine ⟨s,t,hs,ht,hpst,?_⟩
    exact (frame_common_tag_iff_equal B H E n D F i s t hs ht).mp
      ⟨q,hq,hRs,hRt⟩
  · rintro ⟨s,t,hs,ht,hpst,heq⟩
    obtain ⟨q,hq,hRs,hRt⟩ :=
      (frame_common_tag_iff_equal B H E n D F i s t hs ht).mpr heq
    exact (hG p).mpr ⟨s,t,hs,ht,hpst,q,hq,hRs,hRt⟩

/-- Agreement on a finite list of decoded coordinates. -/
def AgreeOn (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (J : Finset (Fin n)) (s t : V) : Prop :=
  ∀ j : Fin n, j ∈ J →
    F.decodeRaw B H E n D s j = F.decodeRaw B H E n D t j

/-- Every finite intersection of the coordinate-equality edge graphs
    can be constructed with the nine axioms. -/
theorem frame_agreement_graph_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D) :
    ∀ J : Finset (Fin n),
      HasMembers B.mem
        (UndirectedGraph B F.sort (AgreeOn B H E n D F J)) := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty =>
      obtain ⟨P,hP⟩ := unordered_product_exists B H F.sort F.sort
      refine ⟨P, ?_⟩
      intro p
      constructor
      · intro hp
        obtain ⟨s,t,hs,ht,hpst⟩ := (hP p).mp hp
        exact ⟨s,t,hs,ht,hpst,by simp [AgreeOn]⟩
      · rintro ⟨s,t,hs,ht,hpst,_⟩
        exact (hP p).mpr ⟨s,t,hs,ht,hpst⟩
  | @insert j J hnot ih =>
      obtain ⟨G,hG⟩ := frame_one_coordinate_agreement_exists B H E n D F j
      have hSym : ∀ s t : V,
          F.decodeRaw B H E n D s j = F.decodeRaw B H E n D t j →
          F.decodeRaw B H E n D t j = F.decodeRaw B H E n D s j := by
        intro s t h
        exact h.symm
      obtain ⟨I,hI⟩ := undirected_graph_intersection_exists B H F.sort
          (AgreeOn B H E n D F J)
          (fun s t => F.decodeRaw B H E n D s j =
            F.decodeRaw B H E n D t j) hSym ih ⟨G,hG⟩
      refine ⟨I, ?_⟩
      intro p
      constructor
      · intro hp
        obtain ⟨s,t,hs,ht,hpst,hOld,hNew⟩ := (hI p).mp hp
        refine ⟨s,t,hs,ht,hpst,?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with hkj | hkJ
        · simpa only [hkj] using hNew
        · exact hOld k hkJ
      · rintro ⟨s,t,hs,ht,hpst,hAgree⟩
        apply (hI p).mpr
        refine ⟨s,t,hs,ht,hpst,?_,?_⟩
        · intro k hk
          exact hAgree k (Finset.mem_insert_of_mem hk)
        · exact hAgree j (Finset.mem_insert_self j J)

/-- Bounded coordinate elimination (cylindrification), without any
    separation hypothesis or an assumed relational image operator. -/
theorem frame_cylindrification_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (k : Fin n) (S : V)
    (hST : ∀ s, B.mem s S → B.mem s F.sort) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      ∃ s : V, B.mem s S ∧
        ∀ j : Fin n, j ≠ k →
          F.decodeRaw B H E n D s j = F.decodeRaw B H E n D t j) := by
  classical
  let J : Finset (Fin n) := Finset.univ.erase k
  obtain ⟨G,hG⟩ := frame_agreement_graph_exists B H E n D F J
  obtain ⟨Q,hQ⟩ := unordered_product_exists B H S F.sort
  obtain ⟨I,hI⟩ := H.intersection G Q
  obtain ⟨U,hU⟩ := H.setUnion I
  obtain ⟨O,hO⟩ := H.intersection F.sort U
  refine ⟨O, ?_⟩
  intro t
  have hJ (s t : V) :
      AgreeOn B H E n D F J s t ↔
      ∀ j : Fin n, j ≠ k →
        F.decodeRaw B H E n D s j = F.decodeRaw B H E n D t j := by
    constructor
    · intro h j hj
      exact h j (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)
    · intro h j hj
      exact h j (Finset.mem_erase.mp hj).1
  constructor
  · intro htO
    obtain ⟨htT,htU⟩ := (hO t).mp htO
    obtain ⟨p,hpI,htp⟩ := (hU t).mp htU
    obtain ⟨hpG,hpQ⟩ := (hI p).mp hpI
    obtain ⟨s,v,hsS,hvT,hpsv⟩ := (hQ p).mp hpQ
    obtain ⟨a,b,haT,hbT,hpab,hAgree⟩ := (hG p).mp hpG
    have hRel : AgreeOn B H E n D F J s v := by
      rcases unordered_pair_endpoints B hpab hpsv with hh | hh
      · rcases hh with ⟨h1,h2⟩
        simpa only [h1,h2] using hAgree
      · rcases hh with ⟨h1,h2⟩
        intro j hj
        have hab := hAgree j hj
        simpa only [h1,h2] using hab.symm
    rcases (hpsv t).mp htp with htS | htV
    · have hts : t = s := htS
      refine ⟨htT,s,hsS,?_⟩
      intro j hj
      rw [hts]
    · refine ⟨htT,s,hsS,?_⟩
      intro j hj
      simpa only [htV] using (hJ s v).mp hRel j hj
  · rintro ⟨htT,s,hsS,hAgree⟩
    have hsT : B.mem s F.sort := hST s hsS
    obtain ⟨p,hp⟩ := unordered_pair_exists B.mem H s t
    have hpQ : B.mem p Q := (hQ p).mpr ⟨s,t,hsS,htT,hp⟩
    have hpG : B.mem p G := (hG p).mpr
      ⟨s,t,hsT,htT,hp,(hJ s t).mpr hAgree⟩
    have hpI : B.mem p I := (hI p).mpr ⟨hpG,hpQ⟩
    have htp : B.mem t p := (hp t).mpr (Or.inr rfl)
    exact (hO t).mpr ⟨htT,(hU t).mpr ⟨p,hpI,htp⟩⟩

end NineAxiomBZ
