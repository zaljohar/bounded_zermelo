import FoundationFreeFregeOne
import TypedComposition

/-!
# Filters for flat tagged tuples

When tags and candidates lie in disjoint sorts and a tag cannot contain
a candidate, the unordered membership filter reads candidate incidence.
Composing this graph with the inequality graph on the tag sort detects
candidates containing two distinct tags from that sort.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- The graph linking a candidate to each tag it contains. -/
theorem tuple_membership_edges_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (C U : V)
    (hReverse : ∀ t u : V, B.mem t C → B.mem u U → ¬ B.mem t u) :
    ∃ G : V, TypedEdges B.mem C U (fun t u => B.mem u t) G := by
  obtain ⟨Q, hQ⟩ := unordered_product_without_foundation B H C U
  obtain ⟨G, hG⟩ := H.unorderedMembership Q
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨hpQ, a, b, hpab, hab⟩ := (hG p).mp hp
    obtain ⟨t, u, ht, hu, hptu⟩ := (hQ p).mp hpQ
    have hEither : B.mem t u ∨ B.mem u t := by
      rcases unordered_pair_endpoints_nf B hpab hptu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    exact ⟨t, u, ht, hu, hptu, hEither.resolve_left (hReverse t u ht hu)⟩
  · rintro ⟨t, u, ht, hu, hptu, hut⟩
    exact (hG p).mpr ⟨(hQ p).mpr ⟨t, u, ht, hu, hptu⟩, t, u, hptu, Or.inr hut⟩

/-- Removing singleton edges from the full graph leaves unordered pairs
whose two endpoints are distinct. -/
private theorem distinct_tag_edges_exists
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (U : V) :
    ∃ L : V, TypedEdges B.mem U U (fun u v => u ≠ v) L := by
  obtain ⟨Q, hQ⟩ := unordered_product_without_foundation B H U U
  obtain ⟨S, hS⟩ := singleton_images_from_nine_no_foundation B H U
  obtain ⟨L, hL⟩ := H.difference Q S
  refine ⟨L, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨hpQ, hpS⟩ := (hL p).mp hp
    obtain ⟨u, v, hu, hv, hpuv⟩ := (hQ p).mp hpQ
    refine ⟨u, v, hu, hv, hpuv, ?_⟩
    rintro rfl
    exact hpS ((hS p).mpr ⟨u, hu, fun x => by simpa only [or_self] using hpuv x⟩)
  · rintro ⟨u, v, hu, hv, hpuv, hne⟩
    refine (hL p).mpr ⟨(hQ p).mpr ⟨u, v, hu, hv, hpuv⟩, ?_⟩
    intro hpS
    obtain ⟨a, _ha, hpa⟩ := (hS p).mp hpS
    exact hne (((hpa u).mp ((hpuv u).mpr (Or.inl rfl))).trans
      ((hpa v).mp ((hpuv v).mpr (Or.inr rfl))).symm)

/-- Keeping only original incidence edges in the composition with the
inequality graph ensures that both distinct tags belong to the candidate. -/
private theorem duplicate_tag_edges_exists
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (C U G : V)
    (hCU : DisjointSortNF B.mem C U)
    (hG : TypedEdges B.mem C U (fun t u => B.mem u t) G) :
    ∃ J : V, TypedEdges B.mem C U
      (fun t u => B.mem u t ∧ ∃ v : V, B.mem v U ∧ B.mem v t ∧ v ≠ u) J := by
  obtain ⟨L, hL⟩ := distinct_tag_edges_exists B H U
  obtain ⟨K, hK⟩ := H.unorderedComposition G L
  obtain ⟨J, hJ⟩ := H.intersection G K
  refine ⟨J, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨hpG, hpK⟩ := (hJ p).mp hp
    obtain ⟨t, u, ht, hu, hptu, hut⟩ := (hG p).mp hpG
    obtain ⟨a, b, c, hpac, ⟨g, hg, hgab⟩, ⟨l, hl, hlbc⟩⟩ := (hK p).mp hpK
    obtain ⟨t', v, ht', hv, hgtv, hvt'⟩ := (hG g).mp hg
    obtain ⟨w, z, hw, hz, hlwz, hwz⟩ := (hL l).mp hl
    have hbc : B.mem b U ∧ B.mem c U ∧ b ≠ c := by
      rcases unordered_pair_endpoints_nf B hlbc hlwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hw, hz, hwz⟩
      · exact ⟨hz, hw, Ne.symm hwz⟩
    have hab : a = t' ∧ b = v :=
      (unordered_pair_endpoints_nf B hgab hgtv).resolve_right
        (fun h => hCU t' b ht' hbc.1 h.2.symm)
    have hac : a = t ∧ c = u :=
      (unordered_pair_endpoints_nf B hpac hptu).resolve_right
        (fun h => hCU t c ht hbc.2.1 h.2.symm)
    refine ⟨t, u, ht, hu, hptu, hut, b, hbc.1, ?_, hac.2 ▸ hbc.2.2⟩
    simpa only [hab.2, ← hac.1, hab.1] using hvt'
  · rintro ⟨t, u, ht, hu, hptu, hut, v, hv, hvt, hne⟩
    obtain ⟨g, hgtv⟩ := unordered_pair_exists B.mem H t v
    obtain ⟨l, hlvu⟩ := unordered_pair_exists B.mem H v u
    exact (hJ p).mpr ⟨(hG p).mpr ⟨t, u, ht, hu, hptu, hut⟩,
      (hK p).mpr ⟨t, v, u, hptu,
        ⟨g, (hG g).mpr ⟨t, v, ht, hv, hgtv, hvt⟩, hgtv⟩,
        ⟨l, (hL l).mpr ⟨v, u, hv, hu, hlvu, hne⟩, hlvu⟩⟩⟩

/-- The left endpoints of a typed graph are the left sort's members
that occur in the union of its edges. -/
private theorem left_endpoints_exist
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (C U G : V)
    (R : V → V → Prop) (hCU : DisjointSortNF B.mem C U)
    (hG : TypedEdges B.mem C U R G) :
    HasMembers B.mem (fun t : V => B.mem t C ∧ ∃ u : V, B.mem u U ∧ R t u) := by
  obtain ⟨S, hS⟩ := H.setUnion G
  obtain ⟨P, hP⟩ := H.intersection C S
  refine ⟨P, ?_⟩
  intro t
  constructor
  · intro htP
    obtain ⟨ht, htS⟩ := (hP t).mp htP
    obtain ⟨p, hp, htp⟩ := (hS t).mp htS
    obtain ⟨s, u, _hs, hu, hpsu, hR⟩ := (hG p).mp hp
    rcases (hpsu t).mp htp with rfl | htu
    · exact ⟨ht, u, hu, hR⟩
    · exact False.elim (hCU t u ht hu htu)
  · rintro ⟨ht, u, hu, hR⟩
    obtain ⟨p, hptu⟩ := unordered_pair_exists B.mem H t u
    exact (hP t).mpr ⟨ht, (hS t).mpr
      ⟨p, (hG p).mpr ⟨t, u, ht, hu, hptu, hR⟩, (hptu t).mpr (Or.inl rfl)⟩⟩

/-- Among the candidates, retain precisely those with one tag in U. -/
theorem exactly_one_tag_filter_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (C U : V)
    (hCU : DisjointSortNF B.mem C U)
    (hReverse : ∀ t u : V, B.mem t C → B.mem u U → ¬ B.mem t u) :
    HasMembers B.mem (fun t : V =>
      B.mem t C ∧ ∃! u : V, B.mem u U ∧ B.mem u t) := by
  classical
  obtain ⟨G, hG⟩ := tuple_membership_edges_exists_nf B H C U hReverse
  obtain ⟨J, hJ⟩ := duplicate_tag_edges_exists B H C U G hCU hG
  obtain ⟨A, hA⟩ := left_endpoints_exist B H C U G (fun t u => B.mem u t) hCU hG
  obtain ⟨M, hM⟩ := left_endpoints_exist B H C U J _ hCU hJ
  obtain ⟨F, hF⟩ := H.difference A M
  refine ⟨F, ?_⟩
  intro t
  constructor
  · intro htF
    obtain ⟨htA, htM⟩ := (hF t).mp htF
    obtain ⟨ht, u, hu, hut⟩ := (hA t).mp htA
    refine ⟨ht, u, ⟨hu, hut⟩, ?_⟩
    rintro v ⟨hv, hvt⟩
    by_contra hne
    exact htM ((hM t).mpr ⟨ht, u, hu, hut, v, hv, hvt, hne⟩)
  · rintro ⟨ht, u, ⟨hu, hut⟩, hUnique⟩
    refine (hF t).mpr ⟨(hA t).mpr ⟨ht, u, hu, hut⟩, ?_⟩
    intro htM
    obtain ⟨_ht, w, hw, hwt, v, hv, hvt, hne⟩ := (hM t).mp htM
    exact hne ((hUnique v ⟨hv, hvt⟩).trans (hUnique w ⟨hw, hwt⟩).symm)

end NineAxiomBZ.NoFoundation
