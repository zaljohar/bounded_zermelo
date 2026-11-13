import FoundationFreeFreshTag
import FoundationFreeDiagonal
/-!
A *conditional* Foundation-free version of the tagged matching graph.
All reverse membership edges are ruled out by bounded freshness facts,
not by Foundation or acyclicity.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- The graph u ↦ {u,marker} exists when the marker avoids U and all sets
at membership distance two below U. -/
theorem tagged_matching_from_deep_marker
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U marker : V)
    (hmU : ¬ B.mem marker U)
    (hdeep : ∀ u v : V, B.mem u U → B.mem v u → ¬ B.mem marker v) :
    HasMembers B.mem (fun p : V =>
      ∃ u f : V, B.mem u U ∧ IsUPair B.mem f u marker ∧
          IsUPair B.mem p u f) := by
  obtain ⟨F, hF⟩ := corrected_fan_no_foundation B H U marker hmU
  obtain ⟨Q, hQ⟩ := unordered_product_without_foundation B H U F
  obtain ⟨E, hE⟩ := H.unorderedMembership Q
  refine ⟨E, ?_⟩
  intro p
  constructor
  · intro hpE
    obtain ⟨hpQ, a, b, hpab, habmem⟩ := (hE p).1 hpE
    obtain ⟨u, f, huU, hfF, hpuf⟩ := (hQ p).1 hpQ
    obtain ⟨v, hvU, hfvm⟩ := (hF f).1 hfF
    have huv_or_hvu : B.mem u f ∨ B.mem f u := by
      rcases unordered_pair_endpoints_nf B hpab hpuf with h | h
      · rcases h with ⟨hau, hbf⟩
        rcases habmem with h | h
        · exact Or.inl (by simpa [hau, hbf] using h)
        · exact Or.inr (by simpa [hau, hbf] using h)
      · rcases h with ⟨haf, hbu⟩
        rcases habmem with h | h
        · exact Or.inr (by simpa [haf, hbu] using h)
        · exact Or.inl (by simpa [haf, hbu] using h)
    have hmF : B.mem marker f := (hfvm marker).2 (Or.inr rfl)
    have hnot_fu : ¬ B.mem f u := by
      intro hfu
      exact hdeep u f huU hfu hmF
    have huf : B.mem u f := huv_or_hvu.resolve_right hnot_fu
    have huv : u = v ∨ u = marker := (hfvm u).1 huf
    have huv' : u = v := by
      rcases huv with h | h
      · exact h
      · exact False.elim (hmU (h ▸ huU))
    have hf_um : IsUPair B.mem f u marker := by
      intro x
      simpa only [huv'] using hfvm x
    exact ⟨u, f, huU, hf_um, hpuf⟩
  · rintro ⟨u, f, huU, hf_um, hpuf⟩
    have hfF : B.mem f F := (hF f).2 ⟨u, huU, hf_um⟩
    have hpQ : B.mem p Q := (hQ p).2 ⟨u, f, huU, hfF, hpuf⟩
    have huf : B.mem u f := (hf_um u).2 (Or.inl rfl)
    exact (hE p).2 ⟨hpQ, u, f, hpuf, Or.inl huf⟩

/-- A matching edge incident to u ∈ U has the uniquely determined second
endpoint {u,marker}. The proof avoids all cycle-exclusion lemmas. -/
private theorem tagged_neighbor_from_freshness
    (B : BackgroundNoFoundation V) (U marker E : V)
    (hnotInside : ∀ x : V, B.mem x U → ¬ B.mem marker x)
    (hE : ∀ p : V, B.mem p E ↔
      ∃ u f : V, B.mem u U ∧ IsUPair B.mem f u marker ∧
          IsUPair B.mem p u f)
    (u b edge : V) (hu : B.mem u U)
    (he : B.mem edge E) (hp : IsUPair B.mem edge u b) :
    IsUPair B.mem b u marker := by
  obtain ⟨v, f, hv, hf, hEdge⟩ := (hE edge).1 he
  have hmF : B.mem marker f := (hf marker).2 (Or.inr rfl)
  have hfNotU : ¬ B.mem f U := by
    intro hfU
    exact hnotInside f hfU hmF
  rcases unordered_pair_endpoints_nf B hp hEdge with h | h
  · rcases h with ⟨huv, hbf⟩
    subst v
    subst b
    exact hf
  · rcases h with ⟨huf, hbv⟩
    have hfU : B.mem f U := huf ▸ hu
    exact False.elim (hfNotU hfU)

/-- Every singleton image exists if the three-level fresh marker exists.
This is a genuine derivation from T₉ once `NoUniversal` is separately proved.
It does NOT assert that `NoUniversal` is a new axiom of BZ⁻ + T₉. -/
theorem singleton_image_from_deep_marker
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U marker : V)
    (hmU : ¬ B.mem marker U)
    (hnotInside : ∀ x : V, B.mem x U → ¬ B.mem marker x)
    (hdeep : ∀ u v : V, B.mem u U → B.mem v u → ¬ B.mem marker v) :
    SingletonImageOn B.mem U := by
  obtain ⟨E, hE⟩ := tagged_matching_from_deep_marker B H U marker hmU hdeep
  obtain ⟨C, hC⟩ := H.unorderedComposition E E
  obtain ⟨P, hP⟩ := B.powerset U
  obtain ⟨I, hI⟩ := H.intersection C P
  refine ⟨I, ?_⟩
  intro s
  constructor
  · intro hs
    have hsC : B.mem s C := ((hI s).1 hs).1
    have hsP : B.mem s P := ((hI s).1 hs).2
    obtain ⟨a, b, c, hsac, ⟨p, hpE, hpab⟩,
      ⟨q, hqE, hqbc⟩⟩ := (hC s).1 hsC
    have haU : B.mem a U := (hP s).1 hsP a ((hsac a).2 (Or.inl rfl))
    have hcU : B.mem c U := (hP s).1 hsP c ((hsac c).2 (Or.inr rfl))
    have hb_am : IsUPair B.mem b a marker :=
      tagged_neighbor_from_freshness B U marker E hnotInside hE
        a b p haU hpE hpab
    have hqcb : IsUPair B.mem q c b := by
      intro x
      constructor
      · intro hx
        rcases (hqbc x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (hqbc x).2 (Or.inr h)
        · exact (hqbc x).2 (Or.inl h)
    have hb_cm : IsUPair B.mem b c marker :=
      tagged_neighbor_from_freshness B U marker E hnotInside hE
        c b q hcU hqE hqcb
    have hac : a = c := by
      have ha_b : B.mem a b := (hb_am a).2 (Or.inl rfl)
      rcases (hb_cm a).1 ha_b with h | h
      · exact h
      · exact False.elim (hmU (h ▸ haU))
    refine ⟨a, haU, ?_⟩
    intro x
    rw [hsac x, hac]
    tauto
  · rintro ⟨u, huU, hs⟩
    obtain ⟨f, hf⟩ := unordered_pair_exists B.mem H u marker
    obtain ⟨e, he⟩ := unordered_pair_exists B.mem H u f
    have heE : B.mem e E := (hE e).2 ⟨u, f, huU, hf, he⟩
    have hsuu : IsUPair B.mem s u u := by
      intro x
      constructor
      · intro hx
        exact Or.inl ((hs x).1 hx)
      · intro hx
        rcases hx with hx | hx
        · exact (hs x).2 hx
        · exact (hs x).2 hx
    have heu_reverse : IsUPair B.mem e f u := by
      intro x
      constructor
      · intro hx
        rcases (he x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (he x).2 (Or.inr h)
        · exact (he x).2 (Or.inl h)
    have hsC : B.mem s C :=
      (hC s).2 ⟨u, f, u, hsuu, ⟨e, heE, he⟩,
        ⟨e, heE, heu_reverse⟩⟩
    have hsP : B.mem s P := by
      apply (hP s).2
      intro x hxs
      exact (hs x).1 hxs ▸ huU
    exact (hI s).2 ⟨hsC, hsP⟩

/-- The key *conditional* replacement for the old Foundation-based
singleton-image theorem. The only extra hypothesis is `NoUniversal`. -/
theorem singleton_image_if_no_universal
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hn : NoUniversal B) (U : V) :
    SingletonImageOn B.mem U := by
  obtain ⟨marker, hnotU, hnotInside, hdeep⟩ :=
    fresh_marker_three_levels B H hn U
  exact singleton_image_from_deep_marker B H U marker
    hnotU hnotInside hdeep

end NineAxiomBZ.NoFoundation
