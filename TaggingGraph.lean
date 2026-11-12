import NineAxiomCore
/-!
The first missing relational-algebra lemma for the nine-axiom program.

No separation axiom, `sorry`, or auxiliary proof axiom occurs here.
The argument requires ONLY Background and NineAxioms from the parent file.

IMPORTANT: this source has not been checked by Lean, which is unavailable in
this runtime. The parent file still contains an open bounded-separation theorem.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Given U, form the graph of `u ↦ {u,{U}}` as an unordered edge set. -/
theorem tagging_graph_exists
    (B : Background V) (H : NineAxioms B.mem) (U : V) :
    ∃ m : V, (∀ x : V, B.mem x m ↔ x = U) ∧
      HasMembers B.mem (fun p : V =>
        ∃ u f : V, B.mem u U ∧ IsUPair B.mem f u m ∧
          IsUPair B.mem p u f) := by
  obtain ⟨m, hm⟩ := H.singleton U
  have hUm : B.mem U m := (hm U).2 rfl
  have hmU : ¬ B.mem m U := by
    intro hmU
    exact no_membership_two_cycle B H U m ⟨hUm, hmU⟩
  obtain ⟨F, hF⟩ := corrected_fan_exists B H U m hmU
  obtain ⟨Q, hQ⟩ := unordered_product_exists B H U F
  obtain ⟨E, hE⟩ := H.unorderedMembership Q
  refine ⟨m, hm, E, ?_⟩
  intro p
  constructor
  · intro hpE
    obtain ⟨hpQ, a, b, hpab, habmem⟩ := (hE p).1 hpE
    obtain ⟨u, f, huU, hfF, hpuf⟩ := (hQ p).1 hpQ
    obtain ⟨v, hvU, hfvm⟩ := (hF f).1 hfF
    have huv_or_hvu : B.mem u f ∨ B.mem f u := by
      rcases unordered_pair_endpoints B hpab hpuf with h | h
      · rcases h with ⟨hau, hbf⟩
        rcases habmem with h | h
        · exact Or.inl (by simpa [hau, hbf] using h)
        · exact Or.inr (by simpa [hau, hbf] using h)
      · rcases h with ⟨haf, hbu⟩
        rcases habmem with h | h
        · exact Or.inr (by simpa [haf, hbu] using h)
        · exact Or.inl (by simpa [haf, hbu] using h)
    have hmF : B.mem m f := (hfvm m).2 (Or.inr rfl)
    have hnot_fu : ¬ B.mem f u := by
      intro hfu
      exact no_membership_four_cycle B H m f u U
        ⟨hmF, hfu, huU, hUm⟩
    have huf : B.mem u f := huv_or_hvu.resolve_right hnot_fu
    have huv : u = v ∨ u = m := (hfvm u).1 huf
    have huv' : u = v := by
      rcases huv with h | h
      · exact h
      · exact False.elim (hmU (h ▸ huU))
    have hf_um : IsUPair B.mem f u m := by
      intro x
      simpa only [huv'] using hfvm x
    exact ⟨u, f, huU, hf_um, hpuf⟩
  · rintro ⟨u, f, huU, hf_um, hpuf⟩
    have hfF : B.mem f F := (hF f).2 ⟨u, huU, hf_um⟩
    have hpQ : B.mem p Q := (hQ p).2 ⟨u, f, huU, hfF, hpuf⟩
    have huf : B.mem u f := (hf_um u).2 (Or.inl rfl)
    exact (hE p).2 ⟨hpQ, u, f, hpuf, Or.inl huf⟩

end NineAxiomBZ

namespace NineAxiomBZ
variable {V : Type u}

/-- An edge of the matching incident to a raw point `u ∈ U` has precisely
`{u,m}` as its other endpoint. -/
private theorem tagging_edge_neighbor
    (B : Background V) (H : NineAxioms B.mem)
    (U m E : V)
    (hUm : B.mem U m)
    (hE : ∀ p : V, B.mem p E ↔
      ∃ u f : V, B.mem u U ∧ IsUPair B.mem f u m ∧
        IsUPair B.mem p u f)
    (u b edge : V) (hu : B.mem u U)
    (he : B.mem edge E) (hpair : IsUPair B.mem edge u b) :
    IsUPair B.mem b u m := by
  obtain ⟨v, f, hvU, hf, hep⟩ := (hE edge).1 he
  have hmF : B.mem m f := (hf m).2 (Or.inr rfl)
  have hfU : ¬ B.mem f U := by
    intro hfU
    exact no_membership_three_cycle B H m f U ⟨hmF, hfU, hUm⟩
  rcases unordered_pair_endpoints B hpair hep with h | h
  · rcases h with ⟨huv, hbf⟩
    subst v
    subst b
    exact hf
  · rcases h with ⟨huf, hbv⟩
    have hfU' : B.mem f U := huf ▸ hu
    exact False.elim (hfU hfU')

/-- The image of `u ↦ {u}` exists for every set U. This is not an instance
of Separation: its proof uses the unordered membership and composition
operations and first-order Foundation. -/
theorem singleton_image_exists
    (B : Background V) (H : NineAxioms B.mem) (U : V) :
    HasMembers B.mem (fun s : V =>
      ∃ u : V, B.mem u U ∧ ∀ x : V, B.mem x s ↔ x = u) := by
  obtain ⟨m, hm, E, hE⟩ := tagging_graph_exists B H U
  have hUm : B.mem U m := (hm U).2 rfl
  have hmU : ¬ B.mem m U := by
    intro hmU
    exact no_membership_two_cycle B H U m ⟨hUm, hmU⟩
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
    have hb_am : IsUPair B.mem b a m :=
      tagging_edge_neighbor B H U m E hUm hE a b p haU hpE hpab
    have hb_cm : IsUPair B.mem b c m := by
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
      exact tagging_edge_neighbor B H U m E hUm hE c b q hcU hqE hqcb
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
    obtain ⟨f, hf⟩ := unordered_pair_exists B.mem H u m
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

end NineAxiomBZ
