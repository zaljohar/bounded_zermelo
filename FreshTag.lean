import FiniteFoundation
/-!
Tagging over an arbitrary finite support set W (rather than only W=U).
Foundation excludes the five-cycle that would introduce reverse edges.
This extends `tagging_graph_exists` to fresh tags for later coordinates.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- If the domain U is listed as an element of the support W, the marker
`m={W}` produces a matching `u ↔ {u,m}` as an actual set of unordered edges. -/
theorem fresh_tagging_graph_exists
    (B : Background V) (H : NineAxioms B.mem)
    (U W : V) (hUW : B.mem U W) :
    ∃ m : V, (∀ x : V, B.mem x m ↔ x = W) ∧
      HasMembers B.mem (fun p : V =>
        ∃ u f : V, B.mem u U ∧ IsUPair B.mem f u m ∧
          IsUPair B.mem p u f) := by
  obtain ⟨m, hm⟩ := H.singleton W
  have hWm : B.mem W m := (hm W).2 rfl
  have hmU : ¬ B.mem m U := by
    intro hmU
    exact no_membership_three_cycle B H m U W ⟨hmU, hUW, hWm⟩
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
      exact no_membership_five_cycle B H m f u U W
        ⟨hmF, hfu, huU, hUW, hWm⟩
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
