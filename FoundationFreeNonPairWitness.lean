import FoundationFreeInfiniteSupply

/-!
# Disjoint non-pair witnesses, without Foundation

This is the combinatorial heart of the Frege-1 construction on page 2 of
Al-Johar, *Short Axiomatization of Stratified Comprehension* (2020).
For distinct a,b we construct disjoint sets n,k, each with at least three
members, such that a∈n and b∈k. Hence neither n nor k is an unordered pair.

All witnesses use finitely many applications of empty, singleton, pairing
and binary union. We never assert the existence of the internal set of all
pure finite objects.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

private theorem not_pair_if_three
    (m : V → V → Prop) {n a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : m a n) (hb : m b n) (hc : m c n) :
    ¬ ∃ x y : V, IsUPair m n x y := by
  rintro ⟨x, y, hxy⟩
  have ha' := (hxy a).mp ha
  have hb' := (hxy b).mp hb
  have hc' := (hxy c).mp hc
  rcases ha' with hax | hay <;>
    rcases hb' with hbx | hby <;>
    rcases hc' with hcx | hcy <;>
    simp_all

/-- Non-pair witnesses required to distinguish a two-element set from a
singleton using the unordered intersection relation. -/
theorem disjoint_nonpair_witnesses
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (a b : V) (hab : a ≠ b) :
    ∃ n k : V,
      (¬ ∃ x y : V, IsUPair B.mem n x y) ∧
      (¬ ∃ x y : V, IsUPair B.mem k x y) ∧
      (∀ z : V, ¬ (B.mem z n ∧ B.mem z k)) ∧
      B.mem a n ∧ B.mem b k := by
  classical
  let m := B.mem
  letI : Infinite V := infinite_carrier_from_nine m H
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({a, b} : Finset V)
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset ({a, b, c} : Finset V)
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset ({a, b, c, d} : Finset V)
  obtain ⟨f, hf⟩ := Infinite.exists_notMem_finset ({a, b, c, d, e} : Finset V)
  have hca : c ≠ a := by intro h; exact hc (by simp [h])
  have hcb : c ≠ b := by intro h; exact hc (by simp [h])
  have hda : d ≠ a := by intro h; exact hd (by simp [h])
  have hdb : d ≠ b := by intro h; exact hd (by simp [h])
  have hdc : d ≠ c := by intro h; exact hd (by simp [h])
  have hea : e ≠ a := by intro h; exact he (by simp [h])
  have heb : e ≠ b := by intro h; exact he (by simp [h])
  have hec : e ≠ c := by intro h; exact he (by simp [h])
  have hed : e ≠ d := by intro h; exact he (by simp [h])
  have hfa : f ≠ a := by intro h; exact hf (by simp [h])
  have hfb : f ≠ b := by intro h; exact hf (by simp [h])
  have hfc : f ≠ c := by intro h; exact hf (by simp [h])
  have hfd : f ≠ d := by intro h; exact hf (by simp [h])
  have hfe : f ≠ e := by intro h; exact hf (by simp [h])
  obtain ⟨ac, hac⟩ := unordered_pair_exists m H a c
  obtain ⟨sd, hsd⟩ := H.singleton d
  obtain ⟨n, hn⟩ := binary_union_exists m H ac sd
  obtain ⟨be, hbe⟩ := unordered_pair_exists m H b e
  obtain ⟨sf, hsf⟩ := H.singleton f
  obtain ⟨k, hk⟩ := binary_union_exists m H be sf
  have hn' (z : V) : m z n ↔ z = a ∨ z = c ∨ z = d := by
    rw [hn z]
    change (B.mem z ac ∨ B.mem z sd) ↔ _
    have hac' : B.mem z ac ↔ z = a ∨ z = c := by
      simpa [m] using hac z
    have hsd' : B.mem z sd ↔ z = d := by
      simpa using hsd z
    rw [hac', hsd']
    constructor
    · rintro (h | h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hk' (z : V) : m z k ↔ z = b ∨ z = e ∨ z = f := by
    rw [hk z]
    change (B.mem z be ∨ B.mem z sf) ↔ _
    have hbe' : B.mem z be ↔ z = b ∨ z = e := by
      simpa [m] using hbe z
    have hsf' : B.mem z sf ↔ z = f := by
      simpa using hsf z
    rw [hbe', hsf']
    constructor
    · rintro (h | h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  refine ⟨n, k, ?_, ?_, ?_, (hn' a).mpr (Or.inl rfl),
    (hk' b).mpr (Or.inl rfl)⟩
  · apply not_pair_if_three m hca.symm hda.symm hdc.symm
    · exact (hn' a).mpr (Or.inl rfl)
    · exact (hn' c).mpr (Or.inr (Or.inl rfl))
    · exact (hn' d).mpr (Or.inr (Or.inr rfl))
  · apply not_pair_if_three m heb.symm hfb.symm hfe.symm
    · exact (hk' b).mpr (Or.inl rfl)
    · exact (hk' e).mpr (Or.inr (Or.inl rfl))
    · exact (hk' f).mpr (Or.inr (Or.inr rfl))
  · intro z ⟨hzn, hzk⟩
    have hzn' := (hn' z).mp hzn
    have hzk' := (hk' z).mp hzk
    rcases hzn' with h | h | h <;>
      rcases hzk' with h' | h' | h' <;>
      subst_vars <;> simp_all

end NineAxiomBZ.NoFoundation
