import TaggingGraph
/-!
# Diagonal extraction without Separation

The singleton-image `SI(T)={{t}:t∈T}` lets us extract the self-loops
of *any* undirected edge set `R`, purely by intersection and set union:

  ∪ (R ∩ SI(T)) = {t∈T | {t}∈R}.

This operation is needed to turn a binary relational test on assignments
into a unary truth-set predicate.

NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Diagonal extraction from a relation `R` and a set `T` of possible points. -/
theorem diagonal_filter_exists
    (B : Background V) (H : NineAxioms B.mem)
    (T R : V) :
    HasMembers B.mem (fun t : V =>
      B.mem t T ∧ ∃ e : V,
        B.mem e R ∧ IsUPair B.mem e t t) := by
  obtain ⟨SI, hSI⟩ := singleton_image_exists B H T
  obtain ⟨D, hD⟩ := H.intersection R SI
  obtain ⟨U, hU⟩ := H.setUnion D
  refine ⟨U, ?_⟩
  intro t
  constructor
  · intro htU
    obtain ⟨e, heD, hte⟩ := (hU t).1 htU
    have heR : B.mem e R := ((hD e).1 heD).1
    have heSI : B.mem e SI := ((hD e).1 heD).2
    obtain ⟨v, hvT, hev⟩ := (hSI e).1 heSI
    have htv : t = v := (hev t).1 hte
    have hett : IsUPair B.mem e t t := by
      intro x
      constructor
      · intro hxe
        left
        exact ((hev x).1 hxe).trans htv.symm
      · intro hx
        rcases hx with h | h
        · exact (hev x).2 (h.trans htv)
        · exact (hev x).2 (h.trans htv)
    exact ⟨htv.symm ▸ hvT, e, heR, hett⟩
  · rintro ⟨htT, e, heR, hett⟩
    have hesingleton : ∀ x : V, B.mem x e ↔ x = t := by
      intro x
      constructor
      · intro hx
        rcases (hett x).1 hx with h | h
        · exact h
        · exact h
      · intro hx
        exact (hett x).2 (Or.inl hx)
    have heSI : B.mem e SI :=
      (hSI e).2 ⟨t, htT, hesingleton⟩
    have heD : B.mem e D := (hD e).2 ⟨heR, heSI⟩
    exact (hU t).2 ⟨e, heD, (hett t).2 (Or.inl rfl)⟩

end NineAxiomBZ
