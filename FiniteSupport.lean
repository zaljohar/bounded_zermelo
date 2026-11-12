import NineAxiomCore
/-!
# Finite families of objects are sets: no Replacement used

A complete bounded-formula truth compiler needs a finite registry W
containing all earlier coordinate sorts, tuple sorts and support sets.
This lemma uses only the derived Pairing/finite Union axioms.

NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The range of each meta-theoretically finite family of model objects is
represented by an actual object-language set.  This uses no Replacement or
Separation; the finite family is assembled by Pairing and Union. -/
theorem finite_family_range_exists
    (B : Background V) (H : NineAxioms B.mem) :
    ∀ (n : Nat) (f : Fin n → V),
      HasMembers B.mem (fun x : V => ∃ i : Fin n, x = f i) := by
  intro n
  induction n with
  | zero =>
      intro f
      obtain ⟨e, he⟩ := H.empty
      refine ⟨e, ?_⟩
      intro x
      constructor
      · intro hx
        exact False.elim ((he x).1 hx)
      · rintro ⟨i, _⟩
        exact i.elim0
  | succ n ih =>
      intro f
      obtain ⟨tailSet, hTail⟩ := ih (fun i : Fin n => f i.succ)
      obtain ⟨headSet, hHead⟩ := H.singleton (f 0)
      obtain ⟨all, hAll⟩ :=
        binary_union_exists B.mem H headSet tailSet
      refine ⟨all, ?_⟩
      intro x
      constructor
      · intro hx
        rcases (hAll x).1 hx with hh | ht
        · exact ⟨0, (hHead x).1 hh⟩
        · obtain ⟨i, hi⟩ := (hTail x).1 ht
          exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            exact (hAll x).2 (Or.inl ((hHead x).2 hi))
        | succ j =>
            exact (hAll x).2 (Or.inr ((hTail x).2 ⟨j, hi⟩))

/-- One support set contains the two fixed seeds and each member of two
arbitrary finite families as elements (not just as subsets). -/
theorem finite_registry_exists
    (B : Background V) (H : NineAxioms B.mem)
    (n k : Nat) (f : Fin n → V) (g : Fin k → V)
    (X T : V) :
    ∃ W : V,
      B.mem X W ∧ B.mem T W ∧
      (∀ i : Fin n, B.mem (f i) W) ∧
      (∀ j : Fin k, B.mem (g j) W) := by
  obtain ⟨F, hF⟩ := finite_family_range_exists B H n f
  obtain ⟨G, hG⟩ := finite_family_range_exists B H k g
  obtain ⟨FG, hFG⟩ := binary_union_exists B.mem H F G
  obtain ⟨XT, hXT⟩ := unordered_pair_exists B.mem H X T
  obtain ⟨W, hW⟩ := binary_union_exists B.mem H FG XT
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact (hW X).2 (Or.inr ((hXT X).2 (Or.inl rfl)))
  · exact (hW T).2 (Or.inr ((hXT T).2 (Or.inr rfl)))
  · intro i
    exact (hW (f i)).2 (Or.inl ((hFG (f i)).2
      (Or.inl ((hF (f i)).2 ⟨i, rfl⟩))))
  · intro j
    exact (hW (g j)).2 (Or.inl ((hFG (g j)).2
      (Or.inr ((hG (g j)).2 ⟨j, rfl⟩))))

end NineAxiomBZ
