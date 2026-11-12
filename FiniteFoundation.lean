import NineAxiomCore
/-!
Finite-set closure and consequences of FIRST-ORDER Foundation. This file
neither assumes well-founded membership in Lean's metatheory nor uses any
separation instance.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Every externally finite list of model elements has an internal set of
exactly its entries, using only derived Pairing and binary Union. -/
theorem list_members_exists (B : Background V) (H : NineAxioms B.mem)
    (l : List V) :
    HasMembers B.mem (fun x : V => x ∈ l) := by
  induction l with
  | nil =>
      obtain ⟨e, he⟩ := H.empty
      refine ⟨e, ?_⟩
      intro x
      simpa using he x
  | cons a l ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨sa, hsa⟩ := H.singleton a
      obtain ⟨r, hr⟩ := binary_union_exists B.mem H sa s
      refine ⟨r, ?_⟩
      intro x
      simpa [List.mem_cons, hsa x, hs x] using hr x

/-- Finite directed membership graphs without a source cannot exist under
first-order Foundation. This proves finite acyclicity for *any fixed length*;
it does not covertly strengthen Foundation to external WellFounded. -/
theorem no_finite_predecessor_closed_list
    (B : Background V) (H : NineAxioms B.mem)
    (l : List V) (hne : l ≠ [])
    (hpred : ∀ x : V, x ∈ l → ∃ y : V, y ∈ l ∧ B.mem y x) : False := by
  obtain ⟨s, hs⟩ := list_members_exists B H l
  have hneS : ∃ x : V, B.mem x s := by
    cases l with
    | nil => exact False.elim (hne rfl)
    | cons a rest =>
        exact ⟨a, (hs a).2 (by simp)⟩
  obtain ⟨x, hxS, hmin⟩ := B.foundation s hneS
  obtain ⟨y, hyList, hyx⟩ := hpred x ((hs x).1 hxS)
  exact (hmin y ((hs y).2 hyList)) hyx

/-- Explicit 5-cycle exclusion for use in the fresh-tag construction. -/
theorem no_membership_five_cycle
    (B : Background V) (H : NineAxioms B.mem)
    (a b c d e : V) :
    ¬ (B.mem a b ∧ B.mem b c ∧ B.mem c d ∧
       B.mem d e ∧ B.mem e a) := by
  rintro ⟨hab, hbc, hcd, hde, hea⟩
  apply no_finite_predecessor_closed_list B H [a,b,c,d,e] (by simp)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨e, by simp, hea⟩
  · exact ⟨a, by simp, hab⟩
  · exact ⟨b, by simp, hbc⟩
  · exact ⟨c, by simp, hcd⟩
  · exact ⟨d, by simp, hde⟩

/-- Explicit 6-cycle exclusion for prefix projection on nested tuples. -/
theorem no_membership_six_cycle
    (B : Background V) (H : NineAxioms B.mem)
    (a b c d e f : V) :
    ¬ (B.mem a b ∧ B.mem b c ∧ B.mem c d ∧
       B.mem d e ∧ B.mem e f ∧ B.mem f a) := by
  rintro ⟨hab, hbc, hcd, hde, hef, hfa⟩
  apply no_finite_predecessor_closed_list B H [a,b,c,d,e,f] (by simp)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨f, by simp, hfa⟩
  · exact ⟨a, by simp, hab⟩
  · exact ⟨b, by simp, hbc⟩
  · exact ⟨c, by simp, hcd⟩
  · exact ⟨d, by simp, hde⟩
  · exact ⟨e, by simp, hef⟩

end NineAxiomBZ
