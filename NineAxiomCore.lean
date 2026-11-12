import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Unrestricted unordered operations and Δ₀-Separation

Core lemmas for the finite nine-axiom proposal.

The only nonlogical assumptions in `Background` and `NineAxioms` are the
standard residual Bounded-Zermelo axioms required by the construction and
precisely the nine globally quantified operations of the proposal.

This file contains no `sorry` or extra auxiliary axioms.  The complete
project was elaborated and kernel-checked with Lean 4.20.0.

This is a semantic theorem (validity in every structure satisfying the
axioms), not a proof inside a syntactic FOL deduction calculus.
-/

universe u

namespace NineAxiomBZ

variable {V : Type u}

/-- Membership-only interpretation of a set in a one-sorted first-order model. -/
def HasMembers (mem : V → V → Prop) (P : V → Prop) : Prop :=
  ∃ s : V, ∀ x : V, mem x s ↔ P x

/-- An unordered pair, including the degenerate case `a = b`. -/
def IsUPair (mem : V → V → Prop) (p a b : V) : Prop :=
  ∀ x : V, mem x p ↔ x = a ∨ x = b

/-- The portions of BZ^- needed for the proposed proof.  In particular there
is **no** instance of separation among the fields.  Infinity and Choice are
not needed for this finite construction and can be added separately. -/
structure Background (V : Type u) where
  mem : V → V → Prop
  extensionality : ∀ a b : V, (∀ x : V, mem x a ↔ mem x b) → a = b
  powerset : ∀ a : V,
    HasMembers mem (fun x : V => ∀ y : V, mem y x → mem y a)
  foundation : ∀ a : V, (∃ x : V, mem x a) →
    ∃ x : V, mem x a ∧ ∀ y : V, mem y a → ¬ mem y x

/-- The eight unrestricted operations from the first MathOverflow post plus
(9) the common-superset principle.  These assert existence, not the existence
of a global universal set or a bounded relational milieu. -/
structure NineAxioms (mem : V → V → Prop) where
  empty : HasMembers mem (fun _ : V => False)
  singleton : ∀ a : V, HasMembers mem (fun x : V => x = a)
  difference : ∀ a b : V,
    HasMembers mem (fun x : V => mem x a ∧ ¬ mem x b)
  intersection : ∀ a b : V,
    HasMembers mem (fun x : V => mem x a ∧ mem x b)
  setUnion : ∀ a : V,
    HasMembers mem (fun x : V => ∃ y : V, mem y a ∧ mem x y)
  unorderedComposition : ∀ q r : V,
    HasMembers mem (fun t : V =>
      ∃ a b c : V,
        IsUPair mem t a c ∧
        (∃ p : V, mem p q ∧ IsUPair mem p a b) ∧
        (∃ p : V, mem p r ∧ IsUPair mem p b c))
  unorderedIntersection : ∀ x : V,
    HasMembers mem (fun t : V =>
      mem t x ∧ ∃ a b : V,
        IsUPair mem t a b ∧
        ∃ z : V, mem z a ∧ mem z b)
  unorderedMembership : ∀ x : V,
    HasMembers mem (fun t : V =>
      mem t x ∧ ∃ a b : V,
        IsUPair mem t a b ∧ (mem a b ∨ mem b a))
  commonSuperset : ∀ a b : V,
    ∃ c : V, ∀ x : V, mem x a ∨ mem x b → mem x c

section DerivedFiniteOperations

variable (m : V → V → Prop) (H : NineAxioms m)
include H

/-- Pairing is derivable from the singleton, difference and common-superset
axioms; it is not added to the signature as a new postulate. -/
theorem unordered_pair_exists (a b : V) :
    HasMembers m (fun x : V => x = a ∨ x = b) := by
  obtain ⟨sa, hsa⟩ := H.singleton a
  obtain ⟨sb, hsb⟩ := H.singleton b
  obtain ⟨c, hc⟩ := H.commonSuperset sa sb
  have ha : m a c := hc a (Or.inl ((hsa a).2 rfl))
  have hb : m b c := hc b (Or.inr ((hsb b).2 rfl))
  obtain ⟨ca, hca⟩ := H.difference c sa
  obtain ⟨cab, hcab⟩ := H.difference ca sb
  obtain ⟨p, hp⟩ := H.difference c cab
  refine ⟨p, ?_⟩
  intro x
  constructor
  · intro hx
    have hxc : m x c := ((hp x).1 hx).1
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr hxb
    have hxsa : ¬ m x sa := by
      intro h
      exact hxa ((hsa x).1 h)
    have hxsb : ¬ m x sb := by
      intro h
      exact hxb ((hsb x).1 h)
    have hxca : m x ca := (hca x).2 ⟨hxc, hxsa⟩
    have hxcab : m x cab := (hcab x).2 ⟨hxca, hxsb⟩
    exact False.elim (((hp x).1 hx).2 hxcab)
  · intro hx
    rcases hx with hxa | hxb
    · subst x
      apply (hp a).2
      refine ⟨ha, ?_⟩
      intro hacab
      have haca : m a ca := ((hcab a).1 hacab).1
      exact ((hca a).1 haca).2 ((hsa a).2 rfl)
    · subst x
      apply (hp b).2
      refine ⟨hb, ?_⟩
      intro hbcab
      exact ((hcab b).1 hbcab).2 ((hsb b).2 rfl)

/-- Binary union follows from derived pairing followed by axiom (5). -/
theorem binary_union_exists (a b : V) :
    HasMembers m (fun x : V => m x a ∨ m x b) := by
  obtain ⟨p, hp⟩ := unordered_pair_exists m H a b
  obtain ⟨u, hu⟩ := H.setUnion p
  refine ⟨u, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (hu x).1 hx
    rcases (hp s).1 hs with rfl | rfl
    · exact Or.inl hxs
    · exact Or.inr hxs
  · intro hx
    rcases hx with hxa | hxb
    · exact (hu x).2 ⟨a, (hp a).2 (Or.inl rfl), hxa⟩
    · exact (hu x).2 ⟨b, (hp b).2 (Or.inr rfl), hxb⟩

/-- Equality separation is already a theorem of the nine axioms. -/
theorem separate_eq_exists (a b : V) :
    HasMembers m (fun x : V => m x a ∧ x = b) := by
  obtain ⟨s, hs⟩ := H.singleton b
  obtain ⟨t, ht⟩ := H.intersection a s
  refine ⟨t, ?_⟩
  intro x
  constructor
  · rintro h
    exact ⟨((ht x).1 h).1, (hs x).1 (((ht x).1 h).2)⟩
  · rintro ⟨hxa, hxb⟩
    exact (ht x).2 ⟨hxa, (hs x).2 hxb⟩

/-- The easier direction of membership separation. -/
theorem separate_mem_right_exists (a b : V) :
    HasMembers m (fun x : V => m x a ∧ m x b) :=
  H.intersection a b

/-- The relative-complement instance of bounded separation. -/
theorem separate_not_mem_right_exists (a b : V) :
    HasMembers m (fun x : V => m x a ∧ ¬ m x b) :=
  H.difference a b

end DerivedFiniteOperations

/-!
## Finite consequences of first-order Foundation

Crucial caution: the following arguments use *first-order Foundation*,
not meta-theoretic well-foundedness of membership.  Only finite cycles
are excluded.  This works even for externally non-well-founded models.
-/

section FoundationConsequences

variable (B : Background V) (H : NineAxioms B.mem)
include H

/-- Foundation rules out a membership 2-cycle. -/
theorem no_membership_two_cycle (a b : V) :
    ¬ (B.mem a b ∧ B.mem b a) := by
  rintro ⟨hab, hba⟩
  obtain ⟨p, hp⟩ := unordered_pair_exists B.mem H a b
  have ha : B.mem a p := (hp a).2 (Or.inl rfl)
  have hb : B.mem b p := (hp b).2 (Or.inr rfl)
  obtain ⟨x, hx, hmin⟩ := B.foundation p ⟨a, ha⟩
  rcases (hp x).1 hx with rfl | rfl
  · exact (hmin b hb) hba
  · exact (hmin a ha) hab

/-- Foundation rules out a membership 3-cycle. -/
theorem no_membership_three_cycle (a b c : V) :
    ¬ (B.mem a b ∧ B.mem b c ∧ B.mem c a) := by
  rintro ⟨hab, hbc, hca⟩
  obtain ⟨ab, habp⟩ := unordered_pair_exists B.mem H a b
  obtain ⟨cs, hcs⟩ := H.singleton c
  obtain ⟨abc, habc⟩ := binary_union_exists B.mem H ab cs
  have ha : B.mem a abc :=
    (habc a).2 (Or.inl ((habp a).2 (Or.inl rfl)))
  have hb : B.mem b abc :=
    (habc b).2 (Or.inl ((habp b).2 (Or.inr rfl)))
  have hc : B.mem c abc :=
    (habc c).2 (Or.inr ((hcs c).2 rfl))
  obtain ⟨x, hx, hmin⟩ := B.foundation abc ⟨a, ha⟩
  rcases (habc x).1 hx with hxab | hxcs
  · rcases (habp x).1 hxab with rfl | rfl
    · exact (hmin c hc) hca
    · exact (hmin a ha) hab
  · have hxc : x = c := (hcs x).1 hxcs
    subst x
    exact (hmin b hb) hbc

/-- This four-cycle lemma is needed to ensure that the proposed
singleton-image matching has no reverse-membership edges. -/
theorem no_membership_four_cycle (a b c d : V) :
    ¬ (B.mem a b ∧ B.mem b c ∧ B.mem c d ∧ B.mem d a) := by
  rintro ⟨hab, hbc, hcd, hda⟩
  obtain ⟨ab, habp⟩ := unordered_pair_exists B.mem H a b
  obtain ⟨cd, hcdp⟩ := unordered_pair_exists B.mem H c d
  obtain ⟨s, hs⟩ := binary_union_exists B.mem H ab cd
  have ha : B.mem a s :=
    (hs a).2 (Or.inl ((habp a).2 (Or.inl rfl)))
  have hb : B.mem b s :=
    (hs b).2 (Or.inl ((habp b).2 (Or.inr rfl)))
  have hc : B.mem c s :=
    (hs c).2 (Or.inr ((hcdp c).2 (Or.inl rfl)))
  have hd : B.mem d s :=
    (hs d).2 (Or.inr ((hcdp d).2 (Or.inr rfl)))
  obtain ⟨x, hx, hmin⟩ := B.foundation s ⟨a, ha⟩
  rcases (hs x).1 hx with hxab | hxcd
  · rcases (habp x).1 hxab with rfl | rfl
    · exact (hmin d hd) hda
    · exact (hmin a ha) hab
  · rcases (hcdp x).1 hxcd with rfl | rfl
    · exact (hmin b hb) hbc
    · exact (hmin c hc) hcd

/-- One finite marker can avoid two given sets, and avoid membership in
any member of either.  This is what the corrected fan and the graph of
the singleton-image operation require. -/
theorem fresh_marker_for_two (U W : V) :
    ∃ m : V,
      (¬ B.mem m U) ∧
      (¬ B.mem m W) ∧
      (∀ u : V, B.mem u U ∨ B.mem u W → ¬ B.mem m u) := by
  obtain ⟨UW, hUW⟩ := binary_union_exists B.mem H U W
  obtain ⟨m, hm⟩ := H.singleton UW
  have hUWm : B.mem UW m := (hm UW).2 rfl
  have hmuw : ¬ B.mem m UW := by
    intro hmw
    exact no_membership_two_cycle B H UW m ⟨hUWm, hmw⟩
  refine ⟨m, ?_, ?_, ?_⟩
  · intro hmu
    exact hmuw ((hUW m).2 (Or.inl hmu))
  · intro hmv
    exact hmuw ((hUW m).2 (Or.inr hmv))
  · intro u hu hmu
    have huUW : B.mem u UW := (hUW u).2 hu
    exact no_membership_three_cycle B H m u UW ⟨hmu, huUW, hUWm⟩

end FoundationConsequences

/-!
## Corrected fan construction

`P(U ∪ {m}) ∘̲ {{m}}` includes the unwanted singleton `{m}`.
The next lemma removes it; importantly, it does not appeal to Separation.
-/

section CorrectedFan

variable (B : Background V) (H : NineAxioms B.mem)
include H

/-- With a marker `m` outside `U`, construct exactly the undirected star
`{{u,m} | u ∈ U}`. -/
theorem corrected_fan_exists (U m : V) (hmU : ¬ B.mem m U) :
    HasMembers B.mem (fun t : V =>
      ∃ u : V, B.mem u U ∧ IsUPair B.mem t u m) := by
  obtain ⟨sm, hsm⟩ := H.singleton m
  obtain ⟨D, hD⟩ := binary_union_exists B.mem H U sm
  obtain ⟨P, hP⟩ := B.powerset D
  obtain ⟨ssm, hssm⟩ := H.singleton sm
  obtain ⟨C, hC⟩ := H.unorderedComposition P ssm
  obtain ⟨F, hF⟩ := H.difference C ssm
  refine ⟨F, ?_⟩
  intro t
  constructor
  · intro ht
    have htC : B.mem t C := ((hF t).1 ht).1
    have htNotSSM : ¬ B.mem t ssm := ((hF t).1 ht).2
    obtain ⟨a, b, c, htPair, ⟨p, hpP, hpab⟩,
      ⟨r, hrSSM, hrbc⟩⟩ := (hC t).1 htC
    have hr : r = sm := (hssm r).1 hrSSM
    subst r
    have hb : b = m := (hsm b).1 ((hrbc b).2 (Or.inl rfl))
    have hc : c = m := (hsm c).1 ((hrbc c).2 (Or.inr rfl))
    subst b
    subst c
    have haP : B.mem a p := (hpab a).2 (Or.inl rfl)
    have haD : B.mem a D := (hP p).1 hpP a haP
    rcases (hD a).1 haD with haU | haSm
    · exact ⟨a, haU, htPair⟩
    · have ham : a = m := (hsm a).1 haSm
      subst a
      have htsm : t = sm := by
        apply B.extensionality
        intro x
        rw [htPair x, hsm x]
        tauto
      exact False.elim (htNotSSM ((hssm t).2 htsm))
  · rintro ⟨u, huU, htPair⟩
    obtain ⟨p, hp⟩ := unordered_pair_exists B.mem H u m
    have hpP : B.mem p P := by
      apply (hP p).2
      intro x hxp
      rcases (hp x).1 hxp with hxu | hxm
      · simpa only [hxu] using (hD u).2 (Or.inl huU)
      · simpa only [hxm] using (hD m).2 (Or.inr ((hsm m).2 rfl))
    have hsmPair : IsUPair B.mem sm m m := by
      intro x
      constructor
      · intro hx
        exact Or.inl ((hsm x).1 hx)
      · intro hx
        rcases hx with hx | hx
        · exact (hsm x).2 hx
        · exact (hsm x).2 hx
    have htC : B.mem t C := by
      apply (hC t).2
      exact ⟨u, m, m, htPair, ⟨p, hpP, hp⟩,
        ⟨sm, (hssm sm).2 rfl, hsmPair⟩⟩
    have htNotSSM : ¬ B.mem t ssm := by
      intro htS
      have htsm : t = sm := (hssm t).1 htS
      have huT : B.mem u t := (htPair u).2 (Or.inl rfl)
      have huSM : B.mem u sm := by simpa [htsm] using huT
      have hum : u = m := (hsm u).1 huSM
      subst u
      exact hmU huU
    exact (hF t).2 ⟨htC, htNotSSM⟩

end CorrectedFan

/-!
## Unordered Cartesian products

The next lemma is the finite edge-orientation calculation needed to
prove that composing corrected fans does not create unwanted edges.
-/

section UnorderedProduct

variable (B : Background V) (H : NineAxioms B.mem)

/-- Two descriptions of the same unordered pair have equal endpoints
up to reversal.  No stratification or Separation is involved. -/
theorem unordered_pair_endpoints
    {p a b c d : V}
    (h₁ : IsUPair B.mem p a b)
    (h₂ : IsUPair B.mem p c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a = c ∨ a = d := (h₂ a).1 ((h₁ a).2 (Or.inl rfl))
  rcases ha with hac | had
  · left
    refine ⟨hac, ?_⟩
    by_cases hba : b = a
    · have hda : d = a := by
        rcases (h₁ d).1 ((h₂ d).2 (Or.inr rfl)) with h | h
        · exact h
        · exact h.trans hba
      exact hba.trans hda.symm
    · rcases (h₂ b).1 ((h₁ b).2 (Or.inr rfl)) with hbc | hbd
      · exact False.elim (hba (hbc.trans hac.symm))
      · exact hbd
  · right
    refine ⟨had, ?_⟩
    by_cases hba : b = a
    · have hca : c = a := by
        rcases (h₁ c).1 ((h₂ c).2 (Or.inl rfl)) with h | h
        · exact h
        · exact h.trans hba
      exact hba.trans hca.symm
    · rcases (h₂ b).1 ((h₁ b).2 (Or.inr rfl)) with hbc | hbd
      · exact hbc
      · exact False.elim (hba (hbd.trans had.symm))

include H
/-- For *arbitrary* inputs U,W, the set of all unordered cross-pairs exists.
This is the main unconditional relation-algebra construction preceding
singletons, tagged copies and arbitrary finite tuples. -/
theorem unordered_product_exists (U W : V) :
    HasMembers B.mem (fun t : V =>
      ∃ u w : V, B.mem u U ∧ B.mem w W ∧ IsUPair B.mem t u w) := by
  obtain ⟨m, hmU, hmW, _⟩ := fresh_marker_for_two B H U W
  obtain ⟨FU, hFU⟩ := corrected_fan_exists B H U m hmU
  obtain ⟨FW, hFW⟩ := corrected_fan_exists B H W m hmW
  obtain ⟨R, hR⟩ := H.unorderedComposition FU FW
  obtain ⟨sm, hsm⟩ := H.singleton m
  obtain ⟨ssm, hssm⟩ := H.singleton sm
  obtain ⟨P, hP⟩ := H.difference R ssm
  refine ⟨P, ?_⟩
  intro t
  constructor
  · intro ht
    have htR : B.mem t R := ((hP t).1 ht).1
    have htNotSSM : ¬ B.mem t ssm := ((hP t).1 ht).2
    obtain ⟨a, b, c, htPair, ⟨p, hpFU, hpab⟩,
      ⟨q, hqFW, hqbc⟩⟩ := (hR t).1 htR
    obtain ⟨u, huU, hpum⟩ := (hFU p).1 hpFU
    obtain ⟨w, hwW, hqwm⟩ := (hFW q).1 hqFW
    have hpEnds := unordered_pair_endpoints B hpab hpum
    have hqEnds := unordered_pair_endpoints B hqbc hqwm
    rcases hpEnds with ⟨hau, hbm⟩ | ⟨ham, hbu⟩
    · rcases hqEnds with ⟨hbv, hcm⟩ | ⟨hbm', hcv⟩
      · have hwm : w = m := hbv.symm.trans hbm
        exact False.elim (hmW (hwm ▸ hwW))
      · refine ⟨u, w, huU, hwW, ?_⟩
        intro x
        simpa only [hau, hcv] using htPair x
    · rcases hqEnds with ⟨hbv, hcm⟩ | ⟨hbm, hcv⟩
      · have ham' : a = m := ham
        have hcm' : c = m := hcm
        have htsm : t = sm := by
          apply B.extensionality
          intro x
          rw [htPair x, hsm x]
          rw [ham', hcm']
          tauto
        exact False.elim (htNotSSM ((hssm t).2 htsm))
      · have hum : u = m := hbu.symm.trans hbm
        exact False.elim (hmU (hum ▸ huU))
  · rintro ⟨u, w, huU, hwW, htPair⟩
    obtain ⟨p, hp⟩ := unordered_pair_exists B.mem H u m
    obtain ⟨q, hq⟩ := unordered_pair_exists B.mem H w m
    have hpFU : B.mem p FU := (hFU p).2 ⟨u, huU, hp⟩
    have hqFW : B.mem q FW := (hFW q).2 ⟨w, hwW, hq⟩
    have hqmw : IsUPair B.mem q m w := by
      intro x
      constructor
      · intro hx
        rcases (hq x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (hq x).2 (Or.inr h)
        · exact (hq x).2 (Or.inl h)
    have htR : B.mem t R := (hR t).2
      ⟨u, m, w, htPair, ⟨p, hpFU, hp⟩, ⟨q, hqFW, hqmw⟩⟩
    have htNotSSM : ¬ B.mem t ssm := by
      intro htSSM
      have htsm : t = sm := (hssm t).1 htSSM
      have huT : B.mem u t := (htPair u).2 (Or.inl rfl)
      have huSM : B.mem u sm := by simpa [htsm] using huT
      have hum : u = m := (hsm u).1 huSM
      subst u
      exact hmU huU
    exact (hP t).2 ⟨htR, htNotSSM⟩

end UnorderedProduct


end NineAxiomBZ
