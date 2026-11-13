import FoundationFreeUnorderedProduct
/-!
# Foundation-free star (fan) operation
Adapted from the original corrected-fan proof. The proof only needs
`marker ∉ U`, not Foundation. No set separation is used.
This file has not been compiled in the current environment.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

theorem corrected_fan_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U marker : V) (hmU : ¬ B.mem marker U) :
    HasMembers B.mem (fun t : V =>
      ∃ u : V, B.mem u U ∧ IsUPair B.mem t u marker) := by
  obtain ⟨sm, hsm⟩ := H.singleton marker
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
    have hb : b = marker := (hsm b).1 ((hrbc b).2 (Or.inl rfl))
    have hc : c = marker := (hsm c).1 ((hrbc c).2 (Or.inr rfl))
    subst b
    subst c
    have haP : B.mem a p := (hpab a).2 (Or.inl rfl)
    have haD : B.mem a D := (hP p).1 hpP a haP
    rcases (hD a).1 haD with haU | haSm
    · exact ⟨a, haU, htPair⟩
    · have ham : a = marker := (hsm a).1 haSm
      subst a
      have htsm : t = sm := by
        apply B.extensionality
        intro x
        rw [htPair x, hsm x]
        tauto
      exact False.elim (htNotSSM ((hssm t).2 htsm))
  · rintro ⟨u, huU, htPair⟩
    obtain ⟨p, hp⟩ := unordered_pair_exists B.mem H u marker
    have hpP : B.mem p P := by
      apply (hP p).2
      intro x hxp
      rcases (hp x).1 hxp with hxu | hxm
      · simpa only [hxu] using (hD u).2 (Or.inl huU)
      · simpa only [hxm] using (hD marker).2 (Or.inr ((hsm marker).2 rfl))
    have hsmPair : IsUPair B.mem sm marker marker := by
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
      exact ⟨u, marker, marker, htPair, ⟨p, hpP, hp⟩,
        ⟨sm, (hssm sm).2 rfl, hsmPair⟩⟩
    have htNotSSM : ¬ B.mem t ssm := by
      intro htS
      have htsm : t = sm := (hssm t).1 htS
      have huT : B.mem u t := (htPair u).2 (Or.inl rfl)
      have huSM : B.mem u sm := by simpa [htsm] using huT
      have hum : u = marker := (hsm u).1 huSM
      subst u
      exact hmU huU
    exact (hF t).2 ⟨htC, htNotSSM⟩


end NineAxiomBZ.NoFoundation
