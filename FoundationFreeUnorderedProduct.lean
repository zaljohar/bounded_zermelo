import FoundationFreeCore
/-!
# Unordered Cartesian products without Foundation

The old development constructed marker-fans using finite acyclicity.
Here is a stronger, marker-free derivation from the two Power Set instances
and the unordered composition axiom:

  fan(U,D) = P(U) ∘̲ P(D) = {{u,d} | u∈U, d∈D},  provided U⊆D.

For D = U∪V, the two fans have intersection U*V.  This explicitly
avoids Foundation and uses neither Δ₀-Separation nor singleton-image sets.

No code in this module relies on the original `Background.foundation` field.
This source has NOT been compiled in the current environment.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

private theorem isUPair_flip
    (m : V → V → Prop) {t a b : V}
    (h : IsUPair m t a b) : IsUPair m t b a := by
  intro x
  rw [h x]
  tauto

theorem unordered_pair_endpoints_nf
    (B : BackgroundNoFoundation V)
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


/-- A local fan exists using only Power Set and unordered composition.
    `D` is an arbitrary upper bound on the points of `U`. -/
theorem local_fan_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U D : V) (hUD : ∀ x : V, B.mem x U → B.mem x D) :
    HasMembers B.mem (fun t : V =>
      ∃ a c : V, B.mem a U ∧ B.mem c D ∧ IsUPair B.mem t a c) := by
  let m := B.mem
  obtain ⟨pU, hpU⟩ := B.powerset U
  obtain ⟨pD, hpD⟩ := B.powerset D
  obtain ⟨F, hF⟩ := H.unorderedComposition pU pD
  refine ⟨F, ?_⟩
  intro t
  constructor
  · intro ht
    obtain ⟨a, b, c, htPair, ⟨p, hpU', hpab⟩,
       ⟨q, hpD', hpbc⟩⟩ := (hF t).mp ht
    have haU : m a U := (hpU p).mp hpU' a ((hpab a).mpr (Or.inl rfl))
    have hcD : m c D := (hpD q).mp hpD' c ((hpbc c).mpr (Or.inr rfl))
    exact ⟨a, c, haU, hcD, htPair⟩
  · rintro ⟨a, c, haU, hcD, htPair⟩
    obtain ⟨pa, hpa⟩ := H.singleton a
    obtain ⟨pac, hpac⟩ := unordered_pair_exists m H a c
    have hpaU : m pa pU := by
      apply (hpU pa).mpr
      intro x hx
      have hxa : x = a := (hpa x).mp hx
      simpa [hxa] using haU
    have hpacD : m pac pD := by
      apply (hpD pac).mpr
      intro x hx
      rcases (hpac x).mp hx with rfl | rfl
      · exact hUD _ haU
      · exact hcD
    have hpaPair : IsUPair m pa a a := by
      intro x
      simpa [or_self] using (hpa x)
    exact (hF t).mpr ⟨a, a, c, htPair,
      ⟨pa, hpaU, hpaPair⟩, ⟨pac, hpacD, hpac⟩⟩

/-- Every unordered product exists, even when the factors overlap. -/
theorem unordered_product_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U W : V) :
    HasMembers B.mem (fun t : V =>
      ∃ u w : V, B.mem u U ∧ B.mem w W ∧ IsUPair B.mem t u w) := by
  let m := B.mem
  obtain ⟨D, hD⟩ := binary_union_exists m H U W
  have hUD : ∀ x : V, m x U → m x D := by
    intro x hx
    exact (hD x).mpr (Or.inl hx)
  have hWD : ∀ x : V, m x W → m x D := by
    intro x hx
    exact (hD x).mpr (Or.inr hx)
  obtain ⟨FU, hFU⟩ := local_fan_without_foundation B H U D hUD
  obtain ⟨FW, hFW⟩ := local_fan_without_foundation B H W D hWD
  obtain ⟨R, hR⟩ := H.intersection FU FW
  refine ⟨R, ?_⟩
  intro t
  rw [hR t]
  constructor
  · rintro ⟨htFU, htFW⟩
    obtain ⟨a, c, haU, hcD, hac⟩ := (hFU t).mp htFU
    obtain ⟨b, d, hbW, hdD, hbd⟩ := (hFW t).mp htFW
    have hbT : m b t := (hbd b).mpr (Or.inl rfl)
    rcases (hac b).mp hbT with hba | hbc
    · have haW : m a W := by simpa [hba] using hbW
      rcases (hD c).mp hcD with hcU | hcW
      · exact ⟨c, a, hcU, haW, isUPair_flip m hac⟩
      · exact ⟨a, c, haU, hcW, hac⟩
    · have hcW : m c W := by simpa [hbc] using hbW
      exact ⟨a, c, haU, hcW, hac⟩
  · rintro ⟨a, c, haU, hcW, hac⟩
    constructor
    · exact (hFU t).mpr ⟨a, c, haU, hWD c hcW, hac⟩
    · exact (hFW t).mpr ⟨c, a, hcW, hUD a haU, isUPair_flip m hac⟩

end NineAxiomBZ.NoFoundation
