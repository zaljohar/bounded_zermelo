import FiniteFoundation
import PrefixGraph
/-!
A fresh extension of a tuple-sort T by a tagged copy of X; existence
of the exact first-coordinate (prefix) projection graph follows from
Foundation plus the nine axioms.

This is the local induction step; the finite tower and formula compiler
are not yet assembled here.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Extend a tuple sort `T` by fresh tags from `X`. The new sort N is the
unordered product of T and the new tagged-coordinate sort F. -/
theorem fresh_prefix_step_exists
    (B : Background V) (H : NineAxioms B.mem)
    (X T W : V) (hXW : B.mem X W) (hTW : B.mem T W) :
    ∃ (m F N Γ : V),
      (∀ z : V, B.mem z m ↔ z = W) ∧
      (∀ f : V, B.mem f F ↔
        ∃ x : V, B.mem x X ∧ IsUPair B.mem f x m) ∧
      (∀ t : V, B.mem t N ↔
        ∃ s f : V, B.mem s T ∧ B.mem f F ∧ IsUPair B.mem t s f) ∧
      (∀ p : V, B.mem p Γ ↔
        ∃ t s f : V, B.mem t N ∧ B.mem s T ∧ B.mem f F ∧
          IsUPair B.mem t s f ∧ IsUPair B.mem p t s) := by
  obtain ⟨m, hm⟩ := H.singleton W
  have hWm : B.mem W m := (hm W).2 rfl
  have hmX : ¬ B.mem m X := by
    intro hmX
    exact no_membership_three_cycle B H m X W ⟨hmX, hXW, hWm⟩
  obtain ⟨F, hF⟩ := corrected_fan_exists B H X m hmX
  obtain ⟨N, hN⟩ := unordered_product_exists B H T F
  have hTF : ∀ s f : V, B.mem s T → B.mem f F → s ≠ f := by
    intro s f hsT hfF hsf
    obtain ⟨x, hxX, hfxm⟩ := (hF f).1 hfF
    have hmf : B.mem m f := (hfxm m).2 (Or.inr rfl)
    have hfT : B.mem f T := hsf ▸ hsT
    exact no_membership_four_cycle B H m f T W
      ⟨hmf, hfT, hTW, hWm⟩
  have hreverse : ∀ t s : V, B.mem t N → B.mem s T → ¬ B.mem t s := by
    intro t s htN hsT hts
    obtain ⟨s0, f, hs0T, hfF, hts0f⟩ := (hN t).1 htN
    obtain ⟨x, hxX, hfxm⟩ := (hF f).1 hfF
    have hmf : B.mem m f := (hfxm m).2 (Or.inr rfl)
    have hft : B.mem f t := (hts0f f).2 (Or.inr rfl)
    exact no_membership_six_cycle B H m f t s T W
      ⟨hmf, hft, hts, hsT, hTW, hWm⟩
  obtain ⟨Γ, hΓ⟩ := first_coordinate_graph_exists B H T F N hN hTF hreverse
  exact ⟨m, F, N, Γ, hm, hF, hN, hΓ⟩

end NineAxiomBZ

namespace NineAxiomBZ
variable {V : Type u}

/-- At every new tuple level we can construct BOTH projections: the prefix
and the newly appended coordinate. -/
theorem fresh_both_projections_exist
    (B : Background V) (H : NineAxioms B.mem)
    (X T W : V) (hXW : B.mem X W) (hTW : B.mem T W) :
    ∃ (m F N Γ Λ : V),
      (∀ z : V, B.mem z m ↔ z = W) ∧
      (∀ f : V, B.mem f F ↔
        ∃ x : V, B.mem x X ∧ IsUPair B.mem f x m) ∧
      (∀ t : V, B.mem t N ↔
        ∃ s f : V, B.mem s T ∧ B.mem f F ∧ IsUPair B.mem t s f) ∧
      (∀ p : V, B.mem p Γ ↔
        ∃ t s f : V, B.mem t N ∧ B.mem s T ∧ B.mem f F ∧
          IsUPair B.mem t s f ∧ IsUPair B.mem p t s) ∧
      (∀ p : V, B.mem p Λ ↔
        ∃ t s f : V, B.mem t N ∧ B.mem s T ∧ B.mem f F ∧
          IsUPair B.mem t s f ∧ IsUPair B.mem p t f) := by
  obtain ⟨m, F, N, Γ, hm, hF, hN, hΓ⟩ :=
    fresh_prefix_step_exists B H X T W hXW hTW
  have hWm : B.mem W m := (hm W).2 rfl
  have hTF : ∀ s f : V, B.mem s T → B.mem f F → s ≠ f := by
    intro s f hsT hfF hsf
    obtain ⟨x, hxX, hfxm⟩ := (hF f).1 hfF
    have hmf : B.mem m f := (hfxm m).2 (Or.inr rfl)
    have hfT : B.mem f T := hsf ▸ hsT
    exact no_membership_four_cycle B H m f T W
      ⟨hmf, hfT, hTW, hWm⟩
  have hNswap : ∀ t : V, B.mem t N ↔
      ∃ f s : V, B.mem f F ∧ B.mem s T ∧ IsUPair B.mem t f s := by
    intro t
    constructor
    · intro ht
      obtain ⟨s, f, hs, hf, htsf⟩ := (hN t).1 ht
      refine ⟨f, s, hf, hs, ?_⟩
      intro z
      constructor
      · intro hz
        rcases (htsf z).1 hz with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hz
        rcases hz with h | h
        · exact (htsf z).2 (Or.inr h)
        · exact (htsf z).2 (Or.inl h)
    · rintro ⟨f, s, hf, hs, htfs⟩
      apply (hN t).2
      refine ⟨s, f, hs, hf, ?_⟩
      intro z
      constructor
      · intro hz
        rcases (htfs z).1 hz with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hz
        rcases hz with h | h
        · exact (htfs z).2 (Or.inr h)
        · exact (htfs z).2 (Or.inl h)
  have hreverseF : ∀ t f0 : V, B.mem t N → B.mem f0 F →
      ¬ B.mem t f0 := by
    intro t f0 htN hf0 htf0
    obtain ⟨s, f, hs, hf, htsf⟩ := (hN t).1 htN
    obtain ⟨x0, hx0, hf0pair⟩ := (hF f0).1 hf0
    obtain ⟨x, hx, hfpair⟩ := (hF f).1 hf
    have hmf : B.mem m f := (hfpair m).2 (Or.inr rfl)
    have hft : B.mem f t := (htsf f).2 (Or.inr rfl)
    rcases (hf0pair t).1 htf0 with htx | htm
    · have htX : B.mem t X := htx ▸ hx0
      exact no_membership_five_cycle B H m f t X W
        ⟨hmf, hft, htX, hXW, hWm⟩
    · have hfm : B.mem f m := htm ▸ hft
      exact no_membership_two_cycle B H m f ⟨hmf, hfm⟩
  have hFT : ∀ f s : V, B.mem f F → B.mem s T → f ≠ s := by
    intro f s hf hs hfs
    exact hTF s f hs hf hfs.symm
  obtain ⟨Λ, hΛ⟩ := first_coordinate_graph_exists B H F T N
    hNswap hFT hreverseF
  refine ⟨m, F, N, Γ, Λ, hm, hF, hN, hΓ, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨t, f, s, htN, hf, hs, htfs, hptf⟩ := (hΛ p).1 hp
    refine ⟨t, s, f, htN, hs, hf, ?_, hptf⟩
    intro z
    constructor
    · intro hz
      rcases (htfs z).1 hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro hz
      rcases hz with h | h
      · exact (htfs z).2 (Or.inr h)
      · exact (htfs z).2 (Or.inl h)
  · rintro ⟨t, s, f, htN, hs, hf, htsf, hptf⟩
    apply (hΛ p).2
    refine ⟨t, f, s, htN, hf, hs, ?_, hptf⟩
    intro z
    constructor
    · intro hz
      rcases (htsf z).1 hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro hz
      rcases hz with h | h
      · exact (htsf z).2 (Or.inr h)
      · exact (htsf z).2 (Or.inl h)

end NineAxiomBZ
