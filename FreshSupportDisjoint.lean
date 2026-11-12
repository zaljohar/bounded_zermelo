import FreshPrefixStep
import TypedComposition
/-!
# One-step freshness relative to every old sort in the finite support

The previous fresh-prefix lemma only gave the prefix/last projection edges.
This strengthened construction also proves that all newly created tag and
tuple objects are fresh relative to *every* old sort Y∈W.

The proofs require only finite 4- and 5-cycle exclusions derived from
first-order Foundation, not an ambient well-foundedness assumption.

NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Building one fresh tagged coordinate and tuple level relative to a support
W proves disjointness from every previously registered sort `Y∈W`, as well
as freshness of the new marker from all its elements. -/
theorem fresh_both_projections_with_support
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
          IsUPair B.mem t s f ∧ IsUPair B.mem p t f) ∧
      (∀ Y : V, B.mem Y W →
        DisjointSort B.mem F Y ∧
        DisjointSort B.mem N Y ∧
        (∀ d : V, B.mem d Y → ¬ B.mem m d)) := by
  obtain ⟨m, F, N, Γ, Λ, hm, hF, hN, hΓ, hΛ⟩ :=
    fresh_both_projections_exist B H X T W hXW hTW
  refine ⟨m, F, N, Γ, Λ, hm, hF, hN, hΓ, hΛ, ?_⟩
  intro Y hYW
  have hWm : B.mem W m := (hm W).2 rfl
  constructor
  · intro f y hfF hyY hfy
    obtain ⟨x, hxX, hfxm⟩ := (hF f).1 hfF
    have hmf : B.mem m f := (hfxm m).2 (Or.inr rfl)
    have hfY : B.mem f Y := hfy.symm ▸ hyY
    exact no_membership_four_cycle B H m f Y W
      ⟨hmf, hfY, hYW, hWm⟩
  constructor
  · intro t y htN hyY hty
    obtain ⟨s, f, hsT, hfF, htsf⟩ := (hN t).1 htN
    obtain ⟨x, hxX, hfxm⟩ := (hF f).1 hfF
    have hmf : B.mem m f := (hfxm m).2 (Or.inr rfl)
    have hft : B.mem f t := (htsf f).2 (Or.inr rfl)
    have htY : B.mem t Y := hty.symm ▸ hyY
    exact no_membership_five_cycle B H m f t Y W
      ⟨hmf, hft, htY, hYW, hWm⟩
  · intro d hdY hmd
    exact no_membership_four_cycle B H m d Y W
      ⟨hmd, hdY, hYW, hWm⟩

end NineAxiomBZ
