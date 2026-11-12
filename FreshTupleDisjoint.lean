import FreshSupportDisjoint
import TagUniqueness
/-!
# Fresh tuple codes do not collide with their last-coordinate tags

`FreshSupportDisjoint` already proves the new tuple sort is disjoint from
all registered old sorts. Here we also prove that it is disjoint from the
NEW tagged-coordinate sort produced at the same step. This is necessary
to use the last-coordinate relation as a typed graph.

No bounded separation or tuple-frame existence is assumed.
DRAFT: not elaborated; the runtime has no Lean toolchain.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Suppose `m={W}`, T∈W, F={ {x,m}: x∈X }, and N=T*F.
Then N and F are disjoint, by first-order Foundation. -/
theorem fresh_tuple_tag_disjoint
    (B : Background V) (H : NineAxioms B.mem)
    (X T W m F N : V)
    (hTW : B.mem T W)
    (hm : ∀ z : V, B.mem z m ↔ z = W)
    (hF : ∀ f : V, B.mem f F ↔
      ∃ x : V, B.mem x X ∧ IsUPair B.mem f x m)
    (hN : ∀ t : V, B.mem t N ↔
      ∃ s f : V, B.mem s T ∧ B.mem f F ∧
        IsUPair B.mem t s f) :
    DisjointSort B.mem N F := by
  intro t f htN hfF htf
  obtain ⟨s, f0, hsT, hf0F, htsf⟩ := (hN t).mp htN
  obtain ⟨x, _hxX, hfx⟩ := (hF f).mp hfF
  obtain ⟨y, _hyX, hf0y⟩ := (hF f0).mp hf0F
  have hWm : B.mem W m := (hm W).mpr rfl
  have hmf : B.mem m f := (hfx m).mpr (Or.inr rfl)
  have hmt : B.mem m t := by simpa only [htf] using hmf
  rcases (htsf m).mp hmt with hms | hmf0
  · have hmT : B.mem m T := by simpa only [hms] using hsT
    exact no_membership_three_cycle B H m T W
      ⟨hmT, hTW, hWm⟩
  · have hm_f0 : B.mem m f0 := (hf0y m).mpr (Or.inr rfl)
    have hmm : B.mem m m := by simpa only [hmf0] using hm_f0
    exact no_self_membership_for_tags B H m hmm

/-- The immediate output of `fresh_both_projections_with_support` has
pairwise disjoint source tuple, last-tag, and new tuple sorts. -/
theorem fresh_three_sorts_disjoint
    (B : Background V) (H : NineAxioms B.mem)
    (X T W m F N : V)
    (hXW : B.mem X W) (hTW : B.mem T W)
    (hm : ∀ z : V, B.mem z m ↔ z = W)
    (hF : ∀ f : V, B.mem f F ↔
      ∃ x : V, B.mem x X ∧ IsUPair B.mem f x m)
    (hN : ∀ t : V, B.mem t N ↔
      ∃ s f : V, B.mem s T ∧ B.mem f F ∧
        IsUPair B.mem t s f) :
    DisjointSort B.mem T F ∧
    DisjointSort B.mem N T ∧
    DisjointSort B.mem N F := by
  have hWm : B.mem W m := (hm W).mpr rfl
  have hTF : DisjointSort B.mem T F := by
    intro s f hsT hfF hsf
    obtain ⟨x, hxX, hfx⟩ := (hF f).mp hfF
    have hmf : B.mem m f := (hfx m).mpr (Or.inr rfl)
    have hfT : B.mem f T := by simpa only [hsf] using hsT
    exact no_membership_four_cycle B H m f T W
      ⟨hmf, hfT, hTW, hWm⟩
  have hNT : DisjointSort B.mem N T := by
    intro t s htN hsT hts
    obtain ⟨s0, f, hs0T, hfF, htsf⟩ := (hN t).mp htN
    obtain ⟨x, hxX, hfx⟩ := (hF f).mp hfF
    have hmf : B.mem m f := (hfx m).mpr (Or.inr rfl)
    have hft : B.mem f t := (htsf f).mpr (Or.inr rfl)
    have hfs : B.mem f s := by simpa only [hts] using hft
    exact no_membership_five_cycle B H m f s T W
      ⟨hmf, hfs, hsT, hTW, hWm⟩
  have hNF := fresh_tuple_tag_disjoint B H X T W m F N hTW hm hF hN
  exact ⟨hTF, hNT, hNF⟩

end NineAxiomBZ
