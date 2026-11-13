import FoundationFreeAcyclicMarker

/-!
# Foundation-free three-sort tuple extension

Given raw-prefix sort T and raw-value domain X, both registered as
members of a support set W, construct

  F = { {x,m} | x∈X }
  N = T * F = { {t,f} | t∈T, f∈F }

with T, F, N pairwise disjoint and with NO reversed membership
edges from N into either T or F.  The marker is a fresh, two-cycle-free
finite code constructed from a relative Russell set.  The original
proof of these statements invoked Foundation's 2- through 5-cycle
exclusion lemmas; the present proof makes none of those assumptions.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Disjoint coordinate sorts, with no Foundation premise. -/
def DisjointSortNF (m : V → V → Prop) (U W : V) : Prop :=
  ∀ u w : V, m u U → m w W → u ≠ w

/-- The separation invariants required for the next prefix/last-coordinate
projection step. -/
theorem fresh_three_sorts_without_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (X T W : V) (hXW : B.mem X W) (hTW : B.mem T W) :
    ∃ (marker F N : V),
      (∀ f : V, B.mem marker f → ¬ B.mem f marker) ∧
      (∀ f : V, B.mem f F ↔
        ∃ x : V, B.mem x X ∧ IsUPair B.mem f x marker) ∧
      (∀ n : V, B.mem n N ↔
        ∃ t f : V, B.mem t T ∧ B.mem f F ∧
          IsUPair B.mem n t f) ∧
      DisjointSortNF B.mem T F ∧
      DisjointSortNF B.mem N T ∧
      DisjointSortNF B.mem N F ∧
      (∀ n t : V, B.mem n N → B.mem t T → ¬ B.mem n t) ∧
      (∀ n f : V, B.mem n N → B.mem f F → ¬ B.mem n f) ∧
      (∀ Y : V, B.mem Y W →
        DisjointSortNF B.mem F Y ∧ DisjointSortNF B.mem N Y) ∧
      (∀ Y z : V, B.mem Y W → B.mem z Y → ¬ B.mem marker z) ∧
      (∀ Y : V, B.mem Y W → ¬ B.mem marker Y) ∧
      (∀ Y z v : V, B.mem Y W → B.mem z Y → B.mem v z →
        ¬ B.mem marker v) := by
  let m := B.mem
  obtain ⟨marker, hNoTwo, hFresh⟩ :=
    fresh_no_two_cycle_marker_at_depth B H W 6
  have havoid {z : V} (k : Nat) (hk : k ≤ 6)
      (hz : ReachableWithin m W k z) : ¬ m marker z :=
    hFresh z (reachableWithin_mono m W hk hz)
  have hnotX : ¬ m marker X :=
    havoid 0 (by omega) hXW
  obtain ⟨F, hF⟩ := corrected_fan_no_foundation B H X marker hnotX
  obtain ⟨N, hN⟩ := unordered_product_without_foundation B H T F

  have hmarker_f {f : V} (hf : m f F) : m marker f := by
    obtain ⟨x, _hx, hxf⟩ := (hF f).mp hf
    exact (hxf marker).mpr (Or.inr rfl)

  have hTF : DisjointSortNF m T F := by
    intro t f ht hf hEq
    have hfT : m f T := by simpa [hEq] using ht
    have hr : ReachableWithin m W 1 f :=
      Or.inr ⟨T, hTW, hfT⟩
    exact (havoid 1 (by omega) hr) (hmarker_f hf)

  have hNT : DisjointSortNF m N T := by
    intro n t hn ht hEq
    obtain ⟨t0, f0, ht0, hf0, hnPair⟩ := (hN n).mp hn
    have hf0n : m f0 n := (hnPair f0).mpr (Or.inr rfl)
    have hnT : m n T := by simpa [hEq] using ht
    have hnr : ReachableWithin m W 1 n :=
      Or.inr ⟨T, hTW, hnT⟩
    have hfr : ReachableWithin m W 2 f0 :=
      Or.inr ⟨n, hnr, hf0n⟩
    exact (havoid 2 (by omega) hfr) (hmarker_f hf0)

  have hNF : DisjointSortNF m N F := by
    intro n f0 hn hf0 hEq
    obtain ⟨t, f, ht, hf, hnPair⟩ := (hN n).mp hn
    obtain ⟨x0, hx0, hf0Pair⟩ := (hF f0).mp hf0
    have hfn : m f n := (hnPair f).mpr (Or.inr rfl)
    have hff0 : m f f0 := by simpa [hEq] using hfn
    rcases (hf0Pair f).mp hff0 with hfx | hfm
    · have hfX : m f X := by simpa [hfx] using hx0
      have hfr : ReachableWithin m W 1 f :=
        Or.inr ⟨X, hXW, hfX⟩
      exact (havoid 1 (by omega) hfr) (hmarker_f hf)
    · have hmSelf : m marker marker := by
        have hmF : m marker f := hmarker_f hf
        rw [hfm] at hmF
        exact hmF
      exact (hNoTwo marker hmSelf) hmSelf

  have hReverseNT : ∀ n t : V,
      m n N → m t T → ¬ m n t := by
    intro n t hn ht hnt
    obtain ⟨t0, f0, ht0, hf0, hnPair⟩ := (hN n).mp hn
    have hfn : m f0 n := (hnPair f0).mpr (Or.inr rfl)
    have htr : ReachableWithin m W 1 t :=
      Or.inr ⟨T, hTW, ht⟩
    have hnr : ReachableWithin m W 2 n :=
      Or.inr ⟨t, htr, hnt⟩
    have hfr : ReachableWithin m W 3 f0 :=
      Or.inr ⟨n, hnr, hfn⟩
    exact (havoid 3 (by omega) hfr) (hmarker_f hf0)

  have hReverseNF : ∀ n f0 : V,
      m n N → m f0 F → ¬ m n f0 := by
    intro n f0 hn hf0 hnf0
    obtain ⟨t, f, ht, hf, hnPair⟩ := (hN n).mp hn
    obtain ⟨x0, hx0, hf0Pair⟩ := (hF f0).mp hf0
    rcases (hf0Pair n).mp hnf0 with hnx | hnm
    · have hnX : m n X := by simpa [hnx] using hx0
      have hfn : m f n := (hnPair f).mpr (Or.inr rfl)
      have hnr : ReachableWithin m W 1 n :=
        Or.inr ⟨X, hXW, hnX⟩
      have hfr : ReachableWithin m W 2 f :=
        Or.inr ⟨n, hnr, hfn⟩
      exact (havoid 2 (by omega) hfr) (hmarker_f hf)
    · have hfm : m f marker := by
        have hfn : m f n := (hnPair f).mpr (Or.inr rfl)
        simpa [hnm] using hfn
      exact (hNoTwo f (hmarker_f hf)) hfm

  have hFreshOld : ∀ Y : V, m Y W →
      DisjointSortNF m F Y ∧ DisjointSortNF m N Y := by
    intro Y hYW
    constructor
    · intro f y hfF hyY hEq
      have hfY : m f Y := by simpa [hEq] using hyY
      have hfr : ReachableWithin m W 1 f :=
        Or.inr ⟨Y, hYW, hfY⟩
      exact (havoid 1 (by omega) hfr) (hmarker_f hfF)
    · intro n y hnN hyY hEq
      obtain ⟨t, f, ht, hf, hnPair⟩ := (hN n).mp hnN
      have hfn : m f n := (hnPair f).mpr (Or.inr rfl)
      have hnY : m n Y := by simpa [hEq] using hyY
      have hnr : ReachableWithin m W 1 n :=
        Or.inr ⟨Y, hYW, hnY⟩
      have hfr : ReachableWithin m W 2 f :=
        Or.inr ⟨n, hnr, hfn⟩
      exact (havoid 2 (by omega) hfr) (hmarker_f hf)

  have hMarkerFreshOld : ∀ Y z : V,
      m Y W → m z Y → ¬ m marker z := by
    intro Y z hYW hzY
    have hzr : ReachableWithin m W 1 z :=
      Or.inr ⟨Y, hYW, hzY⟩
    exact havoid 1 (by omega) hzr

  have hMarkerOutsideOld : ∀ Y : V, m Y W → ¬ m marker Y := by
    intro Y hYW
    exact havoid 0 (by omega) hYW
  have hMarkerDeepOld : ∀ Y z v : V,
      m Y W → m z Y → m v z → ¬ m marker v := by
    intro Y z v hYW hz hv
    have hzr : ReachableWithin m W 1 z :=
      Or.inr ⟨Y, hYW, hz⟩
    have hvr : ReachableWithin m W 2 v :=
      Or.inr ⟨z, hzr, hv⟩
    exact havoid 2 (by omega) hvr
  exact ⟨marker, F, N, hNoTwo, hF, hN,
    hTF, hNT, hNF, hReverseNT, hReverseNF,
    hFreshOld, hMarkerFreshOld, hMarkerOutsideOld, hMarkerDeepOld⟩

end NineAxiomBZ.NoFoundation
