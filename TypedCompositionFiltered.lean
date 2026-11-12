import TypedComposition
/-!
# A typed relational join with the SAME source and target sort

The original `typed_composition_exists` assumed three pairwise-disjoint
sorts.  That is too strong for the diagonal truth-set construction, where
the source and target can both be the assignment sort `T`.

This lemma removes the unnecessary hypothesis `DisjointSort U Z`: it
intersects the unordered composition with `U*Z`.  Wrongly oriented paths
have both endpoints in the middle sort `W`, hence are removed by the filter.

This is a new substantive proof step, not an axiom or a sorry.
NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Composition with a final U-to-Z edge filter. No disjointness between
U and Z is needed (in particular U=Z is permitted). -/
theorem typed_composition_filtered_exists
    (B : Background V) (H : NineAxioms B.mem)
    (U W Z E F : V) (R S : V → V → Prop)
    (hUW : DisjointSort B.mem U W)
    (hWZ : DisjointSort B.mem W Z)
    (hE : TypedEdges B.mem U W R E)
    (hF : TypedEdges B.mem W Z S F) :
    HasMembers B.mem (fun p : V =>
      ∃ u z : V, B.mem u U ∧ B.mem z Z ∧
        IsUPair B.mem p u z ∧
        ∃ w : V, B.mem w W ∧ R u w ∧ S w z) := by
  obtain ⟨C, hC⟩ := H.unorderedComposition E F
  obtain ⟨Q, hQ⟩ := unordered_product_exists B H U Z
  obtain ⟨I, hI⟩ := H.intersection C Q
  refine ⟨I, ?_⟩
  intro p
  constructor
  · intro hp
    have hpC : B.mem p C := ((hI p).1 hp).1
    have hpQ : B.mem p Q := ((hI p).1 hp).2
    obtain ⟨u0, z0, hu0, hz0, hpu0z0⟩ := (hQ p).1 hpQ
    obtain ⟨a, b, c, hpac, ⟨e, heE, heab⟩,
      ⟨f, hfF, hfbc⟩⟩ := (hC p).1 hpC
    obtain ⟨u, w, huU, hwW, heuw, hRuw⟩ := (hE e).1 heE
    obtain ⟨w', z, hw'W, hzZ, hfwz, hSwz⟩ := (hF f).1 hfF
    rcases unordered_pair_endpoints B heab heuw with h | h
    · rcases h with ⟨hau, hbw⟩
      rcases unordered_pair_endpoints B hfbc hfwz with h' | h'
      · rcases h' with ⟨hbw', hcz⟩
        have hww' : w = w' := hbw.symm.trans hbw'
        refine ⟨u, z, huU, hzZ, ?_, w, hwW, hRuw, ?_⟩
        · intro x
          simpa only [hau, hcz] using hpac x
        · simpa only [hww'] using hSwz
      · rcases h' with ⟨hbz, hcw'⟩
        have hwz : w = z := hbw.symm.trans hbz
        exact False.elim (hWZ w z hwW hzZ hwz)
    · rcases h with ⟨haw, hbu⟩
      rcases unordered_pair_endpoints B hfbc hfwz with h' | h'
      · rcases h' with ⟨hbw', hcz⟩
        have huw' : u = w' := hbu.symm.trans hbw'
        exact False.elim (hUW u w' huU hw'W huw')
      · rcases h' with ⟨hbz, hcw'⟩
        rcases unordered_pair_endpoints B hpac hpu0z0 with h'' | h''
        · rcases h'' with ⟨hau0, _⟩
          have hwu0 : w = u0 := haw.symm.trans hau0
          exact False.elim (hUW u0 w hu0 hwW hwu0.symm)
        · rcases h'' with ⟨haz0, _⟩
          have hwz0 : w = z0 := haw.symm.trans haz0
          exact False.elim (hWZ w z0 hwW hz0 hwz0)
  · rintro ⟨u, z, huU, hzZ, hpuz, w, hwW, hRuw, hSwz⟩
    obtain ⟨e, he⟩ := unordered_pair_exists B.mem H u w
    obtain ⟨f, hf⟩ := unordered_pair_exists B.mem H w z
    have heE : B.mem e E := (hE e).2 ⟨u, w, huU, hwW, he, hRuw⟩
    have hfF : B.mem f F := (hF f).2 ⟨w, z, hwW, hzZ, hf, hSwz⟩
    have hpC : B.mem p C := (hC p).2 ⟨u, w, z, hpuz,
      ⟨e, heE, he⟩, ⟨f, hfF, hf⟩⟩
    have hpQ : B.mem p Q := (hQ p).2 ⟨u, z, huU, hzZ, hpuz⟩
    exact (hI p).2 ⟨hpC, hpQ⟩

end NineAxiomBZ
