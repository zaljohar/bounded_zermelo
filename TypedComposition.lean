import NineAxiomCore
/-!
# Composition of typed unordered relations

This algebraic lemma is the mechanism that turns undirected composition
into a *directed* relational join.  When the three coordinate sorts are
pairwise disjoint, the three unwanted endpoint orientations are impossible.

No separation axiom, `sorry`, or graph-construction postulate is used.
NOT YET ELABORATED: the runtime has no Lean toolchain.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Cross-disjointness of two (object-level) sets. -/
def DisjointSort (m : V → V → Prop) (U W : V) : Prop :=
  ∀ u w : V, m u U → m w W → u ≠ w

/-- A set of undirected cross-pairs, interpreted as directed edges from
`U` to `W` by the separation of the two sorts. -/
def TypedEdges (m : V → V → Prop)
    (U W : V) (R : V → V → Prop) (E : V) : Prop :=
  ∀ p : V, m p E ↔
    ∃ u w : V, m u U ∧ m w W ∧ IsUPair m p u w ∧ R u w

/-- Exact relational composition: for pairwise disjoint sorts U,W,Z,
composition of U-to-W and W-to-Z relations has exactly the intended
U-to-Z edges and no extra orientations. -/
theorem typed_composition_exists
    (B : Background V) (H : NineAxioms B.mem)
    (U W Z E F : V) (R S : V → V → Prop)
    (hUW : DisjointSort B.mem U W)
    (hUZ : DisjointSort B.mem U Z)
    (hWZ : DisjointSort B.mem W Z)
    (hE : TypedEdges B.mem U W R E)
    (hF : TypedEdges B.mem W Z S F) :
    HasMembers B.mem (fun p : V =>
      ∃ u z : V, B.mem u U ∧ B.mem z Z ∧
        IsUPair B.mem p u z ∧
        ∃ w : V, B.mem w W ∧ R u w ∧ S w z) := by
  obtain ⟨C, hC⟩ := H.unorderedComposition E F
  refine ⟨C, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨a, b, c, hpac, ⟨e, heE, heab⟩,
      ⟨f, hfF, hfbc⟩⟩ := (hC p).1 hp
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
        have huz : u = z := hbu.symm.trans hbz
        exact False.elim (hUZ u z huU hzZ huz)
  · rintro ⟨u, z, huU, hzZ, hpuz, w, hwW, hRuw, hSwz⟩
    obtain ⟨e, he⟩ := unordered_pair_exists B.mem H u w
    obtain ⟨f, hf⟩ := unordered_pair_exists B.mem H w z
    have heE : B.mem e E := (hE e).2 ⟨u, w, huU, hwW, he, hRuw⟩
    have hfF : B.mem f F := (hF f).2 ⟨w, z, hwW, hzZ, hf, hSwz⟩
    exact (hC p).2 ⟨u, w, z, hpuz,
      ⟨e, heE, he⟩, ⟨f, hfF, hf⟩⟩

end NineAxiomBZ
