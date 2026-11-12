import NineAxiomCore
/-!
# Injectivity of a tagged copy and no self-membership

These lemmas guarantee that the unordered encoding does not identify
values in the same coordinate, and dispose of the diagonal membership
atom `v_i ∈ v_i` in a Foundation model.

No Separation or unproved lemma is introduced.
NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- An unordered tagged copy `{a,m}` is injective on any domain not
containing its marker `m`. -/
theorem tagged_value_injective
    (B : Background V) (H : NineAxioms B.mem)
    (D m a b ua ub : V)
    (hmD : ¬ B.mem m D)
    (ha : B.mem a D) (hb : B.mem b D)
    (hua : IsUPair B.mem ua a m)
    (hub : IsUPair B.mem ub b m)
    (h : ua = ub) : a = b := by
  have hua' : IsUPair B.mem ua b m := by
    simpa only [h] using hub
  rcases unordered_pair_endpoints B hua hua' with hpair | hswap
  · exact hpair.1
  · rcases hswap with ⟨ham, hmb⟩
    exact False.elim (hmD (ham ▸ ha))

/-- First-order Foundation already excludes `x∈x`: the proof uses the
existence of the singleton from axiom 2. -/
theorem no_self_membership_for_tags
    (B : Background V) (H : NineAxioms B.mem) (a : V) :
    ¬ B.mem a a := by
  intro haa
  obtain ⟨s, hs⟩ := H.singleton a
  have has : B.mem a s := (hs a).2 rfl
  obtain ⟨x, hxs, hminimal⟩ := B.foundation s ⟨a, has⟩
  have hxa : x = a := (hs x).1 hxs
  subst x
  exact (hminimal a has) haa

end NineAxiomBZ
