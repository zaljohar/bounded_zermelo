import TypedComposition
import RelationProjection
/-!
# Existential image of a typed relation

This packages `RelationProjection` with `TypedEdges`, giving exactly the
image of a subset S of the source sort under a typed undirected edge set.
It is the final projection needed after the bounded-formula truth compiler.

No Separation instance or hidden comprehension principle is assumed.
NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Exact existential image under a relation between disjoint sorts. -/
theorem typed_relational_image_exists
    (B : Background V) (H : NineAxioms B.mem)
    (T U E S : V) (R : V → V → Prop)
    (hST : ∀ x : V, B.mem x S → B.mem x T)
    (hTU : DisjointSort B.mem T U)
    (hE : TypedEdges B.mem T U R E) :
    HasMembers B.mem (fun u : V =>
      B.mem u U ∧ ∃ t : V, B.mem t S ∧ R t u) := by
  obtain ⟨Q, hQ⟩ :=
    relational_image_exists B H T U E S hST hTU
  refine ⟨Q, ?_⟩
  intro u
  constructor
  · intro huQ
    obtain ⟨huU, t, p, htS, hpE, hptu⟩ := (hQ u).1 huQ
    obtain ⟨t', u', ht'T, hu'U, hpt'u', hRt'u'⟩ := (hE p).1 hpE
    rcases unordered_pair_endpoints B hptu hpt'u' with h | h
    · rcases h with ⟨htt', huu'⟩
      refine ⟨huU, t, htS, ?_⟩
      simpa only [htt', huu'] using hRt'u'
    · rcases h with ⟨htu', hut'⟩
      have htT : B.mem t T := hST t htS
      exact False.elim (hTU t u' htT hu'U htu')
  · rintro ⟨huU, t, htS, hRtu⟩
    obtain ⟨p, hp⟩ := unordered_pair_exists B.mem H t u
    have htT : B.mem t T := hST t htS
    have hpE : B.mem p E :=
      (hE p).2 ⟨t, u, htT, huU, hp, hRtu⟩
    exact (hQ u).2 ⟨huU, t, p, htS, hpE, hp⟩

/-- A pair of typed relations can successively project an assignment set
through its coordinate tag and then back to the raw coordinate value. -/
theorem two_step_typed_image_exists
    (B : Background V) (H : NineAxioms B.mem)
    (T U D P E S : V) (R : V → V → Prop) (Q : V → V → Prop)
    (hST : ∀ t : V, B.mem t S → B.mem t T)
    (hTU : DisjointSort B.mem T U)
    (hUD : DisjointSort B.mem U D)
    (hP : TypedEdges B.mem T U R P)
    (hE : TypedEdges B.mem U D Q E) :
    HasMembers B.mem (fun d : V =>
      B.mem d D ∧
      ∃ t u : V, B.mem t S ∧ B.mem u U ∧ R t u ∧ Q u d) := by
  obtain ⟨Y, hY⟩ :=
    typed_relational_image_exists B H T U P S R hST hTU hP
  have hYU : ∀ u : V, B.mem u Y → B.mem u U := by
    intro u hu
    exact ((hY u).1 hu).1
  obtain ⟨Z, hZ⟩ :=
    typed_relational_image_exists B H U D E Y Q hYU hUD hE
  refine ⟨Z, ?_⟩
  intro d
  constructor
  · intro hd
    obtain ⟨hdD, u, huY, hQud⟩ := (hZ d).1 hd
    obtain ⟨huU, t, htS, hRtu⟩ := (hY u).1 huY
    exact ⟨hdD, t, u, htS, huU, hRtu, hQud⟩
  · rintro ⟨hdD, t, u, htS, huU, hRtu, hQud⟩
    have huY : B.mem u Y := (hY u).2 ⟨huU, t, htS, hRtu⟩
    exact (hZ d).2 ⟨hdD, u, huY, hQud⟩

end NineAxiomBZ
