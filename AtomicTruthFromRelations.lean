import TypedCompositionFiltered
import DiagonalFilter
/-!
# Atomic truth sets from coordinate projections

Given a set T of complete assignments, two disjoint tagged coordinate
sorts U and W, projection relations P:T→U and Q:T→W, and an atomic
relation R:U→W, construct exactly the assignments satisfying R.

Uses: the two typed-composition lemmas and singleton-image diagonal
extraction.  No Separation schema or assumed truth-set compiler.

NOT YET ELABORATED: no Lean toolchain in this runtime.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Bounded binary atomic relations admit truth sets on any assignment space
when the two required coordinate projection graphs are available. -/
theorem atomic_truth_from_typed_edges
    (B : Background V) (H : NineAxioms B.mem)
    (T U W P Q E : V)
    (RP : V → V → Prop) (RQ : V → V → Prop)
    (RA : V → V → Prop)
    (hTU : DisjointSort B.mem T U)
    (hTW : DisjointSort B.mem T W)
    (hUW : DisjointSort B.mem U W)
    (hP : TypedEdges B.mem T U RP P)
    (hQ : TypedEdges B.mem T W RQ Q)
    (hE : TypedEdges B.mem U W RA E) :
    HasMembers B.mem (fun t : V =>
      B.mem t T ∧
      ∃ u w : V, B.mem u U ∧ B.mem w W ∧
        RP t u ∧ RA u w ∧ RQ t w) := by
  let RX : V → V → Prop := fun t w =>
    ∃ u : V, B.mem u U ∧ RP t u ∧ RA u w
  obtain ⟨D, hD⟩ :=
    typed_composition_exists B H T U W P E RP RA hTU hTW hUW hP hE
  have hDtyped : TypedEdges B.mem T W RX D := by
    intro p
    constructor
    · intro hp
      obtain ⟨t, w, htT, hwW, hptw, u, huU, hRP, hRA⟩ := (hD p).1 hp
      exact ⟨t, w, htT, hwW, hptw, u, huU, hRP, hRA⟩
    · rintro ⟨t, w, htT, hwW, hptw, u, huU, hRP, hRA⟩
      exact (hD p).2 ⟨t, w, htT, hwW, hptw, u, huU, hRP, hRA⟩
  have hQreverse :
      TypedEdges B.mem W T (fun w t => RQ t w) Q := by
    intro p
    constructor
    · intro hp
      obtain ⟨t, w, htT, hwW, hptw, hRQ⟩ := (hQ p).1 hp
      refine ⟨w, t, hwW, htT, ?_, hRQ⟩
      intro x
      constructor
      · intro hx
        rcases (hptw x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (hptw x).2 (Or.inr h)
        · exact (hptw x).2 (Or.inl h)
    · rintro ⟨w, t, hwW, htT, hpwt, hRQ⟩
      apply (hQ p).2
      refine ⟨t, w, htT, hwW, ?_, hRQ⟩
      intro x
      constructor
      · intro hx
        rcases (hpwt x).1 hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · intro hx
        rcases hx with h | h
        · exact (hpwt x).2 (Or.inr h)
        · exact (hpwt x).2 (Or.inl h)
  obtain ⟨Z, hZ⟩ :=
    typed_composition_filtered_exists B H T W T D Q
      RX (fun w t => RQ t w) hTW
      (fun w t hw ht hwt => hTW t w ht hw hwt.symm)
      hDtyped hQreverse
  obtain ⟨S, hS⟩ := diagonal_filter_exists B H T Z
  refine ⟨S, ?_⟩
  intro t
  constructor
  · intro htS
    obtain ⟨htT, e, heZ, hett⟩ := (hS t).1 htS
    obtain ⟨t0, t1, ht0T, ht1T, het0t1, w, hwW, hRX, hRQ⟩ :=
      (hZ e).1 heZ
    have ht0eq : t0 = t := by
      rcases unordered_pair_endpoints B het0t1 hett with h | h
      · exact h.1
      · exact h.1
    have ht1eq : t1 = t := by
      rcases unordered_pair_endpoints B het0t1 hett with h | h
      · exact h.2
      · exact h.2
    obtain ⟨u, huU, hRP, hRA⟩ := hRX
    refine ⟨htT, u, w, huU, hwW, ?_, hRA, ?_⟩
    · simpa only [ht0eq] using hRP
    · simpa only [ht1eq] using hRQ
  · rintro ⟨htT, u, w, huU, hwW, hRP, hRA, hRQ⟩
    obtain ⟨e, he⟩ := H.singleton t
    have hett : IsUPair B.mem e t t := by
      intro x
      constructor
      · intro hx
        exact Or.inl ((he x).1 hx)
      · intro hx
        rcases hx with hx | hx
        · exact (he x).2 hx
        · exact (he x).2 hx
    have heZ : B.mem e Z := (hZ e).2
      ⟨t, t, htT, htT, hett, w, hwW,
        ⟨u, huU, hRP, hRA⟩, hRQ⟩
    exact (hS t).2 ⟨htT, e, heZ, hett⟩

end NineAxiomBZ
