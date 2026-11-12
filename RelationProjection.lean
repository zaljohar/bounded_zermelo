import NineAxiomCore
/-!
Existential image/projection along an unordered binary relation joining
disjoint source and target sorts. The construction uses only unordered
products, intersection, setUnion and intersection again.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The image of a subset S of T under an arbitrary edge set P is constructible
when T and U are disjoint. It is crucial that this lemma makes NO bounded
Separation assumption. -/
theorem relational_image_exists
    (B : Background V) (H : NineAxioms B.mem)
    (T U P S : V)
    (hSU : ∀ x : V, B.mem x S → B.mem x T)
    (hTU : ∀ t u : V, B.mem t T → B.mem u U → t ≠ u) :
    HasMembers B.mem (fun u : V => B.mem u U ∧
      ∃ t p : V, B.mem t S ∧ B.mem p P ∧
        IsUPair B.mem p t u) := by
  obtain ⟨Q, hQ⟩ := unordered_product_exists B H S U
  obtain ⟨I, hI⟩ := H.intersection P Q
  obtain ⟨R, hR⟩ := H.setUnion I
  obtain ⟨D, hD⟩ := H.intersection U R
  refine ⟨D, ?_⟩
  intro u
  constructor
  · intro huD
    have huU : B.mem u U := ((hD u).1 huD).1
    have huR : B.mem u R := ((hD u).1 huD).2
    obtain ⟨p, hpI, hup⟩ := (hR u).1 huR
    have hpP : B.mem p P := ((hI p).1 hpI).1
    have hpQ : B.mem p Q := ((hI p).1 hpI).2
    obtain ⟨t, v, htS, hvU, hptv⟩ := (hQ p).1 hpQ
    rcases (hptv u).1 hup with hut | huv
    · have htT : B.mem t T := hSU t htS
      exact False.elim (hTU t u htT huU hut.symm)
    · subst v
      exact ⟨huU, t, p, htS, hpP, hptv⟩
  · rintro ⟨huU, t, p, htS, hpP, hptu⟩
    have hpQ : B.mem p Q := (hQ p).2 ⟨t, u, htS, huU, hptu⟩
    have hpI : B.mem p I := (hI p).2 ⟨hpP, hpQ⟩
    have huR : B.mem u R := (hR u).2 ⟨p, hpI, (hptu u).2 (Or.inr rfl)⟩
    exact (hD u).2 ⟨huU, huR⟩

end NineAxiomBZ
