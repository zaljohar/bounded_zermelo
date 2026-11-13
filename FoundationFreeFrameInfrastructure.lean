import FoundationFreePrefixProjection
import TypedComposition

/-!
# Foundation-free finite frame infrastructure

All new existence assertions below are derived from `NineAxioms`, not from
Foundation, Separation, Replacement or an assumed finite-frame compiler.

This is a proof draft pending Lean elaboration.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- A finite, externally indexed family can be collected without Replacement. -/
theorem finite_family_range_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    ∀ (n : Nat) (f : Fin n → V),
      HasMembers B.mem (fun x : V => ∃ i : Fin n, x = f i) := by
  intro n
  induction n with
  | zero =>
      intro f
      obtain ⟨e, he⟩ := H.empty
      refine ⟨e, ?_⟩
      intro x
      constructor
      · intro hx
        exact False.elim ((he x).mp hx)
      · rintro ⟨i, _⟩
        exact i.elim0
  | succ n ih =>
      intro f
      obtain ⟨tailSet, hTail⟩ := ih (fun i : Fin n => f i.succ)
      obtain ⟨headSet, hHead⟩ := H.singleton (f 0)
      obtain ⟨all, hAll⟩ := binary_union_exists B.mem H headSet tailSet
      refine ⟨all, ?_⟩
      intro x
      constructor
      · intro hx
        rcases (hAll x).mp hx with hh | ht
        · exact ⟨0, (hHead x).mp hh⟩
        · obtain ⟨i, hi⟩ := (hTail x).mp ht
          exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero => exact (hAll x).mpr (Or.inl ((hHead x).mpr hi))
        | succ j =>
            exact (hAll x).mpr (Or.inr ((hTail x).mpr ⟨j, hi⟩))

/-- Construct a common finite registry for all older sorts and both seeds. -/
theorem finite_registry_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (n k : Nat) (f : Fin n → V) (g : Fin k → V)
    (X T : V) :
    ∃ W : V, B.mem X W ∧ B.mem T W ∧
      (∀ i : Fin n, B.mem (f i) W) ∧
      (∀ j : Fin k, B.mem (g j) W) := by
  obtain ⟨F, hF⟩ := finite_family_range_exists_nf B H n f
  obtain ⟨G, hG⟩ := finite_family_range_exists_nf B H k g
  obtain ⟨FG, hFG⟩ := binary_union_exists B.mem H F G
  obtain ⟨XT, hXT⟩ := unordered_pair_exists B.mem H X T
  obtain ⟨W, hW⟩ := binary_union_exists B.mem H FG XT
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact (hW X).mpr (Or.inr ((hXT X).mpr (Or.inl rfl)))
  · exact (hW T).mpr (Or.inr ((hXT T).mpr (Or.inr rfl)))
  · intro i
    exact (hW (f i)).mpr (Or.inl ((hFG (f i)).mpr
      (Or.inl ((hF (f i)).mpr ⟨i, rfl⟩))))
  · intro j
    exact (hW (g j)).mpr (Or.inl ((hFG (g j)).mpr
      (Or.inr ((hG (g j)).mpr ⟨j, rfl⟩))))

/-- Same typed unordered-relational composition theorem as in the original
proof, but over a background containing NO Foundation. -/
theorem typed_composition_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U W Z E F : V) (R S : V → V → Prop)
    (hUW : DisjointSortNF B.mem U W)
    (hUZ : DisjointSortNF B.mem U Z)
    (hWZ : DisjointSortNF B.mem W Z)
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
      ⟨f, hfF, hfbc⟩⟩ := (hC p).mp hp
    obtain ⟨u, w, huU, hwW, heuw, hRuw⟩ := (hE e).mp heE
    obtain ⟨w', z, hw'W, hzZ, hfwz, hSwz⟩ := (hF f).mp hfF
    rcases unordered_pair_endpoints_nf B heab heuw with h | h
    · rcases h with ⟨hau, hbw⟩
      rcases unordered_pair_endpoints_nf B hfbc hfwz with h' | h'
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
      rcases unordered_pair_endpoints_nf B hfbc hfwz with h' | h'
      · rcases h' with ⟨hbw', hcz⟩
        have huw' : u = w' := hbu.symm.trans hbw'
        exact False.elim (hUW u w' huU hw'W huw')
      · rcases h' with ⟨hbz, hcw'⟩
        have huz : u = z := hbu.symm.trans hbz
        exact False.elim (hUZ u z huU hzZ huz)
  · rintro ⟨u, z, huU, hzZ, hpuz, w, hwW, hRuw, hSwz⟩
    obtain ⟨e, he⟩ := unordered_pair_exists B.mem H u w
    obtain ⟨f, hf⟩ := unordered_pair_exists B.mem H w z
    have heE : B.mem e E := (hE e).mpr
      ⟨u, w, huU, hwW, he, hRuw⟩
    have hfF : B.mem f F := (hF f).mpr
      ⟨w, z, hwW, hzZ, hf, hSwz⟩
    exact (hC p).mpr ⟨u, w, z, hpuz,
      ⟨e, heE, he⟩, ⟨f, hfF, hf⟩⟩

/-- Lift the complete finite family of old projections along one freshly
constructed prefix graph.  This is an external finite choice, not set-level
Replacement and not an added axiom. -/
theorem lift_finite_coordinate_projections_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (n : Nat) (T N : V) (U : Fin n → V)
    (Γ : V) (P : Fin n → V)
    (pref : V → V → Prop)
    (coord : Fin n → V → V → Prop)
    (hNT : DisjointSortNF B.mem N T)
    (hNU : ∀ i : Fin n, DisjointSortNF B.mem N (U i))
    (hTU : ∀ i : Fin n, DisjointSortNF B.mem T (U i))
    (hΓ : TypedEdges B.mem N T pref Γ)
    (hP : ∀ i : Fin n, TypedEdges B.mem T (U i) (coord i) (P i)) :
    ∃ Q : Fin n → V, ∀ i : Fin n,
      TypedEdges B.mem N (U i)
        (fun t u => ∃ s : V, B.mem s T ∧ pref t s ∧ coord i s u)
        (Q i) := by
  classical
  have hEach (i : Fin n) :
      ∃ Q : V, TypedEdges B.mem N (U i)
        (fun t u => ∃ s : V,
          B.mem s T ∧ pref t s ∧ coord i s u) Q := by
    exact typed_composition_exists_nf B H N T (U i)
      Γ (P i) pref (coord i)
      hNT (hNU i) (hTU i) hΓ (hP i)
  refine ⟨(fun i => Classical.choose (hEach i)), ?_⟩
  intro i
  exact Classical.choose_spec (hEach i)

/-- Uniqueness of a two-sort unordered tuple.  No membership acyclicity
is needed: the distinct, disjoint endpoint sorts already orient it. -/
theorem disjoint_unordered_tuple_unique_nf
    (B : BackgroundNoFoundation V) (T F : V)
    (hTF : DisjointSortNF B.mem T F)
    (t s f s' f' : V)
    (hs : B.mem s T) (hf : B.mem f F)
    (hs' : B.mem s' T) (hf' : B.mem f' F)
    (h : IsUPair B.mem t s f)
    (h' : IsUPair B.mem t s' f') :
    s = s' ∧ f = f' := by
  rcases unordered_pair_endpoints_nf B h h' with hSame | hSwap
  · exact hSame
  · exact False.elim (hTF s f' hs hf' hSwap.1)

/-- A tagged pair `{a,m}` uniquely determines `a`, even if `a=m`.
This is a pure consequence of unordered-pair extensionality. -/
theorem tagged_pair_payload_unique_nf
    (B : BackgroundNoFoundation V) (f x y m : V)
    (hx : IsUPair B.mem f x m)
    (hy : IsUPair B.mem f y m) : x = y := by
  rcases unordered_pair_endpoints_nf B hx hy with h | h
  · exact h.1
  · exact h.1.trans h.2

end NineAxiomBZ.NoFoundation
