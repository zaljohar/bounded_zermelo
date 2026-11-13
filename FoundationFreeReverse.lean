import FoundationFreeCore
/-!
# Foundation-free reverse implication (new proposed compilation target)
This is the reverse construction from the verified project, parameterized by
Extensionality and Power Set alone.  Crucially: the definitions and proof below
DO NOT assume Foundation.  The forward direction has NOT been obtained.
This file has NOT been compiled in the current environment.
-/

universe u
namespace NineAxiomBZ.NoFoundation

variable {V : Type u}

/-- Bounded Zermelo over the common Extensionality/Power Set background.
Any optional additional axiom (e.g., Infinity) may be added to both sides of
our equivalence without changing the proof. -/
structure BoundedZermeloCore (B : BackgroundNoFoundation V) : Prop where
  empty : HasMembers B.mem (fun _ : V => False)
  pairing : ∀ a b : V, HasMembers B.mem (fun x : V => x = a ∨ x = b)
  union : ∀ a : V, HasMembers B.mem (fun x : V =>
    ∃ y : V, B.mem y a ∧ B.mem x y)
  separation : BoundedSeparation B.mem

/-- Boolean disjunction, in the given `DeltaZero` syntax. -/
def dzOr {n : Nat} (φ ψ : DeltaZero n) : DeltaZero n :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Bounded universal quantification, in the given `DeltaZero` syntax. -/
def dzBall {n : Nat} (i : Fin n) (φ : DeltaZero (n + 1)) : DeltaZero n :=
  .neg (.bex i (.neg φ))

private theorem dzOr_holds (m : V → V → Prop) {n : Nat}
    (φ ψ : DeltaZero n) (ρ : Fin n → V) :
    (dzOr φ ψ).holds m ρ ↔ φ.holds m ρ ∨ ψ.holds m ρ := by
  classical
  change (¬ (¬ φ.holds m ρ ∧ ¬ ψ.holds m ρ)) ↔
    (φ.holds m ρ ∨ ψ.holds m ρ)
  tauto

private theorem dzBall_holds (m : V → V → Prop) {n : Nat}
    (i : Fin n) (φ : DeltaZero (n + 1)) (ρ : Fin n → V) :
    (dzBall i φ).holds m ρ ↔
      ∀ z : V, m z (ρ i) → φ.holds m (Fin.cases z ρ) := by
  classical
  change (¬ ∃ z : V, m z (ρ i) ∧ ¬ φ.holds m (Fin.cases z ρ)) ↔
    (∀ z : V, m z (ρ i) → φ.holds m (Fin.cases z ρ))
  constructor
  · intro h z hz
    by_contra hnot
    exact h ⟨z, hz, hnot⟩
  · intro h hcontra
    obtain ⟨z, hz, hnot⟩ := hcontra
    exact hnot (h z hz)

/-- Δ₀ formula saying that `p` has exactly the members `a,b`.
The only universal quantifier is bounded by `p`. -/
def dzUPair {n : Nat} (p a b : Fin n) : DeltaZero n :=
  .conj (.member a p)
    (.conj (.member b p)
      (dzBall p (dzOr (.equal 0 (Fin.succ a))
                          (.equal 0 (Fin.succ b)))))

private theorem dzUPair_holds (m : V → V → Prop) {n : Nat}
    (p a b : Fin n) (ρ : Fin n → V) :
    (dzUPair p a b).holds m ρ ↔ IsUPair m (ρ p) (ρ a) (ρ b) := by
  classical
  rw [dzUPair]
  simp only [DeltaZero.holds, dzBall_holds, dzOr_holds]
  change
    (m (ρ a) (ρ p) ∧ m (ρ b) (ρ p) ∧
      (∀ z : V, m z (ρ p) → (z = ρ a ∨ z = ρ b))) ↔
      (∀ z : V, m z (ρ p) ↔ z = ρ a ∨ z = ρ b)
  constructor
  · rintro ⟨ha, hb, hsmall⟩ z
    constructor
    · exact hsmall z
    · intro hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
  · intro h
    exact ⟨(h (ρ a)).2 (Or.inl rfl),
           (h (ρ b)).2 (Or.inr rfl),
           fun z hz => (h z).1 hz⟩

/-- A Δ₀ formula coding the unordered-intersection filter's defining test.
It quantifies `a,b` only over the candidate unordered pair `t`, and `z`
only over `a`. -/
def dzIntersectingPair : DeltaZero 1 :=
  .bex 0 (.bex 1
    (.conj (dzUPair 2 1 0) (.bex 1 (.member 0 1))))

/-- A Δ₀ formula coding the unordered-membership filter's defining test. -/
def dzMembershipPair : DeltaZero 1 :=
  .bex 0 (.bex 1
    (.conj (dzUPair 2 1 0) (dzOr (.member 1 0) (.member 0 1))))

private theorem dzIntersectingPair_holds (m : V → V → Prop) (t : V) :
    dzIntersectingPair.holds m (Fin.cases t (Fin.elim0 : Fin 0 → V)) ↔
    ∃ a b : V, IsUPair m t a b ∧
      ∃ z : V, m z a ∧ m z b := by
  change (∃ a : V, m a t ∧ ∃ b : V, m b t ∧
    (dzUPair (2 : Fin 3) 1 0).holds m
      (Fin.cases b (Fin.cases a (Fin.cases t Fin.elim0))) ∧
    (∃ z : V, m z a ∧ m z b)) ↔ _
  simp only [dzUPair_holds]
  change (∃ a : V, m a t ∧ ∃ b : V, m b t ∧
    IsUPair m t a b ∧ (∃ z : V, m z a ∧ m z b)) ↔ _
  constructor
  · rintro ⟨a, _, b, _, hp, hz⟩
    exact ⟨a, b, hp, hz⟩
  · rintro ⟨a, b, hp, hz⟩
    exact ⟨a, (hp a).2 (Or.inl rfl),
           b, (hp b).2 (Or.inr rfl), hp, hz⟩

private theorem dzMembershipPair_holds (m : V → V → Prop) (t : V) :
    dzMembershipPair.holds m (Fin.cases t (Fin.elim0 : Fin 0 → V)) ↔
    ∃ a b : V, IsUPair m t a b ∧ (m a b ∨ m b a) := by
  change (∃ a : V, m a t ∧ ∃ b : V, m b t ∧
    (dzUPair (2 : Fin 3) 1 0).holds m
      (Fin.cases b (Fin.cases a (Fin.cases t Fin.elim0))) ∧
    (dzOr (.member 1 0) (.member 0 1)).holds m
      (Fin.cases b (Fin.cases a (Fin.cases t Fin.elim0)))) ↔ _
  simp only [dzUPair_holds, dzOr_holds]
  change (∃ a : V, m a t ∧ ∃ b : V, m b t ∧
    IsUPair m t a b ∧ (m a b ∨ m b a)) ↔ _
  constructor
  · rintro ⟨a, _, b, _, hp, hrel⟩
    exact ⟨a, b, hp, hrel⟩
  · rintro ⟨a, b, hp, hrel⟩
    exact ⟨a, (hp a).2 (Or.inl rfl),
           b, (hp b).2 (Or.inr rfl), hp, hrel⟩

/-- The Δ₀ test for unordered composition, with free variables
`[t,q,r,D]`. The witness variables `a,b,c` and the two edges are
bounded by `D`, `q`, and `r`, respectively. -/
def dzComposition : DeltaZero 4 :=
  .bex 3 (.bex 4 (.bex 5
    (.conj (dzUPair 3 2 0)
      (.conj
        (.bex 4 (dzUPair 0 3 2))
        (.bex 5 (dzUPair 0 2 1))))))

private theorem dzComposition_holds (m : V → V → Prop)
    (t q r d : V) :
    dzComposition.holds m (Fin.cases t (![q, r, d] : Fin 3 → V)) ↔
      ∃ a b c : V,
        m a d ∧ m b d ∧ m c d ∧
        IsUPair m t a c ∧
        (∃ p : V, m p q ∧ IsUPair m p a b) ∧
        (∃ p : V, m p r ∧ IsUPair m p b c) := by
  let env0 : Fin 4 → V := Fin.cases t (![q, r, d] : Fin 3 → V)
  change (∃ a : V, m a d ∧ ∃ b : V, m b d ∧ ∃ c : V, m c d ∧
    (dzUPair (3 : Fin 7) 2 0).holds m
      (Fin.cases c (Fin.cases b (Fin.cases a env0))) ∧
    (∃ p : V, m p q ∧
      (dzUPair (0 : Fin 8) 3 2).holds m
        (Fin.cases p (Fin.cases c (Fin.cases b (Fin.cases a env0))))) ∧
    (∃ p : V, m p r ∧
      (dzUPair (0 : Fin 8) 2 1).holds m
        (Fin.cases p (Fin.cases c (Fin.cases b (Fin.cases a env0)))))) ↔ _
  simp only [dzUPair_holds]
  change (∃ a : V, m a d ∧ ∃ b : V, m b d ∧ ∃ c : V, m c d ∧
    IsUPair m t a c ∧
    (∃ p : V, m p q ∧ IsUPair m p a b) ∧
    (∃ p : V, m p r ∧ IsUPair m p b c)) ↔ _
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, ht, hp, hq⟩
    exact ⟨a, b, c, ha, hb, hc, ht, hp, hq⟩
  · rintro ⟨a, b, c, ha, hb, hc, ht, hp, hq⟩
    exact ⟨a, ha, b, hb, c, hc, ht, hp, hq⟩

/-- Union of two sets is available from ordinary Pairing and Union. -/
private theorem bz_binary_union (B : BackgroundNoFoundation V) (h : BoundedZermeloCore B)
    (a b : V) :
    HasMembers B.mem (fun x : V => B.mem x a ∨ B.mem x b) := by
  obtain ⟨p, hp⟩ := h.pairing a b
  obtain ⟨s, hs⟩ := h.union p
  refine ⟨s, ?_⟩
  intro x
  constructor
  · intro hxs
    obtain ⟨y, hy, hxy⟩ := (hs x).1 hxs
    rcases (hp y).1 hy with rfl | rfl
    · exact Or.inl hxy
    · exact Or.inr hxy
  · intro hx
    rcases hx with hxa | hxb
    · exact (hs x).2 ⟨a, (hp a).2 (Or.inl rfl), hxa⟩
    · exact (hs x).2 ⟨b, (hp b).2 (Or.inr rfl), hxb⟩

/-- Derives the exact nine-axiom record from ordinary Bounded Zermelo,
without putting any of the nine operations into the premises. -/
theorem bounded_zermelo_implies_nine_axioms
    (B : BackgroundNoFoundation V) (h : BoundedZermeloCore B) :
    NineAxioms B.mem := by
  let m := B.mem
  refine {
    empty := h.empty,
    singleton := ?_,
    difference := ?_,
    intersection := ?_,
    setUnion := h.union,
    unorderedComposition := ?_,
    unorderedIntersection := ?_,
    unorderedMembership := ?_,
    commonSuperset := ?_
  }
  · intro a
    obtain ⟨s, hs⟩ := h.pairing a a
    refine ⟨s, ?_⟩
    intro x
    simpa [or_self] using (hs x)
  · intro a b
    obtain ⟨s, hs⟩ := h.separation 1
      (.neg (.member 0 1)) a (![b] : Fin 1 → V)
    refine ⟨s, ?_⟩
    intro x
    simpa [DeltaZero.holds] using (hs x)
  · intro a b
    obtain ⟨s, hs⟩ := h.separation 1
      (.member 0 1) a (![b] : Fin 1 → V)
    refine ⟨s, ?_⟩
    intro x
    simpa [DeltaZero.holds] using (hs x)
  · intro q r
    -- Every endpoint of an edge in q or r belongs to the union of those
    -- relations. The candidate unordered output pairs therefore lie in P(D).
    obtain ⟨uq, huq⟩ := h.union q
    obtain ⟨ur, hur⟩ := h.union r
    obtain ⟨d, hd⟩ := bz_binary_union B h uq ur
    obtain ⟨pd, hpd⟩ := B.powerset d
    obtain ⟨s, hs⟩ := h.separation 3 dzComposition pd
      (![q, r, d] : Fin 3 → V)
    refine ⟨s, ?_⟩
    intro t
    rw [hs t]
    constructor
    · rintro ⟨_, hcomp⟩
      have hcomp' : dzComposition.holds m
          (Fin.cases t (![q, r, d] : Fin 3 → V)) := by
        simpa [m] using hcomp
      obtain ⟨a, b, c, _, _, _, hab, hq, hr⟩ :=
        (dzComposition_holds m t q r d).mp hcomp'
      exact ⟨a, b, c, hab, hq, hr⟩
    · rintro ⟨a, b, c, ht, ⟨p, hpq, hpab⟩,
          ⟨w, hwr, hwbc⟩⟩
      have ha_d : m a d := by
        apply (hd a).2
        left
        apply (huq a).2
        exact ⟨p, hpq, (hpab a).2 (Or.inl rfl)⟩
      have hb_d : m b d := by
        apply (hd b).2
        left
        apply (huq b).2
        exact ⟨p, hpq, (hpab b).2 (Or.inr rfl)⟩
      have hc_d : m c d := by
        apply (hd c).2
        right
        apply (hur c).2
        exact ⟨w, hwr, (hwbc c).2 (Or.inr rfl)⟩
      have ht_pd : m t pd := by
        apply (hpd t).2
        intro z hzt
        rcases (ht z).1 hzt with rfl | rfl
        · exact ha_d
        · exact hc_d
      refine ⟨ht_pd, ?_⟩
      have hcomp' : dzComposition.holds m
          (Fin.cases t (![q, r, d] : Fin 3 → V)) :=
        (dzComposition_holds m t q r d).mpr
          ⟨a, b, c, ha_d, hb_d, hc_d, ht,
           ⟨p, hpq, hpab⟩, ⟨w, hwr, hwbc⟩⟩
      simpa [m] using hcomp'
  · intro x
    obtain ⟨s, hs⟩ := h.separation 0 dzIntersectingPair x
      (Fin.elim0 : Fin 0 → V)
    refine ⟨s, ?_⟩
    intro t
    simpa only [dzIntersectingPair_holds] using (hs t)
  · intro x
    obtain ⟨s, hs⟩ := h.separation 0 dzMembershipPair x
      (Fin.elim0 : Fin 0 → V)
    refine ⟨s, ?_⟩
    intro t
    simpa only [dzMembershipPair_holds] using (hs t)
  · intro a b
    obtain ⟨p, hp⟩ := h.pairing a b
    obtain ⟨s, hs⟩ := h.union p
    refine ⟨s, ?_⟩
    intro x hx
    apply (hs x).2
    rcases hx with hxa | hxb
    · exact ⟨a, (hp a).2 (Or.inl rfl), hxa⟩
    · exact ⟨b, (hp b).2 (Or.inr rfl), hxb⟩

end NineAxiomBZ.NoFoundation

#print axioms NineAxiomBZ.NoFoundation.bounded_zermelo_implies_nine_axioms
