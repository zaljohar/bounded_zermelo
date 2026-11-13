import FoundationFreeRussellFresh

/-!
# Fresh markers excluding 1- and 2-cycles without Foundation

A Russell marker R is fresh and satisfies R ∉ R, but by itself this
DOES NOT rule out a two-cycle R ∈ f ∈ R.  We therefore wrap a fresh
seed `r` into the finite pure-shaped object

  m = { ∅, {{r}} }.

For EVERY set f, m∈f implies f∉m: the only members of m are ∅ and
{{r}}, and m cannot equal {r} since m has two distinct members.

Because r ∈ {r} ∈ {{r}} ∈ m, choosing r outside an envelope four
levels deeper than a given finite support makes m fresh relative to
that support.  This uses only A1,A2, pairing (derived from T9),
and the Russell/envelope lemmas.  No Foundation or Separation is added.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Build a marker which never participates as the lower endpoint of a
membership two-cycle.  This is an unconditional finite construction. -/
theorem no_two_cycle_marker_from_seed
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (seed : V) :
    ∃ (marker s ss : V),
      B.mem seed s ∧ B.mem s ss ∧ B.mem ss marker ∧
      (∀ f : V, B.mem marker f → ¬ B.mem f marker) := by
  let m := B.mem
  obtain ⟨e, he⟩ := H.empty
  obtain ⟨s, hs⟩ := H.singleton seed
  obtain ⟨ss, hss⟩ := H.singleton s
  obtain ⟨marker, hm⟩ := unordered_pair_exists m H e ss
  have heSS : e ≠ ss := by
    intro heq
    have h : m s e := by
      rw [heq]
      exact (hss s).mpr rfl
    exact (he s).mp h
  have hmarker_ne_s : marker ≠ s := by
    intro hms
    have heMarker : m e marker := (hm e).mpr (Or.inl rfl)
    have hssMarker : m ss marker := (hm ss).mpr (Or.inr rfl)
    have heSeed : e = seed := by
      apply (hs e).mp
      rw [← hms]
      exact heMarker
    have hssSeed : ss = seed := by
      apply (hs ss).mp
      rw [← hms]
      exact hssMarker
    exact heSS (heSeed.trans hssSeed.symm)
  refine ⟨marker, s, ss,
    (hs seed).mpr rfl, (hss s).mpr rfl,
    (hm ss).mpr (Or.inr rfl), ?_⟩
  intro f hmf hfm
  rcases (hm f).mp hfm with hfe | hfss
  · have hmEmpty : m marker e := by
      rw [hfe] at hmf
      exact hmf
    exact (he marker).mp hmEmpty
  · have hmSS : m marker ss := by
      rw [hfss] at hmf
      exact hmf
    exact hmarker_ne_s ((hss marker).mp hmSS)

/-- A safe marker exists at every finite depth, including a local
anti-two-cycle condition needed for typed relation and tuple decoding.
No Foundation, `NoUniversal` premise or membership-cycle exclusion is
used. -/
theorem fresh_no_two_cycle_marker_at_depth
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (W : V) (n : Nat) :
    ∃ marker : V,
      (∀ f : V, B.mem marker f → ¬ B.mem f marker) ∧
      (∀ t : V, ReachableWithin B.mem W n t →
        ¬ B.mem marker t) := by
  obtain ⟨seed, _, _, hOutside⟩ :=
    irreflexive_fresh_marker_at_depth B H W (n + 4)
  obtain ⟨marker, s, ss, hrs, hss, hms, hNo2⟩ :=
    no_two_cycle_marker_from_seed B H seed
  refine ⟨marker, hNo2, ?_⟩
  intro t ht hmt
  have h1 : ReachableWithin B.mem W (n + 1) marker :=
    Or.inr ⟨t, ht, hmt⟩
  have h2 : ReachableWithin B.mem W (n + 2) ss :=
    Or.inr ⟨marker, h1, hms⟩
  have h3 : ReachableWithin B.mem W (n + 3) s :=
    Or.inr ⟨ss, h2, hss⟩
  have h4 : ReachableWithin B.mem W (n + 4) seed :=
    Or.inr ⟨s, h3, hrs⟩
  exact hOutside h4

/-- In particular, a safe marker is irreflexive, even in models with
other self-membered objects and arbitrary membership cycles. -/
theorem fresh_no_self_marker_at_depth
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (W : V) (n : Nat) :
    ∃ marker : V,
      ¬ B.mem marker marker ∧
      (∀ t : V, ReachableWithin B.mem W n t →
        ¬ B.mem marker t) := by
  obtain ⟨marker, hNo2, hFresh⟩ :=
    fresh_no_two_cycle_marker_at_depth B H W n
  have hIrrefl : ¬ B.mem marker marker := by
    intro hself
    exact (hNo2 marker hself) hself
  exact ⟨marker, hIrrefl, hFresh⟩

end NineAxiomBZ.NoFoundation
