import FoundationFreeFrameInfrastructure

/-!
# Foundation-free complete finite assignment frames

This is a direct adaptation of the original verified frame induction, with
Foundation replaced by the explicit finite-depth freshness guarantees of
`FoundationFreePrefixProjection`.  In contrast with the old frame, there is
no `supportSpec` asserting that the marker is a singleton; its only uses in
the later semantic induction are represented graph typing and freshness.

Draft pending Lean elaboration and kernel verification.  It does not prove
full bounded separation on its own.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Foundation-free represented finite assignment frame.
Unlike the original frame, markers are NOT required to be singleton supports.
Only their observable freshness and tagging properties are retained. -/
structure FiniteAssignmentFrameNF (B : BackgroundNoFoundation V) (E : V)
    (n : Nat) (D : Fin n → V) where
  sort : V
  tagSort : Fin n → V
  marker : Fin n → V
  support : Fin n → V
  rawInSupport : ∀ i : Fin n, B.mem (D i) (support i)
  rawDisjoint : ∀ i : Fin n, DisjointSortNF B.mem E (tagSort i)
  projectionGraph : Fin n → V
  projectionRel : Fin n → V → V → Prop
  rawBound : ∀ i : Fin n, ∀ x : V, B.mem x (D i) → B.mem x E
  tagSpec : ∀ i : Fin n, ∀ f : V,
    B.mem f (tagSort i) ↔
      ∃ x : V, B.mem x (D i) ∧ IsUPair B.mem f x (marker i)
  markerFresh : ∀ i : Fin n, ∀ x : V,
    B.mem x E → ¬ B.mem (marker i) x
  markerOutsideDomain : ∀ i : Fin n,
    ¬ B.mem (marker i) (D i)
  markerDeep : ∀ i : Fin n, ∀ x y : V,
    B.mem x (D i) → B.mem y x → ¬ B.mem (marker i) y
  tupleTagDisjoint : ∀ i : Fin n,
    DisjointSortNF B.mem sort (tagSort i)
  tagPairwiseDisjoint : ∀ i j : Fin n, i ≠ j →
    DisjointSortNF B.mem (tagSort i) (tagSort j)
  projectionSpec : ∀ i : Fin n,
    TypedEdges B.mem sort (tagSort i)
      (projectionRel i) (projectionGraph i)
  coordinateUnique : ∀ t : V, B.mem t sort →
    ∀ i : Fin n, ∃! u : V,
      B.mem u (tagSort i) ∧ projectionRel i t u
  realizes : ∀ (values : Fin n → V),
    (∀ i : Fin n, B.mem (values i) (D i)) →
    ∃ t : V, B.mem t sort ∧ ∀ i : Fin n,
      ∃ u : V, B.mem u (tagSort i) ∧
        IsUPair B.mem u (values i) (marker i) ∧
        projectionRel i t u

/-- Empty arity: use a singleton set of one distinguished empty tuple.
All coordinate assertions are vacuous. -/
theorem empty_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (E : V) :
    Nonempty (FiniteAssignmentFrameNF B E 0 Fin.elim0) := by
  obtain ⟨e, _he⟩ := H.empty
  obtain ⟨T, hT⟩ := H.singleton e
  refine ⟨{
    sort := T
    tagSort := Fin.elim0
    marker := Fin.elim0
    support := Fin.elim0
    rawInSupport := ?_
    rawDisjoint := ?_
    projectionGraph := Fin.elim0
    projectionRel := Fin.elim0
    rawBound := ?_
    tagSpec := ?_
    markerFresh := ?_
    markerOutsideDomain := ?_
    markerDeep := ?_
    tupleTagDisjoint := ?_
    tagPairwiseDisjoint := ?_
    projectionSpec := ?_
    coordinateUnique := ?_
    realizes := ?_
  }⟩
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro t _ i
    exact i.elim0
  · intro values _
    refine ⟨e, (hT e).mpr rfl, ?_⟩
    intro i
    exact i.elim0

/-- Extend an already represented `n`-coordinate frame by a fresh coordinate
at index zero, retaining every earlier represented projection graph.
There is no finite-frame or truth-set existence premise. -/
theorem extend_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (old : FiniteAssignmentFrameNF B E n D)
    (X : V) (hXE : ∀ x : V, B.mem x X → B.mem x E) :
    Nonempty (FiniteAssignmentFrameNF B E (n + 1) (Fin.cases X D)) := by
  -- Put E, X, the old tuple sort, and all old tagged sorts in one support.
  obtain ⟨W, hEW, hXW, hUW, hTW⟩ :=
    finite_registry_exists_nf B H n 1 old.tagSort
      (fun _ : Fin 1 => old.sort) E X
  have hTInW : B.mem old.sort W := hTW 0
  obtain ⟨m, F, N, Γ, Λ, hF, hN, hΓ, hΛ,
    hTF, hNT, hNF, hFresh, hMarkerFresh,
    hMarkerOutside, hMarkerDeep⟩ :=
    fresh_two_projections_without_foundation B H
      X old.sort W hXW hTInW
  have hNU (i : Fin n) : DisjointSortNF B.mem N (old.tagSort i) :=
    (hFresh (old.tagSort i) (hUW i)).2
  have hFU (i : Fin n) : DisjointSortNF B.mem F (old.tagSort i) :=
    (hFresh (old.tagSort i) (hUW i)).1
  let pref : V → V → Prop := fun t s =>
    ∃ f : V, B.mem f F ∧ IsUPair B.mem t s f
  let last : V → V → Prop := fun t f =>
    ∃ s : V, B.mem s old.sort ∧ IsUPair B.mem t s f
  have hΓtyped : TypedEdges B.mem N old.sort pref Γ := by
    intro p
    constructor
    · intro hp
      obtain ⟨t, s, f, htN, hsT, hfF, htsf, hpts⟩ := (hΓ p).mp hp
      exact ⟨t, s, htN, hsT, hpts, f, hfF, htsf⟩
    · rintro ⟨t, s, htN, hsT, hpts, f, hfF, htsf⟩
      exact (hΓ p).mpr ⟨t, s, f, htN, hsT, hfF, htsf, hpts⟩
  have hΛtyped : TypedEdges B.mem N F last Λ := by
    intro p
    constructor
    · intro hp
      obtain ⟨t, s, f, htN, hsT, hfF, htsf, hptf⟩ := (hΛ p).mp hp
      exact ⟨t, f, htN, hfF, hptf, s, hsT, htsf⟩
    · rintro ⟨t, f, htN, hfF, hptf, s, hsT, htsf⟩
      exact (hΛ p).mpr ⟨t, s, f, htN, hsT, hfF, htsf, hptf⟩
  obtain ⟨Q, hQ⟩ :=
    lift_finite_coordinate_projections_nf B H n old.sort N
      old.tagSort Γ old.projectionGraph
      pref old.projectionRel
      hNT hNU old.tupleTagDisjoint hΓtyped old.projectionSpec
  let tag' : Fin (n + 1) → V := Fin.cases F old.tagSort
  let mark' : Fin (n + 1) → V := Fin.cases m old.marker
  let support' : Fin (n + 1) → V := Fin.cases W old.support
  let graph' : Fin (n + 1) → V := Fin.cases Λ Q
  let relation' : Fin (n + 1) → V → V → Prop :=
    Fin.cases last (fun i t u =>
      ∃ s : V, B.mem s old.sort ∧ pref t s ∧
        old.projectionRel i s u)
  refine ⟨{
    sort := N
    tagSort := tag'
    marker := mark'
    support := support'
    rawInSupport := ?_
    rawDisjoint := ?_
    projectionGraph := graph'
    projectionRel := relation'
    rawBound := ?_
    tagSpec := ?_
    markerFresh := ?_
    markerOutsideDomain := ?_
    markerDeep := ?_
    tupleTagDisjoint := ?_
    tagPairwiseDisjoint := ?_
    projectionSpec := ?_
    coordinateUnique := ?_
    realizes := ?_
  }⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact hXW
    | succ j => exact old.rawInSupport j
  · intro i
    cases i using Fin.cases with
    | zero =>
        intro e f he hf hef
        exact (hFresh E hEW).1 f e hf he hef.symm
    | succ j => exact old.rawDisjoint j
  · intro i x hx
    cases i using Fin.cases with
    | zero => exact hXE x hx
    | succ j => exact old.rawBound j x hx
  · intro i f
    cases i using Fin.cases with
    | zero => exact hF f
    | succ j => exact old.tagSpec j f
  · intro i x hx
    cases i using Fin.cases with
    | zero => exact hMarkerFresh E x hEW hx
    | succ j => exact old.markerFresh j x hx
  · intro i
    cases i using Fin.cases with
    | zero => exact hMarkerOutside X hXW
    | succ j => exact old.markerOutsideDomain j
  · intro i x y hx hy
    cases i using Fin.cases with
    | zero => exact hMarkerDeep X x y hXW hx hy
    | succ j => exact old.markerDeep j x y hx hy
  · intro i
    cases i using Fin.cases with
    | zero => exact hNF
    | succ j => exact hNU j
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (hij rfl)
        | succ k => exact hFU k
    | succ k =>
        cases j using Fin.cases with
        | zero =>
            intro u f hu hf huf
            exact hFU k f u hf hu huf.symm
        | succ l =>
            apply old.tagPairwiseDisjoint k l
            intro hkl
            exact hij (congrArg Fin.succ hkl)
  · intro i
    cases i using Fin.cases with
    | zero => exact hΛtyped
    | succ j => exact hQ j
  · intro t htN i
    obtain ⟨s, f, hsT, hfF, htsf⟩ := (hN t).mp htN
    cases i using Fin.cases with
    | zero =>
        refine ⟨f, ⟨hfF, s, hsT, htsf⟩, ?_⟩
        intro f' hf'
        obtain ⟨hf'F, s', hs'T, hts'f'⟩ := hf'
        have hsff' := disjoint_unordered_tuple_unique_nf B old.sort F
          hTF t s f s' f' hsT hfF hs'T hf'F htsf hts'f'
        exact hsff'.2.symm
    | succ j =>
        obtain ⟨u, hu, hUniq⟩ := old.coordinateUnique s hsT j
        have hu' : B.mem u (old.tagSort j) ∧
            (∃ s' : V, B.mem s' old.sort ∧ pref t s' ∧
              old.projectionRel j s' u) := by
          refine ⟨hu.1, s, hsT, ?_, hu.2⟩
          exact ⟨f, hfF, htsf⟩
        refine ⟨u, hu', ?_⟩
        intro u' hu'
        obtain ⟨hu'F, s', hs'T, hPref', hRel'⟩ := hu'
        obtain ⟨f', hf'F, hts'f'⟩ := hPref'
        have hss' := disjoint_unordered_tuple_unique_nf B old.sort F
          hTF t s f s' f' hsT hfF hs'T hf'F htsf hts'f'
        have hu'old : B.mem u' (old.tagSort j) ∧ old.projectionRel j s u' :=
          ⟨hu'F, hss'.1.symm ▸ hRel'⟩
        exact hUniq u' hu'old
  · intro values hVals
    let oldVals : Fin n → V := fun i => values i.succ
    have hOldVals : ∀ i : Fin n, B.mem (oldVals i) (D i) := by
      intro i
      exact hVals i.succ
    obtain ⟨s, hsT, hReal⟩ := old.realizes oldVals hOldVals
    obtain ⟨f, hfm⟩ := unordered_pair_exists B.mem H (values 0) m
    have hfF : B.mem f F :=
      (hF f).mpr ⟨values 0, hVals 0, hfm⟩
    obtain ⟨t, htsf⟩ := unordered_pair_exists B.mem H s f
    have htN : B.mem t N :=
      (hN t).mpr ⟨s, f, hsT, hfF, htsf⟩
    refine ⟨t, htN, ?_⟩
    intro i
    cases i using Fin.cases with
    | zero =>
        exact ⟨f, hfF, hfm, s, hsT, htsf⟩
    | succ j =>
        obtain ⟨u, hu, htag, hCoord⟩ := hReal j
        refine ⟨u, hu, htag, s, hsT, ?_, hCoord⟩
        exact ⟨f, hfF, htsf⟩

/-- There is a represented finite frame for ANY prescribed external finite
family of raw domains inside E; no separation schema is invoked. -/
theorem finite_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (E : V) :
    ∀ (n : Nat) (D : Fin n → V),
      (∀ i : Fin n, ∀ x : V, B.mem x (D i) → B.mem x E) →
      Nonempty (FiniteAssignmentFrameNF B E n D) := by
  intro n
  induction n with
  | zero =>
      intro D _
      have hD : D = (Fin.elim0 : Fin 0 → V) := by
        funext i
        exact i.elim0
      exact hD ▸ empty_assignment_frame_exists_nf B H E
  | succ n ih =>
      intro D hDE
      let Dtail : Fin n → V := fun i => D i.succ
      have hTail : ∀ (i : Fin n) (x : V),
          B.mem x (Dtail i) → B.mem x E := by
        intro i x hx
        exact hDE i.succ x hx
      obtain ⟨old⟩ := ih Dtail hTail
      have hHead : ∀ x : V, B.mem x (D 0) → B.mem x E :=
        hDE 0
      obtain ⟨newFrame⟩ :=
        extend_assignment_frame_exists_nf B H E n Dtail old (D 0) hHead
      -- A family `D` and its `Fin.cases` reconstruction are definitionally
      -- extensionally equal. Cast the resulting frame along that equality.
      have hDomains : Fin.cases (D 0) Dtail = D := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      exact ⟨hDomains ▸ newFrame⟩


end NineAxiomBZ.NoFoundation
