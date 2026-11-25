import FoundationFreeFrameInfrastructure
import FoundationFreeFlatTupleFilters
import FoundationFreeRussellFresh

/-!
# Foundation-free finite assignment frames with flat tuples

For fixed local markers `m i`, the tuple for a valuation `a` has members
exactly the tags `{a i, m i}`. Its set of codes is constructed by filtering
the power set of the union of the tag sorts. Each coordinate projection
is given by membership in the flat code.
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

/-- Choose distinct local markers containing the empty object, all outside
the depth-two envelope of E. A single fresh seed occurs inside every marker. -/
private theorem flat_markers_exist
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (E e : V) (n : Nat) :
    ∃ m : Fin n → V, Function.Injective m ∧
      ∀ i : Fin n, B.mem e (m i) ∧ ¬ ReachableWithin B.mem E 2 (m i) := by
  obtain ⟨W, hW⟩ := finite_envelope_exists B H E 4
  obtain ⟨r, _hr, hrOutside, _hrSelf⟩ := relative_russell_fresh_irreflexive B H W
  let code (i : Fin n) := pureFiniteObjects B.mem H i.val
  obtain ⟨a, ha⟩ := Classical.skolem.mp
    (fun i : Fin n => unordered_pair_exists B.mem H (code i) r)
  obtain ⟨m, hm⟩ := Classical.skolem.mp
    (fun i : Fin n => unordered_pair_exists B.mem H (a i) e)
  refine ⟨m, ?_, ?_⟩
  · intro i j hij
    have hai : IsUPair B.mem (m i) (a i) e := hm i
    have haj : IsUPair B.mem (m i) (a j) e := hij.symm ▸ hm j
    have haEq := tagged_pair_payload_unique_nf B (m i) (a i) (a j) e hai haj
    have hci : IsUPair B.mem (a i) (code i) r := ha i
    have hcj : IsUPair B.mem (a i) (code j) r := haEq.symm ▸ ha j
    have hcEq := tagged_pair_payload_unique_nf B (a i) (code i) (code j) r hci hcj
    exact Fin.ext (pureFiniteObjects_injective B.mem H hcEq)
  · intro i
    refine ⟨(hm i e).mpr (Or.inr rfl), ?_⟩
    intro hi
    have haReach : ReachableWithin B.mem E 3 (a i) :=
      Or.inr ⟨m i, hi, (hm i (a i)).mpr (Or.inl rfl)⟩
    have hrReach : ReachableWithin B.mem E 4 r :=
      Or.inr ⟨a i, haReach, (ha i r).mpr (Or.inr rfl)⟩
    exact hrOutside ((hW r).mpr hrReach)

/-- A finite conjunction of tests on a common candidate set is represented
by iterating binary intersection over the externally indexed coordinates. -/
private theorem finite_coordinate_filters_exist
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (C : V) :
    ∀ (n : Nat) (P : Fin n → V → Prop),
      (∀ i, HasMembers B.mem (fun t => B.mem t C ∧ P i t)) →
      HasMembers B.mem (fun t => B.mem t C ∧ ∀ i, P i t) := by
  intro n
  induction n with
  | zero =>
      intro P _hP
      exact ⟨C, fun _ => ⟨fun ht => ⟨ht, fun i => i.elim0⟩, And.left⟩⟩
  | succ n ih =>
      intro P hP
      obtain ⟨F, hF⟩ := hP 0
      obtain ⟨G, hG⟩ := ih (fun i => P i.succ) (fun i => hP i.succ)
      obtain ⟨T, hT⟩ := H.intersection F G
      refine ⟨T, ?_⟩
      intro t
      constructor
      · intro ht
        obtain ⟨htF, htG⟩ := (hT t).mp ht
        obtain ⟨htC, hHead⟩ := (hF t).mp htF
        refine ⟨htC, ?_⟩
        intro i
        cases i using Fin.cases with
        | zero => exact hHead
        | succ j => exact ((hG t).mp htG).2 j
      · rintro ⟨htC, hAll⟩
        exact (hT t).mpr ⟨(hF t).mpr ⟨htC, hAll 0⟩,
          (hG t).mpr ⟨htC, fun i => hAll i.succ⟩⟩

/-- A nonzero-arity frame whose codes are exactly the flat sets of one tag
per coordinate. Projection to a tagged value is ordinary membership. -/
theorem flat_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (E : V)
    (n : Nat) (D : Fin (n + 1) → V)
    (hDE : ∀ i : Fin (n + 1), ∀ x : V, B.mem x (D i) → B.mem x E) :
    ∃ F : FiniteAssignmentFrameNF B E (n + 1) D,
      (∀ t : V, B.mem t F.sort ↔
        (∀ u : V, B.mem u t → ∃ i : Fin (n + 1), B.mem u (F.tagSort i)) ∧
        ∀ i : Fin (n + 1), ∃! u : V, B.mem u (F.tagSort i) ∧ B.mem u t) ∧
      ∀ (i : Fin (n + 1)) (t u : V), F.projectionRel i t u ↔ B.mem u t := by
  classical
  obtain ⟨e, he⟩ := H.empty
  obtain ⟨m, hmInjective, hm⟩ := flat_markers_exist B H E e (n + 1)
  have hOutside (i : Fin (n + 1)) : ¬ B.mem (m i) E :=
    fun h => (hm i).2 (Or.inl (Or.inl h))
  have hFresh (i : Fin (n + 1)) {x : V} (hx : B.mem x E) :
      ¬ B.mem (m i) x :=
    fun h => (hm i).2 (Or.inl (Or.inr ⟨x, hx, h⟩))
  have hDeep (i : Fin (n + 1)) {x y : V} (hx : B.mem x E) (hy : B.mem y x) :
      ¬ B.mem (m i) y :=
    fun h => (hm i).2 (Or.inr ⟨y, Or.inr ⟨x, hx, hy⟩, h⟩)
  have hOutsideD (i : Fin (n + 1)) : ¬ B.mem (m i) (D i) :=
    fun h => hOutside i (hDE i _ h)
  obtain ⟨U, hU⟩ := Classical.skolem.mp
    (fun i : Fin (n + 1) => corrected_fan_no_foundation B H (D i) (m i) (hOutsideD i))
  have hRaw (i : Fin (n + 1)) : DisjointSortNF B.mem E (U i) := by
    intro x u hx hu hEq
    subst x
    obtain ⟨a, _ha, hp⟩ := (hU i u).mp hu
    exact hFresh i hx ((hp (m i)).mpr (Or.inr rfl))
  have hDisjoint (i j : Fin (n + 1)) (hij : i ≠ j) :
      DisjointSortNF B.mem (U i) (U j) := by
    intro u v hu hv hEq
    subst v
    obtain ⟨a, _ha, hp⟩ := (hU i u).mp hu
    obtain ⟨b, hb, hq⟩ := (hU j u).mp hv
    rcases (hq (m i)).mp ((hp (m i)).mpr (Or.inr rfl)) with h | h
    · exact hOutside i (by simpa only [h] using hDE j b hb)
    · exact hij (hmInjective h)
  obtain ⟨R, hR⟩ := finite_family_range_exists_nf B H (n + 1) U
  obtain ⟨A, hA⟩ := H.setUnion R
  have hTags (u : V) : B.mem u A ↔ ∃ i : Fin (n + 1), B.mem u (U i) := by
    constructor
    · intro hu
      obtain ⟨S, hS, hIn⟩ := (hA u).mp hu
      obtain ⟨i, rfl⟩ := (hR S).mp hS
      exact ⟨i, hIn⟩
    · rintro ⟨i, hu⟩
      exact (hA u).mpr ⟨U i, (hR (U i)).mpr ⟨i, rfl⟩, hu⟩
  have hEmptyOutside : ¬ B.mem e A := by
    intro h
    obtain ⟨i, hi⟩ := (hTags e).mp h
    obtain ⟨a, _ha, hp⟩ := (hU i e).mp hi
    exact (he a).mp ((hp a).mpr (Or.inl rfl))
  obtain ⟨Power, hPower⟩ := B.powerset A
  obtain ⟨SingleEmpty, hSingleEmpty⟩ := H.singleton e
  obtain ⟨C, hC⟩ := H.difference Power SingleEmpty
  have hCandidate (t : V) :
      B.mem t C ↔ (∀ u : V, B.mem u t → B.mem u A) ∧ t ≠ e := by
    rw [hC t]
    change (B.mem t Power ∧ ¬ B.mem t SingleEmpty) ↔ _
    rw [hPower t, hSingleEmpty t]
  have hNonempty {t : V} (ht : B.mem t C) : ∃ u : V, B.mem u t := by
    by_contra h
    apply ((hCandidate t).mp ht).2
    apply B.extensionality
    intro u
    exact iff_of_false (fun hu => h ⟨u, hu⟩) (he u).mp
  have hCandidateOutsideE {t : V} (ht : B.mem t C) : ¬ B.mem t E := by
    intro htE
    obtain ⟨u, hut⟩ := hNonempty ht
    obtain ⟨i, hi⟩ := (hTags u).mp (((hCandidate t).mp ht).1 u hut)
    obtain ⟨a, _ha, hp⟩ := (hU i u).mp hi
    exact hDeep i htE hut ((hp (m i)).mpr (Or.inr rfl))
  have hCandidateDisjoint (i : Fin (n + 1)) : DisjointSortNF B.mem C (U i) := by
    intro t u ht hu hEq
    subst u
    obtain ⟨a, ha, hp⟩ := (hU i t).mp hu
    have haA := ((hCandidate t).mp ht).1 a ((hp a).mpr (Or.inl rfl))
    obtain ⟨j, hj⟩ := (hTags a).mp haA
    exact hRaw j a a (hDE i a ha) hj rfl
  have hReverse (i : Fin (n + 1)) (t u : V) (ht : B.mem t C) (hu : B.mem u (U i)) :
      ¬ B.mem t u := by
    intro htu
    obtain ⟨a, ha, hp⟩ := (hU i u).mp hu
    rcases (hp t).mp htu with h | h
    · exact hCandidateOutsideE ht (by simpa only [h] using hDE i a ha)
    · exact hEmptyOutside (((hCandidate t).mp ht).1 e (h.symm ▸ (hm i).1))
  obtain ⟨T, hT⟩ := finite_coordinate_filters_exist B H C (n + 1)
    (fun i t => ∃! u : V, B.mem u (U i) ∧ B.mem u t)
    (fun i => exactly_one_tag_filter_exists_nf B H C (U i) (hCandidateDisjoint i) (hReverse i))
  have hTflat (t : V) : B.mem t T ↔
      (∀ u : V, B.mem u t → ∃ i : Fin (n + 1), B.mem u (U i)) ∧
      ∀ i : Fin (n + 1), ∃! u : V, B.mem u (U i) ∧ B.mem u t := by
    constructor
    · intro ht
      obtain ⟨htC, hEach⟩ := (hT t).mp ht
      exact ⟨fun u hu => (hTags u).mp (((hCandidate t).mp htC).1 u hu), hEach⟩
    · rintro ⟨hTagsIn, hEach⟩
      obtain ⟨u, hu, _hUnique⟩ := hEach 0
      refine (hT t).mpr ⟨(hCandidate t).mpr ⟨fun v hv => (hTags v).mpr (hTagsIn v hv), ?_⟩,
        hEach⟩
      intro h
      exact (he u).mp (h ▸ hu.2)
  obtain ⟨P, hP⟩ := Classical.skolem.mp
    (fun i : Fin (n + 1) => tuple_membership_edges_exists_nf B H T (U i) (fun t u ht hu =>
      hReverse i t u ((hT t).mp ht).1 hu))
  obtain ⟨S, hS⟩ := finite_family_range_exists_nf B H (n + 1) D
  refine ⟨{
    sort := T
    tagSort := U
    marker := m
    support := fun _ => S
    rawInSupport := fun i => (hS (D i)).mpr ⟨i, rfl⟩
    rawDisjoint := hRaw
    projectionGraph := P
    projectionRel := fun _ t u => B.mem u t
    rawBound := hDE
    tagSpec := hU
    markerFresh := fun i _ hx => hFresh i hx
    markerOutsideDomain := hOutsideD
    markerDeep := fun i x _ hx hy => hDeep i (hDE i x hx) hy
    tupleTagDisjoint := fun i t u ht hu => hCandidateDisjoint i t u ((hT t).mp ht).1 hu
    tagPairwiseDisjoint := hDisjoint
    projectionSpec := hP
    coordinateUnique := fun t ht i => ((hT t).mp ht).2 i
    realizes := ?_
  }, hTflat, fun _ _ _ => Iff.rfl⟩
  intro values hValues
  obtain ⟨u, hu⟩ := Classical.skolem.mp
    (fun i : Fin (n + 1) => unordered_pair_exists B.mem H (values i) (m i))
  have hTag (i : Fin (n + 1)) : B.mem (u i) (U i) :=
    (hU i (u i)).mpr ⟨values i, hValues i, hu i⟩
  obtain ⟨t, ht⟩ := finite_family_range_exists_nf B H (n + 1) u
  have hIn (i : Fin (n + 1)) : B.mem (u i) t := (ht (u i)).mpr ⟨i, rfl⟩
  refine ⟨t, (hTflat t).mpr ⟨?_, ?_⟩, fun i => ⟨u i, hTag i, hu i, hIn i⟩⟩
  · intro v hv
    obtain ⟨j, rfl⟩ := (ht v).mp hv
    exact ⟨j, hTag j⟩
  · intro i
    refine ⟨u i, ⟨hTag i, hIn i⟩, ?_⟩
    rintro v ⟨hvU, hvt⟩
    obtain ⟨j, rfl⟩ := (ht v).mp hvt
    by_cases hij : j = i
    · exact congrArg u hij
    · exact False.elim (hDisjoint j i hij _ _ (hTag j) hvU rfl)

/-- A represented finite frame for every externally indexed family of raw
domains in E. The zero-coordinate frame consists of the empty tuple. -/
theorem finite_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) (E : V) :
    ∀ (n : Nat) (D : Fin n → V),
      (∀ i : Fin n, ∀ x : V, B.mem x (D i) → B.mem x E) →
      Nonempty (FiniteAssignmentFrameNF B E n D) := by
  intro n
  cases n with
  | zero =>
      intro D _hDE
      have hD : D = (Fin.elim0 : Fin 0 → V) := by
        funext i
        exact i.elim0
      exact hD ▸ empty_assignment_frame_exists_nf B H E
  | succ n =>
      intro D hDE
      obtain ⟨F, _hFlat, _hProjection⟩ := flat_assignment_frame_exists_nf B H E n D hDE
      exact ⟨F⟩

/-- A frame exists after adding a first coordinate to the domain family of
a represented frame. The flat construction treats all domains together. -/
theorem extend_assignment_frame_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (old : FiniteAssignmentFrameNF B E n D)
    (X : V) (hXE : ∀ x : V, B.mem x X → B.mem x E) :
    Nonempty (FiniteAssignmentFrameNF B E (n + 1) (Fin.cases X D)) := by
  apply finite_assignment_frame_exists_nf B H E
  intro i
  cases i using Fin.cases with
  | zero => exact hXE
  | succ j => exact old.rawBound j

end NineAxiomBZ.NoFoundation
