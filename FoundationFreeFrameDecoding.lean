import FoundationFreeFiniteAssignmentFrame
/-!
Unique raw decoding of the finite tagged assignment frames. The existence
of an object-level tuple set, every coordinate projection graph, and all
assignments is provided by `FiniteAssignmentFrameNF.lean`. This file proves
that those tag-projections uniquely determine the original raw values.

Kernel-checked with Lean 4.20.0.
No separation, `sorry`, `admit`, new axioms, or open proof hypotheses.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- A represented tuple `t` has exactly one raw value in coordinate `i`.
Here equality of represented singleton-marker pairs is proved by the
unordered-pair endpoint lemma, not assumed as a decoding axiom. -/
theorem finite_frame_raw_coordinate_unique_nf
    (B : BackgroundNoFoundation V) (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (t : V) (ht : B.mem t F.sort) (i : Fin n) :
    ∃! x : V, B.mem x (D i) ∧
      ∃ u : V, B.mem u (F.tagSort i) ∧
        F.projectionRel i t u ∧
        IsUPair B.mem u x (F.marker i) := by
  obtain ⟨u, hu, hUniqueU⟩ := F.coordinateUnique t ht i
  obtain ⟨x, hx, htag⟩ := (F.tagSpec i u).mp hu.1
  refine ⟨x, ⟨hx, u, hu.1, hu.2, htag⟩, ?_⟩
  intro y hy
  obtain ⟨_hyD, v, hvTag, hvRel, hvPair⟩ := hy
  have hvu : v = u := hUniqueU v ⟨hvTag, hvRel⟩
  subst v
  exact (tagged_pair_payload_unique_nf B u x y (F.marker i) htag hvPair).symm

/-- A harmless default object for codes outside the frame comes from the
empty-set axiom. On actual tuple codes, the function is uniquely specified. -/
noncomputable def FiniteAssignmentFrameNF.decodeRaw
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (t : V) (i : Fin n) : V := by
  classical
  exact if ht : B.mem t F.sort then
      Classical.choose (finite_frame_raw_coordinate_unique_nf B E n D F t ht i)
    else
      Classical.choose H.empty

/-- Correctness of the raw coordinate decoder on genuine tuple codes. -/
theorem FiniteAssignmentFrameNF.decodeRaw_correct
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (t : V) (ht : B.mem t F.sort) (i : Fin n) :
    B.mem (F.decodeRaw B H E n D t i) (D i) ∧
      ∃ u : V, B.mem u (F.tagSort i) ∧
        F.projectionRel i t u ∧
        IsUPair B.mem u (F.decodeRaw B H E n D t i) (F.marker i) := by
  classical
  unfold FiniteAssignmentFrameNF.decodeRaw
  rw [dif_pos ht]
  exact (Classical.choose_spec
    (finite_frame_raw_coordinate_unique_nf B E n D F t ht i)).1

/-- All prescribed assignments are realized by codes with exactly the
prescribed decoded values. This is the finite-arity surjectivity theorem. -/
theorem finite_frame_realizes_raw_values_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrameNF B E n D)
    (values : Fin n → V)
    (hValues : ∀ i : Fin n, B.mem (values i) (D i)) :
    ∃ t : V, B.mem t F.sort ∧
      ∀ i : Fin n, F.decodeRaw B H E n D t i = values i := by
  obtain ⟨t, ht, hReal⟩ := F.realizes values hValues
  refine ⟨t, ht, ?_⟩
  intro i
  obtain ⟨u, huTag, huRaw, huProj⟩ := hReal i
  have hY : B.mem (values i) (D i) ∧
      ∃ v : V, B.mem v (F.tagSort i) ∧
        F.projectionRel i t v ∧
        IsUPair B.mem v (values i) (F.marker i) :=
    ⟨hValues i, u, huTag, huProj, huRaw⟩
  have hUnique := finite_frame_raw_coordinate_unique_nf B E n D F t ht i
  have hEq := (Classical.choose_spec hUnique).2 (values i) hY
  -- `hEq` is values[i] = the unique decoded value.
  have hDecoded : F.decodeRaw B H E n D t i =
      Classical.choose hUnique := by
    unfold FiniteAssignmentFrameNF.decodeRaw
    rw [dif_pos ht]
  exact hDecoded.trans hEq.symm

end NineAxiomBZ.NoFoundation
