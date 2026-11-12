import FiniteFrameCoordinateImage
/-!
# Unconditional target: nine axioms imply full Δ₀-Separation

This is a complete dependency chain using a single uniform finite
assignment frame. It introduces no postulated `FiniteFrameObligation`, no
`ConverseExists`, no `GodelEight` hypothesis and no separation axiom.

The complete import chain was checked by the Lean 4.20.0 kernel.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The finite envelope can be arranged to contain both the distinguished
    domain and all parameters, not merely to preserve Δ₀ satisfaction. -/
theorem bounded_envelope_with_roots
    (B : Background V) (H : NineAxioms B.mem)
    (n : Nat) (φ : DeltaZero (n + 1))
    (A : V) (params : Fin n → V) :
    ∃ E : V,
      (∀ x, B.mem x A → B.mem x E) ∧
      (∀ i : Fin n, B.mem (params i) E) ∧
      (∀ x, B.mem x A →
        (φ.holds B.mem (Fin.cases x params) ↔
         φ.holdsIn B.mem E (Fin.cases x params))) := by
  obtain ⟨seed, hA, hp⟩ := initial_seed_exists B H n A params
  obtain ⟨E,hE⟩ :=
    reachable_envelope_exists B.mem H seed φ.boundDepth
  have hIncl : ∀ z, B.mem z seed → B.mem z E := by
    intro z hz
    apply (hE z).mpr
    exact reachable_mono B.mem seed
      (show 0 ≤ φ.boundDepth by omega) hz
  refine ⟨E,(fun x hx => hIncl x (hA x hx)),
    (fun i => hIncl (params i) (hp i)), ?_⟩
  intro x hxA
  let ρ : Fin (n + 1) → V :=
    @Fin.cases n (fun _ => V) x params
  have hρ : ∀ i : Fin (n + 1),
      Reachable B.mem seed 0 (ρ i) := by
    exact @Fin.cases n
      (fun i => Reachable B.mem seed 0 (ρ i))
      (by simpa [ρ] using hA x hxA)
      (fun j => by simpa [ρ] using hp j)
  have hBound : ∀ z,
      Reachable B.mem seed (0 + φ.boundDepth) z → B.mem z E := by
    intro z hz
    exact (hE z).mpr (by simpa using hz)
  simpa [ρ] using
    DeltaZero.holds_iff_holdsIn B.mem E seed φ 0 ρ hρ hBound

/-- All bounded formulas with arbitrary parameters are separable from A.
    The proof uses one finite frame of length `n+1+φ.boundDepth`, not an
    assumed infinite tower. -/
theorem bounded_separation_from_nine_completed_draft
    (B : Background V) (H : NineAxioms B.mem) :
    BoundedSeparation B.mem := by
  classical
  intro n φ A params
  -- The empty domain case needs no assignment frame or filler value.
  by_cases hNonempty : ∃ a : V, B.mem a A
  swap
  · obtain ⟨Z,hZ⟩ := H.empty
    refine ⟨Z, ?_⟩
    intro x
    constructor
    · intro hx
      exact False.elim ((hZ x).mp hx)
    · rintro ⟨hx,_⟩
      exact False.elim (hNonempty ⟨x,hx⟩)
  obtain ⟨a0,ha0A⟩ := hNonempty
  obtain ⟨E,hAE,hpE,hφLoc⟩ :=
    bounded_envelope_with_roots B H n φ A params
  let m : Nat := n + 1
  let N : Nat := m + φ.boundDepth
  have hmN : m ≤ N := by dsimp [N]; omega
  have hrootN : n < N := by dsimp [N,m]; omega
  let root : Fin N := ⟨n,hrootN⟩
  let singletonParam : Fin n → V :=
    fun i => Classical.choose (H.singleton (params i))
  have hParam (i : Fin n) (z : V) :
      B.mem z (singletonParam i) ↔ z = params i :=
    Classical.choose_spec (H.singleton (params i)) z
  -- The distinguished variable is physical slot n, parameters occupy
  -- slots n-1,...,0, and newly bound variables occupy slots >= n+1.
  let D : Fin N → V := fun q =>
    if hq : q.val < n then
      singletonParam ⟨n - 1 - q.val, by omega⟩
    else if q.val = n then A else E
  have hDroot : D root = A := by
    dsimp [D,root]
    simp
  have hDTail : ∀ q : Fin N, m ≤ q.val → D q = E := by
    intro q hq
    dsimp [D]
    rw [dif_neg (show ¬ q.val < n by omega)]
    rw [if_neg (show q.val ≠ n by omega)]
  have hDParam (i : Fin n) (z : V) :
      B.mem z (D (reverseSlot N m hmN i.succ)) ↔
        z = params i := by
    have hlt : (reverseSlot N m hmN i.succ).val < n := by
      dsimp [reverseSlot,m]
      omega
    have hIndex :
        (⟨n - 1 - (reverseSlot N m hmN i.succ).val,
           by omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [reverseSlot,m]
      omega
    dsimp [D]
    rw [dif_pos hlt]
    simpa only [hIndex] using hParam i z
  have hDE : ∀ (q : Fin N) (z : V),
      B.mem z (D q) → B.mem z E := by
    intro q z hz
    by_cases hlt : q.val < n
    · have hp := hParam (⟨n - 1 - q.val, by omega⟩ : Fin n) z
      have hparam : z = params ⟨n - 1 - q.val, by omega⟩ := by
        exact hp.mp (by simpa only [D, dif_pos hlt] using hz)
      rw [hparam]
      exact hpE _
    · by_cases heq : q.val = n
      · have hzA : B.mem z A := by
          simpa only [D, dif_neg hlt, if_pos heq] using hz
        exact hAE z hzA
      · have hzE : B.mem z E := by
          simpa only [D, dif_neg hlt, if_neg heq] using hz
        exact hzE
  obtain ⟨F⟩ := finite_assignment_frame_exists B H E N D hDE
  obtain ⟨S,hS⟩ := finite_frame_bounded_truth_exists
    B H E N m D F hDTail φ (by omega) (by
      dsimp [N,m]
      omega)
  have hST : ∀ t, B.mem t S → B.mem t F.sort := by
    intro t ht
    exact ((hS t).mp ht).1
  obtain ⟨Z,hZ⟩ := finite_frame_coordinate_image_exists
    B H E N D hDE F root S hST
  -- The arity-m environment read from an arbitrary represented tuple.
  let env (t : V) : Fin m → V :=
    fun i => F.decodeRaw B H E N D t
      (reverseSlot N m hmN i)
  have hRootSlot : reverseSlot N m hmN (0 : Fin m) = root := by
    apply Fin.ext
    dsimp [reverseSlot, root,m]
  have hEnvForTuple (t : V) (ht : B.mem t F.sort) :
      env t = Fin.cases (F.decodeRaw B H E N D t root) params := by
    funext i
    cases i using Fin.cases with
    | zero => exact congrArg (F.decodeRaw B H E N D t) hRootSlot
    | succ i =>
        have hDi := (F.decodeRaw_correct B H E N D t ht
          (reverseSlot N m hmN i.succ)).1
        exact (hDParam i _).mp hDi
  refine ⟨Z, ?_⟩
  intro x
  constructor
  · intro hxZ
    obtain ⟨hxD,t,htS,hDec⟩ := (hZ x).mp hxZ
    have hxA : B.mem x A := by simpa only [hDroot] using hxD
    have ht : B.mem t F.sort := hST t htS
    have hRaw := ((hS t).mp htS).2
    have henv := hEnvForTuple t ht
    have hEq : env t = Fin.cases x params := by
      simpa only [hDec] using henv
    have hφIn : φ.holdsIn B.mem E (Fin.cases x params) := by
      have hRawEnv : φ.holdsIn B.mem E (env t) := by
        simpa [env] using hRaw
      rw [hEq] at hRawEnv
      exact hRawEnv
    exact ⟨hxA, (hφLoc x hxA).mpr hφIn⟩
  · rintro ⟨hxA,hφ⟩
    -- Every tuple coordinate in the frame's tail may take a0 as filler;
    -- all values y reached by bounded quantifiers are in E.
    let values : Fin N → V := fun q =>
      if hq : q.val < n then params ⟨n - 1 - q.val, by omega⟩
      else if q.val = n then x else a0
    have hValues : ∀ q : Fin N, B.mem (values q) (D q) := by
      intro q
      by_cases hlt : q.val < n
      · have hv : values q = params ⟨n - 1 - q.val, by omega⟩ := by
          simp only [values, dif_pos hlt]
        have hd : D q = singletonParam ⟨n - 1 - q.val, by omega⟩ := by
          simp only [D, dif_pos hlt]
        rw [hv, hd]
        exact (hParam _ _).mpr rfl
      · by_cases heq : q.val = n
        · have hv : values q = x := by
            simp only [values, dif_neg hlt, if_pos heq]
          rw [hv]
          simpa only [D, dif_neg hlt, if_pos heq] using hxA
        · have hv : values q = a0 := by
            simp only [values, dif_neg hlt, if_neg heq]
          rw [hv]
          simpa only [D, dif_neg hlt, if_neg heq] using hAE a0 ha0A
    obtain ⟨t,ht,hDecode⟩ := finite_frame_realizes_raw_values
      B H E N D F values hValues
    have hRootVal : values root = x := by
      dsimp [values,root]
      simp
    have hEnv : env t = Fin.cases x params := by
      calc
        env t = Fin.cases (F.decodeRaw B H E N D t root) params :=
          hEnvForTuple t ht
        _ = Fin.cases x params := by
          rw [hDecode root, hRootVal]
    have hφIn : φ.holdsIn B.mem E (Fin.cases x params) :=
      (hφLoc x hxA).mp hφ
    have htS : B.mem t S := by
      apply (hS t).mpr
      refine ⟨ht, ?_⟩
      change φ.holdsIn B.mem E (env t)
      rw [hEnv]
      exact hφIn
    have hxD : B.mem x (D root) := by
      simpa only [hDroot] using hxA
    exact (hZ x).mpr ⟨hxD,t,htS,by rw [hDecode root, hRootVal]⟩

end NineAxiomBZ
