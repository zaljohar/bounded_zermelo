import DeltaZeroSyntax
import FiniteSupport
/-!
# Finite bound for the quantifiers of a Δ₀ formula

This module proves a necessary part of the full finite-axiomatization theorem:
all bounded witnesses, for a fixed formula and fixed free-variable domain,
lie inside one explicitly constructed finite Union envelope.

This is a semantic *localization theorem*, not Separation.  No truth-set
compiler and no instance of Separation are assumed.  In particular, it does
not depend on the open endpoint in NineAxiomBoundedSeparation.lean.

DRAFT: requires Lean elaboration; no Lean executable is present here.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The membership descendants of `seed` reachable in at most `d` steps.
This is a metatheoretic predicate; the lemma `reachable_envelope_exists`
constructs an *object-language set* representing it. -/
def Reachable (m : V → V → Prop) (seed : V) : Nat → V → Prop
  | 0, x => m x seed
  | d + 1, x =>
      Reachable m seed d x ∨
      ∃ y : V, Reachable m seed d y ∧ m x y

theorem reachable_step (m : V → V → Prop) (seed : V)
    (d : Nat) (x : V) :
    Reachable m seed d x → Reachable m seed (d + 1) x := by
  intro h
  exact Or.inl h

theorem reachable_child (m : V → V → Prop) (seed : V)
    (d : Nat) (x y : V) :
    Reachable m seed d y → m x y → Reachable m seed (d + 1) x := by
  intro hy hxy
  exact Or.inr ⟨y, hy, hxy⟩

theorem reachable_add (m : V → V → Prop) (seed : V)
    (k d : Nat) (x : V) :
    Reachable m seed k x → Reachable m seed (k + d) x := by
  intro hx
  induction d with
  | zero => simpa using hx
  | succ d ih =>
      rw [Nat.add_succ]
      exact reachable_step m seed (k + d) x ih

theorem reachable_mono (m : V → V → Prop) (seed : V)
    {k l : Nat} (hkl : k ≤ l) {x : V} :
    Reachable m seed k x → Reachable m seed l x := by
  intro hx
  have hsum : k + (l - k) = l := by omega
  rw [← hsum]
  exact reachable_add m seed k (l - k) x hx

/-- The maximum number of nested bounded quantifiers in a formula. -/
def DeltaZero.boundDepth : {n : Nat} → DeltaZero n → Nat
  | _, .equal _ _ => 0
  | _, .member _ _ => 0
  | _, .falsum => 0
  | _, .neg φ => φ.boundDepth
  | _, .conj φ ψ => max φ.boundDepth ψ.boundDepth
  | _, .bex _ φ => φ.boundDepth + 1

/-- Evaluate a bounded formula with the *additional* requirement that each
newly quantified object lie in the preselected envelope `E`.  The theorem
below removes this requirement when E is sufficiently deep. -/
def DeltaZero.holdsIn (m : V → V → Prop) (E : V) :
    {n : Nat} → DeltaZero n → (Fin n → V) → Prop
  | _, .equal i j, ρ => ρ i = ρ j
  | _, .member i j, ρ => m (ρ i) (ρ j)
  | _, .falsum, _ => False
  | _, .neg φ, ρ => ¬ φ.holdsIn m E ρ
  | _, .conj φ ψ, ρ => φ.holdsIn m E ρ ∧ ψ.holdsIn m E ρ
  | _, .bex i φ, ρ =>
      ∃ y : V, m y E ∧ m y (ρ i) ∧ φ.holdsIn m E (Fin.cases y ρ)

/-- Ordinary and envelope-restricted Δ₀ semantics coincide when the free
variables are within `k` membership steps of the initial seed and E contains
all descendants out to the formula's quantifier depth. -/
theorem DeltaZero.holds_iff_holdsIn
    (m : V → V → Prop) (E seed : V) :
    ∀ {n : Nat} (φ : DeltaZero n) (k : Nat) (ρ : Fin n → V),
      (∀ i, Reachable m seed k (ρ i)) →
      (∀ x, Reachable m seed (k + φ.boundDepth) x → m x E) →
      (φ.holds m ρ ↔ φ.holdsIn m E ρ) := by
  intro n φ
  induction φ with
  | equal i j =>
      intro k ρ _ _
      rfl
  | member i j =>
      intro k ρ _ _
      rfl
  | falsum =>
      intro k ρ _ _
      rfl
  | neg ψ ih =>
      intro k ρ hρ hE
      exact not_congr (ih k ρ hρ hE)
  | conj ψ θ ihψ ihθ =>
      intro k ρ hρ hE
      have hEψ : ∀ x : V,
          Reachable m seed (k + ψ.boundDepth) x → m x E := by
        intro x hx
        apply hE x
        apply reachable_mono m seed
          (show k + ψ.boundDepth ≤ k + max ψ.boundDepth θ.boundDepth
            from Nat.add_le_add_left (le_max_left _ _) k)
        exact hx
      have hEθ : ∀ x : V,
          Reachable m seed (k + θ.boundDepth) x → m x E := by
        intro x hx
        apply hE x
        apply reachable_mono m seed
          (show k + θ.boundDepth ≤ k + max ψ.boundDepth θ.boundDepth
            from Nat.add_le_add_left (le_max_right _ _) k)
        exact hx
      exact and_congr (ihψ k ρ hρ hEψ) (ihθ k ρ hρ hEθ)
  | @bex n i ψ ih =>
      intro k ρ hρ hE
      have hNextE : ∀ x : V,
          Reachable m seed ((k + 1) + ψ.boundDepth) x → m x E := by
        intro x hx
        apply hE x
        have heq : (k + 1) + ψ.boundDepth = k + (ψ.boundDepth + 1) := by
          omega
        simpa only [heq] using hx
      let ρy (y : V) : Fin (n + 1) → V :=
        @Fin.cases n (fun _ => V) y ρ
      have hEnv (y : V) (hy : m y (ρ i)) :
          ∀ j : Fin (n + 1),
            Reachable m seed (k + 1) (ρy y j) := by
        exact @Fin.cases n
          (fun j => Reachable m seed (k + 1) (ρy y j))
          (by simpa [ρy] using
            reachable_child m seed k y (ρ i) (hρ i) hy)
          (fun j => by simpa [ρy] using
            reachable_step m seed k (ρ j) (hρ j))
      constructor
      · rintro ⟨y, hy, hψ⟩
        have hyR : Reachable m seed (k + 1) y :=
          reachable_child m seed k y (ρ i) (hρ i) hy
        have hyE : m y E := by
          apply hNextE y
          exact reachable_mono m seed
            (show k + 1 ≤ (k + 1) + ψ.boundDepth by omega) hyR
        exact ⟨y, hyE, hy,
          (ih (k + 1) (ρy y) (hEnv y hy) hNextE).mp hψ⟩
      · rintro ⟨y, _hyE, hy, hψ⟩
        exact ⟨y, hy,
          (ih (k + 1) (ρy y) (hEnv y hy) hNextE).mpr hψ⟩

/-- Every finite-depth descendant predicate has a genuine representing set.
Only Pairing, Union and the nine operations are used, not Separation. -/
theorem reachable_envelope_exists (m : V → V → Prop)
    (H : NineAxioms m) (seed : V) :
    ∀ d : Nat, HasMembers m (Reachable m seed d) := by
  intro d
  induction d with
  | zero =>
      exact ⟨seed, fun x => Iff.rfl⟩
  | succ d ih =>
      obtain ⟨D, hD⟩ := ih
      obtain ⟨UD, hUD⟩ := H.setUnion D
      obtain ⟨E, hE⟩ := binary_union_exists m H D UD
      refine ⟨E, ?_⟩
      intro x
      constructor
      · intro hx
        rcases (hE x).mp hx with hXD | hXUD
        · exact Or.inl ((hD x).mp hXD)
        · obtain ⟨y, hyD, hxy⟩ := (hUD x).mp hXUD
          exact Or.inr ⟨y, (hD y).mp hyD, hxy⟩
      · intro hx
        rcases hx with hOld | hNew
        · exact (hE x).mpr (Or.inl ((hD x).mpr hOld))
        · obtain ⟨y, hyD, hxy⟩ := hNew
          exact (hE x).mpr (Or.inr ((hUD x).mpr
            ⟨y, (hD y).mpr hyD, hxy⟩))

/-- Choose one initial seed containing every possible x∈A and all fixed
parameter values.  Its construction needs only Pairing and binary Union. -/
theorem initial_seed_exists (B : Background V)
    (H : NineAxioms B.mem) (n : Nat) (A : V) (params : Fin n → V) :
    ∃ seed : V,
      (∀ x : V, B.mem x A → B.mem x seed) ∧
      (∀ i : Fin n, B.mem (params i) seed) := by
  obtain ⟨P, hP⟩ := finite_family_range_exists B H n params
  obtain ⟨seed, hseed⟩ := binary_union_exists B.mem H A P
  refine ⟨seed, ?_, ?_⟩
  · intro x hxA
    exact (hseed x).mpr (Or.inl hxA)
  · intro i
    exact (hseed (params i)).mpr
      (Or.inr ((hP (params i)).mpr ⟨i, rfl⟩))

/-- The restriction envelope can be chosen *uniformly* for every x∈A;
no x-dependent choices and no Separation instances enter the proof. -/
theorem bounded_formula_envelope_exists
    (B : Background V) (H : NineAxioms B.mem)
    (n : Nat) (φ : DeltaZero (n + 1))
    (A : V) (params : Fin n → V) :
    ∃ E : V, ∀ x : V, B.mem x A →
      (φ.holds B.mem (Fin.cases x params) ↔
       φ.holdsIn B.mem E (Fin.cases x params)) := by
  obtain ⟨seed, hA, hp⟩ := initial_seed_exists B H n A params
  obtain ⟨E, hE⟩ :=
    reachable_envelope_exists B.mem H seed φ.boundDepth
  refine ⟨E, ?_⟩
  intro x hxA
  let env : Fin (n + 1) → V :=
    @Fin.cases n (fun _ => V) x params
  have hρ : ∀ i : Fin (n + 1),
      Reachable B.mem seed 0 (env i) := by
    exact @Fin.cases n
      (fun i => Reachable B.mem seed 0 (env i))
      (by simpa [env] using hA x hxA)
      (fun j => by simpa [env] using hp j)
  have hBound : ∀ v,
      Reachable B.mem seed (0 + φ.boundDepth) v → B.mem v E := by
    intro v hv
    exact (hE v).mpr (by simpa using hv)
  simpa [env] using
    DeltaZero.holds_iff_holdsIn B.mem E seed φ 0 env hρ hBound

end NineAxiomBZ
