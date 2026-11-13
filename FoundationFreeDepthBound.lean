import DepthBound
import FoundationFreeFrameInfrastructure

/-!
The standard Δ₀ finite-depth localization lemmas are independent of
Foundation.  Only the finite seed-collection lemma needed adapting to the
Foundation-free background structure.

Kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- A set containing every element of A and all parameter values. -/
theorem initial_seed_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (n : Nat) (A : V) (params : Fin n → V) :
    ∃ seed : V,
      (∀ x : V, B.mem x A → B.mem x seed) ∧
      (∀ i : Fin n, B.mem (params i) seed) := by
  obtain ⟨P, hP⟩ := finite_family_range_exists_nf B H n params
  obtain ⟨seed, hseed⟩ := binary_union_exists B.mem H A P
  refine ⟨seed, ?_, ?_⟩
  · intro x hxA
    exact (hseed x).mpr (Or.inl hxA)
  · intro i
    exact (hseed (params i)).mpr
      (Or.inr ((hP (params i)).mpr ⟨i, rfl⟩))

end NineAxiomBZ.NoFoundation
