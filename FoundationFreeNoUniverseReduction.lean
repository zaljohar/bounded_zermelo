import FoundationFreeTaggedMatching
import FoundationFreeOverlapSelector
/-!
# Why the no-universal-set lemma is the key missing assumption
If a universal set U admits the singleton-image set U^ι, axiom 8 gives
{x : x ∈ x}, and relative difference yields Russell's contradiction.
This proof needs no Foundation, and carefully keeps the singleton-image
requirement *conditional*, so it introduces no hidden assumption into T₉.
-/
universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- A singleton image just for a hypothetical universal set already
refutes its existence, via A₈ and Russell's argument. -/
theorem no_universal_from_global_singletons
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hGlobal : ∀ U : V, (∀ x : V, B.mem x U) → SingletonImageOn B.mem U) :
    NoUniversal B := by
  intro D
  by_contra hnone
  have hUniv : ∀ x : V, B.mem x D := by
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩
  obtain ⟨W, hW⟩ :=
    diagonal_membership_from_singleton_image B.mem H D (hGlobal D hUniv)
  obtain ⟨R, hR⟩ := H.difference D W
  have hRself : B.mem R R ↔ ¬ B.mem R R := by
    have hRR := hR R
    have hWR := hW R
    have hDR := hUniv R
    tauto
  tauto

/-- Consequently, if the global singleton-image case is discharged,
all bounded singleton images exist without Foundation.  The old proof
had required membership-cycle exclusions here. -/
theorem local_singletons_from_global_singletons
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (hGlobal : ∀ U : V, (∀ x : V, B.mem x U) → SingletonImageOn B.mem U)
    (A : V) : SingletonImageOn B.mem A := by
  exact singleton_image_if_no_universal B H
    (no_universal_from_global_singletons B H hGlobal) A

end NineAxiomBZ.NoFoundation
