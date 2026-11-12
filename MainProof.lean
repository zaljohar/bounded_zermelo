import BoundedSeparationFinalDraft
/-!
Main theorem of the finite axiomatization of Delta_0 Separation.

All local project dependencies are source files included in this package.
The only mathematical hypotheses are `Background` and `NineAxioms`.

This source and its complete import chain were elaborated and kernel-checked
with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Unconditional endpoint: all instances of bounded separation
follow from the nine existence axioms and the separation-free background. -/
theorem nine_axioms_imply_delta_zero_separation
    (B : Background V) (H : NineAxioms B.mem) :
    BoundedSeparation B.mem :=
  bounded_separation_from_nine_completed_draft B H

end NineAxiomBZ

#print axioms NineAxiomBZ.nine_axioms_imply_delta_zero_separation
