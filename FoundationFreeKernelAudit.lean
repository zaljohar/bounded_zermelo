import FoundationFreeEquivalenceCandidate

/-!
Kernel audit for the Foundation-free endpoint.

Run with:

  lake env lean FoundationFreeKernelAudit.lean

The commands below force Lean to elaborate the endpoint declarations and
report every axiom on which they depend.
-/

#check NineAxiomBZ.NoFoundation.bounded_envelope_with_roots_nf
#check NineAxiomBZ.NoFoundation.bounded_separation_from_nine_no_foundation
#check NineAxiomBZ.NoFoundation.nine_axioms_imply_bounded_zermelo_no_foundation
#check NineAxiomBZ.NoFoundation.bounded_zermelo_iff_nine_no_foundation
#check NineAxiomBZ.NoFoundation.bounded_zermelo_iff_bzminus_plus_nine_no_foundation

#print axioms NineAxiomBZ.NoFoundation.bounded_envelope_with_roots_nf
#print axioms NineAxiomBZ.NoFoundation.bounded_separation_from_nine_no_foundation
#print axioms NineAxiomBZ.NoFoundation.nine_axioms_imply_bounded_zermelo_no_foundation
#print axioms NineAxiomBZ.NoFoundation.bounded_zermelo_iff_nine_no_foundation
#print axioms NineAxiomBZ.NoFoundation.bounded_zermelo_iff_bzminus_plus_nine_no_foundation
