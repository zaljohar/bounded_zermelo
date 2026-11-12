import FiniteFrameDecoding
import FiniteAtomicTruth
/-!
Bridge from the new complete finite assignment frames to the existing
atomic equality/membership truth-set constructions. This is a definitional
interface, not a hypothesis asserting that atomic truth sets exist.

The two results here cover distinct coordinates. Diagonal atomic instances
and coherence across quantified extensions must still be integrated.
No Lean toolchain was available for elaboration.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Extract the concrete finite tagged family from a complete assignment
frame. This does not need a new existence axiom. -/
def FiniteAssignmentFrame.asTaggedDomains
    (B : Background V) (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D) :
    FiniteTaggedDomains B E n D :=
  { U := F.tagSort
    marker := F.marker
    support := F.support
    supportSpec := F.supportSpec
    rawInSupport := F.rawInSupport
    spec := F.tagSpec
    rawDisjoint := F.rawDisjoint
    pairwise := F.tagPairwiseDisjoint
    markerFresh := F.markerFresh }

/-- The frame's actual object-level coordinate graphs satisfy the typed
projection interface used by the atomic relation algebra. -/
def FiniteAssignmentFrame.asCoordinateProjections
    (B : Background V) (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D) :
    FiniteCoordinateProjections B E n D
      (F.asTaggedDomains B E n D) F.sort :=
  { P := F.projectionGraph
    coord := F.projectionRel
    disjoint := F.tupleTagDisjoint
    edges := F.projectionSpec }

/-- Actual truth-set existence for equal raw values on two *distinct*
coordinates of a represented finite assignment frame. -/
theorem finite_frame_equality_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      ∃ u v : V,
        B.mem u (F.tagSort i) ∧ B.mem v (F.tagSort j) ∧
        F.projectionRel i t u ∧ F.projectionRel j t v ∧
        ∃ a : V, B.mem a E ∧
          (B.mem a (D i) ∧ IsUPair B.mem u a (F.marker i)) ∧
          (B.mem a (D j) ∧ IsUPair B.mem v a (F.marker j))) := by
  exact finite_assignment_equality_truth_exists
    B H E n D F.rawBound (F.asTaggedDomains B E n D)
    F.sort (F.asCoordinateProjections B E n D) i j hij

/-- Actual truth-set existence for directed membership of distinct raw
coordinate values. This is the nonstratified atomic operation. -/
theorem finite_frame_membership_truth_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (F : FiniteAssignmentFrame B E n D)
    (i j : Fin n) (hij : i ≠ j) :
    HasMembers B.mem (fun t : V =>
      B.mem t F.sort ∧
      ∃ u v : V,
        B.mem u (F.tagSort i) ∧ B.mem v (F.tagSort j) ∧
        F.projectionRel i t u ∧ F.projectionRel j t v ∧
        ∃ b : V, B.mem b E ∧
          (∃ a : V, B.mem a (D i) ∧
            IsUPair B.mem u a (F.marker i) ∧ B.mem a b) ∧
          (B.mem b (D j) ∧ IsUPair B.mem v b (F.marker j))) := by
  exact finite_assignment_membership_truth_exists
    B H E n D F.rawBound (F.asTaggedDomains B E n D)
    F.sort (F.asCoordinateProjections B E n D) i j hij

end NineAxiomBZ
