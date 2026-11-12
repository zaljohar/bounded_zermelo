import TypedComposition
/-!
# Lifting all finite coordinate projections across one new tuple level

An important frame-construction induction step: if P_i represents the
projection from old tuples T to old coordinate sort U_i, and Γ represents
the prefix map from new tuples N to T, then all N-to-U_i projections
exist simultaneously. No Replacement is used: the index set is finite
externally and each witness is chosen separately.

DRAFT, NOT ELABORATED. No Separation or frame existence assumption.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- The finite family of lifted coordinate edge sets. The returned relation
on new tuples is the composite `prefix ; oldCoordinate_i`.

The relations `R` and `prefix` are only *specifications*: the corresponding
object-level graphs Γ and P_i are supplied as actual sets, and the resulting
edge sets are constructed by the nine operations. -/
theorem lift_finite_coordinate_projections
    (B : Background V) (H : NineAxioms B.mem)
    (n : Nat) (T N : V) (U : Fin n → V)
    (Γ : V) (P : Fin n → V)
    (pref : V → V → Prop)
    (coord : Fin n → V → V → Prop)
    (hNT : DisjointSort B.mem N T)
    (hNU : ∀ i : Fin n, DisjointSort B.mem N (U i))
    (hTU : ∀ i : Fin n, DisjointSort B.mem T (U i))
    (hΓ : TypedEdges B.mem N T pref Γ)
    (hP : ∀ i : Fin n,
      TypedEdges B.mem T (U i) (coord i) (P i)) :
    ∃ Q : Fin n → V, ∀ i : Fin n,
      TypedEdges B.mem N (U i)
        (fun t u => ∃ s : V,
          B.mem s T ∧ pref t s ∧ coord i s u) (Q i) := by
  classical
  have hEach (i : Fin n) :
      ∃ Q : V,
        TypedEdges B.mem N (U i)
          (fun t u => ∃ s : V,
            B.mem s T ∧ pref t s ∧ coord i s u) Q := by
    exact typed_composition_exists B H N T (U i) Γ (P i)
      pref (coord i) hNT (hNU i) (hTU i) hΓ (hP i)
  refine ⟨(fun i => Classical.choose (hEach i)), ?_⟩
  intro i
  exact Classical.choose_spec (hEach i)

end NineAxiomBZ
