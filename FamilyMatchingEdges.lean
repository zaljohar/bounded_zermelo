import FiniteTaggedDomains
import FreshTag
/-!
# Matching graphs for an arbitrary finite family of tagged domains

This works with the *actual marker* chosen by `FiniteTaggedDomains`, rather
than invoking a separate tag-construction with an unrelated marker.
The matching graph is typed from the common raw envelope E to the ith
coordinate sort.

DRAFT: no Lean toolchain was available for elaboration.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Symmetry of unordered-pair representation. -/
theorem upair_swap (m : V → V → Prop) {p a b : V}
    (h : IsUPair m p a b) : IsUPair m p b a := by
  intro x
  constructor
  · intro hx
    rcases (h x).mp hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx
  · intro hx
    rcases hx with hx | hx
    · exact (h x).mpr (Or.inr hx)
    · exact (h x).mpr (Or.inl hx)

/-- A typed unoriented graph can be used in the reverse direction.
No new set needs to be constructed. -/
theorem typedEdges_reverse (m : V → V → Prop)
    (U W : V) (R : V → V → Prop) (G : V)
    (hG : TypedEdges m U W R G) :
    TypedEdges m W U (fun w u => R u w) G := by
  intro p
  constructor
  · intro hp
    obtain ⟨u, w, hu, hw, hpuw, hR⟩ := (hG p).mp hp
    exact ⟨w, u, hw, hu, upair_swap m hpuw, hR⟩
  · rintro ⟨w, u, hw, hu, hpwu, hR⟩
    exact (hG p).mpr ⟨u, w, hu, hw, upair_swap m hpwu, hR⟩

/-- For any coordinate, the raw-to-tag matching edges are represented by
an actual object set.  Support freshness plus extensionality shows that
the marker used by `fresh_tagging_graph_exists` is exactly the marker in
the finite family. -/
theorem family_matching_edges_exists
    (B : Background V) (H : NineAxioms B.mem)
    (E : V) (n : Nat) (D : Fin n → V)
    (hDE : ∀ (i : Fin n) (x : V),
      B.mem x (D i) → B.mem x E)
    (F : FiniteTaggedDomains B E n D) (i : Fin n) :
    ∃ G : V,
      TypedEdges B.mem E (F.U i)
        (fun x u => B.mem x (D i) ∧
          IsUPair B.mem u x (F.marker i)) G := by
  obtain ⟨m, hm, G, hG⟩ :=
    fresh_tagging_graph_exists B H (D i) (F.support i)
      (F.rawInSupport i)
  have hmark : m = F.marker i := by
    apply B.extensionality
    intro x
    exact (hm x).trans (F.supportSpec i x).symm
  -- A single set G represents all correct edges, not merely a relation
  -- specified in the metalanguage.
  refine ⟨G, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨a, u, ha, hua, hpau⟩ := (hG p).mp hp
    have hu : B.mem u (F.U i) := by
      apply (F.spec i u).mpr
      exact ⟨a, ha, hmark ▸ hua⟩
    exact ⟨a, u, hDE i a ha, hu, hpau,
      ⟨ha, hmark ▸ hua⟩⟩
  · rintro ⟨a, u, haE, hu, hpau, haD, huam⟩
    apply (hG p).mpr
    exact ⟨a, u, haD, hmark.symm ▸ huam, hpau⟩

end NineAxiomBZ
