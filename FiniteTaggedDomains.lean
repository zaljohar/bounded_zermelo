import FreshSupportDisjoint
import FiniteSupport
/-!
# Finite families of mutually disjoint tagged coordinate domains

This file proves, by induction on a *metatheoretically finite* index set,
that arbitrary finite families of object-level sets admit pairwise disjoint
tagged copies. Every tag avoids all elements of a common raw envelope E.

No Separation instance is used. The construction uses a finite support set,
Foundation to exclude finite membership cycles, and the nine operations.

This file and its imported proof chain were checked by the Lean 4.20.0 kernel.
-/

universe u
namespace NineAxiomBZ
variable {V : Type u}

/-- Exchange the two arguments of disjointness. -/
theorem disjointSort_symm
    (m : V → V → Prop) {U W : V}
    (h : DisjointSort m U W) : DisjointSort m W U := by
  intro w v hw hv heq
  exact h v w hv hw heq.symm

/-- Each `U i` is a copy of `D i`, represented by `{x,marker i}`.
The copies are pairwise disjoint and avoid the raw envelope E.
The envelope contains the values of each domain, not necessarily the
individual domain sets as members. -/
structure FiniteTaggedDomains (B : Background V)
    (E : V) (n : Nat) (D : Fin n → V) where
  U : Fin n → V
  marker : Fin n → V
  support : Fin n → V
  supportSpec : ∀ (i : Fin n) (z : V),
    B.mem z (marker i) ↔ z = support i
  rawInSupport : ∀ i : Fin n, B.mem (D i) (support i)
  spec : ∀ (i : Fin n) (u : V), B.mem u (U i) ↔
    ∃ x : V, B.mem x (D i) ∧ IsUPair B.mem u x (marker i)
  rawDisjoint : ∀ i : Fin n, DisjointSort B.mem E (U i)
  pairwise : ∀ i j : Fin n, i ≠ j →
    DisjointSort B.mem (U i) (U j)
  markerFresh : ∀ (i : Fin n) (x : V),
    B.mem x E → ¬ B.mem (marker i) x

/-- *Unconditional finite tagging theorem* (conditional only on the
ambient Background and nine axioms).  This is not the still-open
`FiniteFrameObligation`: it supplies its pairwise-disjoint coordinate
sorts, but not the complete tuple decoder or its atomic truth sets.

The induction introduces a fresh coordinate at index 0, shifts all old
coordinates by `Fin.succ`, and registers the old sorts in a support set W.
The support-based freshness theorem makes the new sort disjoint from every
old sort, independently of the length of the list. -/
theorem finite_tagged_domains_exist
    (B : Background V) (H : NineAxioms B.mem) (E : V) :
    ∀ (n : Nat) (D : Fin n → V),
      (∀ (i : Fin n) (x : V), B.mem x (D i) → B.mem x E) →
      Nonempty (FiniteTaggedDomains B E n D) := by
  intro n
  induction n with
  | zero =>
      intro D hDE
      refine ⟨{
        U := Fin.elim0
        marker := Fin.elim0
        support := Fin.elim0
        supportSpec := ?_
        rawInSupport := ?_
        spec := ?_
        rawDisjoint := ?_
        pairwise := ?_
        markerFresh := ?_
      }⟩
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
  | succ n ih =>
      intro D hDE
      let Dtail : Fin n → V := fun i => D i.succ
      have hDEtail : ∀ (i : Fin n) (x : V),
          B.mem x (Dtail i) → B.mem x E := by
        intro i x hx
        exact hDE i.succ x hx
      obtain ⟨old⟩ := ih Dtail hDEtail
      -- The actual object W contains E, the new raw domain D 0, and
      -- every previously constructed coordinate sort as an element.
      obtain ⟨W, hEW, hDW, hOldW, _⟩ :=
        finite_registry_exists B H n 0 old.U Fin.elim0 E (D 0)
      -- Fresh copies are constructed by the nine operations; N and the
      -- projection graphs are not used yet, but their existence gives
      -- the required freshness against *every* Y∈W.
      obtain ⟨m, F, N, Γ, Λ, hm, hF, hN, hΓ, hΛ, hFresh⟩ :=
        fresh_both_projections_with_support B H (D 0) E W hDW hEW
      have hFE : DisjointSort B.mem F E := (hFresh E hEW).1
      have hFUi (i : Fin n) :
          DisjointSort B.mem F (old.U i) :=
        (hFresh (old.U i) (hOldW i)).1
      let Unew : Fin (n + 1) → V := Fin.cases F old.U
      let Mnew : Fin (n + 1) → V := Fin.cases m old.marker
      let Wnew : Fin (n + 1) → V := Fin.cases W old.support
      refine ⟨{
        U := Unew
        marker := Mnew
        support := Wnew
        supportSpec := ?_
        rawInSupport := ?_
        spec := ?_
        rawDisjoint := ?_
        pairwise := ?_
        markerFresh := ?_
      }⟩
      · intro i z
        cases i using Fin.cases with
        | zero =>
            exact hm z
        | succ j =>
            exact old.supportSpec j z
      · intro i
        cases i using Fin.cases with
        | zero =>
            exact hDW
        | succ j =>
            exact old.rawInSupport j
      · intro i u
        cases i using Fin.cases with
        | zero =>
            exact hF u
        | succ j =>
            exact old.spec j u
      · intro i
        cases i using Fin.cases with
        | zero =>
            exact disjointSort_symm B.mem hFE
        | succ j =>
            exact old.rawDisjoint j
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (hij rfl)
            | succ k =>
                exact hFUi k
        | succ k =>
            cases j using Fin.cases with
            | zero =>
                exact disjointSort_symm B.mem (hFUi k)
            | succ l =>
                apply old.pairwise k l
                intro hkl
                exact hij (congrArg Fin.succ hkl)
      · intro i x hxE
        cases i using Fin.cases with
        | zero =>
            exact (hFresh E hEW).2.2 x hxE
        | succ j =>
            exact old.markerFresh j x hxE

end NineAxiomBZ
