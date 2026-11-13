import FoundationFreeFixedFrameCylindrification
import DepthBound
/-!
# Fixed-frame Δ₀ truth induction

A formula with `m` free variables is interpreted in a single physical frame
of `N` coordinates (`m + boundDepth ≤ N`). Variables use reversed indices:
variable 0 is physical coordinate m-1, variable 1 coordinate m-2, ... .
At a bounded quantifier the new variable occupies physical coordinate m.
This avoids the old unproved infinite coherent-frame interface.

All underlying object-level set existence theorems are imported as proofs
from the nine-axiom project, not postulated.

This Foundation-free adaptation has NOT been Lean-elaborated or kernel-checked.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

/-- Reversed de Bruijn coordinates for a fixed frame. -/
def reverseSlot (N m : Nat) (hm : m ≤ N) (i : Fin m) : Fin N :=
  ⟨m - 1 - i.val, by have hi := i.isLt; omega⟩

private theorem reverseSlot_zero (N m : Nat) (h : m + 1 ≤ N) :
    reverseSlot N (m + 1) h (0 : Fin (m + 1)) =
      (⟨m, by omega⟩ : Fin N) := by
  apply Fin.ext
  simp [reverseSlot]

private theorem reverseSlot_succ (N m : Nat)
    (h : m + 1 ≤ N) (h' : m ≤ N) (i : Fin m) :
    reverseSlot N (m + 1) h i.succ = reverseSlot N m h' i := by
  apply Fin.ext
  simp [reverseSlot]
  omega

/-- The next unused physical slot is distinct from every old variable. -/
private theorem reverseSlot_ne_new (N m : Nat) (h : m + 1 ≤ N)
    (i : Fin m) :
    reverseSlot N m (by omega) i ≠ (⟨m, by omega⟩ : Fin N) := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp [reverseSlot] at hv
  omega

/-- A finite frame has all possible bounded-truth sets for one fixed arity,
provided every freshly bound variable has the full local envelope E as
its coordinate domain. This uses `frame_cylindrification_exists_nf` in the
only non-Boolean case. -/
theorem finite_frame_bounded_truth_exists_nf
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (E : V) (N start : Nat) (D : Fin N → V)
    (F : FiniteAssignmentFrameNF B E N D)
    (hTail : ∀ i : Fin N, start ≤ i.val → D i = E) :
    ∀ {m : Nat} (φ : DeltaZero m), start ≤ m →
      (hbound : m + φ.boundDepth ≤ N) →
      HasMembers B.mem (fun t : V =>
        B.mem t F.sort ∧
        φ.holdsIn B.mem E
          (fun i => F.decodeRaw B H E N D t
            (reverseSlot N m (by omega) i))) := by
  classical
  intro m φ
  induction φ with
  | @equal n i j =>
      intro hstart hbound
      exact frame_all_equality_truth_exists_nf B H E N D F
        (reverseSlot N n (by omega) i)
        (reverseSlot N n (by omega) j)
  | @member n i j =>
      intro hstart hbound
      exact frame_all_membership_truth_exists_nf B H E N D F
        (reverseSlot N n (by omega) i)
        (reverseSlot N n (by omega) j)
  | @falsum n =>
      intro hstart hbound
      obtain ⟨Z,hZ⟩ := H.empty
      refine ⟨Z, ?_⟩
      intro t
      constructor
      · intro h
        exact False.elim ((hZ t).mp h)
      · rintro ⟨_, hFalse⟩
        exact False.elim hFalse
  | @neg n ψ ih =>
      intro hstart hbound
      obtain ⟨S,hS⟩ := ih hstart hbound
      obtain ⟨C,hC⟩ := H.difference F.sort S
      refine ⟨C, ?_⟩
      intro t
      constructor
      · intro htC
        obtain ⟨ht,hnS⟩ := (hC t).mp htC
        refine ⟨ht, ?_⟩
        intro hψ
        exact hnS ((hS t).mpr ⟨ht,hψ⟩)
      · rintro ⟨ht,hnψ⟩
        apply (hC t).mpr
        refine ⟨ht, ?_⟩
        intro htS
        exact hnψ ((hS t).mp htS).2
  | @conj n ψ θ ihψ ihθ =>
      intro hstart hbound
      have hbψ : n + ψ.boundDepth ≤ N := by
        have h := hbound
        simp only [DeltaZero.boundDepth] at h
        omega
      have hbθ : n + θ.boundDepth ≤ N := by
        have h := hbound
        simp only [DeltaZero.boundDepth] at h
        omega
      obtain ⟨S,hS⟩ := ihψ hstart hbψ
      obtain ⟨T,hT⟩ := ihθ hstart hbθ
      obtain ⟨I,hI⟩ := H.intersection S T
      refine ⟨I, ?_⟩
      intro t
      constructor
      · intro htI
        obtain ⟨htS,htT⟩ := (hI t).mp htI
        obtain ⟨ht,hψ⟩ := (hS t).mp htS
        exact ⟨ht,hψ,((hT t).mp htT).2⟩
      · rintro ⟨ht,hψ,hθ⟩
        exact (hI t).mpr ⟨(hS t).mpr ⟨ht,hψ⟩,
                               (hT t).mpr ⟨ht,hθ⟩⟩
  | @bex n i ψ ih =>
      intro hstart hbound
      have hnext : (n + 1) + ψ.boundDepth ≤ N := by
        have h := hbound
        simp only [DeltaZero.boundDepth] at h
        omega
      have hmn : n + 1 ≤ N := by omega
      have hOld : n ≤ N := by omega
      let k : Fin N := ⟨n, by omega⟩
      let j : Fin N := reverseSlot N n hOld i
      have hkj : j ≠ k := reverseSlot_ne_new N n hmn i
      have hkE : D k = E := hTail k hstart
      obtain ⟨S,hS⟩ := ih (by omega) hnext
      obtain ⟨M,hM⟩ := frame_all_membership_truth_exists_nf
        B H E N D F k j
      obtain ⟨I,hI⟩ := H.intersection S M
      have hIT : ∀ t, B.mem t I → B.mem t F.sort := by
        intro t ht
        exact ((hS t).mp ((hI t).mp ht).1).1
      obtain ⟨C,hC⟩ := frame_cylindrification_exists_nf
        B H E N D F k I hIT
      refine ⟨C, ?_⟩
      intro t
      have hSlot0 : reverseSlot N (n + 1) (by omega)
            (0 : Fin (n + 1)) = k := by
        exact reverseSlot_zero N n hmn
      have hSlotSucc (q : Fin n) :
          reverseSlot N (n + 1) (by omega) q.succ =
            reverseSlot N n hOld q :=
        reverseSlot_succ N n hmn hOld q
      let dec : V → Fin N → V := fun z q => F.decodeRaw B H E N D z q
      have hEnv (s : V)
          (hag : ∀ q : Fin N, q ≠ k → dec s q = dec t q) :
          (fun q : Fin (n + 1) => dec s
              (reverseSlot N (n + 1) (by omega) q)) =
          Fin.cases (dec s k)
            (fun q : Fin n => dec t (reverseSlot N n hOld q)) := by
        funext q
        cases q using Fin.cases with
        | zero => simp [hSlot0]
        | succ q =>
            simp only [Fin.cases_succ, hSlotSucc q]
            exact hag (reverseSlot N n hOld q) (reverseSlot_ne_new N n hmn q)
      constructor
      · intro htC
        obtain ⟨ht,s,hsI,hAgreement⟩ := (hC t).mp htC
        obtain ⟨hsS,hsM⟩ := (hI s).mp hsI
        obtain ⟨hs,hψ⟩ := (hS s).mp hsS
        obtain ⟨_,hMem⟩ := (hM s).mp hsM
        let y : V := dec s k
        have hyE : B.mem y E := by
          have hyD := (F.decodeRaw_correct B H E N D s hs k).1
          simpa only [hkE] using hyD
        have hBound : B.mem y (dec t j) := by
          have hjEq := hAgreement j hkj
          simpa only [y, hjEq] using hMem
        have hψ' : ψ.holdsIn B.mem E
            (Fin.cases y (fun q : Fin n => dec t (reverseSlot N n hOld q))) := by
          have hValEq := hEnv s hAgreement
          change ψ.holdsIn B.mem E
            (Fin.cases (dec s k)
              (fun q : Fin n => dec t (reverseSlot N n hOld q)))
          rw [← hValEq]
          simpa [dec] using hψ
        exact ⟨ht,y,hyE,hBound,hψ'⟩
      · rintro ⟨ht,y,hyE,hyBound,hψ⟩
        let values : Fin N → V := Function.update (dec t) k y
        have hValues : ∀ q : Fin N, B.mem (values q) (D q) := by
          intro q
          by_cases hq : q = k
          · subst q
            simpa [values, hkE] using hyE
          · have hqd := (F.decodeRaw_correct B H E N D t ht q).1
            simpa [values, Function.update, hq] using hqd
        obtain ⟨s,hs,hReal⟩ := finite_frame_realizes_raw_values_nf
          B H E N D F values hValues
        have hAgree : ∀ q : Fin N, q ≠ k → dec s q = dec t q := by
          intro q hq
          have h := hReal q
          simpa [values, Function.update, hq] using h
        have hsZero : dec s k = y := by
          have h := hReal k
          simpa [values] using h
        have hψs : ψ.holdsIn B.mem E
            (fun q : Fin (n + 1) => dec s
              (reverseSlot N (n + 1) (by omega) q)) := by
          have hValEq := hEnv s hAgree
          simpa only [hValEq, hsZero] using hψ
        have hsS : B.mem s S := (hS s).mpr ⟨hs,hψs⟩
        have hsM : B.mem s M := by
          apply (hM s).mpr
          refine ⟨hs, ?_⟩
          have hJ := hAgree j hkj
          change B.mem (dec s k) (dec s j)
          rw [hsZero, hJ]
          exact hyBound
        have hsI : B.mem s I := (hI s).mpr ⟨hsS,hsM⟩
        exact (hC t).mpr ⟨ht,s,hsI,hAgree⟩

end NineAxiomBZ.NoFoundation
