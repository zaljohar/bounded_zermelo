import FoundationFreeFregeDoubleton
import FoundationFreeUniversalBridge

/-!
# Direct local Frege-1 construction under a hypothetical universal set

This replaces the most difficult missing step in the prior Foundation-free
attempt by a shorter construction than the original global formula in
Al-Johar (2020). It uses the *already derived* unordered Cartesian product:

    P2  = { t | t is an unordered pair }
    NP  = U \\ P2
    J   = (NP * NP) \\ intersecting(NP * NP)
    K   = intersecting(NP * P2)
    L   = (J ∘ K) ∩ K
    Two = P2 ∩ ⋃L
    One = P2 \\ Two.

If U is universal, `One` consists exactly of singleton sets. The key
finite-combinatorial lemma is `disjoint_nonpair_witnesses`: every doubleton
can be hit by two disjoint nonpairs. It uses no Foundation.

No Separation, Foundation, NF comprehension, or hidden set-existence axiom
is assumed. The construction is kernel-checked with Lean 4.20.0.
-/

universe u
namespace NineAxiomBZ.NoFoundation
variable {V : Type u}

private theorem intersection_test_on_pair
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (X T : V)
    (hT : ∀ t : V, B.mem t T ↔ B.mem t X ∧
      ∃ a b : V, IsUPair B.mem t a b ∧ Intersects B.mem a b)
    {t a b : V} (ht : IsUPair B.mem t a b) :
    B.mem t T ↔ B.mem t X ∧ Intersects B.mem a b := by
  constructor
  · intro h
    obtain ⟨hX, x, y, hxy, w, hwx, hwy⟩ := (hT t).mp h
    refine ⟨hX, ?_⟩
    rcases unordered_pair_endpoints_nf B ht hxy with h | h
    · obtain ⟨hax, hby⟩ := h
      refine ⟨w, ?_, ?_⟩
      · simpa [hax] using hwx
      · simpa [hby] using hwy
    · obtain ⟨hay, hbx⟩ := h
      refine ⟨w, ?_, ?_⟩
      · simpa [hay] using hwy
      · simpa [hbx] using hwx
  · rintro ⟨hX, w, hwa, hwb⟩
    exact (hT t).mpr ⟨hX, a, b, ht, w, hwa, hwb⟩

private theorem flipped_pair
    (m : V → V → Prop) {t a b : V}
    (h : IsUPair m t a b) : IsUPair m t b a := by
  intro z
  rw [h z]
  tauto

private theorem disj_symmetric (m : V → V → Prop) {a b : V}
    (h : DisjointSets m a b) : DisjointSets m b a := by
  intro z hz
  exact h z ⟨hz.2, hz.1⟩

/-- The characteristic predicate of all doubletons, using only non-pairs,
non-intersection, and intersection tests. -/
private theorem doubleton_iff_test
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (p : V) (hp : IsUnorderedPair B.mem p) :
    Doubleton B.mem p ↔ DisjointNonpairWitness B.mem p :=
  doubleton_iff_disjoint_nonpair_witnesses B H p hp

/-- In an unordered edge, a pair endpoint cannot equal a non-pair
endpoint. Thus a typed edge has a unique orientation. -/
private theorem typed_pair_orientation
    (B : BackgroundNoFoundation V)
    {t a b n p : V}
    (ha : ¬ IsUnorderedPair B.mem a)
    (hb : IsUnorderedPair B.mem b)
    (hn : ¬ IsUnorderedPair B.mem n)
    (hp : IsUnorderedPair B.mem p)
    (hab : IsUPair B.mem t a b)
    (hnp : IsUPair B.mem t n p) : a = n ∧ b = p := by
  rcases unordered_pair_endpoints_nf B hab hnp with h | h
  · exact h
  · obtain ⟨hap, hbn⟩ := h
    have haPair : IsUnorderedPair B.mem a := by
      simpa [hap] using hp
    exact False.elim (ha haPair)

/-- A set of all singleton objects is available under any hypothetical
universal object, using precisely the original T9 axioms. -/
theorem frege_one_if_universal
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (U : V) (hU : IsUniversal B U) : FregeOne B := by
  classical
  let m := B.mem
  obtain ⟨P2, hP2B⟩ := all_unordered_pairs_if_universal B H U hU
  have hP2 (x : V) : m x P2 ↔ IsUnorderedPair m x := by
    simpa only [m, IsUnorderedPair] using hP2B x
  obtain ⟨NP, hNPB⟩ := H.difference U P2
  have hNP0 (x : V) : m x NP ↔ m x U ∧ ¬ m x P2 := by
    simpa only [m] using hNPB x
  have hNP (t : V) : m t NP ↔ ¬ IsUnorderedPair m t := by
    rw [hNP0 t]
    change (m t U ∧ ¬ m t P2) ↔ _
    rw [hP2 t]
    exact and_iff_right (hU t)
  obtain ⟨G, hGB⟩ := unordered_product_without_foundation B H NP NP
  have hG0 (x : V) : m x G ↔
      ∃ u w : V, m u NP ∧ m w NP ∧ IsUPair m x u w := by
    simpa only [m] using hGB x
  obtain ⟨OG, hOGB⟩ := H.unorderedIntersection G
  have hOG (x : V) : m x OG ↔
      m x G ∧ ∃ a b : V, IsUPair m x a b ∧ Intersects m a b := by
    simpa only [m, Intersects] using hOGB x
  obtain ⟨J, hJB⟩ := H.difference G OG
  have hJ0 (x : V) : m x J ↔ m x G ∧ ¬ m x OG := by
    simpa only [m] using hJB x
  obtain ⟨I, hIB⟩ := unordered_product_without_foundation B H NP P2
  have hI0 (x : V) : m x I ↔
      ∃ u w : V, m u NP ∧ m w P2 ∧ IsUPair m x u w := by
    simpa only [m] using hIB x
  obtain ⟨K, hKB⟩ := H.unorderedIntersection I
  have hK0 (x : V) : m x K ↔
      m x I ∧ ∃ a b : V, IsUPair m x a b ∧ Intersects m a b := by
    simpa only [m, Intersects] using hKB x
  obtain ⟨C, hCB⟩ := H.unorderedComposition J K
  have hC (x : V) : m x C ↔
      ∃ a b c : V, IsUPair m x a c ∧
        (∃ p : V, m p J ∧ IsUPair m p a b) ∧
        (∃ p : V, m p K ∧ IsUPair m p b c) := by
    simpa only [m] using hCB x
  obtain ⟨L, hLB⟩ := H.intersection C K
  have hL (x : V) : m x L ↔ m x C ∧ m x K := by
    simpa only [m] using hLB x
  obtain ⟨UL, hULB⟩ := H.setUnion L
  have hUL (x : V) : m x UL ↔ ∃ y : V, m y L ∧ m x y := by
    simpa only [m] using hULB x
  obtain ⟨Two, hTwoB⟩ := H.intersection P2 UL
  have hTwo (x : V) : m x Two ↔ m x P2 ∧ m x UL := by
    simpa only [m] using hTwoB x
  obtain ⟨One, hOneB⟩ := H.difference P2 Two
  have hOne (x : V) : m x One ↔ m x P2 ∧ ¬ m x Two := by
    simpa only [m] using hOneB x

  have hG (z : V) : m z G ↔
      ∃ a b : V, ¬ IsUnorderedPair m a ∧ ¬ IsUnorderedPair m b ∧
        IsUPair m z a b := by
    rw [hG0 z]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (hNP a).mp ha, (hNP b).mp hb, hab⟩
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (hNP a).mpr ha, (hNP b).mpr hb, hab⟩

  have hJ (z : V) : m z J ↔
      ∃ a b : V, ¬ IsUnorderedPair m a ∧ ¬ IsUnorderedPair m b ∧
        IsUPair m z a b ∧ DisjointSets m a b := by
    rw [hJ0 z]
    constructor
    · rintro ⟨hzG, hzNotOG⟩
      obtain ⟨a, b, haNP, hbNP, hab⟩ := (hG z).mp hzG
      refine ⟨a, b, haNP, hbNP, hab, ?_⟩
      intro w hw
      apply hzNotOG
      exact (hOG z).mpr ⟨hzG, a, b, hab, ⟨w, hw.1, hw.2⟩⟩
    · rintro ⟨a, b, haNP, hbNP, hab, hdisj⟩
      have hzG : m z G := (hG z).mpr ⟨a, b, haNP, hbNP, hab⟩
      refine ⟨hzG, ?_⟩
      intro hzOG
      have htouch : Intersects m a b :=
        ((intersection_test_on_pair B H G OG hOG hab).mp hzOG).2
      obtain ⟨w, hwa, hwb⟩ := htouch
      exact hdisj w ⟨hwa, hwb⟩

  have hI (z : V) : m z I ↔
      ∃ a b : V, ¬ IsUnorderedPair m a ∧ IsUnorderedPair m b ∧
        IsUPair m z a b := by
    rw [hI0 z]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (hNP a).mp ha, (hP2 b).mp hb, hab⟩
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (hNP a).mpr ha, (hP2 b).mpr hb, hab⟩

  have hK (z : V) : m z K ↔
      ∃ a b : V, ¬ IsUnorderedPair m a ∧ IsUnorderedPair m b ∧
        IsUPair m z a b ∧ Intersects m a b := by
    constructor
    · intro hz
      have hzI : m z I := ((hK0 z).mp hz).1
      obtain ⟨a, b, haNP, hbPair, hab⟩ := (hI z).mp hzI
      have htouch : Intersects m a b :=
        ((intersection_test_on_pair B H I K hK0 hab).mp hz).2
      exact ⟨a, b, haNP, hbPair, hab, htouch⟩
    · rintro ⟨a, b, haNP, hbPair, hab, htouch⟩
      apply (intersection_test_on_pair B H I K hK0 hab).mpr
      exact ⟨(hI z).mpr ⟨a, b, haNP, hbPair, hab⟩, htouch⟩

  have hJtyped (edge a b : V)
      (hEdge : m edge J) (hab : IsUPair m edge a b) :
      ¬ IsUnorderedPair m a ∧ ¬ IsUnorderedPair m b ∧
        DisjointSets m a b := by
    obtain ⟨n, k, hn, hk, hnk, hdisj⟩ := (hJ edge).mp hEdge
    rcases unordered_pair_endpoints_nf B hab hnk with h | h
    · obtain ⟨han, hbk⟩ := h
      subst n
      subst k
      exact ⟨hn, hk, hdisj⟩
    · obtain ⟨hak, hbn⟩ := h
      subst k
      subst n
      exact ⟨hk, hn, disj_symmetric m hdisj⟩

  have hKtyped (edge a b : V)
      (hEdge : m edge K) (hab : IsUPair m edge a b)
      (haNP : ¬ IsUnorderedPair m a) :
      IsUnorderedPair m b ∧ Intersects m a b := by
    obtain ⟨n, p, hn, hp, hnp, htouch⟩ := (hK edge).mp hEdge
    rcases unordered_pair_endpoints_nf B hab hnp with h | h
    · obtain ⟨han, hbp⟩ := h
      subst n
      subst p
      exact ⟨hp, htouch⟩
    · obtain ⟨hap, hbn⟩ := h
      have haPair : IsUnorderedPair m a := by
        simpa [hap] using hp
      exact False.elim (haNP haPair)

  have hLspec (edge : V) : m edge L ↔
      ∃ n p k : V,
        ¬ IsUnorderedPair m n ∧ IsUnorderedPair m p ∧
        ¬ IsUnorderedPair m k ∧ IsUPair m edge n p ∧
        Intersects m n p ∧ DisjointSets m n k ∧ Intersects m k p := by
    constructor
    · intro heL
      have heC : m edge C := ((hL edge).mp heL).1
      have heK : m edge K := ((hL edge).mp heL).2
      obtain ⟨n, p, hnNP, hpPair, hnp, htouch⟩ := (hK edge).mp heK
      obtain ⟨a, b, c, hac, ⟨j, hj, hjab⟩,
          ⟨kedge, hkedge, hkbc⟩⟩ := (hC edge).mp heC
      obtain ⟨haNP, hbNP, hdab⟩ := hJtyped j a b hj hjab
      obtain ⟨hcPair, htouchbc⟩ := hKtyped kedge b c hkedge hkbc hbNP
      have hor := typed_pair_orientation B haNP hcPair hnNP hpPair hac hnp
      obtain ⟨han, hcp⟩ := hor
      subst a
      subst c
      exact ⟨n, p, b, hnNP, hpPair, hbNP, hnp,
        htouch, hdab, htouchbc⟩
    · rintro ⟨n, p, k, hnNP, hpPair, hkNP,
        hnp, htouchNP, hdisjNK, htouchKP⟩
      obtain ⟨jnk, hjnk⟩ := unordered_pair_exists m H n k
      obtain ⟨ekp, hekp⟩ := unordered_pair_exists m H k p
      have hj : m jnk J :=
        (hJ jnk).mpr ⟨n, k, hnNP, hkNP, hjnk, hdisjNK⟩
      have hk : m ekp K :=
        (hK ekp).mpr ⟨k, p, hkNP, hpPair, hekp, htouchKP⟩
      have heC : m edge C :=
        (hC edge).mpr ⟨n, k, p, hnp,
          ⟨jnk, hj, hjnk⟩, ⟨ekp, hk, hekp⟩⟩
      have heK : m edge K :=
        (hK edge).mpr ⟨n, p, hnNP, hpPair, hnp, htouchNP⟩
      exact (hL edge).mpr ⟨heC, heK⟩

  have hTwoSpec (t : V) : m t Two ↔
      IsUnorderedPair m t ∧ DisjointNonpairWitness m t := by
    rw [hTwo t]
    constructor
    · rintro ⟨htP, htUL⟩
      have htPair : IsUnorderedPair m t := (hP2 t).mp htP
      obtain ⟨edge, heL, hte⟩ := (hUL t).mp htUL
      obtain ⟨n, p, k, hnNP, hpPair, hkNP, hnp,
        htouchNP, hdNK, htouchKP⟩ := (hLspec edge).mp heL
      rcases (hnp t).mp hte with htn | htp
      · have : IsUnorderedPair m n := htn ▸ htPair
        exact False.elim (hnNP this)
      · refine ⟨htPair, n, k, hnNP, hkNP, hdNK, ?_, ?_⟩
        · simpa [htp] using htouchNP
        · simpa [htp] using htouchKP
    · rintro ⟨htPair, n, k, hnNP, hkNP, hdNK, htouchNT, htouchKT⟩
      obtain ⟨edge, hedge⟩ := unordered_pair_exists m H n t
      have heL : m edge L :=
        (hLspec edge).mpr ⟨n, t, k, hnNP, htPair, hkNP,
          hedge, htouchNT, hdNK, htouchKT⟩
      have htUL : m t UL :=
        (hUL t).mpr ⟨edge, heL, (hedge t).mpr (Or.inr rfl)⟩
      exact ⟨(hP2 t).mpr htPair, htUL⟩

  refine ⟨One, ?_⟩
  intro t
  change m t One ↔ ∃ x : V, ∀ y : V, m y t ↔ y = x
  rw [hOne t]
  constructor
  · rintro ⟨htP, htNotTwo⟩
    obtain ⟨a, b, hab⟩ := (hP2 t).mp htP
    have hSame : a = b := by
      by_contra hneq
      have hDouble : Doubleton m t := ⟨a, b, hab, hneq⟩
      have hWitness : DisjointNonpairWitness m t :=
        (doubleton_iff_test B H t ⟨a, b, hab⟩).mp hDouble
      exact htNotTwo ((hTwoSpec t).mpr ⟨⟨a, b, hab⟩, hWitness⟩)
    refine ⟨a, ?_⟩
    intro y
    rw [hab y, hSame]
    tauto
  · rintro ⟨a, hsingle⟩
    have hsinglem (y : V) : m y t ↔ y = a := by
      simpa only [m] using hsingle y
    have htPair : IsUnorderedPair m t := by
      refine ⟨a, a, ?_⟩
      intro y
      rw [hsinglem y]
      tauto
    have htP : m t P2 := (hP2 t).mpr htPair
    refine ⟨htP, ?_⟩
    intro htTwo
    have hDouble : Doubleton m t :=
      (doubleton_iff_test B H t htPair).mpr (((hTwoSpec t).mp htTwo).2)
    obtain ⟨b, c, hbc, hneq⟩ := hDouble
    have hba : b = a := (hsinglem b).mp ((hbc b).mpr (Or.inl rfl))
    have hca : c = a := (hsinglem c).mp ((hbc c).mpr (Or.inr rfl))
    exact hneq (hba.trans hca.symm)

/-- Thus the nine axioms exclude a universal set without Foundation. -/
theorem no_universal_from_nine
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem) :
    NoUniversal B := by
  intro U
  by_contra hNoMarker
  have hU : IsUniversal B U := by
    intro x
    by_contra hx
    exact hNoMarker ⟨x, hx⟩
  have hNoUniversal := no_universal_if_frege_one B H
    (frege_one_if_universal B H U hU)
  obtain ⟨x, hx⟩ := hNoUniversal U
  exact hx (hU x)

/-- Every bounded singleton image follows with no Foundation and without
an additional `NoUniversal` axiom. -/
theorem singleton_images_from_nine_no_foundation
    (B : BackgroundNoFoundation V) (H : NineAxioms B.mem)
    (A : V) : SingletonImageOn B.mem A := by
  exact singleton_image_if_no_universal B H (no_universal_from_nine B H) A

end NineAxiomBZ.NoFoundation
