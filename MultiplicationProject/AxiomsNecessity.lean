/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Necessity of the axioms

In a reduced factorial monoid, the axioms tower faithfulness, TD, and CFI all HOLD;
and if the atom set is countably infinite, CPL⁺ holds as well.
This is the easy ("necessity") direction of the characterization theorem:
together with `thm_A_implies_B` it upgrades the main result to an
exact iff (see `thm_characterization` in MainTheorem.lean).

The workhorse is the unique-atomic-multiset calculus: in a reduced factorial
monoid every element m has a canonical multiset of atoms `factorMS m` with
product m, and the assignment is additive (`factorMS_mul`). CFI then follows
from countwise multiset bookkeeping on disjoint supports.
-/
import MultiplicationProject.APDRedundancy

set_option maxHeartbeats 400000

noncomputable section

open Multiset

/-! ## Uniqueness of atomic multisets -/

/-- In a reduced factorial monoid, two multisets of atoms with the same
    product are equal. -/
lemma multiset_factorization_unique {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M)
    {s t : Multiset M} (hs : ∀ a ∈ s, Irreducible a) (ht : ∀ a ∈ t, Irreducible a)
    (h : s.prod = t.prod) : s = t := by
  by_cases hu : IsUnit s.prod
  · -- a unit product forces both multisets to be empty
    have hs0 : s = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      exact (hs a ha).1 (isUnit_of_dvd_unit (Multiset.dvd_prod ha) hu)
    have ht0 : t = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      exact (ht a ha).1 (isUnit_of_dvd_unit (Multiset.dvd_prod ha) (h ▸ hu))
    rw [hs0, ht0]
  · obtain ⟨u, _, hu_uniq⟩ := h_fact s.prod hu
    have h1 : s = u := hu_uniq s ⟨hs, rfl⟩
    have h2 : t = u := hu_uniq t ⟨ht, h.symm⟩
    rw [h1, h2]

/-! ## The canonical factorization multiset -/

open Classical in
/-- The canonical multiset of atoms of m in a factorial monoid
    (empty for units). -/
def factorMS {M : Type*} [CommMonoid M] (h_fact : Factorial M) (m : M) :
    Multiset M :=
  if h : IsUnit m then 0 else ((h_fact m h).exists).choose

lemma factorMS_spec {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    (∀ a ∈ factorMS h_fact m, Irreducible a) ∧ (factorMS h_fact m).prod = m := by
  unfold factorMS
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · intro a ha
      simp at ha
    · simp [h_reduced m h]
  · exact ((h_fact m h).exists).choose_spec

lemma factorMS_atoms {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    ∀ a ∈ factorMS h_fact m, Irreducible a :=
  (factorMS_spec h_reduced h_fact m).1

lemma factorMS_prod {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    (factorMS h_fact m).prod = m :=
  (factorMS_spec h_reduced h_fact m).2

/-- Any multiset of atoms with product m IS the canonical one. -/
lemma factorMS_eq {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M)
    {m : M} {t : Multiset M}
    (ht : ∀ a ∈ t, Irreducible a) (hp : t.prod = m) :
    t = factorMS h_fact m :=
  multiset_factorization_unique h_reduced h_fact ht
    (factorMS_atoms h_reduced h_fact m)
    (by rw [hp, factorMS_prod h_reduced h_fact])

/-- Additivity: the canonical multiset of a product is the sum of the
    canonical multisets. This is the free-monoid isomorphism in multiset
    clothing. -/
lemma factorMS_mul {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (a b : M) :
    factorMS h_fact (a * b) = factorMS h_fact a + factorMS h_fact b := by
  refine (factorMS_eq h_reduced h_fact ?_ ?_).symm
  · intro q hq
    rcases Multiset.mem_add.mp hq with h | h
    · exact factorMS_atoms h_reduced h_fact a q h
    · exact factorMS_atoms h_reduced h_fact b q h
  · rw [Multiset.prod_add, factorMS_prod h_reduced h_fact,
        factorMS_prod h_reduced h_fact]

lemma factorMS_le_of_dvd {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M)
    {d m : M} (h : d ∣ m) :
    factorMS h_fact d ≤ factorMS h_fact m := by
  obtain ⟨c, rfl⟩ := h
  rw [factorMS_mul h_reduced h_fact]
  exact self_le_add_right _ _

/-! ## Countwise multiset lemmas (pure combinatorics) -/

/-- Cancellation across a disjoint split: if t + r = t' + r' with t, t'
    supported in u and r, r' supported in v, u and v disjoint, then the
    parts agree. -/
lemma eq_of_add_eq_add_of_le_disjoint {α : Type*} [DecidableEq α]
    {t r t' r' u v : Multiset α}
    (ht : t ≤ u) (hr : r ≤ v) (ht' : t' ≤ u) (hr' : r' ≤ v)
    (h : t + r = t' + r') (hd : ∀ a ∈ u, a ∉ v) :
    t = t' ∧ r = r' := by
  have key : ∀ a, t.count a = t'.count a ∧ r.count a = r'.count a := by
    intro a
    have h1 := Multiset.count_le_of_le a ht
    have h2 := Multiset.count_le_of_le a hr
    have h3 := Multiset.count_le_of_le a ht'
    have h4 := Multiset.count_le_of_le a hr'
    have h5 : t.count a + r.count a = t'.count a + r'.count a := by
      rw [← Multiset.count_add, ← Multiset.count_add, h]
    by_cases hu : a ∈ u
    · have hv : v.count a = 0 := Multiset.count_eq_zero.mpr (hd a hu)
      omega
    · have hu0 : u.count a = 0 := Multiset.count_eq_zero.mpr hu
      omega
  exact ⟨Multiset.ext.mpr fun a => (key a).1, Multiset.ext.mpr fun a => (key a).2⟩

/-- Splitting along a disjoint decomposition: if w₀ + w₁ = u + v with u, v
    disjoint, then intersecting with u and v splits each wᵢ, and the u-parts
    (resp. v-parts) reassemble u (resp. v). -/
lemma split_add_eq_add {α : Type*} [DecidableEq α]
    {w₀ w₁ u v : Multiset α}
    (h : w₀ + w₁ = u + v) (hd : ∀ a ∈ u, a ∉ v) :
    (w₀ ∩ u) + (w₀ ∩ v) = w₀ ∧ (w₁ ∩ u) + (w₁ ∩ v) = w₁ ∧
    (w₀ ∩ u) + (w₁ ∩ u) = u ∧ (w₀ ∩ v) + (w₁ ∩ v) = v := by
  have key : ∀ a : α,
      (w₀ ∩ u).count a + (w₀ ∩ v).count a = w₀.count a ∧
      (w₁ ∩ u).count a + (w₁ ∩ v).count a = w₁.count a ∧
      (w₀ ∩ u).count a + (w₁ ∩ u).count a = u.count a ∧
      (w₀ ∩ v).count a + (w₁ ∩ v).count a = v.count a := by
    intro a
    have h5 : w₀.count a + w₁.count a = u.count a + v.count a := by
      rw [← Multiset.count_add, ← Multiset.count_add, h]
    simp only [Multiset.count_inter]
    by_cases hu : a ∈ u
    · have hv : v.count a = 0 := Multiset.count_eq_zero.mpr (hd a hu)
      omega
    · have hu0 : u.count a = 0 := Multiset.count_eq_zero.mpr hu
      omega
  refine ⟨Multiset.ext.mpr fun a => ?_, Multiset.ext.mpr fun a => ?_,
          Multiset.ext.mpr fun a => ?_, Multiset.ext.mpr fun a => ?_⟩
  · rw [Multiset.count_add]; exact (key a).1
  · rw [Multiset.count_add]; exact (key a).2.1
  · rw [Multiset.count_add]; exact (key a).2.2.1
  · rw [Multiset.count_add]; exact (key a).2.2.2

/-! ## Necessity of tower faithfulness, TD, CFI -/

/-- In a reduced factorial monoid, tower faithfulness holds: powers of an atom are distinct. -/
theorem tower_faithful_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) : TowerFaithful M := by
  intro p hp a b hab
  have hp_irr : Irreducible p := hp
  have hrep : Multiset.replicate a p = Multiset.replicate b p := by
    apply multiset_factorization_unique h_reduced h_fact
    · intro q hq
      rw [Multiset.eq_of_mem_replicate hq]
      exact hp_irr
    · intro q hq
      rw [Multiset.eq_of_mem_replicate hq]
      exact hp_irr
    · rw [Multiset.prod_replicate, Multiset.prod_replicate]
      exact hab
  simpa using congrArg Multiset.card hrep

/-- In a reduced factorial monoid, TD holds: an element that is a positive
    power of two atoms forces the atoms to coincide. -/
theorem TD_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) : TD M := by
  intro p q hp hq k m hk hm hpq
  have hp_irr : Irreducible p := hp
  have hq_irr : Irreducible q := hq
  have hrep : Multiset.replicate k p = Multiset.replicate m q := by
    apply multiset_factorization_unique h_reduced h_fact
    · intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      exact hp_irr
    · intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      exact hq_irr
    · rw [Multiset.prod_replicate, Multiset.prod_replicate]
      exact hpq
  have hmem : p ∈ Multiset.replicate m q := by
    rw [← hrep]
    exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
  exact Multiset.eq_of_mem_replicate hmem

/-- In a reduced factorial monoid, CFI holds: for coprime x, y the
    coordinatewise assembly map μ₂ is a bijection. The inverse is the
    canonical disassembly d ↦ (x-part of d, y-part of d) computed on
    factorization multisets. -/
theorem CFI_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) : CFI M := by
  classical
  intro x y hxy
  -- disjointness of the atomic supports
  have hdisj : ∀ a ∈ factorMS h_fact x, a ∉ factorMS h_fact y := by
    intro a hax hay
    have ha_irr : Irreducible a := factorMS_atoms h_reduced h_fact x a hax
    have hdx : a ∣ x := by
      have := Multiset.dvd_prod hax
      rwa [factorMS_prod h_reduced h_fact] at this
    have hdy : a ∣ y := by
      have := Multiset.dvd_prod hay
      rwa [factorMS_prod h_reduced h_fact] at this
    exact hxy a ha_irr hdx hdy
  -- component determination: a product of an x-divisor and a y-divisor
  -- determines both factors
  have hcomp : ∀ fx fy fx' fy' : M, fx ∣ x → fy ∣ y → fx' ∣ x → fy' ∣ y →
      fx * fy = fx' * fy' → fx = fx' ∧ fy = fy' := by
    intro fx fy fx' fy' h1 h2 h3 h4 h5
    have e1 : factorMS h_fact fx + factorMS h_fact fy
            = factorMS h_fact fx' + factorMS h_fact fy' := by
      rw [← factorMS_mul h_reduced h_fact, ← factorMS_mul h_reduced h_fact, h5]
    have hparts := eq_of_add_eq_add_of_le_disjoint
      (factorMS_le_of_dvd h_reduced h_fact h1)
      (factorMS_le_of_dvd h_reduced h_fact h2)
      (factorMS_le_of_dvd h_reduced h_fact h3)
      (factorMS_le_of_dvd h_reduced h_fact h4) e1 hdisj
    constructor
    · calc fx = (factorMS h_fact fx).prod :=
            (factorMS_prod h_reduced h_fact fx).symm
        _ = (factorMS h_fact fx').prod := by rw [hparts.1]
        _ = fx' := factorMS_prod h_reduced h_fact fx'
    · calc fy = (factorMS h_fact fy).prod :=
            (factorMS_prod h_reduced h_fact fy).symm
        _ = (factorMS h_fact fy').prod := by rw [hparts.2]
        _ = fy' := factorMS_prod h_reduced h_fact fy'
  constructor
  · -- injectivity
    rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ ⟨⟨f', hf'⟩, ⟨g', hg'⟩⟩ heq
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
      at hf hg hf' hg'
    have hval : ∀ i : Fin 2, f i * g i = f' i * g' i := by
      intro i
      have h1 := congrArg (fun z => z.val i) heq
      simpa [labeledFactorizationMul] using h1
    have hfdvd : ∀ i : Fin 2, f i ∣ x := by
      rw [Fin.forall_fin_two]
      exact ⟨hf ▸ dvd_mul_right (f 0) (f 1), hf ▸ dvd_mul_left (f 1) (f 0)⟩
    have hgdvd : ∀ i : Fin 2, g i ∣ y := by
      rw [Fin.forall_fin_two]
      exact ⟨hg ▸ dvd_mul_right (g 0) (g 1), hg ▸ dvd_mul_left (g 1) (g 0)⟩
    have hfdvd' : ∀ i : Fin 2, f' i ∣ x := by
      rw [Fin.forall_fin_two]
      exact ⟨hf' ▸ dvd_mul_right (f' 0) (f' 1), hf' ▸ dvd_mul_left (f' 1) (f' 0)⟩
    have hgdvd' : ∀ i : Fin 2, g' i ∣ y := by
      rw [Fin.forall_fin_two]
      exact ⟨hg' ▸ dvd_mul_right (g' 0) (g' 1), hg' ▸ dvd_mul_left (g' 1) (g' 0)⟩
    have hkey : ∀ i : Fin 2, f i = f' i ∧ g i = g' i := fun i =>
      hcomp (f i) (g i) (f' i) (g' i)
        (hfdvd i) (hgdvd i) (hfdvd' i) (hgdvd' i) (hval i)
    refine Prod.ext ?_ ?_ <;> apply Subtype.ext <;> funext i
    · exact (hkey i).1
    · exact (hkey i).2
  · -- surjectivity: canonical disassembly along the supports of x and y
    rintro ⟨w, hw⟩
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hw
    have hsum : factorMS h_fact (w 0) + factorMS h_fact (w 1)
              = factorMS h_fact x + factorMS h_fact y := by
      rw [← factorMS_mul h_reduced h_fact, ← factorMS_mul h_reduced h_fact, hw]
    obtain ⟨hsplit0, hsplit1, hsplitx, hsplity⟩ := split_add_eq_add hsum hdisj
    refine ⟨(⟨fun i => ((factorMS h_fact (w i)) ∩ (factorMS h_fact x)).prod, ?_⟩,
             ⟨fun i => ((factorMS h_fact (w i)) ∩ (factorMS h_fact y)).prod, ?_⟩),
            ?_⟩
    · simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
      rw [← Multiset.prod_add, hsplitx, factorMS_prod h_reduced h_fact]
    · simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
      rw [← Multiset.prod_add, hsplity, factorMS_prod h_reduced h_fact]
    · apply Subtype.ext
      funext i
      have hrecomb : ∀ j : Fin 2,
          ((factorMS h_fact (w j)) ∩ (factorMS h_fact x)).prod *
          ((factorMS h_fact (w j)) ∩ (factorMS h_fact y)).prod = w j := by
        rw [Fin.forall_fin_two]
        constructor
        · rw [← Multiset.prod_add, hsplit0, factorMS_prod h_reduced h_fact]
        · rw [← Multiset.prod_add, hsplit1, factorMS_prod h_reduced h_fact]
      simpa [labeledFactorizationMul] using hrecomb i

/-! ## Necessity of WFD -/

/-- In a reduced factorial monoid, WFD holds: a strict divisor has a
    strictly smaller atomic multiset. -/
theorem WFD_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) : WFD M := by
  have hsub : Subrelation (fun a b : M => StrictDvd a b)
      (InvImage (· < ·) (fun x : M => Multiset.card (factorMS h_fact x))) := by
    intro a b hab
    obtain ⟨c, hc_unit, rfl⟩ := hab
    show Multiset.card (factorMS h_fact a)
       < Multiset.card (factorMS h_fact (a * c))
    rw [factorMS_mul h_reduced h_fact, Multiset.card_add]
    have hc_card : (factorMS h_fact c).card ≠ 0 := by
      intro h0
      have hc_empty : factorMS h_fact c = 0 := Multiset.card_eq_zero.mp h0
      have hprod := factorMS_prod h_reduced h_fact c
      rw [hc_empty] at hprod
      simp only [Multiset.prod_zero] at hprod
      exact hc_unit (hprod ▸ isUnit_one)
    omega
  exact Subrelation.wf hsub (InvImage.wf _ Nat.lt_wfRel.wf)

/-! ## Necessity of CPL⁺ -/

/-- If the atom set is countably infinite, CPL⁺ holds: an enumeration of the
    atoms is a countable coprime basis. (Needs only reducedness.) -/
theorem CCA_of_atoms_countably_infinite {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (hc : (Atoms M).Countable) (hi : Set.Infinite (Atoms M)) :
    CCA M := by
  haveI : Countable (Atoms M) := hc.to_subtype
  haveI : Infinite (Atoms M) := hi.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable (Atoms M)
  set e : ℕ ≃ Atoms M := (Denumerable.eqv (Atoms M)).symm with he
  refine ⟨fun i => (e i : M), ?_, ?_, ?_⟩
  · intro i
    have h_irr : Irreducible ((e i : M)) := (e i).2
    exact h_irr.1
  · intro i j hij
    have hne : ((e i : M)) ≠ ((e j : M)) := by
      intro hcontra
      exact hij (e.injective (Subtype.ext hcontra))
    exact distinct_atoms_coprime h_reduced (e i).2 (e j).2 hne
  · intro p hp
    refine ⟨e.symm ⟨p, hp⟩, ?_⟩
    simp

end
