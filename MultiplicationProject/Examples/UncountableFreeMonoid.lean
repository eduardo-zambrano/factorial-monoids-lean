/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Example 10.5: CPL⁺ fails in the free commutative monoid on uncountably many generators

M := Multiplicative (ℝ →₀ ℕ), the free commutative monoid on continuum-many
generators (written multiplicatively). This monoid:

- satisfies the base assumptions (reduced, atomic, WFD);
- is factorial, hence satisfies tower faithfulness, TD, CFI (necessity direction);
- satisfies the OLD axiom CPL (arbitrarily long pairwise coprime tuples);
- but FAILS CPL⁺: its atom set {single r 1 : r ∈ ℝ} is uncountable, so no
  countable coprime basis can reach every atom.

This is the example that shows the strengthening CPL → CPL⁺ is necessary:
with CPL alone the conclusion M ≅ (ℕ, ×) is false. The CPL⁺ failure is
derived from `thm_characterization` + uncountability of ℝ, rather than
proved by hand.
-/
import MultiplicationProject.MainTheorem

set_option maxHeartbeats 400000

noncomputable section

namespace UncountableFreeMonoidExample

abbrev M := Multiplicative (ℝ →₀ ℕ)

/-! ## Degree calculus -/

/-- Total degree of an element: the sum of all exponents. -/
def deg (x : M) : ℕ := (x.toAdd).degree

lemma deg_mul (x y : M) : deg (x * y) = deg x + deg y := by
  simp only [deg, toAdd_mul]
  exact Finsupp.degree_add _ _

lemma deg_one : deg (1 : M) = 0 := by
  simp only [deg, toAdd_one]
  exact Finsupp.degree_zero

lemma eq_one_of_deg_zero {x : M} (h : deg x = 0) : x = 1 := by
  have h0 : x.toAdd = 0 := (Finsupp.degree_eq_zero_iff _).mp h
  apply Multiplicative.toAdd.injective
  simpa using h0

theorem R_reduced : Reduced M := by
  intro u hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hdeg : deg u + deg v = 0 := by
    rw [← deg_mul, hv, deg_one]
  exact eq_one_of_deg_zero (by omega)

lemma deg_pos_of_not_unit {x : M} (h : ¬IsUnit x) : 1 ≤ deg x := by
  rcases Nat.eq_zero_or_pos (deg x) with h0 | h1
  · exact absurd (show IsUnit x by rw [eq_one_of_deg_zero h0]; exact isUnit_one) h
  · exact h1

/-! ## The atoms: single-variable generators -/

/-- The generator attached to the real number r. -/
def sgl (r : ℝ) : M := Multiplicative.ofAdd (Finsupp.single r 1)

lemma toAdd_sgl (r : ℝ) : (sgl r).toAdd = Finsupp.single r 1 := rfl

lemma deg_sgl (r : ℝ) : deg (sgl r) = 1 := by
  simp only [deg, toAdd_sgl]
  exact Finsupp.degree_single r 1

lemma sgl_injective : Function.Injective sgl := by
  intro a b hab
  have h1 : Finsupp.single a (1 : ℕ) = Finsupp.single b 1 := by
    simpa [sgl] using congrArg Multiplicative.toAdd hab
  exact (Finsupp.single_left_inj one_ne_zero).mp h1

lemma irreducible_of_deg_one {x : M} (h : deg x = 1) : Irreducible x := by
  constructor
  · intro hu
    have h1 : x = 1 := R_reduced x hu
    rw [h1, deg_one] at h
    omega
  · intro a b hab
    have hsum : deg a + deg b = 1 := by
      rw [← deg_mul, ← hab, h]
    rcases (show deg a = 0 ∨ deg b = 0 by omega) with h0 | h0
    · exact Or.inl (by rw [eq_one_of_deg_zero h0]; exact isUnit_one)
    · exact Or.inr (by rw [eq_one_of_deg_zero h0]; exact isUnit_one)

lemma irreducible_sgl (r : ℝ) : Irreducible (sgl r) :=
  irreducible_of_deg_one (deg_sgl r)

/-- Every nonzero finsupp dominates a generator. -/
lemma exists_single_le {f : ℝ →₀ ℕ} (hf : f ≠ 0) :
    ∃ r, Finsupp.single r (1 : ℕ) ≤ f := by
  obtain ⟨r, hr⟩ := Finsupp.support_nonempty_iff.mpr hf
  exact ⟨r, Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hr))⟩

/-- Classification of atoms: every irreducible element is a generator. -/
lemma atom_classification {x : M} (hx : Irreducible x) : ∃ r : ℝ, x = sgl r := by
  have hd1 : 1 ≤ deg x := deg_pos_of_not_unit hx.1
  have hne : x.toAdd ≠ 0 := by
    intro h0
    have hz : deg x = 0 := by
      simp only [deg, h0]
      exact Finsupp.degree_zero
    omega
  obtain ⟨r, hr⟩ := exists_single_le hne
  have hsplit : x.toAdd = Finsupp.single r 1 + (x.toAdd - Finsupp.single r 1) :=
    (add_tsub_cancel_of_le hr).symm
  have hx_eq : x = sgl r * Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1) := by
    apply Multiplicative.toAdd.injective
    simpa [sgl] using hsplit
  rcases hx.isUnit_or_isUnit hx_eq with h | h
  · exact absurd h (irreducible_sgl r).1
  · have hg1 : Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1) = 1 :=
      R_reduced _ h
    have hg0 : x.toAdd - Finsupp.single r 1 = 0 := by
      simpa using congrArg Multiplicative.toAdd hg1
    refine ⟨r, ?_⟩
    rw [hx_eq, hg0]
    simp

/-! ## Base assumptions: atomic, WFD -/

theorem R_atomic : Atomic M := by
  suffices H : ∀ N : ℕ, ∀ x : M, deg x ≤ N → ¬IsUnit x →
      ∃ s : Multiset M, (∀ a ∈ s, Irreducible a) ∧ s.prod = x by
    intro x hx
    exact H (deg x) x le_rfl hx
  intro N
  induction N with
  | zero =>
    intro x hle hx
    exact absurd hle (by have := deg_pos_of_not_unit hx; omega)
  | succ N ih =>
    intro x hle hx
    have hd1 : 1 ≤ deg x := deg_pos_of_not_unit hx
    have hne : x.toAdd ≠ 0 := by
      intro h0
      have hz : deg x = 0 := by
        simp only [deg, h0]
        exact Finsupp.degree_zero
      omega
    obtain ⟨r, hr⟩ := exists_single_le hne
    have hsplit : x.toAdd = Finsupp.single r 1 + (x.toAdd - Finsupp.single r 1) :=
      (add_tsub_cancel_of_le hr).symm
    have hx_eq : x = sgl r * Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1) := by
      apply Multiplicative.toAdd.injective
      simpa [sgl] using hsplit
    have hdeg_rest : deg (Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1))
        = deg x - 1 := by
      have h1 := congrArg deg hx_eq
      rw [deg_mul, deg_sgl] at h1
      omega
    by_cases hg : x.toAdd - Finsupp.single r 1 = 0
    · refine ⟨{sgl r}, ?_, ?_⟩
      · intro a ha
        rw [Multiset.mem_singleton.mp ha]
        exact irreducible_sgl r
      · rw [Multiset.prod_singleton, hx_eq, hg]
        simp
    · have hg_unit : ¬IsUnit (Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1)) := by
        intro hu
        apply hg
        have h1 := R_reduced _ hu
        simpa using congrArg Multiplicative.toAdd h1
      obtain ⟨s, hs_atoms, hs_prod⟩ :=
        ih (Multiplicative.ofAdd (x.toAdd - Finsupp.single r 1)) (by omega) hg_unit
      refine ⟨sgl r ::ₘ s, ?_, ?_⟩
      · intro a ha
        rcases Multiset.mem_cons.mp ha with h | h
        · rw [h]; exact irreducible_sgl r
        · exact hs_atoms a h
      · rw [Multiset.prod_cons, hs_prod, ← hx_eq]

theorem R_wfd : WFD M := by
  have hsub : Subrelation (fun a b : M => StrictDvd a b)
      (InvImage (· < ·) deg) := by
    intro a b hab
    obtain ⟨c, hc_unit, rfl⟩ := hab
    have := deg_pos_of_not_unit hc_unit
    show deg a < deg (a * c)
    rw [deg_mul]
    omega
  exact Subrelation.wf hsub (InvImage.wf _ Nat.lt_wfRel.wf)

/-! ## Factorial structure -/

/-- The exponent of the generator r in a product of atoms counts the
    occurrences of sgl r. -/
lemma count_prod (r : ℝ) : ∀ (s : Multiset M), (∀ a ∈ s, Irreducible a) →
    ((s.prod).toAdd) r = s.count (sgl r) := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    obtain ⟨ra, rfl⟩ := atom_classification (hs a (Multiset.mem_cons_self a s))
    have hs' : ∀ x ∈ s, Irreducible x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hL : (((sgl ra ::ₘ s).prod).toAdd) r
        = (Finsupp.single ra (1 : ℕ)) r + ((s.prod).toAdd) r := by
      rw [Multiset.prod_cons]
      simp [sgl, Finsupp.add_apply]
    rw [hL, ih hs']
    by_cases hcase : ra = r
    · subst hcase
      rw [Finsupp.single_eq_same, Multiset.count_cons_self]
      omega
    · have hne_sgl : sgl r ≠ sgl ra := fun h => hcase (sgl_injective h).symm
      rw [Finsupp.single_eq_of_ne' hcase, Multiset.count_cons_of_ne hne_sgl]
      omega

theorem R_factorial : Factorial M := by
  classical
  intro x hx
  obtain ⟨s, hs_atoms, hs_prod⟩ := R_atomic x hx
  refine ⟨s, ⟨hs_atoms, hs_prod⟩, ?_⟩
  rintro t ⟨ht_atoms, ht_prod⟩
  rw [Multiset.ext]
  intro z
  by_cases hz_t : z ∈ t
  · obtain ⟨r, rfl⟩ := atom_classification (ht_atoms z hz_t)
    rw [← count_prod r t ht_atoms, ← count_prod r s hs_atoms, ht_prod, hs_prod]
  · by_cases hz_s : z ∈ s
    · obtain ⟨r, rfl⟩ := atom_classification (hs_atoms z hz_s)
      rw [← count_prod r t ht_atoms, ← count_prod r s hs_atoms, ht_prod, hs_prod]
    · rw [Multiset.count_eq_zero_of_notMem hz_t, Multiset.count_eq_zero_of_notMem hz_s]

/-! ## tower faithfulness, TD, CFI hold (necessity direction) -/

theorem R_tf : TowerFaithful M := tower_faithful_of_factorial R_reduced R_factorial

theorem R_td : TD M := TD_of_factorial R_reduced R_factorial

theorem R_cfi : CFI M := CFI_of_factorial R_reduced R_factorial

/-! ## The old CPL holds -/

/-- Dividing one generator by another forces the same index. -/
lemma sgl_dvd {a b : ℝ} (h : sgl a ∣ sgl b) : a = b := by
  obtain ⟨c, hc⟩ := h
  have hval := congrArg (fun z : M => (z.toAdd) a) hc
  simp only [sgl, toAdd_mul, toAdd_ofAdd, Finsupp.add_apply,
    Finsupp.single_eq_same] at hval
  by_contra hne
  rw [Finsupp.single_eq_of_ne hne] at hval
  omega

/-- The OLD axiom CPL holds: generators at distinct naturals give arbitrarily
    long pairwise coprime tuples. -/
theorem R_cpl : CPL M := by
  intro n
  refine ⟨List.ofFn (fun i : Fin n => sgl ((i : ℕ) : ℝ)), by simp, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (irreducible_sgl _).1
  · rw [List.pairwise_ofFn]
    intro i j hij
    intro p hp hpi hpj
    have hp_irr : Irreducible p := hp
    obtain ⟨rp, rfl⟩ := atom_classification hp_irr
    have h1 : rp = ((i : ℕ) : ℝ) := sgl_dvd hpi
    have h2 : rp = ((j : ℕ) : ℝ) := sgl_dvd hpj
    have h3 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h1 ▸ h2
    have h4 : (i : ℕ) = (j : ℕ) := Nat.cast_injective h3
    have h5 : (i : ℕ) < (j : ℕ) := hij
    omega

/-! ## CPL⁺ fails -/

/-- The atom set is uncountable: it contains a copy of ℝ. -/
theorem R_atoms_not_countable : ¬(Atoms M).Countable := by
  intro hc
  have hmem : ∀ r : ℝ, sgl r ∈ Atoms M := fun r => irreducible_sgl r
  have hcount : (Set.univ : Set ℝ).Countable := by
    have hpre : sgl ⁻¹' (Atoms M) = Set.univ :=
      Set.eq_univ_of_forall fun r => hmem r
    rw [← hpre]
    exact hc.preimage sgl_injective
  exact Cardinal.not_countable_real hcount

/-- CPL⁺ FAILS — derived from the characterization theorem: if CPL⁺ held,
    the atom set would be countable, contradicting uncountability. -/
theorem R_not_CCA : ¬CCA M := by
  intro h
  have hres := (thm_characterization R_reduced R_atomic R_wfd).mp
    ⟨R_tf, R_td, R_cfi, h⟩
  exact R_atoms_not_countable hres.2.1

/-! ## Summary -/

/-- **Example 10.5**: the free commutative monoid on continuum-many
    generators satisfies the base assumptions, tower faithfulness, TD, CFI, and even the
    old CPL — it is factorial — yet CPL⁺ fails and M ≇ (ℕ, ×). This shows
    the strengthening CPL → CPL⁺ is necessary. -/
theorem uncountable_example :
    Reduced M ∧ Atomic M ∧ WFD M ∧ Factorial M ∧
    TowerFaithful M ∧ TD M ∧ CFI M ∧ CPL M ∧ ¬CCA M :=
  ⟨R_reduced, R_atomic, R_wfd, R_factorial, R_tf, R_td, R_cfi, R_cpl,
   R_not_CCA⟩

end UncountableFreeMonoidExample
