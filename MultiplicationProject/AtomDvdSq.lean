/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano, Claude

# Core Lemma: Any atom dividing q² equals q

This is the foundational lemma for proving PP-P from CFI.

## Main Result

`atom_dvd_sq_eq`: If r | q² where q, r are atoms, then r = q.

## Proof Strategy (Counting Argument)

The key insight is that CFI constrains |F₂(m * n)| = |F₂(m)| * |F₂(n)| for coprime m, n.

For an atom q:
- |F₂(q)| = 2 (only {(q, 1), (1, q)})
- F₂(q²) contains (q, q), (q², 1), (1, q²), so |F₂(q²)| ≥ 3

The contradiction arises as follows:
- Suppose r | q² where r is an atom with r ≠ q
- Then q² = r * s for some s
- Case 1: r and s coprime
  - CFI gives bijection F₂(r) × F₂(s) → F₂(q²)
  - Analyzing preimages shows r | q or s | q
  - If r | q: r = q (atoms dividing atoms), contradiction with r ≠ q
  - If s | q: leads to r | q via similar analysis
- Case 2: r | s (not coprime)
  - Extract r repeatedly: q² = r^k * t where r and t are coprime
  - Apply Case 1 to the coprime factorization

## Status

- Helper lemmas: ✅ Complete
- `qq_preimage_forces_divisibility`: ✅ Complete
- `no_coprime_factorization_with_foreign_atom`: ✅ Complete
- `atom_dvd_sq_eq`: 3 sorries (extraction termination)
-/

import MultiplicationProject.Basic

open scoped BigOperators Classical

set_option maxHeartbeats 400000

noncomputable section

/-!
## Helper Lemmas
-/

/-- In a reduced monoid, the only unit is 1. -/
lemma reduced_eq_one' {M : Type*} [Monoid M] (h_reduced : Reduced M)
    {u : M} (hu : IsUnit u) : u = 1 := h_reduced u hu

/-- In a reduced monoid, distinct atoms are coprime. -/
lemma coprime_of_ne_atoms' {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (hne : p ≠ q) :
    AreCoprime p q := by
  intro r hr hrp hrq
  obtain ⟨s, hs⟩ := hrp
  cases hp.isUnit_or_isUnit hs with
  | inl hr_unit => exact hr.not_isUnit hr_unit
  | inr hs_unit =>
    rw [reduced_eq_one' h_reduced hs_unit, mul_one] at hs
    obtain ⟨t, ht⟩ := hrq
    cases hq.isUnit_or_isUnit ht with
    | inl hr_unit => exact hr.not_isUnit hr_unit
    | inr ht_unit =>
      rw [reduced_eq_one' h_reduced ht_unit, mul_one] at ht
      exact hne (hs.trans ht.symm)

/-- For an atom q, a 2-factorization is either (q, 1) or (1, q). -/
lemma atom_fact2_cases' {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {q : M} (hq : q ∈ Atoms M) {f : Fin 2 → M} (hf : f ∈ LabeledFactorizations 2 q) :
    (f 0 = q ∧ f 1 = 1) ∨ (f 0 = 1 ∧ f 1 = q) := by
  simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hf
  cases hq.isUnit_or_isUnit hf.symm with
  | inl h0_unit =>
    right
    constructor
    · exact reduced_eq_one' h_reduced h0_unit
    · rw [reduced_eq_one' h_reduced h0_unit, one_mul] at hf; exact hf
  | inr h1_unit =>
    left
    constructor
    · rw [reduced_eq_one' h_reduced h1_unit, mul_one] at hf; exact hf
    · exact reduced_eq_one' h_reduced h1_unit

/-- Atoms dividing atoms are equal (in a reduced monoid). -/
lemma atom_dvd_atom' {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h : q ∣ p) : q = p := by
  obtain ⟨m, hm⟩ := h
  cases hp.isUnit_or_isUnit hm with
  | inl hq_unit => exact absurd hq_unit hq.not_isUnit
  | inr hm_unit =>
    rw [reduced_eq_one' h_reduced hm_unit, mul_one] at hm
    exact hm.symm

/-- q and m are coprime, or q | m. -/
lemma coprime_or_dvd' {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {q : M} (hq : q ∈ Atoms M) {m : M} :
    AreCoprime q m ∨ q ∣ m := by
  by_cases h : q ∣ m
  · exact Or.inr h
  · left
    intro r hr hrq hrm
    obtain ⟨s, hs⟩ := hrq
    cases hq.isUnit_or_isUnit hs with
    | inl hr_unit => exact hr.not_isUnit hr_unit
    | inr hs_unit =>
      rw [reduced_eq_one' h_reduced hs_unit, mul_one] at hs
      exact h (hs ▸ hrm)

/-!
## Key Counting Lemma

The main insight: if q² = m * n where m, n are coprime, then CFI constrains
the preimage of (q, q) in F₂(m) × F₂(n), forcing m | q or n | q.
-/

/-- If (q, q) comes from the CFI bijection F₂(m) × F₂(n) → F₂(m*n), then
    either m | q or n | q. This is the core of the counting argument. -/
lemma qq_preimage_forces_divisibility {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_cfi : CFI M) {m n q : M} (hq : q ∈ Atoms M)
    (h_coprime : AreCoprime m n)
    (h_mn_eq_qq : m * n = q * q) :
    m ∣ q ∨ n ∣ q := by
  have h_bij := h_cfi m n h_coprime
  have h_qq_fact : (fun _ : Fin 2 => q) ∈ LabeledFactorizations 2 (m * n) := by
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
    exact h_mn_eq_qq.symm
  obtain ⟨⟨fm, fn⟩, h_preimage⟩ := h_bij.2 ⟨_, h_qq_fact⟩
  have h_eq0 : fm.1 0 * fn.1 0 = q := by
    have := congr_arg (fun f : LabeledFactorizations 2 (m * n) => f.1 0) h_preimage
    simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
    exact this
  have h_eq1 : fm.1 1 * fn.1 1 = q := by
    have := congr_arg (fun f : LabeledFactorizations 2 (m * n) => f.1 1) h_preimage
    simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
    exact this
  have h_fm_prod : fm.1 0 * fm.1 1 = m := by
    have := fm.2
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at this
    exact this
  have h_fn_prod : fn.1 0 * fn.1 1 = n := by
    have := fn.2
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at this
    exact this
  -- Since q is an atom and fm.1 0 * fn.1 0 = q, either fm.1 0 or fn.1 0 is a unit
  cases hq.isUnit_or_isUnit h_eq0.symm with
  | inl hfm0_unit =>
    -- fm.1 0 = 1, so fm.1 1 = m (from h_fm_prod)
    -- h_eq1: m * fn.1 1 = q, hence m | q
    have hfm0_eq_1 := reduced_eq_one' h_reduced hfm0_unit
    rw [hfm0_eq_1, one_mul] at h_fm_prod
    have h_mdiv : m * fn.1 1 = q := h_fm_prod ▸ h_eq1
    left
    exact Dvd.intro (fn.1 1) h_mdiv
  | inr hfn0_unit =>
    -- fn.1 0 = 1, so fn.1 1 = n
    -- h_eq1: fm.1 1 * n = q, hence n | q
    have hfn0_eq_1 := reduced_eq_one' h_reduced hfn0_unit
    rw [hfn0_eq_1, one_mul] at h_fn_prod
    have h_ndiv : n * fm.1 1 = q := by rw [mul_comm]; exact h_fn_prod ▸ h_eq1
    right
    exact Dvd.intro (fm.1 1) h_ndiv

/-- **Key Lemma**: If q² = r * s where r, s are coprime and r is an atom with r ≠ q,
    then we derive a contradiction. -/
lemma no_coprime_factorization_with_foreign_atom {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_cfi : CFI M)
    {q r s : M} (hq : q ∈ Atoms M) (hr : r ∈ Atoms M)
    (h_rs : r * s = q * q) (h_coprime : AreCoprime r s) (hr_ne_q : r ≠ q) : False := by
  have h_div := qq_preimage_forces_divisibility h_reduced h_cfi hq h_coprime h_rs
  cases h_div with
  | inl hr_dvd_q =>
    -- r | q with both atoms implies r = q
    have := atom_dvd_atom' h_reduced hq hr hr_dvd_q
    exact hr_ne_q this
  | inr hs_dvd_q =>
    obtain ⟨t, ht⟩ := hs_dvd_q  -- q = s * t
    cases hq.isUnit_or_isUnit ht with
    | inl hs_unit =>
      -- s = 1, so r = q², contradicting r being an atom
      rw [reduced_eq_one' h_reduced hs_unit, mul_one] at h_rs
      have h_r_not_atom : ¬Irreducible r := by
        rw [h_rs]
        intro h_irr
        cases h_irr.isUnit_or_isUnit rfl with
        | inl hq_unit => exact hq.not_isUnit hq_unit
        | inr hq_unit => exact hq.not_isUnit hq_unit
      exact h_r_not_atom hr
    | inr ht_unit =>
      -- s = q, so r and q are coprime with r * q = q²
      rw [reduced_eq_one' h_reduced ht_unit, mul_one] at ht
      have hs_eq_q : s = q := ht.symm
      have h_rq_coprime : AreCoprime r q := hs_eq_q ▸ h_coprime
      rw [hs_eq_q] at h_rs
      -- Now r * q = q * q, apply CFI again
      have h_bij := h_cfi r q h_rq_coprime
      have h_qq_fact : (fun _ : Fin 2 => q) ∈ LabeledFactorizations 2 (r * q) := by
        simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
        exact h_rs.symm
      obtain ⟨⟨fr, fq⟩, h_preimage⟩ := h_bij.2 ⟨_, h_qq_fact⟩
      have h_eq0 : fr.1 0 * fq.1 0 = q := by
        have := congr_arg (fun f : LabeledFactorizations 2 (r * q) => f.1 0) h_preimage
        simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
        exact this
      have h_eq1 : fr.1 1 * fq.1 1 = q := by
        have := congr_arg (fun f : LabeledFactorizations 2 (r * q) => f.1 1) h_preimage
        simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
        exact this
      cases atom_fact2_cases' h_reduced hr fr.2 with
      | inl h_fr_case1 =>
        rw [h_fr_case1.1] at h_eq0
        cases hq.isUnit_or_isUnit h_eq0.symm with
        | inl hr_unit => exact hr.not_isUnit hr_unit
        | inr hfq0_unit =>
          rw [reduced_eq_one' h_reduced hfq0_unit, mul_one] at h_eq0
          exact hr_ne_q h_eq0
      | inr h_fr_case2 =>
        rw [h_fr_case2.2] at h_eq1
        cases hq.isUnit_or_isUnit h_eq1.symm with
        | inl hr_unit => exact hr.not_isUnit hr_unit
        | inr hfq1_unit =>
          rw [reduced_eq_one' h_reduced hfq1_unit, mul_one] at h_eq1
          exact hr_ne_q h_eq1

/-!
## Main Theorem

The extraction argument: if r | s (not coprime), extract r repeatedly
until reaching a coprime factorization, then apply the counting lemma.
-/

/-- **Core Lemma**: Any atom dividing q² equals q.

This uses CFI to rule out foreign atoms dividing q².
-/
theorem atom_dvd_sq_eq {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {q r : M} (hq : q ∈ Atoms M) (hr : r ∈ Atoms M) (h : r ∣ q * q) : r = q := by
  by_cases hrq : r ∣ q
  · exact atom_dvd_atom' h_reduced hq hr hrq
  · exfalso
    have hr_ne_q : r ≠ q := fun h => hrq (h ▸ dvd_refl q)
    obtain ⟨s, hs⟩ := h
    -- hs : q * q = r * s
    cases coprime_or_dvd' h_reduced hr (m := s) with
    | inl h_rs_coprime =>
      -- r and s coprime: direct contradiction
      exact no_coprime_factorization_with_foreign_atom h_reduced h_cfi hq hr hs.symm h_rs_coprime hr_ne_q
    | inr h_r_dvd_s =>
      -- r | s: extract r to get q² = r² * t
      -- Continue extraction until coprime, then apply counting argument
      -- The extraction terminates because q² has finite "atomic depth"
      -- FORMAL GAP: Need well-founded recursion or termination argument
      -- The key insight is that each extraction reduces the "r-free part"
      -- Since q² = q * q where q is a single atom, after at most 2 extractions
      -- of any atom r, we must reach a coprime situation or derive r = q.
      sorry

end
