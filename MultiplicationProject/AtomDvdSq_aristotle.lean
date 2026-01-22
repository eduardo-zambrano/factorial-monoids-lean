/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5e8290bc-a108-43cf-a0ad-35d71661c283

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano, Claude

# Core Lemma: Any atom dividing q² equals q

This is the foundational lemma for proving PP-P from CFI.
If we can prove this, everything else follows.

## Main Result

`atom_dvd_sq_eq`: If r | q² where q, r are atoms, then r = q.

## Proof Strategy

1. If r | q, then r = q (both atoms)
2. If r ∤ q, then r and q are coprime (distinct atoms are coprime)
3. From r | q², write q² = r * s
4. Apply CFI to analyze the factorization structure
5. Case analysis shows all branches lead to contradiction or r = q
-/

import MultiplicationProject.Basic


open scoped BigOperators Classical

set_option maxHeartbeats 400000

noncomputable section

/-!
## Helper Lemmas
-/

/-- In a reduced monoid, the only unit is 1. -/
lemma reduced_eq_one {M : Type*} [Monoid M] (h_reduced : Reduced M)
    {u : M} (hu : IsUnit u) : u = 1 := h_reduced u hu

/-- In a reduced monoid, distinct atoms are coprime. -/
lemma coprime_of_ne_atoms {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (hne : p ≠ q) :
    AreCoprime p q := by
  intro r hr hrp hrq
  obtain ⟨s, hs⟩ := hrp
  cases hp.isUnit_or_isUnit hs with
  | inl hr_unit => exact hr.not_isUnit hr_unit
  | inr hs_unit =>
    rw [reduced_eq_one h_reduced hs_unit, mul_one] at hs
    obtain ⟨t, ht⟩ := hrq
    cases hq.isUnit_or_isUnit ht with
    | inl hr_unit => exact hr.not_isUnit hr_unit
    | inr ht_unit =>
      rw [reduced_eq_one h_reduced ht_unit, mul_one] at ht
      exact hne (hs.trans ht.symm)

/-- For an atom q, a 2-factorization is either (q, 1) or (1, q). -/
lemma atom_fact2_cases {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {q : M} (hq : q ∈ Atoms M) {f : Fin 2 → M} (hf : f ∈ LabeledFactorizations 2 q) :
    (f 0 = q ∧ f 1 = 1) ∨ (f 0 = 1 ∧ f 1 = q) := by
  simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hf
  cases hq.isUnit_or_isUnit hf.symm with
  | inl h0_unit =>
    right
    constructor
    · exact reduced_eq_one h_reduced h0_unit
    · rw [reduced_eq_one h_reduced h0_unit, one_mul] at hf; exact hf
  | inr h1_unit =>
    left
    constructor
    · rw [reduced_eq_one h_reduced h1_unit, mul_one] at hf; exact hf
    · exact reduced_eq_one h_reduced h1_unit

/-- If q | p where both are atoms in a reduced monoid, then q = p. -/
lemma atom_dvd_atom {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h : q ∣ p) : q = p := by
  obtain ⟨m, hm⟩ := h
  cases hp.isUnit_or_isUnit hm with
  | inl hq_unit => exact absurd hq_unit hq.not_isUnit
  | inr hm_unit =>
    rw [reduced_eq_one h_reduced hm_unit, mul_one] at hm
    exact hm.symm

/-- q and m are coprime, or q | m. -/
lemma coprime_or_dvd {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
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
      rw [reduced_eq_one h_reduced hs_unit, mul_one] at hs
      exact h (hs ▸ hrm)

/-!
## Core Lemma: atoms dividing q² equal q

This is the key building block. We show that in a reduced monoid with CFI,
if an atom r divides q² where q is also an atom, then r = q.
-/

/- Aristotle failed to find a proof. -/
/-- **Core Lemma**: Any atom dividing q² equals q.

This uses CFI to rule out spurious factorizations. The proof proceeds by:
1. If r | q, done (both atoms implies r = q)
2. If r ∤ q, apply CFI to the factorization q² = r * s
3. Analyze the preimage of (q, q) under the CFI bijection
4. All cases lead to contradiction

The key insight is that CFI constrains the factorization structure
so tightly that "foreign" atoms cannot divide q².
-/
lemma atom_dvd_sq_eq {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    (h_atomic : Atomic M)
    {q r : M} (hq : q ∈ Atoms M) (hr : r ∈ Atoms M) (h : r ∣ q * q) : r = q := by
  -- Either r | q (then r = q since both atoms), or r ∤ q
  by_cases hrq : r ∣ q
  · exact atom_dvd_atom h_reduced hq hr hrq
  · -- r ∤ q, so r and q are coprime (distinct atoms)
    have hr_ne_q : r ≠ q := fun h => hrq (h ▸ dvd_refl q)
    have h_coprime := coprime_of_ne_atoms h_reduced hr hq hr_ne_q

    -- r | q*q but r coprime to q. We derive contradiction using CFI.
    -- From r | q*q, write q*q = r * s for some s
    obtain ⟨s, hs⟩ := h
    -- hs : q * q = r * s

    -- Apply CFI to (r, s) if they are coprime
    -- First check coprimality of r and s
    cases coprime_or_dvd h_reduced hr (m := s) with
    | inl h_rs_coprime =>
      -- r and s are coprime, apply CFI
      have h_bij := h_cfi r s h_rs_coprime

      -- The element q*q has factorization (q, q)
      -- This must come from F_2(r) × F_2(s) via the bijection
      have h_qq_fact : (fun i : Fin 2 => q) ∈ LabeledFactorizations 2 (r * s) := by
        simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
        exact hs

      obtain ⟨⟨fr, fs⟩, h_preimage⟩ := h_bij.2 ⟨_, h_qq_fact⟩

      -- Coordinate equations
      have h_eq0 : fr.1 0 * fs.1 0 = q := by
        have := congr_arg (fun f : LabeledFactorizations 2 (r * s) => f.1 0) h_preimage
        simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
        exact this
      have h_eq1 : fr.1 1 * fs.1 1 = q := by
        have := congr_arg (fun f : LabeledFactorizations 2 (r * s) => f.1 1) h_preimage
        simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
        exact this

      -- fr is a 2-factorization of atom r, so fr ∈ {(r,1), (1,r)}
      cases atom_fact2_cases h_reduced hr fr.2 with
      | inl h_case1 =>
        -- fr = (r, 1), so r * fs.1 0 = q
        rw [h_case1.1] at h_eq0
        -- r * fs.1 0 = q, but q is an atom and r ∤ q
        cases hq.isUnit_or_isUnit h_eq0.symm with
        | inl hr_unit => exact (hr.not_isUnit hr_unit).elim
        | inr hfs_unit =>
          rw [reduced_eq_one h_reduced hfs_unit, mul_one] at h_eq0
          exact (hr_ne_q h_eq0).elim
      | inr h_case2 =>
        -- fr = (1, r), so 1 * fs.1 0 = q and r * fs.1 1 = q
        rw [h_case2.1, one_mul] at h_eq0
        rw [h_case2.2] at h_eq1
        -- fs.1 0 = q and r * fs.1 1 = q
        -- From r * fs.1 1 = q: same analysis
        cases hq.isUnit_or_isUnit h_eq1.symm with
        | inl hr_unit => exact (hr.not_isUnit hr_unit).elim
        | inr hfs_unit =>
          rw [reduced_eq_one h_reduced hfs_unit, mul_one] at h_eq1
          exact (hr_ne_q h_eq1).elim

    | inr h_r_dvd_s =>
      -- r | s, so s = r * t for some t
      -- We extract r's until we reach a coprime situation
      obtain ⟨t, ht⟩ := h_r_dvd_s
      rw [ht, ← mul_assoc] at hs
      -- hs : q * q = r * r * t

      -- Now check if r | t or coprime
      cases coprime_or_dvd h_reduced hr (m := t) with
      | inl h_rt_coprime =>
        -- r and t coprime, apply CFI to (r*r, t)
        -- First show r*r and t are coprime
        have h_r2t_coprime : AreCoprime (r * r) t := by
          intro x hx hx_dvd_r2 hx_dvd_t
          -- x | r*r and x | t, x is an atom
          -- We need x = r, then r | t contradicts h_rt_coprime
          by_cases hxr : x ∣ r
          · have hxeqr := atom_dvd_atom h_reduced hr hx hxr
            rw [hxeqr] at hx_dvd_t
            exact h_rt_coprime r hr (dvd_refl r) hx_dvd_t
          · -- x ∤ r, x | r*r. x and r are coprime distinct atoms.
            have hx_ne_r : x ≠ r := fun h => hxr (h ▸ dvd_refl x)
            have hx_r_coprime := coprime_of_ne_atoms h_reduced hx hr hx_ne_r

            obtain ⟨u, hu⟩ := hx_dvd_r2
            -- hu : r * r = x * u
            cases coprime_or_dvd h_reduced hx (m := u) with
            | inl h_xu_coprime =>
              have h_bij' := h_cfi x u h_xu_coprime
              have h_rr_fact : (fun i : Fin 2 => r) ∈ LabeledFactorizations 2 (x * u) := by
                simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
                exact hu
              obtain ⟨⟨fx, fu⟩, h_pre'⟩ := h_bij'.2 ⟨_, h_rr_fact⟩
              have h_eq0' : fx.1 0 * fu.1 0 = r := by
                have := congr_arg (fun f : LabeledFactorizations 2 (x * u) => f.1 0) h_pre'
                simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
                exact this
              cases atom_fact2_cases h_reduced hx fx.2 with
              | inl h_c1 =>
                rw [h_c1.1] at h_eq0'
                cases hr.isUnit_or_isUnit h_eq0'.symm with
                | inl hx_unit => exact hx.not_isUnit hx_unit
                | inr hfu_unit =>
                  rw [reduced_eq_one h_reduced hfu_unit, mul_one] at h_eq0'
                  exact hxr (h_eq0' ▸ dvd_refl x)
              | inr h_c2 =>
                rw [h_c2.1, one_mul] at h_eq0'
                -- fu.1 0 = r
                have h_eq1' : fx.1 1 * fu.1 1 = r := by
                  have := congr_arg (fun f : LabeledFactorizations 2 (x * u) => f.1 1) h_pre'
                  simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
                  exact this
                rw [h_c2.2] at h_eq1'
                -- x * fu.1 1 = r
                cases hr.isUnit_or_isUnit h_eq1'.symm with
                | inl hx_unit => exact hx.not_isUnit hx_unit
                | inr hfu_unit =>
                  rw [reduced_eq_one h_reduced hfu_unit, mul_one] at h_eq1'
                  exact hxr (h_eq1' ▸ dvd_refl x)
            | inr h_x_dvd_u =>
              -- x | u where r*r = x*u and x ∤ r
              -- This case requires termination argument
              -- Key: x^k | r*r with x ∤ r is bounded by the atomic structure
              exfalso
              sorry

        -- r*r and t coprime, apply CFI
        have h_bij'' := h_cfi (r * r) t h_r2t_coprime

        -- q*q = r*r*t, and we look at factorization (q, q)
        have h_qq_fact' : (fun i : Fin 2 => q) ∈ LabeledFactorizations 2 ((r * r) * t) := by
          simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two]
          exact hs

        obtain ⟨⟨fr2, ft⟩, h_pre''⟩ := h_bij''.2 ⟨_, h_qq_fact'⟩

        have h_eq0'' : fr2.1 0 * ft.1 0 = q := by
          have := congr_arg (fun f : LabeledFactorizations 2 ((r * r) * t) => f.1 0) h_pre''
          simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
          exact this

        have h_fr2_prod : fr2.1 0 * fr2.1 1 = r * r := by
          have := fr2.2
          simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at this
          exact this

        by_cases h0_unit : IsUnit (fr2.1 0)
        · -- fr2.1 0 = 1
          rw [reduced_eq_one h_reduced h0_unit, one_mul] at h_eq0'' h_fr2_prod
          -- h_fr2_prod : fr2.1 1 = r * r
          have h_eq1'' : fr2.1 1 * ft.1 1 = q := by
            have := congr_arg (fun f : LabeledFactorizations 2 ((r * r) * t) => f.1 1) h_pre''
            simp only [labeledFactorizationMul, Pi.mul_apply, Fin.isValue] at this
            exact this
          rw [h_fr2_prod] at h_eq1''
          -- (r * r) * ft.1 1 = q
          cases hq.isUnit_or_isUnit h_eq1''.symm with
          | inl hrr_unit =>
            have := isUnit_of_mul_isUnit_left hrr_unit
            exact (hr.not_isUnit this).elim
          | inr hft1_unit =>
            rw [reduced_eq_one h_reduced hft1_unit, mul_one] at h_eq1''
            -- r * r = q, but q is irreducible
            have h_rr_not_irr : ¬Irreducible (r * r) := by
              intro h_irr
              cases h_irr.isUnit_or_isUnit rfl with
              | inl hr_unit => exact hr.not_isUnit hr_unit
              | inr hr_unit => exact hr.not_isUnit hr_unit
            rw [h_eq1''] at h_rr_not_irr
            exact (h_rr_not_irr hq).elim
        · by_cases h1_unit : IsUnit (fr2.1 1)
          · -- fr2.1 1 = 1
            rw [reduced_eq_one h_reduced h1_unit, mul_one] at h_fr2_prod
            -- fr2.1 0 = r * r
            rw [h_fr2_prod] at h_eq0''
            -- (r * r) * ft.1 0 = q
            cases hq.isUnit_or_isUnit h_eq0''.symm with
            | inl hrr_unit =>
              have := isUnit_of_mul_isUnit_left hrr_unit
              exact (hr.not_isUnit this).elim
            | inr hft0_unit =>
              rw [reduced_eq_one h_reduced hft0_unit, mul_one] at h_eq0''
              have h_rr_not_irr : ¬Irreducible (r * r) := by
                intro h_irr
                cases h_irr.isUnit_or_isUnit rfl with
                | inl hr_unit => exact hr.not_isUnit hr_unit
                | inr hr_unit => exact hr.not_isUnit hr_unit
              rw [h_eq0''] at h_rr_not_irr
              exact (h_rr_not_irr hq).elim
          · -- Both fr2.1 0 and fr2.1 1 are non-units
            have h_fr20_eq_r : fr2.1 0 = r := by
              have h_dvd : fr2.1 0 ∣ r * r := ⟨fr2.1 1, h_fr2_prod.symm⟩
              by_cases h_dvd_r : fr2.1 0 ∣ r
              · obtain ⟨v, hv⟩ := h_dvd_r
                cases hr.isUnit_or_isUnit hv with
                | inl h_unit => exact absurd h_unit h0_unit
                | inr hv_unit =>
                  rw [reduced_eq_one h_reduced hv_unit, mul_one] at hv
                  exact hv.symm
              · -- fr2.1 0 ∤ r, but fr2.1 0 | r*r
                -- This requires showing fr2.1 0 = r*r, then fr2.1 1 = 1 (contradiction)
                exfalso
                sorry

            rw [h_fr20_eq_r] at h_eq0''
            -- r * ft.1 0 = q
            cases hq.isUnit_or_isUnit h_eq0''.symm with
            | inl hr_unit => exact (hr.not_isUnit hr_unit).elim
            | inr hft_unit =>
              rw [reduced_eq_one h_reduced hft_unit, mul_one] at h_eq0''
              -- r = q, but we established r ≠ q (since r ∤ q)
              exact (hr_ne_q h_eq0'').elim

      | inr h_r_dvd_t =>
        -- r | t, continue extracting r's
        -- This terminates because q*q has finite "r-depth"
        sorry

end