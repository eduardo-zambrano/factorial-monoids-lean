/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4352aece-5706-4df2-8ef7-dac5883e68e2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Lemma 8.1: Primewise Decomposition

This file proves the primewise decomposition lemma:
Every non-unit m ∈ M can be written as m = ∏_{p ∈ S} p^{v_p(m)}
where S is the support of m (set of atoms dividing m).
-/

import MultiplicationProject.GlobalMultiplicativity
import MultiplicationProject.AtomsArePrime_v2_aristotle


-- Harmonic `generalize_proofs` tactic

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Helper Lemmas for Primewise Decomposition
-/

/-- The support of m is finite for atomic monoids. -/
lemma Support_finite {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (m : M) (hm : ¬IsUnit m) :
    (Support m).Finite := by
  -- Support m ⊆ atoms appearing in atomic factorization of m
  obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
  have h_sub : Support m ⊆ s.toFinset := by
    intro p hp
    simp only [Support, Set.mem_setOf_eq] at hp
    simp only [Multiset.mem_toFinset]
    -- p ∈ Atoms M and p ∣ m = s.prod
    -- Since atoms are prime, p must appear in s
    have h_prime := atoms_are_prime h_reduced h_atomic
    -- p divides s.prod, so by primality p must divide some element of s
    -- Since elements of s are atoms and p is an atom, p must equal some element
    have : p ∣ s.prod := hs_prod ▸ hp.2
    induction s using Multiset.induction with
    | empty => simp at this; exact absurd (isUnit_of_dvd_one this) hp.1.not_isUnit
    | cons a s ih =>
      simp only [Multiset.prod_cons] at this
      cases h_prime p hp.1 a s.prod this with
      | inl h_dvd_a =>
        -- p | a and both are atoms, so p = a
        have ha : Irreducible a := hs_atoms a (Multiset.mem_cons_self a s)
        obtain ⟨c, hc⟩ := h_dvd_a
        have := ha.isUnit_or_isUnit hc
        cases this with
        | inl hp_unit => exact absurd hp_unit hp.1.not_isUnit
        | inr hc_unit =>
          have : a = p := by rw [hc, h_reduced c hc_unit, mul_one]
          simp [this]
      | inr h_dvd_s =>
        have ih' := ih (fun q hq => hs_atoms q (Multiset.mem_cons_of_mem hq)) h_dvd_s
        exact Multiset.mem_cons_of_mem ih'
  exact Set.Finite.subset s.toFinset.finite_toSet h_sub

/- Aristotle failed to find a proof. -/
/-- **Lemma 8.1**: Primewise decomposition.

    Under (PP-D), (PP-P), and atomicity, every m ∈ M can be written as
    m = ∏_{p ∈ S} p^{v_p(m)} where S is the support of m. -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  -- Use the finite support as S
  have h_supp_finite := Support_finite h_reduced h_atomic m hm
  use h_supp_finite.toFinset
  constructor
  · intro p hp
    simp only [Set.Finite.mem_toFinset, Support, Set.mem_setOf_eq] at hp
    exact hp.1
  · -- Need to show m = ∏_{p ∈ Support m} p^{v_p(m)}
    -- Get atomic factorization of m
    obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
    -- Key: Show that m and the product have the same p-valuation for all atoms p
    -- Then they must be equal by unique factorization (which we have from cor_factorial)
    sorry

end