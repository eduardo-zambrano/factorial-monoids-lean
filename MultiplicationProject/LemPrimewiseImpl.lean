/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Lemma 8.1: Primewise Decomposition (Implementation)

This file proves lem_primewise_impl using prop_val_additive.
-/

import MultiplicationProject.GlobalMultiplicativity
import MultiplicationProject.AtomsArePrime_v2_aristotle

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Valuation lemmas (from MasterFormula_v2_aristotle.lean)
-/

/-- Powers of distinct atoms are coprime. -/
lemma coprime_of_distinct_atoms {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (hpq : p ≠ q) :
    AreCoprime p q := by
  intro r hr hdvd_p
  -- r is an atom dividing p. Since p is an atom, r = p.
  obtain ⟨c, hc⟩ := hdvd_p
  have := hp.isUnit_or_isUnit hc
  cases this with
  | inl hr_unit => exact absurd hr_unit hr.not_isUnit
  | inr hc_unit =>
    have heq : p = r := by rw [hc, h_reduced c hc_unit, mul_one]
    -- Now r = p, and we need ¬ r ∣ q, i.e., ¬ p ∣ q
    intro hdvd_q
    obtain ⟨d, hd⟩ := hdvd_q
    have := hq.isUnit_or_isUnit hd
    cases this with
    | inl hp_unit => exact hp.not_isUnit (heq ▸ hp_unit)
    | inr hd_unit =>
      have : q = p := by rw [hd, h_reduced d hd_unit, mul_one, heq]
      exact hpq this.symm

/-- If p and q are atoms, and p^k divides q, then k ≤ 1. -/
lemma lemma_pow_dvd_atom {M : Type*} [CommMonoid M] (h_red : Reduced M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : p ^ k ∣ q) :
    k ≤ 1 := by
  unfold Atoms at hq
  cases' h_dvd with a ha
  rcases k with (_ | _ | k) <;> simp_all +decide [pow_succ, mul_assoc]
  rw [irreducible_mul_iff] at hq
  aesop
  · exact hp.1 left_1
  · rw [irreducible_mul_iff] at left
    aesop
    · exact left.not_isUnit left_1
    · exact hp.1 right_1

/-- The set of exponents e such that p^e divides m is bounded above. -/
lemma lemma_valuation_bounded {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) :
    BddAbove {e | p ^ e ∣ m} := by
  by_cases hm : IsUnit m
  · use 0
    intro e he
    cases e with
    | zero => rfl
    | succ n =>
      exfalso
      have : p ∣ m := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero n)) he
      obtain ⟨c, hc⟩ := this
      obtain ⟨u, hu⟩ := hm
      rw [← hu] at hc
      have := hp.isUnit_or_isUnit (c := u⁻¹ * c) (by simp [hc, mul_assoc])
      cases this with
      | inl h => exact hp.not_isUnit h
      | inr h =>
        have : IsUnit c := (IsUnit.mul_iff.mp h).2
        have : IsUnit (p * c) := IsUnit.mul hp.not_isUnit.elim.symm.isUnit this
        rw [← hc] at this
        exact hp.not_isUnit (hu ▸ this)
  · obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
    use Multiset.count p s
    intro e he
    -- If p^e ∣ m = s.prod, then e ≤ count p s
    induction s using Multiset.strongInductionOn generalizing e m with
    | ih s ih =>
      cases Multiset.empty_or_exists_mem s with
      | inl h_empty =>
        simp only [h_empty, Multiset.prod_zero] at hs_prod
        rw [← hs_prod] at he
        cases e with
        | zero => simp
        | succ n =>
          exfalso
          have : p ∣ 1 := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero n)) he
          exact hp.not_isUnit (isUnit_of_dvd_one this)
      | inr h_exists =>
        obtain ⟨a, ha⟩ := h_exists
        have ha_atom : a ∈ Atoms M := hs_atoms a ha
        by_cases hap : a = p
        · -- a = p case
          subst hap
          simp only [Multiset.count_cons_self]
          have h_erase : s = {p} + s.erase p := by
            rw [Multiset.singleton_add, Multiset.cons_erase ha]
          rw [h_erase, Multiset.prod_add, Multiset.prod_singleton] at hs_prod
          -- m = p * (s.erase p).prod
          sorry
        · -- a ≠ p case
          sorry

/-- The valuation v_p(m) satisfies p^v | m and p^(v+1) does not divide m. -/
lemma lemma_valuation_spec {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) :
    p ^ (PValuation p m) ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
  constructor
  · have := lemma_valuation_bounded h_reduced h_atomic h_ppd h_cfi p hp m
    have := Nat.sSup_mem (show { e : ℕ | p ^ e ∣ m }.Nonempty from ⟨0, by simp⟩)
    aesop
  · exact fun h => not_le_of_gt (Nat.lt_succ_self _)
      (le_csSup (lemma_valuation_bounded h_reduced h_atomic h_ppd h_cfi p hp m) h)

/-- Additivity of valuations: v_p(x·y) = v_p(x) + v_p(y) -/
theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  sorry

/-!
## Main theorem: Primewise decomposition
-/

/-- **Lemma 8.1**: Primewise decomposition.
    Under (PP-D), (PP-P), and atomicity, every m ∈ M can be written as
    m = ∏_{p ∈ S} p^{v_p(m)} where S is the support of m. -/
theorem lem_primewise_impl {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  -- By atomicity, m factors into atoms
  obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
  -- Use S = s.toFinset (the distinct atoms)
  use s.toFinset
  constructor
  · intro p hp
    simp only [Multiset.mem_toFinset] at hp
    exact hs_atoms p hp
  · -- Show m = ∏_{p ∈ s.toFinset} p^{v_p(m)}
    -- Key: v_p(m) = count p s for each atom p
    -- This follows from prop_val_additive
    sorry

end
