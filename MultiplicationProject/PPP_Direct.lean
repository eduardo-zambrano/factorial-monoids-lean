/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Direct Proof of PP-P from CFI (Sketch)

This file sketches a direct proof of Proposition 5.3 (CFI implies PP-P) that
bypasses AtomDvdPower.lean by using only Blockwise_CFI_2 and the bijection structure.

## Strategy

The key insight is that the bijection F_2(x) × F_2(y) ≅ F_2(p^e) (for coprime x, y
with x*y = p^e) constrains what atoms can appear in x and y.

If atom q ≠ p divides x, the bijection forces q to appear in coordinates of
elements in F_2(p^e), which leads to a contradiction since every factorization
of p^e should involve only powers of p.

## Status

This file contains the proof structure with key sorries marking where the
CFI bijection analysis needs to be formalized.
-/

import MultiplicationProject.LocalPurity

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Key Lemma: Atom Divisibility Constraint

If x and y are coprime, x * y = p^e, and CFI holds, then any atom q
dividing x must equal p.
-/

/-- **Key Technical Lemma**: Under CFI, if x and y are coprime with x * y = p^e,
    and q is an atom dividing x, then q = p.

    Proof sketch:
    1. CFI gives bijection F_2(x) × F_2(y) ≅ F_2(p^e)
    2. If q ≠ p divides x, construct factorization (q, x') ∈ F_2(x)
    3. Pair with (1, y) ∈ F_2(y) to get element (q, x'*y) ∈ F_2(p^e)
    4. This element has q as its first coordinate
    5. But the bijection structure (analyzed via surjectivity and injectivity)
       forces all coordinates of F_2(p^e) elements to be powers of p
    6. Since q is an atom and q ≠ p, q cannot be a power of p → contradiction -/
lemma atom_dividing_coprime_product_eq {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    {p : M} (hp : p ∈ Atoms M)
    {x y : M} (h_coprime : AreCoprime x y) {e : ℕ} (h_prod : x * y = p ^ e)
    {q : M} (hq : q ∈ Atoms M) (hq_dvd : q ∣ x) :
    q = p := by
  -- The full proof requires analyzing the CFI bijection structure
  -- to show that q ≠ p leads to a contradiction
  sorry

/-- **Coprime Products in Powers**: If x and y are coprime and x * y = p^e,
    then x and y are both powers of p. -/
theorem coprime_product_powers {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    {p : M} (hp : p ∈ Atoms M)
    {x y : M} (h_coprime : AreCoprime x y) {e : ℕ} (h_prod : x * y = p ^ e) :
    x ∈ Submonoid.powers p ∧ y ∈ Submonoid.powers p := by
  -- Handle trivial cases
  by_cases hx_unit : IsUnit x
  · have hx1 : x = 1 := h_reduced x hx_unit
    rw [hx1, one_mul] at h_prod
    refine ⟨⟨0, ?_⟩, ⟨e, h_prod.symm⟩⟩
    simp [hx1]
  · by_cases hy_unit : IsUnit y
    · have hy1 : y = 1 := h_reduced y hy_unit
      rw [hy1, mul_one] at h_prod
      refine ⟨⟨e, h_prod.symm⟩, ⟨0, ?_⟩⟩
      simp [hy1]
    · -- Neither is a unit, so both have atomic factorizations
      obtain ⟨sx, hsx⟩ := h_atomic x hx_unit
      obtain ⟨sy, hsy⟩ := h_atomic y hy_unit

      -- Every atom in sx equals p (by atom_dividing_coprime_product_eq)
      have hsx_all_p : ∀ a ∈ sx, a = p := fun a ha =>
        atom_dividing_coprime_product_eq h_reduced h_atomic h_cfi hp h_coprime h_prod
          (hsx.1 a ha) (hsx.2 ▸ Multiset.dvd_prod ha)

      -- Every atom in sy equals p (by symmetry)
      have hsy_all_p : ∀ a ∈ sy, a = p := by
        intro a ha
        have h_coprime' : AreCoprime y x := fun q hq hqy hqx => h_coprime q hq hqx hqy
        have h_prod' : y * x = p ^ e := by rw [mul_comm]; exact h_prod
        exact atom_dividing_coprime_product_eq h_reduced h_atomic h_cfi hp h_coprime' h_prod'
          (hsy.1 a ha) (hsy.2 ▸ Multiset.dvd_prod ha)

      -- x = sx.prod = p^|sx| and y = sy.prod = p^|sy|
      have hx_power : x ∈ Submonoid.powers p := by
        rw [← hsx.2, Multiset.eq_replicate_of_mem hsx_all_p]
        exact ⟨Multiset.card sx, by simp⟩
      have hy_power : y ∈ Submonoid.powers p := by
        rw [← hsy.2, Multiset.eq_replicate_of_mem hsy_all_p]
        exact ⟨Multiset.card sy, by simp⟩

      exact ⟨hx_power, hy_power⟩

/-!
## Main Theorem: PP-P from CFI (Coprime Case)

This gives PP-P for the special case where x and y are coprime.
The general case requires decomposing x = p^a * x_pf and y = p^b * y_pf
and applying the blockwise argument to the p-free parts.
-/

/-- **Proposition 5.3 (Coprime Case)**: CFI implies PP-P for coprime elements. -/
theorem Prop_CFI_implies_PPP_Coprime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ x y : M, AreCoprime x y → x * y ∈ Submonoid.powers p →
      x ∈ Submonoid.powers p ∧ y ∈ Submonoid.powers p := fun p hp x y h_coprime ⟨e, he⟩ =>
  coprime_product_powers h_reduced h_atomic h_cfi hp h_coprime he.symm

/-!
## Full PP-P (General Case)

The full PP-P for non-coprime x and y requires:
1. Decompose x = p^a * x_pf and y = p^b * y_pf where x_pf, y_pf are p-free
2. Apply the coprime case to x_pf and y_pf
3. Conclude x_pf = y_pf = 1

This is the paper's blockwise argument from Proposition 5.3.
-/

/-- **Proposition 5.3 (Full)**: CFI implies PP-P. -/
theorem Prop_CFI_implies_PPP_Full {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    PP_P M := by
  intro p hp x y hxy
  obtain ⟨e, he⟩ := hxy
  -- The full proof decomposes x and y into p-parts and p-free parts,
  -- then applies the coprime case to the p-free parts.
  -- This requires formalizing the p-free decomposition and showing
  -- the p-free parts are coprime (which they are, since they're p-free
  -- and disjoint in support).
  sorry

end
