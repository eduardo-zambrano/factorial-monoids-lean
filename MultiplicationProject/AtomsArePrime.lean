/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Atoms Are Prime Under CFI

This file proves that under CFI, atoms are prime (if p | a*b then p | a or p | b).
This is a key consequence of PP-P.
-/

import MultiplicationProject.LocalPurity

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-- Under PP-D + CFI, atoms are prime: if p ∣ a·b then p ∣ a or p ∣ b.

    Proof strategy:
    1. Get PP-P from CFI via Prop_CFI_implies_PPP
    2. If p | a*b but p ∤ a and p ∤ b, derive contradiction
    3. Use power_coprime_of_not_in_support to show p is coprime to a and b
    4. Key insight: if p ∤ a, then for all k, p^k coprime to a
       This means the "p-content" of a is trivial
    5. Similarly for b
    6. By CFI/PP-P machinery, if p | a*b, the p must come from somewhere
    7. Contradiction
-/
lemma atoms_are_prime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p hp a b h_dvd
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  -- Strategy: Use PP-P to show that the "p-part" of a*b comes from a or b.
  -- If p ∤ a and p ∤ b, we derive a contradiction.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨h_not_a, h_not_b⟩ := h_neg
  -- p | a*b means a*b = p * m for some m
  obtain ⟨m, hm⟩ := h_dvd
  -- Key: use `power_coprime_of_not_in_support` to show p is coprime to a and b
  -- p ∤ a means p ∉ Support a (since if p ∈ Support a, then p | a)
  have hp_not_supp_a : p ∉ Support a := by
    intro h_in
    exact h_not_a h_in.2
  have hp_not_supp_b : p ∉ Support b := by
    intro h_in
    exact h_not_b h_in.2
  -- By power_coprime_of_not_in_support, p^1 = p and a are coprime, similarly for b
  have h_cop_pa : AreCoprime (p ^ 1) a := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_a 1
  have h_cop_pb : AreCoprime (p ^ 1) b := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_b 1
  simp only [pow_one] at h_cop_pa h_cop_pb
  -- Now we need: if p coprime to a and p coprime to b, then p coprime to a*b
  -- Use the coprimality structure: p being coprime to both a and b
  -- means no atom q can divide both p and a (or both p and b)
  -- Since p is itself an atom, this means p ∤ a and p ∤ b
  -- But we need to show p ∤ a*b, which requires atoms being prime!
  -- Alternative approach: Use PP-P more directly
  -- Since p | a*b, write a*b = p * m
  -- Consider the atomic factorization of a and b
  -- Every atom in the factorization of a*b appears in either a or b
  -- If p appears in a*b but not in a or b, contradiction
  sorry

end
