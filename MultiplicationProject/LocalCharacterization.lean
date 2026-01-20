/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 6: Local Characterization on Prime Powers

This file proves the local stars-and-bars formula for factorization counts
on prime powers.

Main results:
- `Lemma_PP_Unique`: If p^e = x·y, then x = p^a and y = p^{e-a} for unique a (Lemma 6.1)
- `Theorem_Local_SB`: F_k(p^e) = C(e+k-1, k-1) (Theorem 6.2)

Formalized with assistance from Aristotle.
-/

import MultiplicationProject.LocalPurity

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Lemma 6.1: Unique Factorization within Prime Powers
-/

/-- **Lemma 6.1**: Assume (PP-D) and (PP-P). If p^e = x · y with p an atom,
    then x = p^a and y = p^{e-a} for a unique a ∈ {0, ..., e}. -/
lemma Lemma_PP_Unique {M : Type*} [CommMonoid M] (h_ppd : PP_D M) (h_ppp : PP_P M)
    (p : M) (hp : p ∈ Atoms M) (e : ℕ) (x y : M) (h_eq : p ^ e = x * y) :
    ∃! a : ℕ, a ≤ e ∧ x = p ^ a ∧ y = p ^ (e - a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, x = p ^ a := by
    have := h_ppp p hp x y
    exact this ⟨e, h_eq⟩ |>.1.imp fun n hn => hn.symm
  obtain ⟨b, hb⟩ : ∃ b : ℕ, y = p ^ b := by
    specialize h_ppp p hp x y
    aesop
    exact Exists.elim (h_ppp ⟨e, h_eq⟩ |>.2) fun b hb => ⟨b, hb.symm⟩
  use a
  aesop
  · rw [← pow_add] at h_eq
    have := h_ppd p hp
    linarith [this h_eq]
  · rw [← pow_add] at h_eq
    have := h_ppd p hp h_eq
    aesop
  · exact h_ppd p hp a_2.symm

/-!
## Theorem 6.2: Local Stars-and-Bars
-/

/-- **Theorem 6.2**: Local stars-and-bars formula.

    Under (PP-D) and (PP-P), for all atoms p, exponents e ≥ 0, and k ≥ 1:
    F_k(p^e) = C(e + k - 1, k - 1)

    This counts the number of ways to write e as an ordered sum of k non-negative
    integers, which is the classical stars-and-bars formula. -/
theorem Theorem_Local_SB {M : Type*} [CommMonoid M] (h_ppd : PP_D M) (h_ppp : PP_P M)
    (p : M) (hp : p ∈ Atoms M) (e : ℕ) (k : ℕ) (hk : k ≥ 1) :
    LabeledFactorizationCount k (p ^ e) = Nat.choose (e + k - 1) (k - 1) := by
  have h_count : Set.ncard {f : Fin k → M | ∃ g : Fin k → ℕ, (∀ i, f i = p ^ (g i)) ∧ (∑ i, g i) = e} =
                 Nat.choose (e + k - 1) (k - 1) := by
    rw [show {f : Fin k → M | ∃ g : Fin k → ℕ, (∀ i, f i = p ^ g i) ∧ ∑ i, g i = e} =
            Set.image (fun g : Fin k → ℕ => fun i => p ^ g i) {g : Fin k → ℕ | ∑ i, g i = e} from ?_,
        Set.ncard_image_of_injective]
    · rw [show {g : Fin k → ℕ | ∑ i, g i = e} =
              (Finset.filter (fun g : Fin k → ℕ => ∑ i, g i = e) (Finset.Iic (fun _ => e))) from ?_,
          Set.ncard_eq_toFinset_card'] <;> aesop
      · induction' k with k ih generalizing e <;> aesop
        by_cases hk : 1 ≤ k <;> aesop
        · have h_split : Finset.filter (fun g : Fin (k + 1) → ℕ => ∑ i, g i = e) (Finset.Iic (fun _ => e)) =
              Finset.biUnion (Finset.range (e + 1))
                (fun j => Finset.image (fun g : Fin k → ℕ => Fin.cons j g)
                  (Finset.filter (fun g : Fin k → ℕ => ∑ i, g i = e - j) (Finset.Iic (fun _ => e - j)))) := by
            ext g
            aesop
            · refine' ⟨g 0, _, Fin.tail g, _, _⟩ <;> simp +decide [Fin.sum_univ_succ]
              · exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
              · exact ⟨fun i => Finset.single_le_sum (fun a _ => Nat.zero_le (g (Fin.succ a)))
                                                      (Finset.mem_univ i), rfl⟩
            · exact fun i => by cases i using Fin.inductionOn <;>
                [exact Nat.le_of_lt_succ left; exact le_trans (left_1 _) (Nat.sub_le _ _)]
            · rw [Nat.add_sub_of_le (Nat.le_of_lt_succ left)]
          rw [h_split, Finset.card_biUnion]
          · rw [Finset.sum_congr rfl fun _ _ => Finset.card_image_of_injective _ <|
                fun _ _ h => by simpa [Fin.ext_iff] using h]
            aesop
            exact Nat.recOn e (by simp +arith +decide) fun n ih => by
              cases k <;> simp_all +decide [Nat.choose, add_comm, add_left_comm, Finset.sum_range_succ']
          · intro i hi j hj hij
            simp_all +decide [Finset.disjoint_left]
            intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃
            contrapose! hij
            aesop
        · rw [Finset.card_eq_one]
          use fun _ => e
          ext
          aesop
          exact funext fun i => by fin_cases i; rfl
      · exact Set.ext fun x => ⟨fun hx => ⟨fun i => hx ▸ Finset.single_le_sum
            (fun a _ => Nat.zero_le (x a)) (Finset.mem_univ i), hx⟩, fun hx => hx.2⟩
    · intro g₁ g₂ h_eq
      ext i
      have := congr_fun h_eq i
      aesop
    · aesop
  have h_eq : {f : Fin k → M | Finset.prod Finset.univ f = p ^ e} =
              {f : Fin k → M | ∃ g : Fin k → ℕ, (∀ i, f i = p ^ (g i)) ∧ (∑ i, g i) = e} := by
    ext f
    aesop
    · have h_factor : ∀ i, ∃ g_i : ℕ, f i = p ^ g_i := by
        intro i
        have := h_ppp p hp (f i) (Finset.prod (Finset.univ.erase i) f) ?_
        · exact this.1.imp fun n hn => hn.symm
        · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at *
          aesop
      choose g hg using h_factor
      simp_all +decide [Finset.prod_pow_eq_pow_sum]
      have := h_ppd p hp
      aesop
    · rw [Finset.prod_pow_eq_pow_sum]
  exact h_count ▸ h_eq ▸ rfl

end
