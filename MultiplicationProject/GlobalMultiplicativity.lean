/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 7: Global Multiplicativity from CFI

This file proves that factorization counts are multiplicative on coprime inputs.

Main results:
- `prop_coprime_mult`: F_k(x·y) = F_k(x)·F_k(y) for coprime x, y (Proposition 7.2)

Note: Corollary 7.3 (squarefree diagnostic) is deferred to MasterFormula.lean
where h_prime_atoms can be derived rather than assumed.

Formalized with assistance from Aristotle (uuid: 62b9b7ab-c8d3-4520-b982-52cb3d7e73ba)
-/

import MultiplicationProject.LocalCharacterization

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Coprimality Lemmas
-/

/-- If x, y are coprime and x' ∣ x, y' ∣ y, then x', y' are coprime.
    This is essential for the induction: factors of coprime elements remain coprime. -/
lemma AreCoprime_of_dvd {M : Type*} [CommMonoid M] {x y x' y' : M}
    (h : AreCoprime x y) (hx : x' ∣ x) (hy : y' ∣ y) : AreCoprime x' y' := by
  intro p hp hpx hpy
  exact h p hp (dvd_trans hpx hx) (dvd_trans hpy hy)

/-- Coprimality is symmetric. -/
lemma AreCoprime_symm {M : Type*} [CommMonoid M] {x y : M} :
    AreCoprime x y ↔ AreCoprime y x := by
  constructor
  · exact fun a p hp hpy hpx => a p hp hpx hpy
  · exact fun a p hp hpx hpy => a p hp hpy hpx

/-- If atoms are prime, then coprimality is preserved under multiplication. -/
lemma AreCoprime_mul_of_prime_atoms {M : Type*} [CommMonoid M]
    (h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b)
    {x y z : M} (h1 : AreCoprime x z) (h2 : AreCoprime y z) :
    AreCoprime (x * y) z := by
  intro p hp hxz
  cases' h_prime p hp x y hxz with hx hy
  · exact h1 p hp hx
  · exact h2 p hp hy

/-!
## Splitting Factorizations

These definitions establish an equivalence between (k+1)-factorizations and
pairs of (2-factorization, k-factorization). This is the key structural lemma
for the induction.
-/

/-- Forward map for splitting a factorization.
    Takes a (k+1)-factorization (w₀, w₁, ..., wₖ) and produces:
    - A 2-factorization (w₀, w₁·...·wₖ)
    - A k-factorization (w₁, ..., wₖ) of w₁·...·wₖ -/
def splitFactorizationTo {M : Type*} [CommMonoid M] (k : ℕ) (m : M)
    (w : LabeledFactorizations (k + 1) m) :
    Σ (f : LabeledFactorizations 2 m), LabeledFactorizations k (f.1 1) :=
  let w' := w.1
  let u := Finset.univ.prod (Fin.tail w')
  let f2 : LabeledFactorizations 2 m := ⟨Fin.cons (w' 0) (Fin.cons u Fin.elim0), by
    simp +zetaDelta at *
    convert w.2 using 1
    unfold LabeledFactorizations; simp +decide [Fin.prod_univ_succ, Fin.tail]⟩
  let fk : LabeledFactorizations k u := ⟨Fin.tail w', by aesop⟩
  ⟨f2, fk⟩

/-- Inverse map for splitting a factorization.
    Takes a 2-factorization (a, b) and a k-factorization of b, produces a (k+1)-factorization. -/
def splitFactorizationInv {M : Type*} [CommMonoid M] (k : ℕ) (m : M)
    (s : Σ (f : LabeledFactorizations 2 m), LabeledFactorizations k (f.1 1)) :
    LabeledFactorizations (k + 1) m :=
  let f2 := s.1
  let fk := s.2
  ⟨Fin.cons (f2.1 0) fk.1, by
    unfold LabeledFactorizations at *; aesop⟩

/-- An equivalence between (k+1)-factorizations and pairs of (2-factorization, k-factorization).
    This is the key structural result for the induction in Proposition 7.2. -/
def splitFactorization {M : Type*} [CommMonoid M] (k : ℕ) (m : M) :
    LabeledFactorizations (k + 1) m ≃ Σ (f : LabeledFactorizations 2 m), LabeledFactorizations k (f.1 1) :=
  { toFun := splitFactorizationTo k m
    invFun := splitFactorizationInv k m
    left_inv := by
      intros w
      simp [splitFactorizationTo, splitFactorizationInv]
    right_inv := by
      intro f; unfold splitFactorizationTo splitFactorizationInv; aesop
      · ext i; fin_cases i <;> aesop
      · congr! }

/-!
## Counting Lemmas
-/

/-- F₁(m) = 1 for all m. The only 1-factorization of m is (m) itself. -/
lemma count_one {M : Type*} [CommMonoid M] (m : M) : LabeledFactorizationCount 1 m = 1 := by
  unfold LabeledFactorizationCount LabeledFactorizations
  aesop
  exact ⟨fun _ => m, Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun f hf => by ext i; fin_cases i; exact hf⟩⟩

/-- F_{k+1}(m) equals the sum over all 2-factorizations f of F_k(f(1)).
    This decomposes counting (k+1)-factorizations into counting k-factorizations. -/
lemma count_split {M : Type*} [CommMonoid M] (k : ℕ) (m : M)
    (h_fin2 : (LabeledFactorizations 2 m).Finite)
    (h_fink : ∀ f : LabeledFactorizations 2 m, (LabeledFactorizations k (f.1 1)).Finite) :
    LabeledFactorizationCount (k + 1) m = ∑ f ∈ h_fin2.toFinset, LabeledFactorizationCount k (f 1) := by
  simp +decide [LabeledFactorizationCount]
  rw [show LabeledFactorizations (k + 1) m = Set.image (fun f : Σ (f : LabeledFactorizations 2 m), LabeledFactorizations k (f.1 1) => Fin.cons (f.1.val 0) f.2.val) (Set.univ) from ?_]
  · rw [Set.ncard_image_of_injective]
    · norm_num +zetaDelta at *
      convert Nat.card_sigma
      any_goals exact Set.Finite.fintype h_fin2
      · refine' Finset.sum_bij (fun x hx => ⟨x, _⟩) _ _ _ _ <;> aesop
      · exact fun a => Set.Finite.to_subtype (h_fink a a.2)
    · intro f g hfg
      aesop
      · ext i; fin_cases i <;> aesop
        simp_all +decide [LabeledFactorizations]
      · congr
        · unfold LabeledFactorizations at *; aesop
        · unfold LabeledFactorizations at *; aesop
  · ext f; aesop
    · refine' ⟨Fin.cons (f 0) (Fin.cons (Finset.univ.prod (Fin.tail f)) Fin.elim0), _, Fin.tail f, _, _⟩ <;> simp_all +decide [LabeledFactorizations]
      simp +decide [← a, Fin.univ_succ]
      rfl
    · unfold LabeledFactorizations at *; aesop

/-- The number of k-factorizations of an atom p is k.
    Each factorization has exactly one slot with p and the rest with 1. -/
lemma count_atom {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {k : ℕ} (hk : k ≥ 1) {p : M} (hp : p ∈ Atoms M) :
    LabeledFactorizationCount k p = k := by
  -- Each k-factorization of p has exactly one factor equal to p and the rest equal to 1
  have h_factorizations : ∀ f ∈ LabeledFactorizations k p, ∃ i : Fin k, f i = p ∧ ∀ j : Fin k, j ≠ i → f j = 1 := by
    intro f hf
    have h_factor : ∀ j : Fin k, f j = p ∨ f j = 1 := by
      intro j
      have h_div : f j ∣ p := by
        exact hf ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      cases' h_div with u hu
      cases hp.2 hu <;> aesop
      cases h_reduced u h; aesop
    -- Since p is irreducible, there must be exactly one i such that f(i) = p
    obtain ⟨i, hi⟩ : ∃ i : Fin k, f i = p := by
      contrapose! hf; aesop
      replace a := congr_arg (fun x => x) a; simp_all +decide [Finset.prod_eq_one]
      exact hf ⟨0, hk⟩
    have h_prod_one : ∏ j ∈ Finset.univ \ {i}, f j = 1 := by
      have h_prod_one : ∏ j ∈ Finset.univ, f j = p * ∏ j ∈ Finset.univ \ {i}, f j := by
        rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i), hi]
      cases hp; aesop
      cases isUnit_or_isUnit (show f i = f i * ∏ j ∈ Finset.univ \ {i}, f j from hf.symm.trans h_prod_one) <;> aesop
    have h_all_one : ∀ j ∈ Finset.univ \ {i}, f j = 1 := by
      intro j hj; specialize h_factor j; aesop
      have := h_prod_one ▸ Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by aesop⟩); aesop
      exact h_reduced _ (isUnit_of_dvd_one this)
    exact ⟨i, hi, fun j hj => h_all_one j (by simp [hj])⟩
  -- Count: there are exactly k such factorizations (one for each choice of i)
  have h_count : (LabeledFactorizations k p).ncard = Finset.card (Finset.image (fun i : Fin k => fun j : Fin k => if j = i then p else 1) (Finset.univ : Finset (Fin k))) := by
    rw [← Set.ncard_coe_finset]; congr; ext; aesop
    · obtain ⟨i, hi, hi'⟩ := h_factorizations x a; use i; ext j; by_cases hj : j = i <;> aesop
    · unfold LabeledFactorizations; aesop
  rw [Finset.card_image_of_injective] at h_count
  · aesop
  · intro i j hij; replace hij := congr_fun hij j; aesop
    cases eq_or_ne j i <;> aesop
    exact absurd hp.1 (by simp (config := { decide := Bool.true }))

/-!
## Main Result: Proposition 7.2
-/

/-- **Proposition 7.2**: Coprime multiplicativity of factorization counts.

    Assume (CFI). If x and y are coprime, then F_k(x·y) = F_k(x)·F_k(y) for all k ≥ 1.

    Proof by strong induction on k:
    - Base k=1: F₁(m) = 1 for all m
    - Base k=2: Directly from CFI (bijection gives equal cardinalities)
    - Induction k → k+1: Use splitFactorization to decompose, apply IH to fibers -/
theorem prop_coprime_mult {M : Type*} [CommMonoid M]
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : CFI M)
    {k : ℕ} (hk : k ≥ 1) {x y : M} (h_coprime : AreCoprime x y) :
    LabeledFactorizationCount k (x * y) = LabeledFactorizationCount k x * LabeledFactorizationCount k y := by
  revert hk h_coprime
  induction' k using Nat.strong_induction_on with k ih generalizing x y
  rcases k with (_ | _ | k) <;> simp_all +decide
  · exact fun h => by rw [count_one, count_one, count_one, mul_one]
  · intro h_coprime
    have h_split : LabeledFactorizationCount (k + 2) (x * y) = ∑ f ∈ (h_finite 2 (x * y)).toFinset, LabeledFactorizationCount (k + 1) (f 1) := by
      apply count_split
      exact fun f => h_finite _ _
    -- Using CFI, we have a bijection E: F_2(x) × F_2(y) → F_2(x*y)
    obtain ⟨E, hE⟩ : ∃ E : LabeledFactorizations 2 x × LabeledFactorizations 2 y ≃ LabeledFactorizations 2 (x * y), ∀ (f : LabeledFactorizations 2 x × LabeledFactorizations 2 y), E f = ⟨f.1.1 * f.2.1, by
      aesop
      exact Eq.trans (Finset.prod_mul_distrib) (property.symm ▸ property_1.symm ▸ rfl)⟩ := by
      all_goals generalize_proofs at *
      have := h_cfi x y h_coprime
      exact ⟨Equiv.ofBijective _ this, fun f => rfl⟩
    generalize_proofs at *
    -- For each (f,g) in F_2(x) × F_2(y), we have (f·g)(1) = f(1)·g(1), and these are coprime
    have h_term : ∀ (f : LabeledFactorizations 2 x × LabeledFactorizations 2 y), LabeledFactorizationCount (k + 1) ((f.1.1 * f.2.1) 1) = LabeledFactorizationCount (k + 1) (f.1.1 1) * LabeledFactorizationCount (k + 1) (f.2.1 1) := by
      intro f
      have h_coprime_f : AreCoprime (f.1.1 1) (f.2.1 1) := by
        apply_rules [AreCoprime_of_dvd]
        · have := f.1.2
          exact dvd_trans (by simp +decide) (this.symm ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ 1))
        · exact dvd_trans (by simp +decide) (f.2.2.symm ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ 1))
      exact ih _ (Nat.lt_succ_self _) (Nat.succ_pos _) h_coprime_f
    -- Reindex the sum using the bijection E
    have h_sum_bij : ∑ f ∈ (h_finite 2 (x * y)).toFinset, LabeledFactorizationCount (k + 1) (f 1) = ∑ f ∈ (h_finite 2 x).toFinset ×ˢ (h_finite 2 y).toFinset, LabeledFactorizationCount (k + 1) (f.1 1) * LabeledFactorizationCount (k + 1) (f.2 1) := by
      norm_num +zetaDelta at *
      refine' Finset.sum_bij (fun f hf => (E.symm ⟨f, by aesop⟩ |>.1.val, E.symm ⟨f, by aesop⟩ |>.2.val)) _ _ _ _ <;> simp +decide
      · grind
      · grind
      · intro a ha
        generalize_proofs at *
        convert h_term _ _ _ _
        all_goals norm_num +zetaDelta at *
        have := E.apply_symm_apply ⟨a, ha⟩; aesop
        exact congr_fun this.symm 1
    simp_all +decide [Finset.sum_product]
    rw [count_split, count_split]
    any_goals intro f; exact h_finite _ _
    any_goals exact h_finite _ _
    simp +decide only [← Finset.mul_sum _ _ _, ← Finset.sum_mul]

end
