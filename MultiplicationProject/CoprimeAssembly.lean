/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 7: Global Multiplicativity from CFI

This file proves that factorization counts are multiplicative on coprime inputs.

Main results:
- `prop_coprime_mult`: F_k(x·y) = F_k(x)·F_k(y) for coprime x, y (Proposition 7.2)

Note: Corollary 7.3 (squarefree diagnostic) is deferred to FactorialStructure.lean
where h_prime_atoms can be derived rather than assumed.

Formalized with assistance from Aristotle (uuid: 62b9b7ab-c8d3-4520-b982-52cb3d7e73ba)
-/

import MultiplicationProject.LocalCounting

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


/-!
## CFI extends to all k

The coordinatewise assembly μ_k is a bijection for every k ≥ 1, by induction
from the k = 2 case postulated by CFI. This is the paper's Lemma
"CFI extends to all k". (The case k = 0 is excluded: without reducedness a
unit x ≠ 1 has no 0-factorization while x · x⁻¹ = 1 has one.)
-/

/-- **CFI extends to all k**: for coprime x, y and every k, the coordinatewise
    map μ_{k+1} : F_{k+1}(x) × F_{k+1}(y) → F_{k+1}(xy) is a bijection. -/
theorem CFI_bijective_all_k {M : Type*} [CommMonoid M] (h_cfi : CFI M) :
    ∀ (k : ℕ) {x y : M}, AreCoprime x y →
    Function.Bijective
      (fun p : LabeledFactorizations (k+1) x × LabeledFactorizations (k+1) y =>
        labeledFactorizationMul p.1 p.2) := by
  intro k
  induction k with
  | zero =>
    intro x y _
    constructor
    · rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ ⟨⟨f', hf'⟩, ⟨g', hg'⟩⟩ _
      simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_succ,
        Fin.prod_univ_zero, mul_one] at hf hg hf' hg'
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext <;> funext i
      · show f i = f' i
        have hi : i = 0 := by omega
        subst hi
        rw [hf, hf']
      · show g i = g' i
        have hi : i = 0 := by omega
        subst hi
        rw [hg, hg']
    · rintro ⟨w, hw⟩
      simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_succ,
        Fin.prod_univ_zero, mul_one] at hw
      refine ⟨(⟨fun _ => x, ?_⟩, ⟨fun _ => y, ?_⟩), ?_⟩
      · simp [LabeledFactorizations, Fin.prod_univ_succ]
      · simp [LabeledFactorizations, Fin.prod_univ_succ]
      · apply Subtype.ext
        funext i
        have hi : i = 0 := by omega
        subst hi
        simp only [labeledFactorizationMul, Pi.mul_apply]
        exact hw.symm
  | succ k ih =>
    intro x y hxy
    have hprod2 : ∀ (u : Fin 2 → M) (m : M), u ∈ LabeledFactorizations 2 m →
        u 0 * u 1 = m := by
      intro u m hu
      simpa [LabeledFactorizations, Fin.prod_univ_two] using hu
    have hsplit : ∀ (u : Fin (k+2) → M) (m : M),
        Finset.univ.prod u = m →
        u 0 * Finset.univ.prod (Fin.tail u) = m := by
      intro u m hu
      rw [← hu]
      exact (Fin.prod_univ_succ u).symm
    constructor
    · -- injectivity
      rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ ⟨⟨f', hf'⟩, ⟨g', hg'⟩⟩ heq
      have hval : ∀ i, f i * g i = f' i * g' i := by
        intro i
        have h1 := congrArg (fun z => z.val i) heq
        simpa [labeledFactorizationMul] using h1
      simp only [LabeledFactorizations, Set.mem_setOf_eq] at hf hg hf' hg'
      have hFf : (![f 0, Finset.univ.prod (Fin.tail f)]) ∈
          LabeledFactorizations 2 x := by
        simp [LabeledFactorizations, Fin.prod_univ_two, hsplit f x hf]
      have hFg : (![g 0, Finset.univ.prod (Fin.tail g)]) ∈
          LabeledFactorizations 2 y := by
        simp [LabeledFactorizations, Fin.prod_univ_two, hsplit g y hg]
      have hFf' : (![f' 0, Finset.univ.prod (Fin.tail f')]) ∈
          LabeledFactorizations 2 x := by
        simp [LabeledFactorizations, Fin.prod_univ_two, hsplit f' x hf']
      have hFg' : (![g' 0, Finset.univ.prod (Fin.tail g')]) ∈
          LabeledFactorizations 2 y := by
        simp [LabeledFactorizations, Fin.prod_univ_two, hsplit g' y hg']
      have htailprod : Finset.univ.prod (Fin.tail f) * Finset.univ.prod (Fin.tail g)
          = Finset.univ.prod (Fin.tail f') * Finset.univ.prod (Fin.tail g') := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        exact hval i.succ
      have h2eq : (fun p : LabeledFactorizations 2 x × LabeledFactorizations 2 y =>
          labeledFactorizationMul p.1 p.2) (⟨_, hFf⟩, ⟨_, hFg⟩)
          = (fun p : LabeledFactorizations 2 x × LabeledFactorizations 2 y =>
          labeledFactorizationMul p.1 p.2) (⟨_, hFf'⟩, ⟨_, hFg'⟩) := by
        apply Subtype.ext
        funext i
        fin_cases i
        · simpa [labeledFactorizationMul, Pi.mul_apply] using hval 0
        · simpa [labeledFactorizationMul, Pi.mul_apply] using htailprod
      have h4 := (h_cfi x y hxy).1 h2eq
      have hf0 : f 0 = f' 0 := by
        have := congrArg (fun z => z.1.val 0) h4
        simpa using this
      have hg0 : g 0 = g' 0 := by
        have := congrArg (fun z => z.2.val 0) h4
        simpa using this
      have hTf : Finset.univ.prod (Fin.tail f) = Finset.univ.prod (Fin.tail f') := by
        have := congrArg (fun z => z.1.val 1) h4
        simpa using this
      have hTg : Finset.univ.prod (Fin.tail g) = Finset.univ.prod (Fin.tail g') := by
        have := congrArg (fun z => z.2.val 1) h4
        simpa using this
      have hcop : AreCoprime (Finset.univ.prod (Fin.tail f))
          (Finset.univ.prod (Fin.tail g)) := by
        refine AreCoprime_of_dvd hxy ⟨f 0, ?_⟩ ⟨g 0, ?_⟩
        · rw [mul_comm]; exact (hsplit f x hf).symm
        · rw [mul_comm]; exact (hsplit g y hg).symm
      have hmemf : Fin.tail f ∈ LabeledFactorizations (k+1)
          (Finset.univ.prod (Fin.tail f)) := rfl
      have hmemg : Fin.tail g ∈ LabeledFactorizations (k+1)
          (Finset.univ.prod (Fin.tail g)) := rfl
      have hmemf' : Fin.tail f' ∈ LabeledFactorizations (k+1)
          (Finset.univ.prod (Fin.tail f)) := by
        simp only [LabeledFactorizations, Set.mem_setOf_eq]
        exact hTf.symm
      have hmemg' : Fin.tail g' ∈ LabeledFactorizations (k+1)
          (Finset.univ.prod (Fin.tail g)) := by
        simp only [LabeledFactorizations, Set.mem_setOf_eq]
        exact hTg.symm
      have hiheq : (fun p : LabeledFactorizations (k+1) (Finset.univ.prod (Fin.tail f))
            × LabeledFactorizations (k+1) (Finset.univ.prod (Fin.tail g)) =>
          labeledFactorizationMul p.1 p.2) (⟨_, hmemf⟩, ⟨_, hmemg⟩)
          = (fun p : LabeledFactorizations (k+1) (Finset.univ.prod (Fin.tail f))
            × LabeledFactorizations (k+1) (Finset.univ.prod (Fin.tail g)) =>
          labeledFactorizationMul p.1 p.2) (⟨_, hmemf'⟩, ⟨_, hmemg'⟩) := by
        apply Subtype.ext
        funext i
        simp only [labeledFactorizationMul, Pi.mul_apply]
        exact hval i.succ
      have h5 := (ih hcop).1 hiheq
      have htf : Fin.tail f = Fin.tail f' := by
        have := congrArg (fun z => z.1.val) h5
        simpa using this
      have htg : Fin.tail g = Fin.tail g' := by
        have := congrArg (fun z => z.2.val) h5
        simpa using this
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext <;> funext i <;>
        refine Fin.cases ?_ (fun j => ?_) i
      · exact hf0
      · exact congrFun htf j
      · exact hg0
      · exact congrFun htg j
    · -- surjectivity
      rintro ⟨w, hw⟩
      simp only [LabeledFactorizations, Set.mem_setOf_eq] at hw
      have hw2 : w 0 * Finset.univ.prod (Fin.tail w) = x * y := hsplit w (x * y) hw
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ := (h_cfi x y hxy).2
        ⟨![w 0, Finset.univ.prod (Fin.tail w)], by
          simp [LabeledFactorizations, Fin.prod_univ_two, hw2]⟩
      have hab0 : a 0 * b 0 = w 0 := by
        have := congrArg (fun z => z.val 0) hab
        simpa [labeledFactorizationMul] using this
      have hab1 : a 1 * b 1 = Finset.univ.prod (Fin.tail w) := by
        have := congrArg (fun z => z.val 1) hab
        simpa [labeledFactorizationMul] using this
      have ha2 : a 0 * a 1 = x := hprod2 a x ha
      have hb2 : b 0 * b 1 = y := hprod2 b y hb
      have hcop : AreCoprime (a 1) (b 1) := by
        refine AreCoprime_of_dvd hxy ⟨a 0, ?_⟩ ⟨b 0, ?_⟩
        · rw [mul_comm]; exact ha2.symm
        · rw [mul_comm]; exact hb2.symm
      have hmemw : Fin.tail w ∈ LabeledFactorizations (k+1) (a 1 * b 1) := by
        simp only [LabeledFactorizations, Set.mem_setOf_eq]
        exact hab1.symm
      obtain ⟨⟨⟨fx, hfx⟩, ⟨fy, hfy⟩⟩, hfxy⟩ := (ih hcop).2 ⟨Fin.tail w, hmemw⟩
      simp only [LabeledFactorizations, Set.mem_setOf_eq] at hfx hfy
      have hfxyval : ∀ i, fx i * fy i = Fin.tail w i := by
        intro i
        have := congrArg (fun z => z.val i) hfxy
        simpa [labeledFactorizationMul] using this
      refine ⟨(⟨Fin.cons (a 0) fx, ?_⟩, ⟨Fin.cons (b 0) fy, ?_⟩), ?_⟩
      · show Finset.univ.prod (Fin.cons (a 0) fx) = x
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hfx]
        exact ha2
      · show Finset.univ.prod (Fin.cons (b 0) fy) = y
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hfy]
        exact hb2
      · apply Subtype.ext
        funext i
        simp only [labeledFactorizationMul, Pi.mul_apply]
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [Fin.cons_zero] using hab0
        · simpa [Fin.cons_succ] using hfxyval j

end
