/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1f61f688-28c5-4ba3-8420-c1e0c5468917

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma atoms_are_prime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Atoms Are Prime Under CFI - Direct Proof

This file proves that under CFI, atoms are prime (if p | a*b then p | a or p | b)
using a DIRECT argument from CFI, not going through PP-P.

## Key Insight

The proof uses the CFI bijection structure directly:
1. If p | a*b and a,b are coprime, the factorization (p, m) of a*b must arise from
   F_2(a) × F_2(b).
2. Since p is an atom (irreducible), p = a₁·b₁ forces a₁=1 or b₁=1.
3. This means p divides a or p divides b.

For the general (non-coprime) case, we reduce to coprime parts.
-/

import MultiplicationProject.LocalPurity


set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Auxiliary Lemma: Atom factorization in reduced monoids

In a reduced monoid, if p is an atom and p = a * b, then a = 1 or b = 1.
-/

/-- In a reduced monoid, atoms have only trivial factorizations. -/
lemma atom_eq_mul_iff {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p a b : M} (hp : p ∈ Atoms M) (h : p = a * b) :
    a = 1 ∧ b = p ∨ a = p ∧ b = 1 := by
  -- p is irreducible, so p = a * b means a or b is a unit
  simp only [Atoms, Set.mem_setOf_eq] at hp
  have h_or := hp.isUnit_or_isUnit h
  cases h_or with
  | inl ha =>
    left
    constructor
    · exact h_reduced a ha
    · rw [h_reduced a ha] at h; simp at h; exact h.symm
  | inr hb =>
    right
    constructor
    · rw [h_reduced b hb] at h; simp at h; exact h.symm
    · exact h_reduced b hb

/-!
## Coprime Case: Direct from CFI bijection

When a and b are coprime, we can apply CFI directly.
-/

/-- **Atoms are prime (coprime case)**: If a and b are coprime and p | a*b, then p | a or p | b.

    This uses CFI directly:
    1. CFI gives bijection F_2(a) × F_2(b) ≅ F_2(a*b)
    2. The factorization (p, m) of a*b has a unique preimage
    3. Write p = a₁ * b₁ where (a₁, a₂) ∈ F_2(a) and (b₁, b₂) ∈ F_2(b)
    4. Since p is irreducible: a₁ = 1 (so b₁ = p, hence p | b) or b₁ = 1 (so a₁ = p, hence p | a)
-/
lemma atoms_are_prime_coprime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_cfi : CFI M)
    {p : M} (hp : p ∈ Atoms M)
    {a b : M} (h_coprime : AreCoprime a b) (h_dvd : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  -- p | a*b means a*b = p * m for some m
  obtain ⟨m, hm⟩ := h_dvd
  -- Get the CFI bijection
  have h_bij : Function.Bijective (Function.uncurry (labeledFactorizationMul (k := 2) (x := a) (y := b))) :=
    h_cfi a b h_coprime
  -- The factorization (p, m) is in F_2(a*b)
  have h_prod : p * m = a * b := hm.symm
  -- By surjectivity, (p, m) has a preimage in F_2(a) × F_2(b)
  -- This means there exist factorizations of a and b whose coordinatewise product gives (p, m)
  -- Let's use Coprime_Mul_Split from LocalPurity
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, hab1, hab2⟩ := Coprime_Mul_Split h_cfi a b h_coprime p m h_prod
  -- Now: a₁ * a₂ = a, b₁ * b₂ = b, a₁ * b₁ = p, a₂ * b₂ = m
  -- Since p is an atom, a₁ * b₁ = p implies a₁ = 1 or b₁ = 1
  have h_atom_factor := atom_eq_mul_iff h_reduced hp hab1.symm
  rcases h_atom_factor with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
  · -- a₁ = 1 and b₁ = p
    right
    rw [hb1] at hb
    -- b₁ * b₂ = b means p * b₂ = b, so p | b
    exact ⟨b₂, hb.symm⟩
  · -- a₁ = p and b₁ = 1
    left
    rw [ha1] at ha
    -- a₁ * a₂ = a means p * a₂ = a, so p | a
    exact ⟨a₂, ha.symm⟩

/-!
## General Case: Reduction via p-free decomposition

For the general case where a and b may not be coprime, we use the p-free parts.
-/

/- **Atoms are prime (general case)**: Under CFI, if p | a*b then p | a or p | b.

    Proof strategy:
    1. Decompose a = p^α * a' and b = p^β * b' where a', b' are p-free
    2. If α > 0, then p | a and we're done
    3. If β > 0, then p | b and we're done
    4. If α = β = 0 (both p-free), we need to show p ∤ a*b (contradiction)

    For case 4, we use a more sophisticated argument involving the blockwise CFI structure.
-/
noncomputable section AristotleLemmas

/-
If p divides q^k * m and is coprime to q^k, then p divides m.
-/
lemma atom_dvd_power_mul_coprime {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {p q m : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ)
    (h_coprime : AreCoprime (q ^ k) m) (h_dvd : p ∣ q ^ k * m) (h_neq : p ≠ q) :
    p ∣ m := by
      have := atoms_are_prime_coprime h_reduced h_cfi hp h_coprime h_dvd;
      exact this.resolve_left ( fun h => h_neq <| atom_dvd_power_eq_of_CFI h_reduced h_cfi hq hp h )

/-
If q is an atom not in a multiset of atoms t, and the inductive hypothesis holds for t, then q^k is coprime to t.prod.
-/
lemma coprime_pow_prod_of_forall_neq {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (_h_cfi : CFI M)
    (q : M) (hq : q ∈ Atoms M)
    (t : Multiset M) (_ht : ∀ x ∈ t, x ∈ Atoms M)
    (h_neq : ∀ x ∈ t, x ≠ q)
    (h_ind : ∀ p, p ∈ Atoms M → p ∣ t.prod → p ∈ t)
    (k : ℕ) :
    AreCoprime (q ^ k) t.prod := by
      have h_coprime : ∀ p ∈ Atoms M, p ∣ t.prod → p ≠ q := by
        exact fun p hp hp' => h_neq p ( h_ind p hp hp' );
      -- Use power_coprime_of_not_in_support: need to show q ∉ Support (t.prod)
      have h_not_in_supp : q ∉ Support t.prod := by
        simp only [Support, Set.mem_setOf_eq, not_and]
        intro _ h_dvd
        exact h_coprime q hq h_dvd rfl
      exact power_coprime_of_not_in_support h_reduced _h_cfi hq h_not_in_supp k

/-
If an atom p divides the product of a multiset of atoms s, then p must be in s.
-/
lemma atom_dvd_multiset_prod {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_cfi : CFI M)
    (s : Multiset M) (hs : ∀ x ∈ s, x ∈ Atoms M)
    (p : M) (hp : p ∈ Atoms M) (h_dvd : p ∣ s.prod) :
    p ∈ s := by
      revert s;
      intro s hs h_dvd;
      induction' s using Multiset.strongInductionOn with s ih generalizing p;
      -- Let `q ∈ s`.
      by_cases hq : ∃ q ∈ s, p = q;
      · grind;
      · -- Let `q ∈ s` and `k = s.count q`. Let `t = s.filter (· ≠ q)`.
        obtain ⟨q, hq_mem, hq_count, ht⟩ : ∃ q ∈ s, Multiset.count q s = Multiset.count q s ∧ s = Multiset.replicate (Multiset.count q s) q + s.filter (· ≠ q) := by
          by_cases hs_empty : s = 0;
          · simp_all +decide [ Atoms ];
            exact hp.not_dvd_one h_dvd;
          · obtain ⟨ q, hq ⟩ := Multiset.exists_mem_of_ne_zero hs_empty; use q; simp_all +decide ;
            ext x; by_cases hx : x = q <;> simp +decide [ hx, Multiset.count_replicate ] ;
            aesop;
        -- We have `p ∣ q^k * t.prod`.
        have h_div : p ∣ q ^ Multiset.count q s * (s.filter (· ≠ q)).prod := by
          convert h_dvd using 1;
          conv_rhs => rw [ ht, Multiset.prod_add, Multiset.prod_replicate ] ;
        -- We want to apply `atom_dvd_power_mul_coprime`.
        -- We need `AreCoprime (q^k) t.prod`.
        have h_coprime : AreCoprime (q ^ Multiset.count q s) (s.filter (· ≠ q)).prod := by
          apply coprime_pow_prod_of_forall_neq h_reduced h_cfi q (hs q hq_mem) (s.filter (· ≠ q)) (fun x hx => hs x (Multiset.mem_filter.mp hx).left) (fun x hx => by
            exact Multiset.mem_filter.mp hx |>.2) (fun p hp h_dvd => by
            apply ih (s.filter (· ≠ q)) (by
            refine' lt_of_le_of_ne ( Multiset.filter_le _ _ ) _;
            exact fun h => by simp_all +singlePass ;) p hp (fun x hx => hs x (Multiset.mem_filter.mp hx).left) h_dvd) (Multiset.count q s);
        -- Apply `atom_dvd_power_mul_coprime` with `p, q, k, t.prod`.
        have h_div_t : p ∣ (s.filter (· ≠ q)).prod := by
          apply atom_dvd_power_mul_coprime h_reduced h_cfi hp (hs q hq_mem) (Multiset.count q s) h_coprime h_div;
          exact fun h => hq ⟨ q, hq_mem, h ⟩;
        specialize ih ( Multiset.filter ( fun x => x ≠ q ) s ) ?_ p hp ?_ h_div_t;
        · refine' lt_of_le_of_ne ( Multiset.filter_le _ _ ) _;
          exact fun h => by simp_all +singlePass ;
        · exact fun x hx => hs x ( Multiset.mem_filter.mp hx |>.1 );
        · exact Multiset.mem_of_mem_filter ih

/-
The product of a multiset s is equal to q^(count of q in s) times the product of the elements of s not equal to q.
-/
open scoped Classical

lemma prod_eq_pow_count_mul_prod_filter_ne {M : Type*} [CommMonoid M]
    (s : Multiset M) (q : M) :
    s.prod = q ^ (s.count q) * (s.filter (· ≠ q)).prod := by
      -- We can prove this by induction on the multiset s.
      induction' s using Multiset.induction_on with x s ih;
      · simp +decide;
      · by_cases hx : x = q <;> simp_all +decide [ pow_succ', mul_assoc, mul_left_comm ];
        rw [ Multiset.count_cons_of_ne ] ; aesop

end AristotleLemmas

lemma atoms_are_prime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p hp a b h_dvd
  -- Case split on whether p divides a or b directly
  by_cases ha : p ∣ a
  · left; exact ha
  · by_cases hb : p ∣ b
    · right; exact hb
    · -- Neither p | a nor p | b. We'll derive a contradiction.
      -- This means a and b are "p-free" in the sense that p ∉ Support(a) and p ∉ Support(b)
      exfalso
      -- p ∤ a means p ∉ Support a
      have hp_not_supp_a : p ∉ Support a := fun h_in => ha h_in.2
      have hp_not_supp_b : p ∉ Support b := fun h_in => hb h_in.2
      -- AreCoprime p a means: for all atoms q, q ∣ p → q ∤ a
      -- Since p is an atom, the only atom dividing p is p itself
      -- So AreCoprime p a is equivalent to: p ∤ a (which we have as ha)
      have h_cop_pa : AreCoprime p a := by
        intro q hq hqp
        -- q is an atom and q ∣ p. Since p is an atom, q = p.
        have heq : q = p := by
          simp only [Atoms, Set.mem_setOf_eq] at hp hq
          obtain ⟨r, hr⟩ := hqp
          -- hr : p = q * r
          have := hp.isUnit_or_isUnit hr
          cases this with
          | inl hqu => exact absurd hqu hq.not_isUnit
          | inr hru => rw [h_reduced r hru, mul_one] at hr; exact hr.symm
        rw [heq]
        exact ha
      have h_cop_pb : AreCoprime p b := by
        intro q hq hqp
        have heq : q = p := by
          simp only [Atoms, Set.mem_setOf_eq] at hp hq
          obtain ⟨r, hr⟩ := hqp
          have := hp.isUnit_or_isUnit hr
          cases this with
          | inl hqu => exact absurd hqu hq.not_isUnit
          | inr hru => rw [h_reduced r hru, mul_one] at hr; exact hr.symm
        rw [heq]
        exact hb
      -- Now use the key insight: apply CFI to understand the factorization
      -- Since p | a*b, we have a*b = p * m
      obtain ⟨m, hm⟩ := h_dvd
      -- Consider the decomposition of a and b by their atomic structure
      -- The product a*b contains p as a factor, but p doesn't come from a or b individually
      -- This violates the CFI structure
      --
      -- Key argument: Look at the atomic factorization of a*b.
      -- Since a*b = p * m, the atom p appears in the factorization of a*b.
      -- By atomicity, a has a factorization into atoms, and so does b.
      -- The atoms in a*b are exactly the atoms from a plus the atoms from b (with multiplicities).
      -- Since p doesn't appear in a's factorization (p ∤ a) and doesn't appear in b's (p ∤ b),
      -- p cannot appear in a*b's factorization. Contradiction.
      --
      -- Formalization: Use CFI on suitable coprime pairs to derive the contradiction.
      -- We apply CFI to (p, m) being a factorization of a*b.
      -- By the coprimality structure, this factorization must "factor through" a and b.
      -- But the p component can't come from either, contradiction.
      have h_coprime_ab : ∀ {p : M}, p ∈ Atoms M → p ∣ a * b → p ∣ a ∨ p ∣ b := by
        intro p hp h_div
        obtain ⟨s_a, hs_a⟩ : ∃ s_a : Multiset M, a = s_a.prod ∧ ∀ x ∈ s_a, x ∈ Atoms M := by
          by_cases ha : IsUnit a;
          · obtain ⟨ u, rfl ⟩ := ha;
            have := h_reduced ( u : M ) ; aesop;
          · cases h_atomic a ha ; aesop
        obtain ⟨s_b, hs_b⟩ : ∃ s_b : Multiset M, b = s_b.prod ∧ ∀ x ∈ s_b, x ∈ Atoms M := by
          cases' eq_or_ne b 1 with hb hb <;> simp_all +decide [ Atomic ];
          specialize h_atomic b (by
          contrapose! hb; aesop;);
          aesop;
        have h_coprime_div : p ∣ (s_a + s_b).prod → p ∈ s_a + s_b := by
          apply atom_dvd_multiset_prod h_reduced h_cfi (s_a + s_b) (by
          grind) p hp;
        cases Multiset.mem_add.mp ( h_coprime_div ( by simpa only [ hs_a.1, hs_b.1, Multiset.prod_add ] using h_div ) ) <;> simp_all +decide;
        · exact Or.inl ( Multiset.dvd_prod ‹_› );
        · exact Or.inr ( Multiset.dvd_prod ‹_› );
      exact absurd ( h_coprime_ab hp ( hm.symm ▸ dvd_mul_right _ _ ) ) ( by tauto )

end