/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Sections 2-3: Basic Definitions and Axioms

This file contains the fundamental definitions for characterizing
factorial monoids via labeled factorization counts.

Based on the paper "Characterizing Factorial Monoids via Labeled Factorization Counts"
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
## Core Definitions
-/

/-- A monoid M is reduced if 1 is the only unit. -/
def Reduced (M : Type*) [Monoid M] : Prop :=
  ∀ u : M, IsUnit u → u = 1

/-- M is atomic if every non-unit can be written as a finite product of atoms. -/
def Atomic (M : Type*) [CommMonoid M] : Prop :=
  ∀ x : M, ¬ IsUnit x → ∃ (s : Multiset M), (∀ a ∈ s, Irreducible a) ∧ s.prod = x

/-- M is factorial if every non-unit has a unique factorization into atoms, up to order. -/
def Factorial (M : Type*) [CommMonoid M] : Prop :=
  ∀ x : M, ¬ IsUnit x → ∃! s : Multiset M, (∀ a ∈ s, Irreducible a) ∧ s.prod = x

/-- The set of atoms (irreducible elements) in M. -/
def Atoms (M : Type*) [Monoid M] : Set M := { x | Irreducible x }

/-- The set of labeled k-factorizations of m.
    These are ordered k-tuples (m₁, ..., mₖ) with m₁ · ... · mₖ = m. -/
def LabeledFactorizations {M : Type*} [CommMonoid M] (k : ℕ) (m : M) : Set (Fin k → M) :=
  { f | (Finset.univ.prod f) = m }

/-- The labeled k-factorization count F_k(m) is the cardinality of the set of
    labeled k-factorizations. -/
noncomputable def LabeledFactorizationCount {M : Type*} [CommMonoid M] (k : ℕ) (m : M) : ℕ :=
  Set.ncard (LabeledFactorizations k m)

/-- Two elements are coprime if no atom divides both. -/
def AreCoprime {M : Type*} [Monoid M] (x y : M) : Prop :=
  ∀ p ∈ Atoms M, p ∣ x → ¬ p ∣ y

/-- The support of m is the set of atoms dividing m. -/
def Support {M : Type*} [Monoid M] (m : M) : Set M :=
  { p ∈ Atoms M | p ∣ m }

/-!
## The Four Axioms (System B)

In a reduced atomic commutative monoid, the following four independent axioms
characterize factorial monoids:

- **PP-D**: Powers of atoms are distinct (p^a = p^b → a = b)
- **APD**: Atom-Power-Divisibility (if atom q divides p^k where p is an atom, then q = p)
- **CFI**: Coprime parts factor independently
- **CPL**: Coprime tuples come in every length

Key derived properties:
- **PP-P** (prime powers factorially closed) follows trivially from APD
- **Cancellativity** follows from Factorial (which follows from the four axioms)

This formulation (System B) uses four independent axioms rather than assuming
cancellativity and deriving PP-D and APD from it.
-/

/-- **Axiom PP-D**: Powers of atoms are distinct.
    For every atom p, the map e ↦ p^e is injective. -/
def PP_D (M : Type*) [Monoid M] : Prop :=
  ∀ p ∈ Atoms M, Function.Injective (fun (e : ℕ) => p ^ e)

/-- **Axiom APD**: Atom-Power-Divisibility.
    If an atom q divides p^k where p is also an atom, then q = p.
    This says that prime power submonoids are "pure" - no foreign atoms can divide in. -/
def APD (M : Type*) [Monoid M] : Prop :=
  ∀ p q : M, p ∈ Atoms M → q ∈ Atoms M → ∀ k : ℕ, q ∣ p ^ k → q = p

/-- **Derived Property PP-P**: Prime powers are factorially closed.
    For every atom p, if x * y is a power of p, then x and y are powers of p.
    This follows trivially from APD (see `APD_implies_PPP`). -/
def PP_P (M : Type*) [Monoid M] : Prop :=
  ∀ p ∈ Atoms M, ∀ x y : M, x * y ∈ Submonoid.powers p →
    x ∈ Submonoid.powers p ∧ y ∈ Submonoid.powers p

/-- Helper: The coordinatewise product of a k-factorization of x and a k-factorization of y
    is a k-factorization of x*y. -/
def labeledFactorizationMul {M : Type*} [CommMonoid M] {k : ℕ} {x y : M}
    (f : LabeledFactorizations k x) (g : LabeledFactorizations k y) :
    LabeledFactorizations k (x * y) :=
  ⟨f.1 * g.1, by
    convert congr_arg₂ ( · * · ) f.2 g.2 using 1
    simp [LabeledFactorizations]
    rw [Finset.prod_mul_distrib]⟩

/-- **Axiom CFI**: Coprime parts factor independently.
    If x, y are coprime, then the coordinatewise multiplication map
    from F_2(x) × F_2(y) to F_2(x * y) is a bijection. -/
def CFI (M : Type*) [CommMonoid M] : Prop :=
  ∀ x y : M, AreCoprime x y →
    Function.Bijective (fun p : LabeledFactorizations 2 x × LabeledFactorizations 2 y =>
                          labeledFactorizationMul p.1 p.2)

/-- **Axiom CPL**: Coprime tuples come in every length.
    For every r, there exist r pairwise coprime non-units. -/
def CPL (M : Type*) [Monoid M] : Prop :=
  ∀ r : ℕ, ∃ (L : List M), L.length = r ∧ (∀ x ∈ L, ¬ IsUnit x) ∧ L.Pairwise AreCoprime

/-!
## APD implies PP-P

This is the key lemma that makes System B work: APD trivially implies PP-P.
-/

/-- APD implies PP-P: If atoms can only divide "their own" prime powers,
    then prime power submonoids are factorially closed.

    Proof: Suppose x * y = p^e. If x is a unit, x = 1 ∈ ⟨p⟩ (reduced).
    If x is not a unit, let x = q₁ ⋯ qᵣ be an atomic factorization.
    Each qᵢ divides x, and x divides p^e, so qᵢ ∣ p^e.
    By APD, qᵢ = p for all i. Hence x = p^r ∈ ⟨p⟩. Similarly for y. -/
theorem APD_implies_PPP {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) : PP_P M := by
  intro p hp x y hxy
  obtain ⟨e, he⟩ := hxy
  -- Helper: if x is a non-unit and all atoms dividing x equal p, then x ∈ ⟨p⟩
  have h_in_powers : ∀ z : M, ¬IsUnit z → (∀ q ∈ Atoms M, q ∣ z → q = p) → z ∈ Submonoid.powers p := by
    intro z hz hq
    obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic z hz
    have h_all_p : ∀ a ∈ s, a = p := fun a ha =>
      hq a (hs_atoms a ha) (hs_prod ▸ Multiset.dvd_prod ha)
    rw [← hs_prod, Multiset.eq_replicate_of_mem h_all_p]
    exact ⟨Multiset.card s, by simp [Multiset.prod_replicate]⟩
  -- Show x ∈ ⟨p⟩
  have hx : x ∈ Submonoid.powers p := by
    by_cases hxu : IsUnit x
    · exact ⟨0, by simp [h_reduced x hxu]⟩
    · apply h_in_powers x hxu
      intro q hq hqx
      have hqpe : q ∣ p ^ e := dvd_trans hqx ⟨y, he⟩
      exact h_apd p q hp hq e hqpe
  -- Show y ∈ ⟨p⟩
  have hy : y ∈ Submonoid.powers p := by
    by_cases hyu : IsUnit y
    · exact ⟨0, by simp [h_reduced y hyu]⟩
    · apply h_in_powers y hyu
      intro q hq hqy
      have hqpe : q ∣ p ^ e := dvd_trans hqy ⟨x, by rw [mul_comm]; exact he⟩
      exact h_apd p q hp hq e hqpe
  exact ⟨hx, hy⟩

/-- Powers of an atom are coprime to elements with disjoint support (APD version).
    If p ∉ Support(x), then p^k and x are coprime.

    Proof: Suppose q is an atom dividing both p^k and x.
    By APD, q = p. But q divides x and p ∉ Support(x), contradiction. -/
lemma power_coprime_of_not_in_support_APD {M : Type*} [CommMonoid M]
    (_h_reduced : Reduced M) (h_apd : APD M)
    {p : M} (hp : p ∈ Atoms M) {x : M} (hx : p ∉ Support x) (k : ℕ) :
    AreCoprime (p ^ k) x := by
  intro q hq hqpk hqx
  simp [Support] at hx
  -- By APD, any atom dividing p^k equals p
  have hqp : q = p := h_apd p q hp hq k hqpk
  subst hqp
  exact hx hq hqx

/-- Distinct atoms don't divide each other's powers (APD version). -/
lemma distinct_atom_not_dvd_power_APD {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_apd : APD M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h_neq : p ≠ q) (k : ℕ) :
    ¬ q ∣ p ^ k := by
  intro h_div
  have h_coprime : AreCoprime p q := by
    intro r hr hrp hrq
    -- r divides p, so r = p (both atoms)
    obtain ⟨s, hs⟩ := hrp
    cases hp.isUnit_or_isUnit hs with
    | inl hr_unit => exact hr.not_isUnit hr_unit
    | inr hs_unit =>
      have : s = 1 := h_reduced s hs_unit
      subst this; simp at hs; subst hs
      -- Now r = p, and r divides q
      obtain ⟨t, ht⟩ := hrq
      cases hq.isUnit_or_isUnit ht with
      | inl hp_unit => exact hp.not_isUnit hp_unit
      | inr ht_unit =>
        have : t = 1 := h_reduced t ht_unit
        subst this; simp at ht
        exact h_neq ht.symm
  -- q divides p^k, and p,q are coprime (so p^k and q are coprime)
  have h_coprime_pow : AreCoprime (p ^ k) q := by
    have h_not_in_supp : p ∉ Support q := by
      simp only [Support, Set.mem_setOf_eq, not_and]
      intro _ h_dvd
      exact h_coprime p hp (dvd_refl p) h_dvd
    exact power_coprime_of_not_in_support_APD h_reduced h_apd hp h_not_in_supp k
  exact h_coprime_pow q hq h_div (dvd_refl q)

/-- Distinct atoms don't divide each other (immediate from APD with k=1). -/
lemma distinct_atoms_not_dvd {M : Type*} [CommMonoid M]
    (h_apd : APD M) {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h_neq : p ≠ q) :
    ¬ p ∣ q := by
  intro h
  have h1 : p ∣ q ^ 1 := by simp [h]
  have h2 : p = q := h_apd q p hq hp 1 h1
  exact h_neq h2

/-!
## APD-based Atoms Are Prime

This section proves that atoms are prime under APD + CFI, without requiring cancellativity.
This is the key result that makes System B work.
-/

/-- In a reduced monoid, atoms have only trivial factorizations. -/
lemma atom_eq_mul_iff {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p a b : M} (hp : p ∈ Atoms M) (h : p = a * b) :
    a = 1 ∧ b = p ∨ a = p ∧ b = 1 := by
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

/-- CFI splitting lemma: If x and y are coprime and u * v = x * y,
    then u and v can be split into factors of x and y. -/
lemma Coprime_Mul_Split {M : Type*} [CommMonoid M] (h_cfi : CFI M)
    (x y : M) (h_coprime : AreCoprime x y) (u v : M) (h_uv : u * v = x * y) :
    ∃ a b c d, a * b = x ∧ c * d = y ∧ a * c = u ∧ b * d = v := by
  have h_bij := h_cfi x y h_coprime
  -- The factorization (u, v) of x*y has a preimage in F_2(x) × F_2(y)
  have h_mem : (fun j : Fin 2 => if j = 0 then u else v) ∈ LabeledFactorizations 2 (x * y) := by
    unfold LabeledFactorizations
    simp only [Set.mem_setOf_eq, Fin.prod_univ_two, Fin.isValue]
    simp only [ite_true, Fin.reduceEq, ite_false]
    exact h_uv
  obtain ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, h_eq⟩ := h_bij.2 ⟨_, h_mem⟩
  -- a ∈ F_2(x), c ∈ F_2(y), and labeledFactorizationMul gives (u, v)
  use a 0, a 1, c 0, c 1
  simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two, Fin.isValue] at ha hc
  constructor
  · exact ha
  constructor
  · exact hc
  -- Extract the coordinatewise equality from h_eq
  have h_coord := congr_arg Subtype.val h_eq
  simp only [labeledFactorizationMul] at h_coord
  have h0 : a 0 * c 0 = u := by
    have := congr_fun h_coord 0
    simp only [Fin.isValue] at this
    simp only [ite_true] at this
    exact this
  have h1 : a 1 * c 1 = v := by
    have := congr_fun h_coord 1
    simp only [Fin.isValue, Fin.reduceEq, ite_false] at this
    exact this
  exact ⟨h0, h1⟩

/-- Atoms are prime (coprime case): If a and b are coprime and p | a*b, then p | a or p | b.
    This uses CFI directly and doesn't require cancellativity. -/
lemma atoms_are_prime_coprime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_cfi : CFI M)
    {p : M} (hp : p ∈ Atoms M)
    {a b : M} (h_coprime : AreCoprime a b) (h_dvd : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  obtain ⟨m, hm⟩ := h_dvd
  have h_prod : p * m = a * b := hm.symm
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, hab1, hab2⟩ := Coprime_Mul_Split h_cfi a b h_coprime p m h_prod
  have h_atom_factor := atom_eq_mul_iff h_reduced hp hab1.symm
  rcases h_atom_factor with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
  · right
    rw [hb1] at hb
    exact ⟨b₂, hb.symm⟩
  · left
    rw [ha1] at ha
    exact ⟨a₂, ha.symm⟩

/-- The product of a multiset equals q^(count of q) times the product of elements ≠ q. -/
lemma prod_eq_pow_count_mul_prod_filter_ne {M : Type*} [CommMonoid M]
    (s : Multiset M) (q : M) :
    s.prod = q ^ (s.count q) * (s.filter (· ≠ q)).prod := by
  induction' s using Multiset.induction_on with x s ih
  · simp
  · by_cases hx : x = q
    · -- x = q case: count increases by 1, filter unchanged
      rw [hx, Multiset.prod_cons, Multiset.count_cons_self, pow_succ']
      conv_rhs => rw [mul_assoc]
      congr 1
      have h_filter : (q ::ₘ s).filter (· ≠ q) = s.filter (· ≠ q) := by
        rw [Multiset.filter_cons_of_neg]
        simp
      rw [h_filter, ih]
    · -- x ≠ q case: count unchanged, x added to filter
      rw [Multiset.prod_cons]
      have hqx : q ≠ x := Ne.symm hx
      rw [Multiset.count_cons_of_ne hqx]
      have h_filter : (x ::ₘ s).filter (· ≠ q) = x ::ₘ s.filter (· ≠ q) := by
        rw [Multiset.filter_cons_of_pos]
        exact hx
      rw [h_filter, Multiset.prod_cons, ih]
      -- Goal: x * (q^k * t.prod) = q^k * (x * t.prod)
      rw [mul_comm x, mul_assoc, mul_comm x]

/-- If p is an atom and p | s.prod where s is a multiset of atoms, then p ∈ s.
    APD-based version that doesn't require cancellativity. -/
lemma atom_dvd_multiset_prod_APD {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_apd : APD M) (h_cfi : CFI M)
    (s : Multiset M) (hs : ∀ x ∈ s, x ∈ Atoms M)
    (p : M) (hp : p ∈ Atoms M) (h_dvd : p ∣ s.prod) :
    p ∈ s := by
  induction' s using Multiset.strongInductionOn with s ih generalizing p
  -- If s is empty, then s.prod = 1 and p ∤ 1 (contradiction)
  by_cases hs_empty : s = 0
  · simp_all [Atoms]
    exact hp.not_dvd_one h_dvd
  -- Otherwise, pick some q ∈ s
  obtain ⟨q, hq_mem⟩ := Multiset.exists_mem_of_ne_zero hs_empty
  -- Case split: p = q or p ≠ q
  by_cases h_eq : p = q
  · exact h_eq ▸ hq_mem
  · -- p ≠ q. We'll show p ∣ (s.filter (· ≠ q)).prod and use IH.
    let t := s.filter (· ≠ q)
    have ht_atoms : ∀ x ∈ t, x ∈ Atoms M := fun x hx => hs x (Multiset.mem_filter.mp hx).1
    have hq_atom : q ∈ Atoms M := hs q hq_mem
    -- p and q are distinct atoms, so p ∤ q^k by APD
    have h_p_not_dvd_qk : ¬ p ∣ q ^ (s.count q) := by
      intro h_bad
      -- APD says: p ∣ q^k → p = q
      have h_eq' : p = q := h_apd q p hq_atom hp (s.count q) h_bad
      exact h_eq h_eq'
    -- q^k and t.prod are coprime (q ∉ Support(t.prod))
    have h_t_smaller : t < s := lt_of_le_of_ne (Multiset.filter_le _ _) (by
      intro h_eq_filter
      have hq_in_t : q ∈ t := h_eq_filter ▸ hq_mem
      exact (Multiset.mem_filter.mp hq_in_t).2 rfl)
    have h_cop : AreCoprime (q ^ (s.count q)) t.prod := by
      apply power_coprime_of_not_in_support_APD h_reduced h_apd hq_atom
      simp only [Support, Set.mem_setOf_eq, not_and]
      intro _ h_q_dvd_t
      -- If q | t.prod, then by IH on t, q ∈ t. But t = s.filter (· ≠ q), so q ∉ t.
      have h_q_in_t := ih t h_t_smaller ht_atoms q hq_atom h_q_dvd_t
      exact (Multiset.mem_filter.mp h_q_in_t).2 rfl
    -- s.prod = q^k * t.prod
    have h_split : s.prod = q ^ (s.count q) * t.prod := prod_eq_pow_count_mul_prod_filter_ne s q
    rw [h_split] at h_dvd
    -- Apply atoms_are_prime_coprime: p | q^k ∨ p | t.prod
    have h_cases := atoms_are_prime_coprime h_reduced h_cfi hp h_cop h_dvd
    cases h_cases with
    | inl h_p_qk => exact absurd h_p_qk h_p_not_dvd_qk
    | inr h_p_t =>
      have h_p_in_t := ih t h_t_smaller ht_atoms p hp h_p_t
      exact Multiset.mem_of_mem_filter h_p_in_t

/-- **Atoms are prime (APD version)**: Under APD and CFI, if p | a*b then p | a or p | b.
    This is the System B version that doesn't require cancellativity. -/
theorem atoms_are_prime_APD {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p hp a b h_dvd
  -- Handle unit cases
  by_cases ha_unit : IsUnit a
  · right
    obtain ⟨u, rfl⟩ := ha_unit
    have hu_eq_1 := h_reduced u u.isUnit
    simp [hu_eq_1] at h_dvd ⊢
    exact h_dvd
  · by_cases hb_unit : IsUnit b
    · left
      obtain ⟨u, rfl⟩ := hb_unit
      have hu_eq_1 := h_reduced u u.isUnit
      simp [hu_eq_1] at h_dvd ⊢
      exact h_dvd
    · -- Neither a nor b is a unit; get atomic factorizations
      obtain ⟨s_a, hs_a_atoms, hs_a_prod⟩ := h_atomic a ha_unit
      obtain ⟨s_b, hs_b_atoms, hs_b_prod⟩ := h_atomic b hb_unit
      -- a * b = (s_a + s_b).prod
      have h_ab_prod : a * b = (s_a + s_b).prod := by
        rw [← hs_a_prod, ← hs_b_prod, Multiset.prod_add]
      -- p | (s_a + s_b).prod
      have h_dvd' : p ∣ (s_a + s_b).prod := h_ab_prod ▸ h_dvd
      -- By atom_dvd_multiset_prod_APD, p ∈ s_a + s_b
      have h_in : p ∈ s_a + s_b := atom_dvd_multiset_prod_APD h_reduced h_apd h_cfi
        (s_a + s_b) (fun x hx => by
          cases Multiset.mem_add.mp hx with
          | inl h => exact hs_a_atoms x h
          | inr h => exact hs_b_atoms x h)
        p hp h_dvd'
      -- p ∈ s_a or p ∈ s_b
      cases Multiset.mem_add.mp h_in with
      | inl h_in_a =>
        left
        rw [← hs_a_prod]
        exact Multiset.dvd_prod h_in_a
      | inr h_in_b =>
        right
        rw [← hs_b_prod]
        exact Multiset.dvd_prod h_in_b

/-!
## Helper Definitions
-/

/-- A family of pairs (x_i, y_i) is blockwise disjoint if the supports of distinct blocks
    are disjoint. -/
def BlockwiseDisjoint {M : Type*} [Monoid M] {n : ℕ} (x y : Fin n → M) : Prop :=
  ∀ i j, i ≠ j → Disjoint (Support (x i) ∪ Support (y i)) (Support (x j) ∪ Support (y j))

/-- The p-adic valuation v_p(m) = max{e ≥ 0 : p^e | m} -/
def PValuation {M : Type*} [CommMonoid M] (p : M) (m : M) : ℕ :=
  sSup {e | p ^ e ∣ m}

/-!
## Cancellativity implies PP-D

In a reduced atomic cancellative monoid, powers of atoms are automatically distinct.
This shows that PP-D is a consequence of cancellativity.
-/

/-- In a reduced commutative monoid, a positive power of an atom is not a unit. -/
lemma pow_atom_not_unit {M : Type*} [CommMonoid M] (_h_reduced : Reduced M)
    {p : M} (hp : p ∈ Atoms M) {n : ℕ} (hn : n ≥ 1) : ¬ IsUnit (p ^ n) := by
  intro h_unit
  have h_p_unit : IsUnit p := by
    cases n with
    | zero => omega
    | succ k =>
      rw [pow_succ] at h_unit
      exact isUnit_of_mul_isUnit_right h_unit
  exact hp.not_isUnit h_p_unit

/-- Cancellativity implies PP-D: In a reduced cancellative monoid, powers of atoms are distinct.

    Proof: Suppose p^a = p^b with a < b. Then p^a · 1 = p^a = p^b = p^a · p^{b-a}.
    By left cancellation, 1 = p^{b-a}. Since b > a, p^{b-a} is a positive power of an atom,
    hence not a unit in a reduced monoid. But 1 is a unit, contradiction. So a = b. -/
theorem cancellativity_implies_PP_D {M : Type*} [CancelCommMonoid M]
    (h_reduced : Reduced M) : PP_D M := by
  intro p hp a b hab
  simp only at hab
  by_contra h_neq
  have h_lt : a < b ∨ b < a := Nat.lt_or_gt_of_ne h_neq
  rcases h_lt with h_lt | h_lt
  · -- Case a < b
    have hd : b - a ≥ 1 := by omega
    have hd_eq : b = a + (b - a) := by omega
    have h_expand : p ^ a = p ^ a * p ^ (b - a) := by
      conv_lhs => rw [hab, hd_eq, pow_add]
    have h_one : (1 : M) = p ^ (b - a) := by
      have h1 : p ^ a * 1 = p ^ a * p ^ (b - a) := by rw [mul_one]; exact h_expand
      exact mul_left_cancel h1
    exact absurd (h_one ▸ isUnit_one) (pow_atom_not_unit h_reduced hp hd)
  · -- Case b < a (symmetric)
    have hd : a - b ≥ 1 := by omega
    have hd_eq : a = b + (a - b) := by omega
    have h_expand : p ^ b = p ^ b * p ^ (a - b) := by
      conv_lhs => rw [hab.symm, hd_eq, pow_add]
    have h_one : (1 : M) = p ^ (a - b) := by
      have h1 : p ^ b * 1 = p ^ b * p ^ (a - b) := by rw [mul_one]; exact h_expand
      exact mul_left_cancel h1
    exact absurd (h_one ▸ isUnit_one) (pow_atom_not_unit h_reduced hp hd)

/-- In a reduced atomic commutative monoid, Factorial implies left cancellation. -/
lemma Factorial_implies_mul_left_cancel {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_factorial : Factorial M)
    {a b c : M} (h : a * b = a * c) : b = c := by
  -- If a is a unit, then a = 1 (reduced), so b = c trivially
  by_cases ha : IsUnit a
  · rw [h_reduced a ha, one_mul, one_mul] at h; exact h
  -- Get factorization of a
  obtain ⟨sa, hsa_atoms, hsa_prod⟩ := h_atomic a ha
  -- Handle cases for b and c
  by_cases hb : IsUnit b <;> by_cases hc : IsUnit c
  · -- Both b and c are units (= 1)
    rw [h_reduced b hb, h_reduced c hc]
  · -- b is a unit, c is not: a * 1 = a * c implies c's atoms are empty, contradiction
    rw [h_reduced b hb, mul_one] at h
    obtain ⟨sc, hsc_atoms, hsc_prod⟩ := h_atomic c hc
    -- Factorizations: a has sa, a*c has sa + sc
    have hac_not_unit : ¬IsUnit (a * c) := fun h' => hc (isUnit_of_mul_isUnit_right h')
    have ha_fact : sa.prod = a := hsa_prod
    have hac_fact : (sa + sc).prod = a * c := by rw [Multiset.prod_add, hsa_prod, hsc_prod]
    -- By unique factorization of a = a * c
    obtain ⟨s_uniq, ⟨hs_atoms, hs_prod⟩, h_unique⟩ := h_factorial a ha
    have h1 : sa = s_uniq := h_unique sa ⟨hsa_atoms, hsa_prod⟩
    have h2 : sa + sc = s_uniq := h_unique (sa + sc) ⟨fun p hp =>
      (Multiset.mem_add.mp hp).elim (hsa_atoms p) (hsc_atoms p), by rw [hac_fact, ← h]⟩
    -- sa = sa + sc implies sc = 0, but sc is nonempty since c is not a unit
    have : sc = 0 := by simpa [h1] using h2.symm
    simp [this] at hsc_prod
    exact absurd (hsc_prod ▸ isUnit_one) hc
  · -- b is not a unit, c is a unit: symmetric case
    rw [h_reduced c hc, mul_one] at h
    obtain ⟨sb, hsb_atoms, hsb_prod⟩ := h_atomic b hb
    have hab_not_unit : ¬IsUnit (a * b) := fun h' => hb (isUnit_of_mul_isUnit_right h')
    have hab_fact : (sa + sb).prod = a * b := by rw [Multiset.prod_add, hsa_prod, hsb_prod]
    obtain ⟨s_uniq, ⟨hs_atoms, hs_prod⟩, h_unique⟩ := h_factorial a ha
    have h1 : sa = s_uniq := h_unique sa ⟨hsa_atoms, hsa_prod⟩
    have h2 : sa + sb = s_uniq := h_unique (sa + sb) ⟨fun p hp =>
      (Multiset.mem_add.mp hp).elim (hsa_atoms p) (hsb_atoms p), by rw [hab_fact, h]⟩
    have : sb = 0 := by simpa [h1] using h2.symm
    simp [this] at hsb_prod
    exact absurd (hsb_prod ▸ isUnit_one) hb
  · -- Both b and c are non-units: use unique factorization
    have hab_not_unit : ¬IsUnit (a * b) := fun h' => hb (isUnit_of_mul_isUnit_right h')
    obtain ⟨sb, hsb_atoms, hsb_prod⟩ := h_atomic b hb
    obtain ⟨sc, hsc_atoms, hsc_prod⟩ := h_atomic c hc
    have hab_fact : (sa + sb).prod = a * b := by rw [Multiset.prod_add, hsa_prod, hsb_prod]
    have hac_fact : (sa + sc).prod = a * c := by rw [Multiset.prod_add, hsa_prod, hsc_prod]
    have h_eq_multiset : sa + sb = sa + sc := by
      have hsab_atoms : ∀ p ∈ sa + sb, Irreducible p := fun p hp =>
        (Multiset.mem_add.mp hp).elim (hsa_atoms p) (hsb_atoms p)
      have hsac_atoms : ∀ p ∈ sa + sc, Irreducible p := fun p hp =>
        (Multiset.mem_add.mp hp).elim (hsa_atoms p) (hsc_atoms p)
      obtain ⟨s_uniq, ⟨_, _⟩, h_unique⟩ := h_factorial (a * b) hab_not_unit
      have h1 : sa + sb = s_uniq := h_unique (sa + sb) ⟨hsab_atoms, hab_fact⟩
      have h2 : sa + sc = s_uniq := h_unique (sa + sc) ⟨hsac_atoms, by rw [hac_fact, ← h]⟩
      rw [h1, ← h2]
    rw [← hsb_prod, ← hsc_prod, Multiset.add_right_inj.mp h_eq_multiset]

/-- In a reduced atomic commutative monoid, Factorial implies right cancellation. -/
lemma Factorial_implies_mul_right_cancel {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_factorial : Factorial M)
    {a b c : M} (h : b * a = c * a) : b = c := by
  rw [mul_comm b a, mul_comm c a] at h
  exact Factorial_implies_mul_left_cancel h_reduced h_atomic h_factorial h

end