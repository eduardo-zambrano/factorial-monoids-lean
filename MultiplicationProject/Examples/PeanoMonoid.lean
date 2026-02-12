/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Example 6: The Peano Monoid (Failure of CPL only)

This file formalizes the Peano monoid example from Section 10 of the paper,
demonstrating that CPL is independent of the other three axioms.

The Peano monoid is (ℕ+, ⋆, 1) where x ⋆ y := x + y - 1.

## Main Results

- `PeanoNat`: A wrapper type for ℕ+ with the Peano multiplication
- `peano_reduced`: The Peano monoid is reduced
- `peano_atomic`: The Peano monoid is atomic (unique atom: 2)
- `peano_APD`: The Peano monoid satisfies APD
- `peano_PPD`: The Peano monoid satisfies PP-D
- `peano_CFI`: The Peano monoid satisfies CFI (vacuously)
- `peano_not_CPL`: The Peano monoid does NOT satisfy CPL
-/

import MultiplicationProject.Basic

open scoped Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## The Peano Monoid Structure

We define a new type `PeanoNat` that wraps ℕ+ with the Peano operation
x ⋆ y := x + y - 1 and identity 1.
-/

/-- The Peano monoid type: ℕ+ with multiplication x ⋆ y := x + y - 1. -/
structure PeanoNat where
  val : ℕ
  pos : 0 < val
  deriving DecidableEq

namespace PeanoNat

/-- The underlying natural number. -/
instance : CoeOut PeanoNat ℕ := ⟨fun x => x.val⟩

/-- Extensionality for PeanoNat. -/
@[ext]
lemma ext {x y : PeanoNat} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp at h; simp [h]

/-- Construct from ℕ+. -/
def ofPNat (n : ℕ+) : PeanoNat := ⟨n.val, n.pos⟩

/-- Convert to ℕ+. -/
def toPNat (n : PeanoNat) : ℕ+ := ⟨n.val, n.pos⟩

/-- The Peano multiplication: x ⋆ y := x + y - 1 -/
protected def mul (x y : PeanoNat) : PeanoNat where
  val := x.val + y.val - 1
  pos := by have hx := x.pos; have hy := y.pos; omega

/-- The identity element is 1. -/
protected def one : PeanoNat where
  val := 1
  pos := by omega

instance : One PeanoNat := ⟨PeanoNat.one⟩
instance : Mul PeanoNat := ⟨PeanoNat.mul⟩

@[simp]
lemma mul_val (x y : PeanoNat) : (x * y).val = x.val + y.val - 1 := rfl

@[simp]
lemma one_val : (1 : PeanoNat).val = 1 := rfl

/-- The Peano monoid is a commutative monoid. -/
instance : CommMonoid PeanoNat where
  mul := (· * ·)
  mul_assoc := by
    intros a b c
    ext
    simp only [mul_val]
    have ha := a.pos
    have hb := b.pos
    have hc := c.pos
    omega
  one := 1
  one_mul := by
    intro a
    ext
    simp only [mul_val, one_val]
    have ha := a.pos
    omega
  mul_one := by
    intro a
    ext
    simp only [mul_val, one_val]
    have ha := a.pos
    omega
  mul_comm := by
    intros a b
    ext
    simp only [mul_val]
    ring

/-!
## Basic Properties
-/

/-- The constant 2 in PeanoNat. -/
def two : PeanoNat where
  val := 2
  pos := by omega

@[simp]
lemma two_val : two.val = 2 := rfl

/-- Powers in the Peano monoid: 2^e = e + 1. -/
lemma pow_two (e : ℕ) : two ^ e = ⟨e + 1, by omega⟩ := by
  induction e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    simp only [mul_val, two_val]
    omega

/-- Every n ≥ 2 is a power of 2: n = 2^(n-1). -/
lemma eq_pow_two (n : PeanoNat) (hn : n.val ≥ 2) : n = two ^ (n.val - 1) := by
  rw [pow_two]
  ext
  simp only
  omega

/-!
## Divisibility
-/

/-- Divisibility in the Peano monoid: x | y iff x ≤ y. -/
lemma dvd_iff (x y : PeanoNat) : (∃ z : PeanoNat, y = x * z) ↔ x.val ≤ y.val := by
  constructor
  · rintro ⟨z, hz⟩
    have heq : y.val = x.val + z.val - 1 := by simp [hz]
    have hz_pos := z.pos
    omega
  · intro hle
    have hy := y.pos
    have hx := x.pos
    refine ⟨⟨y.val - x.val + 1, by omega⟩, ?_⟩
    ext
    simp only [mul_val]
    omega

/-- 2 divides every n ≥ 2. -/
lemma two_dvd (n : PeanoNat) (hn : n.val ≥ 2) : ∃ z : PeanoNat, n = two * z := by
  rw [dvd_iff]
  exact hn

/-- In PeanoNat, x * y = 1 implies x = 1 and y = 1. -/
lemma mul_eq_one_iff (x y : PeanoNat) : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro h
    have hval : x.val + y.val - 1 = 1 := by
      have := congr_arg val h
      simp only [mul_val, one_val] at this
      exact this
    have hx := x.pos
    have hy := y.pos
    have hxval : x.val = 1 := by omega
    have hyval : y.val = 1 := by omega
    constructor
    · ext; simp only [one_val]; exact hxval
    · ext; simp only [one_val]; exact hyval
  · intro ⟨hx, hy⟩
    rw [hx, hy]
    simp only [mul_one]

/-!
## Units and Atoms
-/

/-- Only 1 is a unit in the Peano monoid. -/
lemma isUnit_iff (x : PeanoNat) : IsUnit x ↔ x = 1 := by
  constructor
  · intro ⟨u, hu⟩
    have h := u.val_inv
    -- h : u.val * u.inv = 1 which means u.val.val + u.inv.val - 1 = 1
    have hval : u.val.val + u.inv.val - 1 = 1 := by
      have := congr_arg val h
      simp only [mul_val, one_val] at this
      exact this
    have hu_pos := u.val.pos
    have huinv_pos := u.inv.pos
    have hxval : u.val.val = 1 := by omega
    ext
    simp only [one_val]
    rw [← hu]
    exact hxval
  · intro hx
    rw [hx]
    exact isUnit_one

/-- The Peano monoid is reduced (only unit is 1). -/
theorem peano_reduced : Reduced PeanoNat := by
  intro x hx
  exact (isUnit_iff x).mp hx

/-- 2 is irreducible. -/
lemma two_irreducible : Irreducible two := by
  constructor
  · intro h
    have heq := (isUnit_iff two).mp h
    have h2 : two.val = 2 := rfl
    rw [heq] at h2
    simp only [one_val] at h2
    exact absurd h2 (by decide)
  · intros a b hab
    have hval : 2 = a.val + b.val - 1 := by
      have := congr_arg val hab
      simp only [mul_val, two_val] at this
      exact this
    have ha := a.pos
    have hb := b.pos
    have hab_sum : a.val + b.val = 3 := by omega
    have h_cases : (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 1) := by omega
    cases h_cases with
    | inl h => left; rw [isUnit_iff]; ext; simp only [one_val]; exact h.1
    | inr h => right; rw [isUnit_iff]; ext; simp only [one_val]; exact h.2

/-- 2 is the unique atom. -/
lemma atoms_eq : Atoms PeanoNat = {two} := by
  ext x
  simp only [Atoms, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hx_ne_one : x ≠ 1 := by
      intro h
      rw [h] at hx
      exact hx.not_isUnit isUnit_one
    have hx_pos := x.pos
    have hx_ge_2 : x.val ≥ 2 := by
      by_contra h
      push_neg at h
      apply hx_ne_one
      ext; simp only [one_val]; omega
    by_contra hx_ne_2
    have hx_gt_2 : x.val > 2 := by
      have hxval_ne : x.val ≠ 2 := by
        intro h
        apply hx_ne_2
        ext; simp only [two_val]; exact h
      omega
    have hfact : x = two * ⟨x.val - 1, by omega⟩ := by
      ext; simp only [mul_val, two_val]; omega
    have := hx.isUnit_or_isUnit hfact
    cases this with
    | inl h =>
      have heq := (isUnit_iff two).mp h
      have h2 : two.val = 2 := rfl
      rw [heq] at h2
      simp only [one_val] at h2
      exact absurd h2 (by decide)
    | inr h =>
      have heq := (isUnit_iff ⟨x.val - 1, by omega⟩).mp h
      have hv : (⟨x.val - 1, by omega⟩ : PeanoNat).val = x.val - 1 := rfl
      rw [heq] at hv
      simp only [one_val] at hv
      omega
  · intro hx
    rw [hx]
    exact two_irreducible

/-- The Peano monoid is atomic. -/
theorem peano_atomic : Atomic PeanoNat := by
  intro x hx
  have hx_ne_1 : x ≠ 1 := by intro h; rw [h] at hx; exact hx isUnit_one
  have hx_pos := x.pos
  have hx_ge_2 : x.val ≥ 2 := by
    by_contra h; push_neg at h
    apply hx_ne_1
    ext; simp only [one_val]; omega
  use Multiset.replicate (x.val - 1) two
  constructor
  · intro a ha
    simp only [Multiset.mem_replicate] at ha
    rw [ha.2]
    exact two_irreducible
  · rw [Multiset.prod_replicate, pow_two]
    ext; simp only; omega

/-!
## The Four Axioms
-/

/-- APD holds (trivially: unique atom). -/
theorem peano_APD : APD PeanoNat := by
  intro p q hp hq k hdvd
  rw [atoms_eq] at hp hq
  simp only [Set.mem_singleton_iff] at hp hq
  rw [hp, hq]

/-- UAB holds vacuously: with only one atom, p^k = q^m implies p = q = 2. -/
theorem peano_UAB : UAB PeanoNat := by
  intro p q hp hq k m _ _ _
  rw [atoms_eq] at hp hq
  simp only [Set.mem_singleton_iff] at hp hq
  rw [hp, hq]

/-- PP-D holds: 2^e = e + 1 is injective. -/
theorem peano_PPD : PP_D PeanoNat := by
  intro p hp a b hab
  rw [atoms_eq] at hp
  simp only [Set.mem_singleton_iff] at hp
  subst hp
  simp only [pow_two] at hab
  have := congr_arg PeanoNat.val hab
  simp only at this
  omega

/-- The unique element of LabeledFactorizations 2 1. -/
def constOne : LabeledFactorizations 2 (1 : PeanoNat) :=
  ⟨fun _ => 1, by simp [LabeledFactorizations]⟩

/-- Any element of LabeledFactorizations 2 1 must be constOne. -/
lemma labeledFact_one_unique (f : LabeledFactorizations 2 (1 : PeanoNat)) : f = constOne := by
  apply Subtype.ext
  funext i
  simp only [constOne]
  have hprod : Finset.univ.prod f.1 = 1 := f.2
  simp only [Fin.prod_univ_two] at hprod
  have ⟨h0, h1⟩ := mul_eq_one_iff (f.1 0) (f.1 1) |>.mp hprod
  fin_cases i
  · exact h0
  · exact h1

/-- CFI holds vacuously: the only coprime pairs involve 1.
    The proof is vacuous: if x ≠ 1 and y ≠ 1, then both are ≥ 2,
    so 2 | x and 2 | y, contradicting coprimality. -/
theorem peano_CFI : CFI PeanoNat := by
  intro x y hcoprime
  -- If x ≠ 1 and y ≠ 1, they share the atom 2, so cannot be coprime
  by_cases hx : x = 1
  · -- x = 1: The map is essentially projection onto second component
    subst hx
    -- Goal: Function.Bijective on LabeledFactorizations 2 (1 * y)
    constructor
    · -- Injective
      intro ⟨f1, g1⟩ ⟨f2, g2⟩ h
      simp only [labeledFactorizationMul, Subtype.mk.injEq] at h
      have hf1_eq := labeledFact_one_unique f1
      have hf2_eq := labeledFact_one_unique f2
      -- Since f1 = f2 = constOne, g1 and g2 must agree
      have hg_eq : g1 = g2 := by
        apply Subtype.ext
        funext i
        have hi := congr_fun h i
        have hf1i : f1.1 i = 1 := congr_fun (congrArg Subtype.val hf1_eq) i
        have hf2i : f2.1 i = 1 := congr_fun (congrArg Subtype.val hf2_eq) i
        calc g1.1 i = 1 * g1.1 i := (one_mul _).symm
          _ = f1.1 i * g1.1 i := by rw [hf1i]
          _ = f2.1 i * g2.1 i := hi
          _ = 1 * g2.1 i := by rw [hf2i]
          _ = g2.1 i := one_mul _
      simp only [Prod.mk.injEq]
      exact ⟨hf1_eq.trans hf2_eq.symm, hg_eq⟩
    · -- Surjective
      intro g
      -- g : LabeledFactorizations 2 (1 * y), need to find preimage
      have hgy : Finset.univ.prod g.1 = y := by
        have h := g.2
        simp only [one_mul] at h
        exact h
      refine ⟨(constOne, ⟨g.1, hgy⟩), ?_⟩
      apply Subtype.ext
      funext i
      simp only [labeledFactorizationMul, Pi.mul_apply, constOne, one_mul]
  · by_cases hy : y = 1
    · -- y = 1: symmetric case
      subst hy
      constructor
      · -- Injective
        intro ⟨f1, g1⟩ ⟨f2, g2⟩ h
        simp only [labeledFactorizationMul, Subtype.mk.injEq] at h
        have hg1_eq := labeledFact_one_unique g1
        have hg2_eq := labeledFact_one_unique g2
        have hf_eq : f1 = f2 := by
          apply Subtype.ext
          funext i
          have hi := congr_fun h i
          have hg1i : g1.1 i = 1 := congr_fun (congrArg Subtype.val hg1_eq) i
          have hg2i : g2.1 i = 1 := congr_fun (congrArg Subtype.val hg2_eq) i
          calc f1.1 i = f1.1 i * 1 := (mul_one _).symm
            _ = f1.1 i * g1.1 i := by rw [hg1i]
            _ = f2.1 i * g2.1 i := hi
            _ = f2.1 i * 1 := by rw [hg2i]
            _ = f2.1 i := mul_one _
        simp only [Prod.mk.injEq]
        exact ⟨hf_eq, hg1_eq.trans hg2_eq.symm⟩
      · -- Surjective
        intro f
        -- f : LabeledFactorizations 2 (x * 1), need to find preimage
        have hfx : Finset.univ.prod f.1 = x := by
          have h := f.2
          simp only [mul_one] at h
          exact h
        refine ⟨(⟨f.1, hfx⟩, constOne), ?_⟩
        apply Subtype.ext
        funext i
        simp only [labeledFactorizationMul, Pi.mul_apply, constOne, mul_one]
    · -- x ≠ 1 and y ≠ 1: contradiction
      exfalso
      have hx_pos := x.pos
      have hy_pos := y.pos
      have hx_ge_2 : x.val ≥ 2 := by
        by_contra h; push_neg at h
        apply hx; ext; simp only [one_val]; omega
      have hy_ge_2 : y.val ≥ 2 := by
        by_contra h; push_neg at h
        apply hy; ext; simp only [one_val]; omega
      have h2_dvd_x : ∃ z, x = two * z := two_dvd x hx_ge_2
      have h2_dvd_y : ∃ z, y = two * z := two_dvd y hy_ge_2
      have h2_atom : two ∈ Atoms PeanoNat := by rw [atoms_eq]; exact Set.mem_singleton two
      -- AreCoprime says: ∀ p ∈ Atoms M, p ∣ x → ¬ p ∣ y
      -- So hcoprime two h2_atom h2_dvd_x gives ¬ (two ∣ y)
      -- And h2_dvd_y gives two ∣ y, so we have False
      exact hcoprime two h2_atom h2_dvd_x h2_dvd_y

/-- CPL fails: every two non-units share atom 2. -/
theorem peano_not_CPL : ¬ CPL PeanoNat := by
  intro hcpl
  obtain ⟨L, hL_len, hL_nonunit, hL_coprime⟩ := hcpl 2
  have hL_len2 : L.length = 2 := hL_len
  obtain ⟨m₁, m₂, hL_eq⟩ : ∃ m₁ m₂, L = [m₁, m₂] := by
    match L with
    | [] => simp at hL_len2
    | [_] => simp at hL_len2
    | [a, b] => exact ⟨a, b, rfl⟩
    | _ :: _ :: _ :: _ => simp at hL_len2
  rw [hL_eq] at hL_nonunit hL_coprime
  have hm1_nonunit : ¬IsUnit m₁ := hL_nonunit m₁ (by simp)
  have hm2_nonunit : ¬IsUnit m₂ := hL_nonunit m₂ (by simp)
  have hm1_pos := m₁.pos
  have hm2_pos := m₂.pos
  have hm1_ge_2 : m₁.val ≥ 2 := by
    by_contra h; push_neg at h
    apply hm1_nonunit; rw [isUnit_iff]; ext; simp only [one_val]; omega
  have hm2_ge_2 : m₂.val ≥ 2 := by
    by_contra h; push_neg at h
    apply hm2_nonunit; rw [isUnit_iff]; ext; simp only [one_val]; omega
  have hcoprime : AreCoprime m₁ m₂ := by
    have := List.pairwise_cons.mp hL_coprime
    exact this.1 m₂ (by simp)
  have h2_dvd_m1 : ∃ z, m₁ = two * z := two_dvd m₁ hm1_ge_2
  have h2_dvd_m2 : ∃ z, m₂ = two * z := two_dvd m₂ hm2_ge_2
  have h2_atom : two ∈ Atoms PeanoNat := by rw [atoms_eq]; exact Set.mem_singleton two
  -- AreCoprime says: ∀ p ∈ Atoms M, p ∣ x → ¬ p ∣ y
  -- So hcoprime two h2_atom h2_dvd_m1 gives ¬ (two ∣ m₂)
  -- And h2_dvd_m2 gives two ∣ m₂, so we have False
  exact hcoprime two h2_atom h2_dvd_m1 h2_dvd_m2

end PeanoNat

end
