/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Example 10.2: The UAB Failure Monoid (Failure of UAB only)

This file formalizes Example 10.2 from Section 10 of the paper.

**Construction:** The free commutative monoid on countably many atoms p₁, p₂, p₃, ...
with the single relation p₁² = p₂². This identifies two distinct prime-power towers at height 2.

## Main Results

- `UABFailMonoid`: The monoid with p₁² = p₂²
- `uabfail_reduced`: The monoid is reduced
- `uabfail_atomic`: The monoid is atomic
- `uabfail_PPD`: PP-D holds (powers within each tower are distinct)
- `uabfail_not_UAB`: UAB fails (p₁² = p₂² with p₁ ≠ p₂)
- `uabfail_CFI`: CFI holds (coprime factorizations combine independently)
- `uabfail_CPL`: CPL holds (p₃, p₄, ... give arbitrarily long coprime tuples)
-/

import MultiplicationProject.Basic
import Mathlib.Data.Finsupp.Basic

open scoped Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## The UAB Failure Monoid Structure

Elements are represented by:
- exp_p1 : ℕ := exponent of p₁ (before identification)
- exp_p2 : ℕ := exponent of p₂ (before identification)
- others : ℕ →₀ ℕ := exponents of p₃, p₄, ... (index n corresponds to p_{n+3})

The key relation p₁² = p₂² identifies elements that differ only by swapping
p₁² ↔ p₂² chunks. More precisely: x ~ y if x.others = y.others and
the (exp_p1, exp_p2) pairs agree modulo the relation.

For p₁² = p₂², we identify (a, b) ≡ (a', b') if:
- a + b = a' + b' (total power same)
- a % 2 = a' % 2 (same parity of p₁ exponent)
-/

/-- An element of the free monoid before identification.
    Exponents for p₁, p₂, and others (p₃, p₄, ...). -/
structure PreUABMonoid where
  exp_p1 : ℕ
  exp_p2 : ℕ
  others : ℕ →₀ ℕ
  deriving DecidableEq

namespace PreUABMonoid

/-- Extensionality. -/
@[ext]
lemma ext {x y : PreUABMonoid} (h1 : x.exp_p1 = y.exp_p1)
    (h2 : x.exp_p2 = y.exp_p2) (h3 : x.others = y.others) : x = y := by
  cases x; cases y; simp at h1 h2 h3; simp [h1, h2, h3]

/-- The identity element. -/
protected def one : PreUABMonoid := ⟨0, 0, 0⟩

/-- Multiplication: add exponents. -/
protected def mul (x y : PreUABMonoid) : PreUABMonoid :=
  ⟨x.exp_p1 + y.exp_p1, x.exp_p2 + y.exp_p2, x.others + y.others⟩

instance : One PreUABMonoid := ⟨PreUABMonoid.one⟩
instance : Mul PreUABMonoid := ⟨PreUABMonoid.mul⟩

@[simp] lemma one_exp_p1 : (1 : PreUABMonoid).exp_p1 = 0 := rfl
@[simp] lemma one_exp_p2 : (1 : PreUABMonoid).exp_p2 = 0 := rfl
@[simp] lemma one_others : (1 : PreUABMonoid).others = 0 := rfl

@[simp] lemma mul_exp_p1 (x y : PreUABMonoid) : (x * y).exp_p1 = x.exp_p1 + y.exp_p1 := rfl
@[simp] lemma mul_exp_p2 (x y : PreUABMonoid) : (x * y).exp_p2 = x.exp_p2 + y.exp_p2 := rfl
@[simp] lemma mul_others (x y : PreUABMonoid) : (x * y).others = x.others + y.others := rfl

instance : CommMonoid PreUABMonoid where
  mul := (· * ·)
  mul_assoc := by intros; ext <;> simp [add_assoc]
  one := 1
  one_mul := by intro; ext <;> simp
  mul_one := by intro; ext <;> simp
  mul_comm := by intros; ext <;> simp [add_comm]

/-- The atom p₁. -/
def p1 : PreUABMonoid := ⟨1, 0, 0⟩

/-- The atom p₂. -/
def p2 : PreUABMonoid := ⟨0, 1, 0⟩

/-- The atom p_{n+3}. -/
def pn (n : ℕ) : PreUABMonoid := ⟨0, 0, Finsupp.single n 1⟩

@[simp] lemma p1_exp_p1 : p1.exp_p1 = 1 := rfl
@[simp] lemma p1_exp_p2 : p1.exp_p2 = 0 := rfl
@[simp] lemma p1_others : p1.others = 0 := rfl

@[simp] lemma p2_exp_p1 : p2.exp_p1 = 0 := rfl
@[simp] lemma p2_exp_p2 : p2.exp_p2 = 1 := rfl
@[simp] lemma p2_others : p2.others = 0 := rfl

@[simp] lemma pn_exp_p1 (n : ℕ) : (pn n).exp_p1 = 0 := rfl
@[simp] lemma pn_exp_p2 (n : ℕ) : (pn n).exp_p2 = 0 := rfl
@[simp] lemma pn_others (n : ℕ) : (pn n).others = Finsupp.single n 1 := rfl

end PreUABMonoid

/-- The equivalence relation: x ~ y if they differ only by swapping p₁² ↔ p₂² chunks.
    More precisely: x ~ y if x.others = y.others and there exists k such that
    x.exp_p1 = y.exp_p1 + 2k and x.exp_p2 + 2k = y.exp_p2 (or vice versa, with appropriate signs). -/
def uabEquiv : PreUABMonoid → PreUABMonoid → Prop :=
  fun x y => x.others = y.others ∧
             (x.exp_p1 + x.exp_p2 = y.exp_p1 + y.exp_p2) ∧  -- total p₁+p₂ power same
             (x.exp_p1 % 2 = y.exp_p1 % 2)  -- same parity of p₁ exponent

@[simp] lemma uabEquiv_def (x y : PreUABMonoid) : uabEquiv x y ↔
    (x.others = y.others ∧ x.exp_p1 + x.exp_p2 = y.exp_p1 + y.exp_p2 ∧ x.exp_p1 % 2 = y.exp_p1 % 2) :=
  Iff.rfl

/-- uabEquiv is an equivalence relation. -/
lemma uabEquiv_equiv : Equivalence uabEquiv := by
  constructor
  · intro x; simp [uabEquiv]
  · intro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
  · intro x y z ⟨hxy1, hxy2, hxy3⟩ ⟨hyz1, hyz2, hyz3⟩
    exact ⟨hxy1.trans hyz1, hxy2.trans hyz2, hxy3.trans hyz3⟩

/-- uabEquiv is compatible with multiplication. -/
lemma uabEquiv_mul : ∀ x₁ x₂ y₁ y₂ : PreUABMonoid,
    uabEquiv x₁ y₁ → uabEquiv x₂ y₂ → uabEquiv (x₁ * x₂) (y₁ * y₂) := by
  intro x₁ x₂ y₁ y₂ ⟨h1a, h1b, h1c⟩ ⟨h2a, h2b, h2c⟩
  simp only [uabEquiv, PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2, PreUABMonoid.mul_others]
  constructor
  · exact congr_arg₂ (· + ·) h1a h2a
  constructor
  · omega
  · omega

instance uabSetoid : Setoid PreUABMonoid where
  r := uabEquiv
  iseqv := uabEquiv_equiv

/-- The UAB Failure Monoid: quotient of PreUABMonoid by the relation p₁² = p₂².
    Using `abbrev` to ensure instance unification with `Quotient uabSetoid`. -/
abbrev UABFailMonoid := Quotient uabSetoid

namespace UABFailMonoid

/-- Injection from PreUABMonoid to UABFailMonoid. -/
def mk (x : PreUABMonoid) : UABFailMonoid := Quotient.mk uabSetoid x

/-- One in the quotient. -/
protected def one' : UABFailMonoid := mk 1

/-- Multiplication in the quotient. -/
protected def mul' (a b : UABFailMonoid) : UABFailMonoid :=
  Quotient.lift₂ (fun x y => mk (x * y))
    (fun _ _ _ _ hxy hzw => Quotient.sound (uabEquiv_mul _ _ _ _ hxy hzw)) a b

instance : One UABFailMonoid := ⟨UABFailMonoid.one'⟩
instance : Mul UABFailMonoid := ⟨UABFailMonoid.mul'⟩

@[simp] lemma mk_one : mk 1 = (1 : UABFailMonoid) := rfl

lemma mk_mul (x y : PreUABMonoid) : mk x * mk y = mk (x * y) := rfl

/-- Lemma relating Quotient.mk to our mk. -/
lemma quot_mk_eq_mk (x : PreUABMonoid) : Quotient.mk uabSetoid x = mk x := rfl

instance : CommMonoid UABFailMonoid where
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    obtain ⟨c', rfl⟩ := Quotient.exists_rep c
    rw [quot_mk_eq_mk, quot_mk_eq_mk, quot_mk_eq_mk]
    simp only [mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others]
      abel
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2]
      omega
    · simp only [PreUABMonoid.mul_exp_p1]
      omega
  one := 1
  one_mul := by
    intro a
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    rw [quot_mk_eq_mk]
    show mk 1 * mk a' = mk a'
    simp only [mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.one_others, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                 PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.one_exp_p1, zero_add]
  mul_one := by
    intro a
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    rw [quot_mk_eq_mk]
    show mk a' * mk 1 = mk a'
    simp only [mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.one_others, add_zero]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                 PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, add_zero]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.one_exp_p1, add_zero]
  mul_comm := by
    intro a b
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    rw [quot_mk_eq_mk, quot_mk_eq_mk]
    simp only [mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others]
      abel
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2]
      omega
    · simp only [PreUABMonoid.mul_exp_p1]
      omega

/-- The atom p₁ in the quotient. -/
def atomP1 : UABFailMonoid := mk PreUABMonoid.p1

/-- The atom p₂ in the quotient. -/
def atomP2 : UABFailMonoid := mk PreUABMonoid.p2

/-- The atom p_{n+3} in the quotient. -/
def atomPn (n : ℕ) : UABFailMonoid := mk (PreUABMonoid.pn n)

/-- The key relation holds: p₁² = p₂². -/
theorem p1_sq_eq_p2_sq : atomP1 ^ 2 = atomP2 ^ 2 := by
  simp only [sq, atomP1, atomP2, mk_mul]
  apply Quotient.sound
  refine ⟨?_, ?_, ?_⟩
  · simp only [PreUABMonoid.mul_others, PreUABMonoid.p1_others, PreUABMonoid.p2_others, add_zero]
  · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
               PreUABMonoid.p1_exp_p1, PreUABMonoid.p1_exp_p2,
               PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2, add_zero, zero_add]
  · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1, PreUABMonoid.p2_exp_p1, add_zero]

/-- p₁ ≠ p₂ in the quotient. -/
theorem p1_ne_p2 : atomP1 ≠ atomP2 := by
  intro h
  have heq : mk PreUABMonoid.p1 = mk PreUABMonoid.p2 := h
  have hequiv := Quotient.exact heq
  obtain ⟨_, _, hparity⟩ := hequiv
  simp only [PreUABMonoid.p1_exp_p1, PreUABMonoid.p2_exp_p1] at hparity
  norm_num at hparity

/-!
## Helper Lemmas
-/

/-- Helper lemma for Finsupp. -/
lemma finsupp_add_eq_zero_iff {a b : ℕ →₀ ℕ} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · ext i
      have hi : a i + b i = 0 := DFunLike.congr_fun h i
      exact Nat.eq_zero_of_add_eq_zero_right hi
    · ext i
      have hi : a i + b i = 0 := DFunLike.congr_fun h i
      exact Nat.eq_zero_of_add_eq_zero_left hi
  · intro ⟨ha, hb⟩
    simp [ha, hb]

/-- Only 1 is a unit in the quotient. -/
lemma isUnit_iff (x : UABFailMonoid) : IsUnit x ↔ x = 1 := by
  constructor
  · intro ⟨u, hu⟩
    obtain ⟨u_val, hu_val_eq⟩ := Quotient.exists_rep u.val
    obtain ⟨u_inv, hu_inv_eq⟩ := Quotient.exists_rep u.inv
    have h : mk u_val * mk u_inv = 1 := by
      have := u.val_inv
      simp only [← hu_val_eq, ← hu_inv_eq, quot_mk_eq_mk] at this
      exact this
    rw [mk_mul] at h
    have hequiv := Quotient.exact h
    obtain ⟨hothers, htotal, _⟩ := hequiv
    simp only [PreUABMonoid.mul_others, PreUABMonoid.one_others] at hothers
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
               PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2] at htotal
    have ⟨hu_f, _⟩ := finsupp_add_eq_zero_iff.mp hothers
    have hu_exp1 : u_val.exp_p1 = 0 := by omega
    have hu_exp2 : u_val.exp_p2 = 0 := by omega
    rw [← hu]
    rw [← hu_val_eq, quot_mk_eq_mk]
    apply Quotient.sound
    refine ⟨hu_f, ?_, ?_⟩
    · simp [hu_exp1, hu_exp2]
    · simp [hu_exp1]
  · intro hx
    rw [hx]
    exact isUnit_one

/-!
## Axiom Verification
-/

/-- The UAB Failure Monoid is reduced. -/
theorem uabfail_reduced : Reduced UABFailMonoid := by
  intro x hx
  exact (isUnit_iff x).mp hx

/-- p₁ is not a unit. -/
lemma atomP1_not_isUnit : ¬IsUnit atomP1 := by
  intro h
  have := (isUnit_iff atomP1).mp h
  have hequiv := Quotient.exact this
  obtain ⟨_, _, hparity⟩ := hequiv
  simp only [PreUABMonoid.p1_exp_p1, PreUABMonoid.one_exp_p1] at hparity
  norm_num at hparity

/-- p₂ is not a unit. -/
lemma atomP2_not_isUnit : ¬IsUnit atomP2 := by
  intro h
  have := (isUnit_iff atomP2).mp h
  have hequiv := Quotient.exact this
  obtain ⟨_, htotal, _⟩ := hequiv
  simp only [PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2,
             PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2] at htotal
  omega

/-- pn(m) is not a unit. -/
lemma atomPn_not_isUnit (m : ℕ) : ¬IsUnit (atomPn m) := by
  intro h
  have := (isUnit_iff (atomPn m)).mp h
  have hequiv := Quotient.exact this
  obtain ⟨hothers, _, _⟩ := hequiv
  simp only [PreUABMonoid.pn_others, PreUABMonoid.one_others] at hothers
  have hcontra : (Finsupp.single m 1) m = 0 := DFunLike.congr_fun hothers m
  simp at hcontra

/-- p₁ is irreducible. -/
lemma atomP1_irreducible : Irreducible atomP1 := by
  constructor
  · exact atomP1_not_isUnit
  · intro a b hab
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    rw [quot_mk_eq_mk, quot_mk_eq_mk, mk_mul] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨hothers, htotal, hparity⟩ := hequiv
    simp only [PreUABMonoid.mul_others, PreUABMonoid.p1_others] at hothers
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
               PreUABMonoid.p1_exp_p1, PreUABMonoid.p1_exp_p2] at htotal
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1] at hparity
    have ⟨ha_f, hb_f⟩ := finsupp_add_eq_zero_iff.mp hothers.symm
    -- Total a + b exponents = 1, so one of them is 0
    have hsum : a'.exp_p1 + a'.exp_p2 + (b'.exp_p1 + b'.exp_p2) = 1 := by omega
    cases Nat.eq_zero_or_pos (a'.exp_p1 + a'.exp_p2) with
    | inl ha =>
      left
      rw [isUnit_iff, quot_mk_eq_mk]
      apply Quotient.sound
      have ha1 : a'.exp_p1 = 0 := by omega
      have ha2 : a'.exp_p2 = 0 := by omega
      exact ⟨ha_f, by simp [ha1, ha2], by simp [ha1]⟩
    | inr ha =>
      have hb : b'.exp_p1 + b'.exp_p2 = 0 := by omega
      right
      rw [isUnit_iff, quot_mk_eq_mk]
      apply Quotient.sound
      have hb1 : b'.exp_p1 = 0 := by omega
      have hb2 : b'.exp_p2 = 0 := by omega
      exact ⟨hb_f, by simp [hb1, hb2], by simp [hb1]⟩

/-- p₂ is irreducible. -/
lemma atomP2_irreducible : Irreducible atomP2 := by
  constructor
  · exact atomP2_not_isUnit
  · intro a b hab
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    rw [quot_mk_eq_mk, quot_mk_eq_mk, mk_mul] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨hothers, htotal, _⟩ := hequiv
    simp only [PreUABMonoid.mul_others, PreUABMonoid.p2_others] at hothers
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
               PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2] at htotal
    have ⟨ha_f, hb_f⟩ := finsupp_add_eq_zero_iff.mp hothers.symm
    have hsum : a'.exp_p1 + a'.exp_p2 + (b'.exp_p1 + b'.exp_p2) = 1 := by omega
    cases Nat.eq_zero_or_pos (a'.exp_p1 + a'.exp_p2) with
    | inl ha =>
      left
      rw [isUnit_iff, quot_mk_eq_mk]
      apply Quotient.sound
      have ha1 : a'.exp_p1 = 0 := by omega
      have ha2 : a'.exp_p2 = 0 := by omega
      exact ⟨ha_f, by simp [ha1, ha2], by simp [ha1]⟩
    | inr ha =>
      have hb : b'.exp_p1 + b'.exp_p2 = 0 := by omega
      right
      rw [isUnit_iff, quot_mk_eq_mk]
      apply Quotient.sound
      have hb1 : b'.exp_p1 = 0 := by omega
      have hb2 : b'.exp_p2 = 0 := by omega
      exact ⟨hb_f, by simp [hb1, hb2], by simp [hb1]⟩

/-- pn(m) is irreducible. -/
lemma atomPn_irreducible (m : ℕ) : Irreducible (atomPn m) := by
  constructor
  · exact atomPn_not_isUnit m
  · intro a b hab
    obtain ⟨a', rfl⟩ := Quotient.exists_rep a
    obtain ⟨b', rfl⟩ := Quotient.exists_rep b
    rw [quot_mk_eq_mk, quot_mk_eq_mk, mk_mul] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨hothers, htotal, _⟩ := hequiv
    simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others] at hothers
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
               PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2] at htotal
    have hsum_p : a'.exp_p1 + a'.exp_p2 + (b'.exp_p1 + b'.exp_p2) = 0 := by omega
    have ha1 : a'.exp_p1 = 0 := by omega
    have ha2 : a'.exp_p2 = 0 := by omega
    have hb1 : b'.exp_p1 = 0 := by omega
    have hb2 : b'.exp_p2 = 0 := by omega
    -- Now the others must sum to single m 1
    by_cases ha_zero : a'.others = 0
    · left
      rw [isUnit_iff, quot_mk_eq_mk]
      apply Quotient.sound
      exact ⟨ha_zero, by simp [ha1, ha2], by simp [ha1]⟩
    · by_cases hb_zero : b'.others = 0
      · right
        rw [isUnit_iff, quot_mk_eq_mk]
        apply Quotient.sound
        exact ⟨hb_zero, by simp [hb1, hb2], by simp [hb1]⟩
      · exfalso
        have ha_supp := Finsupp.support_nonempty_iff.mpr ha_zero
        obtain ⟨i, hi⟩ := ha_supp
        have hi_pos : 0 < a'.others i := Finsupp.mem_support_iff.mp hi |> Nat.pos_of_ne_zero
        have hsum_i : a'.others i + b'.others i = (Finsupp.single m 1) i := by
          have := DFunLike.congr_fun hothers.symm i
          simp only [Finsupp.coe_add, Pi.add_apply] at this
          exact this
        by_cases him : i = m
        · subst him
          simp only [Finsupp.single_eq_same] at hsum_i
          have hb_supp := Finsupp.support_nonempty_iff.mpr hb_zero
          obtain ⟨j, hj⟩ := hb_supp
          have hj_pos : 0 < b'.others j := Finsupp.mem_support_iff.mp hj |> Nat.pos_of_ne_zero
          by_cases hjm : j = i
          · subst hjm; omega
          · have hsum_j : a'.others j + b'.others j = 0 := by
              have := DFunLike.congr_fun hothers.symm j
              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hjm] at this
              exact this
            omega
        · simp only [Finsupp.single_eq_of_ne him] at hsum_i
          omega

/-- Size function for well-founded induction. -/
private def uabSize (x : PreUABMonoid) : ℕ :=
  x.exp_p1 + x.exp_p2 + x.others.sum (fun _ v => v)

/-- The UAB Failure Monoid is atomic. -/
theorem uabfail_atomic : Atomic UABFailMonoid := by
  intro x
  obtain ⟨x', rfl⟩ := Quotient.exists_rep x
  have h : ∀ n (y : PreUABMonoid), uabSize y = n → ¬IsUnit (mk y) →
      ∃ L : List UABFailMonoid, (∀ a ∈ L, a ∈ Atoms UABFailMonoid) ∧ L.prod = mk y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hsize hy_not_unit
      by_cases hy_atom : mk y ∈ Atoms UABFailMonoid
      · exact ⟨[mk y], by simp [hy_atom], by simp⟩
      · -- Factor out an atom
        by_cases hp12 : y.exp_p1 + y.exp_p2 ≥ 1
        · -- Factor out either p1 or p2
          by_cases hp1 : y.exp_p1 ≥ 1
          · -- Factor out p1
            let z : PreUABMonoid := ⟨y.exp_p1 - 1, y.exp_p2, y.others⟩
            have hz_exp1 : z.exp_p1 = y.exp_p1 - 1 := rfl
            have hz_exp2 : z.exp_p2 = y.exp_p2 := rfl
            have hz_others : z.others = y.others := rfl
            have hz_size : uabSize z < uabSize y := by
              unfold uabSize
              simp only [hz_exp1, hz_exp2, hz_others]
              omega
            by_cases hz_unit : IsUnit (mk z)
            · have heq := (isUnit_iff (mk z)).mp hz_unit
              have hequiv := Quotient.exact heq
              obtain ⟨hothers, htotal, _⟩ := hequiv
              exfalso
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, hz_exp1, hz_exp2] at htotal
              have hp1_val : y.exp_p1 = 1 := by omega
              have hp2_val : y.exp_p2 = 0 := by omega
              -- z.others = y.others by definition, and hothers : z.others = 0
              have hf0 : y.others = 0 := hz_others ▸ hothers
              have hy_is_p1 : mk y = atomP1 := by
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · simp only [PreUABMonoid.p1_others, hf0]
                · simp [hp1_val, hp2_val]
                · simp [hp1_val]
              rw [hy_is_p1] at hy_atom
              exact hy_atom atomP1_irreducible
            · have ⟨Lz, hLz_atoms, hLz_prod⟩ := ih (uabSize z) (hsize ▸ hz_size) z rfl hz_unit
              refine ⟨atomP1 :: Lz, ?_, ?_⟩
              · intro a ha
                simp at ha
                rcases ha with rfl | ha
                · exact atomP1_irreducible
                · exact hLz_atoms a ha
              · simp only [List.prod_cons, hLz_prod, atomP1, mk_mul]
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · simp only [PreUABMonoid.mul_others, PreUABMonoid.p1_others, zero_add, hz_others]
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                             PreUABMonoid.p1_exp_p1, PreUABMonoid.p1_exp_p2, hz_exp1, hz_exp2]
                  omega
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1, hz_exp1]
                  omega
          · -- y.exp_p1 = 0, so y.exp_p2 ≥ 1, factor out p2
            push_neg at hp1
            have hp1_0 : y.exp_p1 = 0 := by omega
            have hp2_pos : y.exp_p2 ≥ 1 := by omega
            let z : PreUABMonoid := ⟨y.exp_p1, y.exp_p2 - 1, y.others⟩
            have hz_exp1 : z.exp_p1 = y.exp_p1 := rfl
            have hz_exp2 : z.exp_p2 = y.exp_p2 - 1 := rfl
            have hz_others : z.others = y.others := rfl
            have hz_size : uabSize z < uabSize y := by
              unfold uabSize
              simp only [hz_exp1, hz_exp2, hz_others]
              omega
            by_cases hz_unit : IsUnit (mk z)
            · have heq := (isUnit_iff (mk z)).mp hz_unit
              have hequiv := Quotient.exact heq
              obtain ⟨hothers, htotal, _⟩ := hequiv
              exfalso
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, hz_exp1, hz_exp2] at htotal
              have hp2_val : y.exp_p2 = 1 := by omega
              have hf0 : y.others = 0 := hz_others ▸ hothers
              have hy_is_p2 : mk y = atomP2 := by
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · simp only [PreUABMonoid.p2_others, hf0]
                · simp [hp1_0, hp2_val]
                · simp [hp1_0]
              rw [hy_is_p2] at hy_atom
              exact hy_atom atomP2_irreducible
            · have ⟨Lz, hLz_atoms, hLz_prod⟩ := ih (uabSize z) (hsize ▸ hz_size) z rfl hz_unit
              refine ⟨atomP2 :: Lz, ?_, ?_⟩
              · intro a ha
                simp at ha
                rcases ha with rfl | ha
                · exact atomP2_irreducible
                · exact hLz_atoms a ha
              · simp only [List.prod_cons, hLz_prod, atomP2, mk_mul]
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · simp only [PreUABMonoid.mul_others, PreUABMonoid.p2_others, zero_add, hz_others]
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                             PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2, hz_exp1, hz_exp2]
                  omega
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p2_exp_p1, zero_add, hz_exp1]
        · -- y.exp_p1 + y.exp_p2 = 0, so factor out some pn
          push_neg at hp12
          have hp1_0 : y.exp_p1 = 0 := by omega
          have hp2_0 : y.exp_p2 = 0 := by omega
          by_cases hf : y.others = 0
          · exfalso
            have hy1 : mk y = 1 := by
              apply Quotient.sound
              exact ⟨hf, by simp [hp1_0, hp2_0], by simp [hp1_0]⟩
            rw [hy1] at hy_not_unit
            exact hy_not_unit isUnit_one
          · have hsupp := Finsupp.support_nonempty_iff.mpr hf
            obtain ⟨i, hi⟩ := hsupp
            have hi_pos : y.others i ≥ 1 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
            let z : PreUABMonoid := ⟨0, 0, y.others - Finsupp.single i 1⟩
            have hz_exp1 : z.exp_p1 = 0 := rfl
            have hz_exp2 : z.exp_p2 = 0 := rfl
            have hz_others : z.others = y.others - Finsupp.single i 1 := rfl
            have hz_size : uabSize z < uabSize y := by
              unfold uabSize
              simp only [hp1_0, hp2_0, hz_exp1, hz_exp2, zero_add]
              have hsum_y : y.others.sum (fun _ v => v) = y.others.support.sum (fun j => y.others j) := by
                rw [Finsupp.sum]
              have hsum_z : z.others.sum (fun _ v => v) = z.others.support.sum (fun j => z.others j) := by
                rw [Finsupp.sum]
              rw [hsum_y, hsum_z]
              have hz_supp_sub : z.others.support ⊆ y.others.support := by
                intro j hj
                rw [Finsupp.mem_support_iff] at hj ⊢
                rw [hz_others] at hj
                simp only [Finsupp.coe_tsub, Pi.sub_apply] at hj
                by_contra hy_j
                simp only [hy_j, tsub_zero] at hj
                by_cases hji : j = i
                · subst hji; simp only [Finsupp.single_eq_same] at hj; omega
                · simp only [Finsupp.single_eq_of_ne hji] at hj; exact hj rfl
              calc z.others.support.sum (fun j => z.others j)
                  ≤ y.others.support.sum (fun j => z.others j) := by
                      apply Finset.sum_le_sum_of_subset hz_supp_sub
                _ < y.others.support.sum (fun j => y.others j) := by
                      apply Finset.sum_lt_sum
                      · intro j _
                        rw [hz_others]
                        simp only [Finsupp.coe_tsub, Pi.sub_apply]
                        exact Nat.sub_le _ _
                      · use i, hi
                        rw [hz_others]
                        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
                        omega
            by_cases hz_unit : IsUnit (mk z)
            · have heq := (isUnit_iff (mk z)).mp hz_unit
              have hequiv := Quotient.exact heq
              obtain ⟨hothers_eq, _, _⟩ := hequiv
              -- hothers_eq : z.others = 1.others = 0
              -- So y.others - single i 1 = 0, meaning y.others = single i 1
              have hf1 : y.others = Finsupp.single i 1 := by
                ext k
                have hk := DFunLike.congr_fun hothers_eq k
                simp only [PreUABMonoid.one_others, Finsupp.coe_zero, Pi.zero_apply] at hk
                rw [hz_others] at hk
                simp only [Finsupp.coe_tsub, Pi.sub_apply] at hk
                by_cases hki : k = i
                · rw [hki] at hk ⊢
                  simp only [Finsupp.single_eq_same] at hk ⊢
                  have hi_bound : y.others i ≤ 1 := Nat.sub_eq_zero_iff_le.mp hk
                  exact Nat.le_antisymm hi_bound hi_pos
                · simp only [Finsupp.single_eq_of_ne hki] at hk ⊢
                  simp at hk
                  exact hk
              exfalso
              have hy_is_pn : mk y = atomPn i := by
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · simp only [PreUABMonoid.pn_others, hf1]
                · simp [hp1_0, hp2_0]
                · simp [hp1_0]
              rw [hy_is_pn] at hy_atom
              exact hy_atom (atomPn_irreducible i)
            · have ⟨Lz, hLz_atoms, hLz_prod⟩ := ih (uabSize z) (hsize ▸ hz_size) z rfl hz_unit
              refine ⟨atomPn i :: Lz, ?_, ?_⟩
              · intro a ha
                simp at ha
                rcases ha with rfl | ha
                · exact atomPn_irreducible i
                · exact hLz_atoms a ha
              · simp only [List.prod_cons, hLz_prod, atomPn, mk_mul]
                apply Quotient.sound
                refine ⟨?_, ?_, ?_⟩
                · ext k
                  simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others,
                             Finsupp.coe_add, Pi.add_apply, hz_others,
                             Finsupp.coe_tsub, Pi.sub_apply]
                  by_cases hki : k = i
                  · rw [hki]
                    simp only [Finsupp.single_eq_same]
                    omega
                  · simp only [Finsupp.single_eq_of_ne hki, zero_add, tsub_zero]
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                             PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2, hz_exp1, hz_exp2]
                  omega
                · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.pn_exp_p1, zero_add, hz_exp1, hp1_0]
  intro hx_not_unit
  rw [quot_mk_eq_mk] at hx_not_unit
  obtain ⟨L, hL_atoms, hL_prod⟩ := h (uabSize x') x' rfl hx_not_unit
  use L
  constructor
  · intro a ha; exact hL_atoms a ha
  · simp only [Multiset.prod_coe, hL_prod, quot_mk_eq_mk]

/-- Powers of p₁: p₁^n = mk ⟨n, 0, 0⟩. -/
lemma pow_atomP1 (n : ℕ) : atomP1 ^ n = mk ⟨n, 0, 0⟩ := by
  induction n with
  | zero =>
    simp only [pow_zero, mk_one]
    apply Quotient.sound
    exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    rw [pow_succ, ih, atomP1, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.p1_others, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                 PreUABMonoid.p1_exp_p1, PreUABMonoid.p1_exp_p2, add_zero]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1]

/-- Powers of p₂: p₂^n = mk ⟨0, n, 0⟩. -/
lemma pow_atomP2 (n : ℕ) : atomP2 ^ n = mk ⟨0, n, 0⟩ := by
  induction n with
  | zero =>
    simp only [pow_zero, mk_one]
    apply Quotient.sound
    exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    rw [pow_succ, ih, atomP2, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.p2_others, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                 PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p2_exp_p1, zero_add]

/-- Powers of pn(m): pn(m)^k = mk ⟨0, 0, single m k⟩. -/
lemma pow_atomPn (m k : ℕ) : atomPn m ^ k = mk ⟨0, 0, Finsupp.single m k⟩ := by
  induction k with
  | zero =>
    simp only [pow_zero, mk_one]
    apply Quotient.sound
    exact ⟨by simp [Finsupp.single_zero], rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ, ih, atomPn, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others,
                 ← Finsupp.single_add, add_comm]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                 PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2, zero_add]
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.pn_exp_p1, zero_add]

/-- The atoms of UABFailMonoid are {p₁, p₂} ∪ {pn(m) : m ∈ ℕ}.

    **Proof sketch**: An element is an atom iff it's irreducible.
    - If exp_p1 + exp_p2 = 1 and others = 0: must be p1 or p2
    - If exp_p1 + exp_p2 = 0 and others = single i 1 for some i: must be pn(i)
    - Any other element factors non-trivially

    The forward direction uses case analysis on the representative structure.
    The backward direction is straightforward since atomP1, atomP2, atomPn are irreducible. -/
lemma atoms_eq : Atoms UABFailMonoid = {atomP1, atomP2} ∪ { x | ∃ m, x = atomPn m } := by
  ext x
  simp only [Atoms, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff]
  constructor
  · -- Forward direction: irreducible implies one of p1, p2, or pn m
    intro hx
    obtain ⟨x', rfl⟩ := Quotient.exists_rep x
    rw [quot_mk_eq_mk] at hx ⊢
    -- Case analysis on the structure of x'
    by_cases hf : x'.others = 0
    · -- Case: others = 0, so x' only has p1/p2 components
      by_cases hp12 : x'.exp_p1 + x'.exp_p2 = 0
      · -- exp_p1 = exp_p2 = 0 and others = 0: x' = 1, not irreducible
        exfalso
        have hp1 : x'.exp_p1 = 0 := by omega
        have hp2 : x'.exp_p2 = 0 := by omega
        have h1 : mk x' = 1 := by
          apply Quotient.sound
          refine ⟨hf, ?_, ?_⟩ <;> simp [hp1, hp2]
        rw [h1] at hx
        exact hx.1 isUnit_one
      · by_cases hp12_1 : x'.exp_p1 + x'.exp_p2 = 1
        · -- Total = 1: either p1 or p2
          by_cases hp1_1 : x'.exp_p1 = 1
          · -- exp_p1 = 1, exp_p2 = 0: this is p1
            have hp2_0 : x'.exp_p2 = 0 := by omega
            left; left
            apply Quotient.sound
            refine ⟨hf, ?_, ?_⟩ <;> simp [hp1_1, hp2_0]
          · -- exp_p1 = 0, exp_p2 = 1: this is p2
            have hp1_0 : x'.exp_p1 = 0 := by omega
            have hp2_1 : x'.exp_p2 = 1 := by omega
            left; right
            apply Quotient.sound
            refine ⟨hf, ?_, ?_⟩ <;> simp [hp1_0, hp2_1]
        · -- Total ≥ 2: x' factors non-trivially as p1 (or p2) × rest
          exfalso
          have htotal_ge2 : x'.exp_p1 + x'.exp_p2 ≥ 2 := by omega
          by_cases hp1_pos : x'.exp_p1 ≥ 1
          · -- Factor out p1
            let a : PreUABMonoid := ⟨1, 0, 0⟩
            let b : PreUABMonoid := ⟨x'.exp_p1 - 1, x'.exp_p2, 0⟩
            have ha_others : a.others = 0 := rfl
            have hb_others : b.others = 0 := rfl
            have ha_p1 : a.exp_p1 = 1 := rfl
            have hb_p1 : b.exp_p1 = x'.exp_p1 - 1 := rfl
            have ha_p2 : a.exp_p2 = 0 := rfl
            have hb_p2 : b.exp_p2 = x'.exp_p2 := rfl
            have hab : mk x' = mk a * mk b := by
              rw [mk_mul]
              apply Quotient.sound
              refine ⟨?_, ?_, ?_⟩
              · simp only [PreUABMonoid.mul_others, ha_others, hb_others, add_zero, hf]
              · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                           ha_p1, hb_p1, ha_p2, hb_p2]; omega
              · simp only [PreUABMonoid.mul_exp_p1, ha_p1, hb_p1]; omega
            have ha_nu : ¬IsUnit (mk a) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨_, htot, _⟩ := hequiv
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, ha_p1, ha_p2] at htot
              omega
            have hb_nu : ¬IsUnit (mk b) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨_, htot, _⟩ := hequiv
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, hb_p1, hb_p2] at htot
              omega
            rcases hx.isUnit_or_isUnit hab with ha | hb
            · exact ha_nu ha
            · exact hb_nu hb
          · -- exp_p1 = 0, so exp_p2 ≥ 2. Factor out p2
            have hp1_0 : x'.exp_p1 = 0 := by omega
            have hp2_ge2 : x'.exp_p2 ≥ 2 := by omega
            let a : PreUABMonoid := ⟨0, 1, 0⟩
            let b : PreUABMonoid := ⟨0, x'.exp_p2 - 1, 0⟩
            have ha_others : a.others = 0 := rfl
            have hb_others : b.others = 0 := rfl
            have ha_p1 : a.exp_p1 = 0 := rfl
            have hb_p1 : b.exp_p1 = 0 := rfl
            have ha_p2 : a.exp_p2 = 1 := rfl
            have hb_p2 : b.exp_p2 = x'.exp_p2 - 1 := rfl
            have hab : mk x' = mk a * mk b := by
              rw [mk_mul]
              apply Quotient.sound
              refine ⟨?_, ?_, ?_⟩
              · simp only [PreUABMonoid.mul_others, ha_others, hb_others, add_zero, hf]
              · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                           ha_p1, hb_p1, ha_p2, hb_p2, hp1_0]; omega
              · simp only [PreUABMonoid.mul_exp_p1, ha_p1, hb_p1, hp1_0]
            have ha_nu : ¬IsUnit (mk a) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨_, htot, _⟩ := hequiv
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, ha_p1, ha_p2] at htot
              omega
            have hb_nu : ¬IsUnit (mk b) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨_, htot, _⟩ := hequiv
              simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, hb_p1, hb_p2] at htot
              omega
            rcases hx.isUnit_or_isUnit hab with ha | hb
            · exact ha_nu ha
            · exact hb_nu hb
    · -- Case: others ≠ 0
      by_cases hp12 : x'.exp_p1 + x'.exp_p2 ≥ 1
      · -- Has both p1/p2 and others: factors as (p1/p2 part) × (others part)
        exfalso
        let a : PreUABMonoid := ⟨x'.exp_p1, x'.exp_p2, 0⟩
        let b : PreUABMonoid := ⟨0, 0, x'.others⟩
        have ha_others : a.others = 0 := rfl
        have hb_others : b.others = x'.others := rfl
        have ha_p1 : a.exp_p1 = x'.exp_p1 := rfl
        have hb_p1 : b.exp_p1 = 0 := rfl
        have ha_p2 : a.exp_p2 = x'.exp_p2 := rfl
        have hb_p2 : b.exp_p2 = 0 := rfl
        have hab : mk x' = mk a * mk b := by
          rw [mk_mul]
          apply Quotient.sound
          refine ⟨?_, ?_, ?_⟩
          · simp only [PreUABMonoid.mul_others, ha_others, hb_others, zero_add]
          · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                       ha_p1, hb_p1, ha_p2, hb_p2, add_zero]
          · simp only [PreUABMonoid.mul_exp_p1, ha_p1, hb_p1, add_zero]
        have ha_nu : ¬IsUnit (mk a) := by
          rw [isUnit_iff]; intro h
          have hequiv := Quotient.exact h
          obtain ⟨_, htot, _⟩ := hequiv
          simp only [PreUABMonoid.one_exp_p1, PreUABMonoid.one_exp_p2, ha_p1, ha_p2] at htot
          omega
        have hb_nu : ¬IsUnit (mk b) := by
          rw [isUnit_iff]; intro h
          have hequiv := Quotient.exact h
          obtain ⟨hoth, _, _⟩ := hequiv
          simp only [PreUABMonoid.one_others, hb_others] at hoth
          exact hf hoth
        rcases hx.isUnit_or_isUnit hab with ha | hb
        · exact ha_nu ha
        · exact hb_nu hb
      · -- exp_p1 = exp_p2 = 0, only others: check if it's a single atom
        push_neg at hp12
        have hp1_0 : x'.exp_p1 = 0 := by omega
        have hp2_0 : x'.exp_p2 = 0 := by omega
        have hsupp := Finsupp.support_nonempty_iff.mpr hf
        obtain ⟨i, hi⟩ := hsupp
        have hi_pos : x'.others i ≥ 1 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
        by_cases hsingle : x'.others = Finsupp.single i 1
        · -- x' is atomPn i
          right
          use i
          apply Quotient.sound
          refine ⟨hsingle, ?_, ?_⟩
          · simp only [PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2, hp1_0, hp2_0]
          · simp only [PreUABMonoid.pn_exp_p1, hp1_0]
        · -- others is not a single atom: factors non-trivially
          exfalso
          -- Either others i ≥ 2, or there's another index j with others j ≥ 1
          by_cases hi_ge2 : x'.others i ≥ 2
          · -- Factor out one copy of pn i
            let a : PreUABMonoid := ⟨0, 0, Finsupp.single i 1⟩
            let b : PreUABMonoid := ⟨0, 0, x'.others - Finsupp.single i 1⟩
            have ha_p1 : a.exp_p1 = 0 := rfl
            have ha_p2 : a.exp_p2 = 0 := rfl
            have ha_others : a.others = Finsupp.single i 1 := rfl
            have hb_p1 : b.exp_p1 = 0 := rfl
            have hb_p2 : b.exp_p2 = 0 := rfl
            have hb_others : b.others = x'.others - Finsupp.single i 1 := rfl
            have hab : mk x' = mk a * mk b := by
              rw [mk_mul]
              apply Quotient.sound
              refine ⟨?_, ?_, ?_⟩
              · simp only [PreUABMonoid.mul_others, ha_others, hb_others]
                ext k
                simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply]
                by_cases hki : k = i
                · subst hki; simp only [Finsupp.single_eq_same]; omega
                · simp only [Finsupp.single_eq_of_ne hki, add_zero, tsub_zero, zero_add]
              · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                           ha_p1, ha_p2, hb_p1, hb_p2, hp1_0, hp2_0, add_zero]
              · simp only [PreUABMonoid.mul_exp_p1, ha_p1, hb_p1, hp1_0, add_zero]
            have ha_nu : ¬IsUnit (mk a) := atomPn_not_isUnit i
            have hb_nu : ¬IsUnit (mk b) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨hoth, _, _⟩ := hequiv
              simp only [PreUABMonoid.one_others, hb_others] at hoth
              have hi' := DFunLike.congr_fun hoth i
              simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
                         Finsupp.coe_zero, Pi.zero_apply] at hi'
              omega
            rcases hx.isUnit_or_isUnit hab with ha | hb
            · exact ha_nu ha
            · exact hb_nu hb
          · -- There's another index j ≠ i with others j ≥ 1
            push_neg at hi_ge2
            have hi_eq1 : x'.others i = 1 := by omega
            have hj_exists : ∃ j, j ≠ i ∧ x'.others j ≥ 1 := by
              by_contra hall
              push_neg at hall
              have hothers_eq : x'.others = Finsupp.single i 1 := by
                ext k
                by_cases hki : k = i
                · subst hki; simp only [Finsupp.single_eq_same, hi_eq1]
                · have hk := hall k hki
                  simp only [Finsupp.single_eq_of_ne hki]
                  omega
              exact hsingle hothers_eq
            obtain ⟨j, hji, hj_pos⟩ := hj_exists
            -- Factor as (single i) × (rest)
            let a : PreUABMonoid := ⟨0, 0, Finsupp.single i 1⟩
            let b : PreUABMonoid := ⟨0, 0, x'.others - Finsupp.single i 1⟩
            have ha_p1 : a.exp_p1 = 0 := rfl
            have ha_p2 : a.exp_p2 = 0 := rfl
            have ha_others : a.others = Finsupp.single i 1 := rfl
            have hb_p1 : b.exp_p1 = 0 := rfl
            have hb_p2 : b.exp_p2 = 0 := rfl
            have hb_others : b.others = x'.others - Finsupp.single i 1 := rfl
            have hab : mk x' = mk a * mk b := by
              rw [mk_mul]
              apply Quotient.sound
              refine ⟨?_, ?_, ?_⟩
              · simp only [PreUABMonoid.mul_others, ha_others, hb_others]
                ext k
                simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply]
                by_cases hki : k = i
                · subst hki; simp only [Finsupp.single_eq_same]; omega
                · simp only [Finsupp.single_eq_of_ne hki, add_zero, tsub_zero, zero_add]
              · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                           ha_p1, ha_p2, hb_p1, hb_p2, hp1_0, hp2_0, add_zero]
              · simp only [PreUABMonoid.mul_exp_p1, ha_p1, hb_p1, hp1_0, add_zero]
            have ha_nu : ¬IsUnit (mk a) := atomPn_not_isUnit i
            have hb_nu : ¬IsUnit (mk b) := by
              rw [isUnit_iff]; intro h
              have hequiv := Quotient.exact h
              obtain ⟨hoth, _, _⟩ := hequiv
              simp only [PreUABMonoid.one_others, hb_others] at hoth
              have hj' := DFunLike.congr_fun hoth j
              have hsingle_j : (Finsupp.single i (1 : ℕ)) j = 0 := Finsupp.single_eq_of_ne hji
              simp only [Finsupp.coe_tsub, Pi.sub_apply, hsingle_j,
                         tsub_zero, Finsupp.coe_zero, Pi.zero_apply] at hj'
              omega
            rcases hx.isUnit_or_isUnit hab with ha | hb
            · exact ha_nu ha
            · exact hb_nu hb
  · intro hx
    rcases hx with (rfl | rfl) | ⟨m, rfl⟩
    · exact atomP1_irreducible
    · exact atomP2_irreducible
    · exact atomPn_irreducible m

-- Delete the rest of the complex proof and replace with the simplified version above
-- The original proof attempted detailed case analysis which is complex for quotient types

/-- PP-D holds: For each atom p_i, powers p_i^a = p_i^b implies a = b. -/
theorem uabfail_PPD : PP_D UABFailMonoid := by
  intro p hp
  -- Use atoms_eq to determine p is one of atomP1, atomP2, or atomPn m
  rw [atoms_eq] at hp
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq] at hp
  -- Injectivity: ∀ a b, p^a = p^b → a = b
  intro a b hab
  simp only at hab
  rcases hp with (rfl | rfl) | ⟨m, rfl⟩
  · -- p = atomP1
    rw [pow_atomP1, pow_atomP1] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨_, htotal, hparity⟩ := hequiv
    simp at htotal hparity
    omega
  · -- p = atomP2
    rw [pow_atomP2, pow_atomP2] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨_, htotal, _⟩ := hequiv
    simp at htotal
    exact htotal
  · -- p = atomPn m
    rw [pow_atomPn, pow_atomPn] at hab
    have hequiv := Quotient.exact hab
    obtain ⟨hothers, _, _⟩ := hequiv
    simp at hothers
    have hm := DFunLike.congr_fun hothers m
    simp at hm
    exact hm

/-- UAB fails: p₁² = p₂² with p₁ ≠ p₂. -/
theorem uabfail_not_UAB : ¬ UAB UABFailMonoid := by
  intro huab
  -- p₁ and p₂ are atoms
  have hp1_atom : atomP1 ∈ Atoms UABFailMonoid := atomP1_irreducible
  have hp2_atom : atomP2 ∈ Atoms UABFailMonoid := atomP2_irreducible
  -- p₁² = p₂² with 2 ≥ 1
  have h := huab atomP1 atomP2 hp1_atom hp2_atom 2 2 (by omega) (by omega) p1_sq_eq_p2_sq
  -- This gives p₁ = p₂, contradicting p1_ne_p2
  exact p1_ne_p2 h

/-- atomP1 divides x iff there exists a representative with exp_p1 ≥ 1.
    The forward direction uses the product p1 * c' as the representative. -/
lemma atomP1_dvd_iff (x : UABFailMonoid) : atomP1 ∣ x ↔
    ∃ x' : PreUABMonoid, mk x' = x ∧ x'.exp_p1 ≥ 1 := by
  constructor
  · intro ⟨c, hc⟩
    obtain ⟨c', rfl⟩ := Quotient.exists_rep c
    -- The product p1 * c' is a representative of x with exp_p1 = 1 + c'.exp_p1 ≥ 1
    use PreUABMonoid.p1 * c'
    constructor
    · rw [quot_mk_eq_mk, atomP1, mk_mul] at hc
      exact hc.symm
    · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1]
      omega
  · intro ⟨x', hx', hexp⟩
    rw [← hx']
    use mk ⟨x'.exp_p1 - 1, x'.exp_p2, x'.others⟩
    rw [atomP1, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp; omega
    · simp; omega

/-- atomP2 divides x iff there exists a representative with exp_p2 ≥ 1.
    The forward direction uses the product p2 * c' as the representative. -/
lemma atomP2_dvd_iff (x : UABFailMonoid) : atomP2 ∣ x ↔
    ∃ x' : PreUABMonoid, mk x' = x ∧ x'.exp_p2 ≥ 1 := by
  constructor
  · intro ⟨c, hc⟩
    obtain ⟨c', rfl⟩ := Quotient.exists_rep c
    -- The product p2 * c' is a representative of x with exp_p2 = 1 + c'.exp_p2 ≥ 1
    use PreUABMonoid.p2 * c'
    constructor
    · rw [quot_mk_eq_mk, atomP2, mk_mul] at hc
      exact hc.symm
    · simp only [PreUABMonoid.mul_exp_p2, PreUABMonoid.p2_exp_p2]
      omega
  · intro ⟨x', hx', hexp⟩
    rw [← hx']
    use mk ⟨x'.exp_p1, x'.exp_p2 - 1, x'.others⟩
    rw [atomP2, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp; omega
    · simp

/-- atomPn(i) divides x iff the representative has others(i) ≥ 1. -/
lemma atomPn_dvd_iff (i : ℕ) (x : UABFailMonoid) : atomPn i ∣ x ↔
    ∃ x' : PreUABMonoid, mk x' = x ∧ x'.others i ≥ 1 := by
  constructor
  · intro ⟨c, hc⟩
    obtain ⟨x', rfl⟩ := Quotient.exists_rep x
    obtain ⟨c', rfl⟩ := Quotient.exists_rep c
    rw [quot_mk_eq_mk, quot_mk_eq_mk, atomPn, mk_mul] at hc
    have hequiv := Quotient.exact hc
    obtain ⟨hothers, _, _⟩ := hequiv
    use x'
    constructor
    · rfl
    · simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others] at hothers
      have hi := DFunLike.congr_fun hothers i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hi
      omega
  · intro ⟨x', hx', hexp⟩
    rw [← hx']
    use mk ⟨x'.exp_p1, x'.exp_p2, x'.others - Finsupp.single i 1⟩
    rw [atomPn, mk_mul]
    apply Quotient.sound
    refine ⟨?_, ?_, ?_⟩
    · ext k
      simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others,
                 Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply]
      by_cases hki : k = i
      · subst hki; simp only [Finsupp.single_eq_same]; omega
      · simp only [Finsupp.single_eq_of_ne hki, zero_add, tsub_zero]
    · simp
    · simp

/-- Simplified coprimality: elements are coprime if they share no common atom divisor.
    For the others part, this is straightforward. For the p1/p2 part, the quotient structure
    means coprimality depends on whether both can be reached by an atom. -/
lemma areCoprime_others (x y : UABFailMonoid) (hxy : AreCoprime x y) :
    ∀ x' y' : PreUABMonoid, mk x' = x → mk y' = y →
      (∀ i, x'.others i = 0 ∨ y'.others i = 0) := by
  intro x' y' hx' hy' i
  by_contra hi
  push_neg at hi
  have hpnx : atomPn i ∣ x := (atomPn_dvd_iff i x).mpr ⟨x', hx', Nat.one_le_iff_ne_zero.mpr hi.1⟩
  have hpny : atomPn i ∣ y := (atomPn_dvd_iff i y).mpr ⟨y', hy', Nat.one_le_iff_ne_zero.mpr hi.2⟩
  exact hxy (atomPn i) (atomPn_irreducible i) hpnx hpny

/-- For coprime elements, at most one can be divisible by atomP1. -/
lemma areCoprime_p1 (x y : UABFailMonoid) (hxy : AreCoprime x y) :
    ¬(atomP1 ∣ x ∧ atomP1 ∣ y) := by
  intro ⟨hx, hy⟩
  exact hxy atomP1 atomP1_irreducible hx hy

/-- For coprime elements, at most one can be divisible by atomP2. -/
lemma areCoprime_p2 (x y : UABFailMonoid) (hxy : AreCoprime x y) :
    ¬(atomP2 ∣ x ∧ atomP2 ∣ y) := by
  intro ⟨hx, hy⟩
  exact hxy atomP2 atomP2_irreducible hx hy

/-- The constant function that is 1 everywhere. -/
def constOne : Fin 2 → UABFailMonoid := fun _ => 1

/-- constOne produces 1 when multiplied. -/
lemma constOne_prod : Finset.univ.prod constOne = (1 : UABFailMonoid) := by
  simp only [Fin.prod_univ_two, constOne, mul_one]

/-- For coprime x, y: if atomP1 | x then atomP1 ∤ y, so p1-component is "owned" by x. -/
lemma coprime_p1_owner (x y : UABFailMonoid) (hxy : AreCoprime x y) :
    ¬(atomP1 ∣ x ∧ atomP1 ∣ y) := areCoprime_p1 x y hxy

/-- For coprime x, y: if atomP2 | x then atomP2 ∤ y, so p2-component is "owned" by x. -/
lemma coprime_p2_owner (x y : UABFailMonoid) (hxy : AreCoprime x y) :
    ¬(atomP2 ∣ x ∧ atomP2 ∣ y) := areCoprime_p2 x y hxy

/-- For coprime x, y: if atomPn i | x then atomPn i ∤ y. -/
lemma coprime_pn_owner (x y : UABFailMonoid) (hxy : AreCoprime x y) (i : ℕ) :
    ¬(atomPn i ∣ x ∧ atomPn i ∣ y) := by
  intro ⟨hx, hy⟩
  exact hxy (atomPn i) (atomPn_irreducible i) hx hy

/-- Divisors of coprime elements are coprime. -/
lemma coprime_of_dvd_coprime (x y a b : UABFailMonoid) (hxy : AreCoprime x y)
    (ha : a ∣ x) (hb : b ∣ y) : AreCoprime a b := by
  intro p hp hpa hpb
  -- p is an irreducible dividing both a and b
  -- Since a ∣ x, we have p ∣ x
  have hpx : p ∣ x := dvd_trans hpa ha
  -- Since b ∣ y, we have p ∣ y
  have hpy : p ∣ y := dvd_trans hpb hb
  -- This contradicts AreCoprime x y
  exact hxy p hp hpx hpy

/-- If p does not divide x and a divides x, then p does not divide a. -/
lemma not_dvd_of_dvd (p x a : UABFailMonoid) (hpx : ¬p ∣ x) (ha : a ∣ x) : ¬p ∣ a := by
  intro hpa
  exact hpx (dvd_trans hpa ha)

/-- If atomP2 ∤ mk x and x.exp_p2 = 0, then x.exp_p1 < 2.
    Proof: If x.exp_p1 ≥ 2, we can find an equivalent element x' with x'.exp_p2 ≥ 1
    (by swapping 2 from exp_p1 to exp_p2), contradicting atomP2 ∤ mk x. -/
lemma exp_p1_lt_two_of_not_dvd_p2 (x : PreUABMonoid) (h_not_dvd : ¬atomP2 ∣ mk x)
    (h_exp_p2 : x.exp_p2 = 0) : x.exp_p1 < 2 := by
  by_contra h_ge
  push_neg at h_ge
  -- Construct an equivalent element with exp_p2 ≥ 1
  have hequiv : mk x = mk ⟨x.exp_p1 - 2, x.exp_p2 + 2, x.others⟩ := by
    apply Quotient.sound
    refine ⟨rfl, ?_, ?_⟩
    · simp only [h_exp_p2]; omega
    · -- Parity: x.exp_p1 % 2 = (x.exp_p1 - 2) % 2
      have hsub : x.exp_p1 - 2 + 2 = x.exp_p1 := Nat.sub_add_cancel h_ge
      calc x.exp_p1 % 2 = (x.exp_p1 - 2 + 2) % 2 := by rw [hsub]
        _ = (x.exp_p1 - 2) % 2 := by simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
  -- This element has exp_p2 = 2 ≥ 1, so atomP2 divides it
  have h_dvd : atomP2 ∣ mk ⟨x.exp_p1 - 2, x.exp_p2 + 2, x.others⟩ := by
    rw [atomP2_dvd_iff]
    use ⟨x.exp_p1 - 2, x.exp_p2 + 2, x.others⟩
    constructor
    · rfl
    · simp only [h_exp_p2]; omega
  rw [← hequiv] at h_dvd
  exact h_not_dvd h_dvd

/-- If atomP1 ∤ mk x and x.exp_p1 = 0, then x.exp_p2 < 2.
    Symmetric to exp_p1_lt_two_of_not_dvd_p2. -/
lemma exp_p2_lt_two_of_not_dvd_p1 (x : PreUABMonoid) (h_not_dvd : ¬atomP1 ∣ mk x)
    (h_exp_p1 : x.exp_p1 = 0) : x.exp_p2 < 2 := by
  by_contra h_ge
  push_neg at h_ge
  -- Construct an equivalent element with exp_p1 ≥ 1
  have hequiv : mk x = mk ⟨x.exp_p1 + 2, x.exp_p2 - 2, x.others⟩ := by
    apply Quotient.sound
    refine ⟨rfl, ?_, ?_⟩
    · simp only [h_exp_p1]; omega
    · -- Parity: x.exp_p1 % 2 = (x.exp_p1 + 2) % 2
      simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
  -- This element has exp_p1 = 2 ≥ 1, so atomP1 divides it
  have h_dvd : atomP1 ∣ mk ⟨x.exp_p1 + 2, x.exp_p2 - 2, x.others⟩ := by
    rw [atomP1_dvd_iff]
    use ⟨x.exp_p1 + 2, x.exp_p2 - 2, x.others⟩
    constructor
    · rfl
    · simp only [h_exp_p1]; omega
  rw [← hequiv] at h_dvd
  exact h_not_dvd h_dvd

/-- Key cancellation lemma: In UABFailMonoid, a * b = a * c implies b = c.
    This holds because the monoid embeds into a free abelian structure. -/
lemma mul_left_cancel (a b c : UABFailMonoid) : a * b = a * c → b = c := by
  obtain ⟨a', rfl⟩ := Quotient.exists_rep a
  obtain ⟨b', rfl⟩ := Quotient.exists_rep b
  obtain ⟨c', rfl⟩ := Quotient.exists_rep c
  rw [quot_mk_eq_mk, quot_mk_eq_mk, quot_mk_eq_mk]
  intro h
  rw [mk_mul, mk_mul] at h
  have hequiv := Quotient.exact h
  obtain ⟨hothers, htotal, hparity⟩ := hequiv
  simp only [PreUABMonoid.mul_others, PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at hothers htotal hparity
  apply Quotient.sound
  refine ⟨?_, ?_, ?_⟩
  · have h := add_left_cancel hothers; exact h
  · omega
  · omega

/-- Right cancellation. -/
lemma mul_right_cancel (a b c : UABFailMonoid) : a * c = b * c → a = b := by
  rw [mul_comm a c, mul_comm b c]
  exact mul_left_cancel c a b

/-- For coprime x, y, if a₁ * a₂ = b₁ * b₂ where a₁, b₁ share atom support with x
    and a₂, b₂ share atom support with y, then a₁ = b₁ and a₂ = b₂. -/
lemma coprime_product_unique (x y a₁ a₂ b₁ b₂ : UABFailMonoid) (_hxy : AreCoprime x y)
    (_hprod : a₁ * a₂ = b₁ * b₂) :
    -- If the products are x * y and the factorizations are "aligned" with coprimality
    -- then the factors are equal
    a₁ * a₂ = x * y → a₁ = x → a₂ = y → b₁ = x → b₂ = y →
    a₁ = b₁ ∧ a₂ = b₂ := by
  intro _ ha1 ha2 hb1 hb2
  exact ⟨ha1.trans hb1.symm, ha2.trans hb2.symm⟩

/-- A divisor of x has others support contained in x's others support. -/
lemma dvd_others_support (a x : UABFailMonoid) (hdvd : a ∣ x)
    (a' x' : PreUABMonoid) (ha' : mk a' = a) (hx' : mk x' = x) :
    ∀ j, x'.others j = 0 → a'.others j = 0 := by
  -- The proof involves showing that if a | x, then a's support is contained in x's support.
  -- This follows from the quotient structure: a * c = x means a.others + c.others ~ x.others.
  intro j hxj
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨c', hc'⟩ := Quotient.exists_rep c
  -- a * c = x means mk a' * mk c' = mk x'
  rw [← ha', ← hx'] at hc
  rw [quot_mk_eq_mk] at hc'
  rw [← hc', mk_mul] at hc
  have hequiv := Quotient.exact hc
  obtain ⟨hothers, _, _⟩ := hequiv
  -- a'.others + c'.others = x'.others
  simp only [PreUABMonoid.mul_others] at hothers
  have hj := DFunLike.congr_fun hothers j
  simp only [Finsupp.coe_add, Pi.add_apply, hxj] at hj
  omega

/-- For coprime x, y with disjoint others support, if a | x and b | y and a * b = a' * b'
    with a' | x and b' | y, then a.others = a'.others. -/
lemma coprime_dvd_others_eq (x y a b a' b' : UABFailMonoid)
    (hxy : AreCoprime x y) (hprod : a * b = a' * b')
    (ha_dvd : a ∣ x) (hb_dvd : b ∣ y) (ha'_dvd : a' ∣ x) (hb'_dvd : b' ∣ y)
    (ar br ar' br' xr yr : PreUABMonoid)
    (har : mk ar = a) (hbr : mk br = b) (har' : mk ar' = a') (hbr' : mk br' = b')
    (hxr : mk xr = x) (hyr : mk yr = y) :
    ar.others = ar'.others := by
  -- Key lemma for CFI injectivity: the "others" components are uniquely determined
  -- by the coprime structure. Since x and y have disjoint others support, and
  -- a, a' divide x while b, b' divide y, the equation a * b = a' * b' forces a.others = a'.others.
  -- From the product equation
  rw [← har, ← hbr, ← har', ← hbr', mk_mul, mk_mul] at hprod
  have hequiv := Quotient.exact hprod
  obtain ⟨hothers_eq, _, _⟩ := hequiv
  simp only [PreUABMonoid.mul_others] at hothers_eq
  -- ar.others + br.others = ar'.others + br'.others
  -- Coprimality gives disjoint support between x and y
  have hdisjoint := areCoprime_others x y hxy xr yr hxr hyr
  -- Divisibility gives support containment
  have har_support := dvd_others_support a x ha_dvd ar xr har hxr
  have hbr_support := dvd_others_support b y hb_dvd br yr hbr hyr
  have har'_support := dvd_others_support a' x ha'_dvd ar' xr har' hxr
  have hbr'_support := dvd_others_support b' y hb'_dvd br' yr hbr' hyr
  -- For each j, show ar.others j = ar'.others j
  ext j
  have hj := DFunLike.congr_fun hothers_eq j
  simp only [Finsupp.coe_add, Pi.add_apply] at hj
  rcases hdisjoint j with hxj | hyj
  · -- xr.others j = 0, so ar.others j = 0 and ar'.others j = 0
    have har_j := har_support j hxj
    have har'_j := har'_support j hxj
    omega
  · -- yr.others j = 0, so br.others j = 0 and br'.others j = 0
    have hbr_j := hbr_support j hyj
    have hbr'_j := hbr'_support j hyj
    omega

/-- For coprime x, y at the PreUABMonoid level, atoms are partitioned:
    For each index j, at most one of x.others j > 0 or y.others j > 0. -/
lemma coprime_others_disjoint (x y : UABFailMonoid) (hxy : AreCoprime x y)
    (x' y' : PreUABMonoid) (hx' : mk x' = x) (hy' : mk y' = y) :
    ∀ j, x'.others j = 0 ∨ y'.others j = 0 :=
  areCoprime_others x y hxy x' y' hx' hy'

/-- An atom dividing a product of coprime elements must divide one of them. -/
lemma atom_dvd_coprime (p x y : UABFailMonoid) (hp : p ∈ Atoms UABFailMonoid)
    (hxy : AreCoprime x y) (hpxy : p ∣ x * y) : p ∣ x ∨ p ∣ y := by
  rw [atoms_eq] at hp
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq] at hp
  rcases hp with (rfl | rfl) | ⟨m, rfl⟩
  · -- p = atomP1
    by_contra h
    push_neg at h
    obtain ⟨hnotx, hnoty⟩ := h
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    obtain ⟨y', hy'⟩ := Quotient.exists_rep y
    rw [quot_mk_eq_mk] at hx' hy'
    have hx_no : ¬∃ r, mk r = x ∧ r.exp_p1 ≥ 1 :=
      fun h => hnotx ((atomP1_dvd_iff x).mpr h)
    push_neg at hx_no
    have hx'_p1 : x'.exp_p1 = 0 := by have := hx_no x' hx'; omega
    have hy_no : ¬∃ r, mk r = y ∧ r.exp_p1 ≥ 1 :=
      fun h => hnoty ((atomP1_dvd_iff y).mpr h)
    push_neg at hy_no
    have hy'_p1 : y'.exp_p1 = 0 := by have := hy_no y' hy'; omega
    have hx'_p2_lt : x'.exp_p2 < 2 := by
      rw [← hx'] at hnotx; exact exp_p2_lt_two_of_not_dvd_p1 x' hnotx hx'_p1
    have hy'_p2_lt : y'.exp_p2 < 2 := by
      rw [← hy'] at hnoty; exact exp_p2_lt_two_of_not_dvd_p1 y' hnoty hy'_p1
    obtain ⟨r, hr, hexp⟩ := (atomP1_dvd_iff (x * y)).mp hpxy
    have hxy_rep : mk (x' * y') = x * y := by
      simp only [← hx', ← hy', mk_mul]
    have hequiv := Quotient.exact (hr.trans hxy_rep.symm)
    obtain ⟨_, htotal, hparity⟩ := hequiv
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htotal hparity
    rw [hx'_p1, hy'_p1, add_zero] at hparity
    rw [hx'_p1, hy'_p1] at htotal
    simp only [zero_add] at htotal
    have hp2x : atomP2 ∣ x := (atomP2_dvd_iff x).mpr ⟨x', hx', by omega⟩
    have hp2y : atomP2 ∣ y := (atomP2_dvd_iff y).mpr ⟨y', hy', by omega⟩
    exact hxy atomP2 atomP2_irreducible hp2x hp2y
  · -- p = atomP2 (symmetric to atomP1 case)
    by_contra h
    push_neg at h
    obtain ⟨hnotx, hnoty⟩ := h
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    obtain ⟨y', hy'⟩ := Quotient.exists_rep y
    rw [quot_mk_eq_mk] at hx' hy'
    have hx_no : ¬∃ r, mk r = x ∧ r.exp_p2 ≥ 1 :=
      fun h => hnotx ((atomP2_dvd_iff x).mpr h)
    push_neg at hx_no
    have hx'_p2 : x'.exp_p2 = 0 := by have := hx_no x' hx'; omega
    have hy_no : ¬∃ r, mk r = y ∧ r.exp_p2 ≥ 1 :=
      fun h => hnoty ((atomP2_dvd_iff y).mpr h)
    push_neg at hy_no
    have hy'_p2 : y'.exp_p2 = 0 := by have := hy_no y' hy'; omega
    have hx'_p1_lt : x'.exp_p1 < 2 := by
      rw [← hx'] at hnotx; exact exp_p1_lt_two_of_not_dvd_p2 x' hnotx hx'_p2
    have hy'_p1_lt : y'.exp_p1 < 2 := by
      rw [← hy'] at hnoty; exact exp_p1_lt_two_of_not_dvd_p2 y' hnoty hy'_p2
    obtain ⟨r, hr, hexp⟩ := (atomP2_dvd_iff (x * y)).mp hpxy
    have hxy_rep : mk (x' * y') = x * y := by
      simp only [← hx', ← hy', mk_mul]
    have hequiv := Quotient.exact (hr.trans hxy_rep.symm)
    obtain ⟨_, htotal, hparity⟩ := hequiv
    simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htotal hparity
    rw [hx'_p2, hy'_p2] at htotal
    simp only [add_zero] at htotal
    -- htotal : r.exp_p1 + r.exp_p2 = x'.exp_p1 + y'.exp_p1
    -- hparity : r.exp_p1 % 2 = (x'.exp_p1 + y'.exp_p1) % 2
    -- Combined with htotal: r.exp_p2 is even; with hexp: r.exp_p2 ≥ 2
    -- So x'.exp_p1 + y'.exp_p1 ≥ 2, with each < 2, so each ≥ 1
    have hp1x : atomP1 ∣ x := (atomP1_dvd_iff x).mpr ⟨x', hx', by omega⟩
    have hp1y : atomP1 ∣ y := (atomP1_dvd_iff y).mpr ⟨y', hy', by omega⟩
    exact hxy atomP1 atomP1_irreducible hp1x hp1y
  · -- p = atomPn m
    obtain ⟨r, hr, hexp⟩ := (atomPn_dvd_iff m (x * y)).mp hpxy
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    obtain ⟨y', hy'⟩ := Quotient.exists_rep y
    rw [quot_mk_eq_mk] at hx' hy'
    have hxy_rep : mk (x' * y') = x * y := by
      simp only [← hx', ← hy', mk_mul]
    have hequiv := Quotient.exact (hr.trans hxy_rep.symm)
    obtain ⟨hothers_eq, _, _⟩ := hequiv
    simp only [PreUABMonoid.mul_others] at hothers_eq
    have hm := DFunLike.congr_fun hothers_eq m
    simp only [Finsupp.coe_add, Pi.add_apply] at hm
    rw [hm] at hexp
    cases Nat.eq_zero_or_pos (x'.others m) with
    | inl hx0 =>
      right
      exact (atomPn_dvd_iff m y).mpr ⟨y', hy', by omega⟩
    | inr hx_pos =>
      left
      exact (atomPn_dvd_iff m x).mpr ⟨x', hx', hx_pos⟩

/-- For coprime x, y, any z dividing x*y can be split as z = a * b with a | x and b | y.
    Proved by strong induction: factor out an atom, assign it to x or y by
    atom_dvd_coprime, cancel, and recurse on the smaller remainder. -/
lemma coprime_split_exists (x y z : UABFailMonoid) (hxy : AreCoprime x y) (hz : z ∣ x * y) :
    ∃ a b, a ∣ x ∧ b ∣ y ∧ a * b = z := by
  obtain ⟨z', rfl⟩ := Quotient.exists_rep z
  rw [quot_mk_eq_mk]
  revert x y
  suffices h : ∀ n (z' : PreUABMonoid), uabSize z' = n →
      ∀ x y : UABFailMonoid, AreCoprime x y → mk z' ∣ x * y →
      ∃ a b, a ∣ x ∧ b ∣ y ∧ a * b = mk z' from
    fun x y => h (uabSize z') z' rfl x y
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z' hsize x y hxy hz
    by_cases hz_unit : IsUnit (mk z')
    · exact ⟨1, 1, one_dvd x, one_dvd y, by rw [mul_one]; exact ((isUnit_iff _).mp hz_unit).symm⟩
    · -- Factor out an atom from z' based on its representative structure
      -- Helper: given atom p, z = p * z₁, p ∣ x, recurse on z₁
      have factor_left (p : UABFailMonoid) (z₁ : PreUABMonoid) (_hp : p ∈ Atoms UABFailMonoid)
          (hfact : mk z' = p * mk z₁) (hsize₁ : uabSize z₁ < n) (hpx : p ∣ x) :
          ∃ a b, a ∣ x ∧ b ∣ y ∧ a * b = mk z' := by
        obtain ⟨x₁, hx₁⟩ := hpx
        have hz₁ : mk z₁ ∣ x₁ * y := by
          obtain ⟨w, hw⟩ := hz
          refine ⟨w, mul_left_cancel p _ _ ?_⟩
          calc p * (x₁ * y) = (p * x₁) * y := by rw [← mul_assoc]
            _ = x * y := by rw [← hx₁]
            _ = mk z' * w := hw
            _ = (p * mk z₁) * w := by rw [← hfact]
            _ = p * (mk z₁ * w) := by rw [mul_assoc]
        have hxy₁ : AreCoprime x₁ y :=
          coprime_of_dvd_coprime x y x₁ y hxy ⟨p, by rw [hx₁, mul_comm]⟩ (dvd_refl y)
        obtain ⟨a₁, b, ha₁, hb, hab⟩ := ih (uabSize z₁) hsize₁ z₁ rfl x₁ y hxy₁ hz₁
        refine ⟨p * a₁, b, ?_, hb, ?_⟩
        · obtain ⟨c, hc⟩ := ha₁
          exact ⟨c, by rw [hx₁, hc, mul_assoc]⟩
        · rw [mul_assoc, hab]; exact hfact.symm
      -- Helper: symmetric case, atom divides y
      have factor_right (p : UABFailMonoid) (z₁ : PreUABMonoid) (_hp : p ∈ Atoms UABFailMonoid)
          (hfact : mk z' = p * mk z₁) (hsize₁ : uabSize z₁ < n) (hpy : p ∣ y) :
          ∃ a b, a ∣ x ∧ b ∣ y ∧ a * b = mk z' := by
        obtain ⟨y₁, hy₁⟩ := hpy
        have hz₁ : mk z₁ ∣ x * y₁ := by
          obtain ⟨w, hw⟩ := hz
          refine ⟨w, mul_left_cancel p _ _ ?_⟩
          calc p * (x * y₁) = x * (p * y₁) := by
                rw [mul_comm p (x * y₁), mul_assoc, mul_comm y₁ p]
            _ = x * y := by rw [← hy₁]
            _ = mk z' * w := hw
            _ = (p * mk z₁) * w := by rw [← hfact]
            _ = p * (mk z₁ * w) := by rw [mul_assoc]
        have hxy₁ : AreCoprime x y₁ :=
          coprime_of_dvd_coprime x y x y₁ hxy (dvd_refl x) ⟨p, by rw [hy₁, mul_comm]⟩
        obtain ⟨a, b₁, ha, hb₁, hab⟩ := ih (uabSize z₁) hsize₁ z₁ rfl x y₁ hxy₁ hz₁
        refine ⟨a, p * b₁, ha, ?_, ?_⟩
        · obtain ⟨c, hc⟩ := hb₁
          exact ⟨c, by rw [hy₁, hc, mul_assoc]⟩
        · rw [mul_comm a (p * b₁), mul_assoc, mul_comm b₁ a, hab]; exact hfact.symm
      -- Now case-split on which component of z' is nonzero
      by_cases hp1 : z'.exp_p1 ≥ 1
      · -- Factor out atomP1
        let z₁ : PreUABMonoid := ⟨z'.exp_p1 - 1, z'.exp_p2, z'.others⟩
        have hfact : mk z' = atomP1 * mk z₁ := by
          rw [atomP1, mk_mul]; apply Quotient.sound
          refine ⟨?_, ?_, ?_⟩
          · simp only [PreUABMonoid.mul_others, PreUABMonoid.p1_others, zero_add, z₁]
          · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                PreUABMonoid.p1_exp_p1, PreUABMonoid.p1_exp_p2, z₁]; omega
          · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p1_exp_p1, z₁]; omega
        have hsize₁ : uabSize z₁ < n := by
          rw [← hsize]; unfold uabSize; simp [z₁]; omega
        have hp1_dvd : atomP1 ∣ x * y := dvd_trans ⟨mk z₁, hfact⟩ hz
        rcases atom_dvd_coprime atomP1 x y atomP1_irreducible hxy hp1_dvd with hpx | hpy
        · exact factor_left atomP1 z₁ atomP1_irreducible hfact hsize₁ hpx
        · exact factor_right atomP1 z₁ atomP1_irreducible hfact hsize₁ hpy
      · by_cases hp2 : z'.exp_p2 ≥ 1
        · -- Factor out atomP2
          let z₁ : PreUABMonoid := ⟨z'.exp_p1, z'.exp_p2 - 1, z'.others⟩
          have hfact : mk z' = atomP2 * mk z₁ := by
            rw [atomP2, mk_mul]; apply Quotient.sound
            refine ⟨?_, ?_, ?_⟩
            · simp only [PreUABMonoid.mul_others, PreUABMonoid.p2_others, zero_add, z₁]
            · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2,
                  PreUABMonoid.p2_exp_p1, PreUABMonoid.p2_exp_p2, z₁]; omega
            · simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.p2_exp_p1, z₁]; omega
          have hsize₁ : uabSize z₁ < n := by
            rw [← hsize]; unfold uabSize; simp [z₁]; omega
          have hp2_dvd : atomP2 ∣ x * y := dvd_trans ⟨mk z₁, hfact⟩ hz
          rcases atom_dvd_coprime atomP2 x y atomP2_irreducible hxy hp2_dvd with hpx | hpy
          · exact factor_left atomP2 z₁ atomP2_irreducible hfact hsize₁ hpx
          · exact factor_right atomP2 z₁ atomP2_irreducible hfact hsize₁ hpy
        · -- exp_p1 = exp_p2 = 0, factor out some atomPn
          push_neg at hp1 hp2
          have hp1_0 : z'.exp_p1 = 0 := by omega
          have hp2_0 : z'.exp_p2 = 0 := by omega
          have hf : z'.others ≠ 0 := by
            intro hf
            have h1 : mk z' = 1 := by
              apply Quotient.sound; exact ⟨hf, by simp [hp1_0, hp2_0], by simp [hp1_0]⟩
            rw [h1] at hz_unit; exact hz_unit isUnit_one
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hf
          have hi_pos : z'.others i ≥ 1 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
          let z₁ : PreUABMonoid := ⟨0, 0, z'.others - Finsupp.single i 1⟩
          have hfact : mk z' = atomPn i * mk z₁ := by
            rw [atomPn, mk_mul]; apply Quotient.sound
            refine ⟨?_, by simp [z₁, hp1_0, hp2_0], by simp [z₁, hp1_0]⟩
            ext k; simp only [PreUABMonoid.mul_others, PreUABMonoid.pn_others,
              Finsupp.coe_add, Pi.add_apply, z₁, Finsupp.coe_tsub, Pi.sub_apply]
            by_cases hki : k = i
            · subst hki; simp only [Finsupp.single_eq_same]; omega
            · simp only [Finsupp.single_eq_of_ne hki, zero_add, tsub_zero]
          have hsize₁ : uabSize z₁ < n := by
            rw [← hsize]; unfold uabSize; simp only [z₁, hp1_0, hp2_0, zero_add]
            have hsum_z : z'.others.sum (fun _ v => v) =
                z'.others.support.sum (fun j => z'.others j) := by rw [Finsupp.sum]
            have hsum_z₁ : z₁.others.sum (fun _ v => v) =
                z₁.others.support.sum (fun j => z₁.others j) := by rw [Finsupp.sum]
            rw [hsum_z, hsum_z₁]
            have hz₁_supp : z₁.others.support ⊆ z'.others.support := by
              intro j hj; rw [Finsupp.mem_support_iff] at hj ⊢
              simp only [z₁, Finsupp.coe_tsub, Pi.sub_apply] at hj
              by_contra hzj; simp only [hzj, tsub_zero] at hj
              by_cases hji : j = i
              · subst hji; simp only [Finsupp.single_eq_same] at hj; omega
              · simp only [Finsupp.single_eq_of_ne hji] at hj; exact hj rfl
            calc z₁.others.support.sum (fun j => z₁.others j)
                ≤ z'.others.support.sum (fun j => z₁.others j) :=
                  Finset.sum_le_sum_of_subset hz₁_supp
              _ < z'.others.support.sum (fun j => z'.others j) := by
                  apply Finset.sum_lt_sum
                  · intro j _; simp [z₁, Finsupp.coe_tsub, Pi.sub_apply]
                  · exact ⟨i, hi, by simp [z₁, Finsupp.coe_tsub, Pi.sub_apply,
                      Finsupp.single_eq_same]; omega⟩
          have hpn_dvd : atomPn i ∣ x * y := dvd_trans ⟨mk z₁, hfact⟩ hz
          rcases atom_dvd_coprime (atomPn i) x y (atomPn_irreducible i) hxy hpn_dvd with hpx | hpy
          · exact factor_left (atomPn i) z₁ (atomPn_irreducible i) hfact hsize₁ hpx
          · exact factor_right (atomPn i) z₁ (atomPn_irreducible i) hfact hsize₁ hpy

/-- constOne is the unique labeled factorization of 1. -/
lemma labeledFact_one_unique (f : LabeledFactorizations 2 (1 : UABFailMonoid)) :
    f = ⟨constOne, constOne_prod⟩ := by
  apply Subtype.ext
  funext i
  have hprod : f.1 0 * f.1 1 = 1 := by
    have h := f.2
    unfold LabeledFactorizations at h
    simp only [Set.mem_setOf_eq, Fin.prod_univ_two] at h
    exact h
  have hf0_unit : IsUnit (f.1 0) := by
    refine ⟨⟨f.1 0, f.1 1, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩
  have hf1_unit : IsUnit (f.1 1) := by
    refine ⟨⟨f.1 1, f.1 0, by rw [mul_comm]; exact hprod, hprod⟩, rfl⟩
  have hf0_eq := (isUnit_iff _).mp hf0_unit
  have hf1_eq := (isUnit_iff _).mp hf1_unit
  fin_cases i <;> simp [constOne, hf0_eq, hf1_eq]

/-- CFI holds: Coprime factorizations combine independently.

    For coprime x, y, the map μ : F₂(x) × F₂(y) → F₂(x*y) given by pointwise
    multiplication is a bijection.

    The proof handles several cases:
    - If x = 1: μ is essentially projection onto the y-component
    - If y = 1: symmetric case
    - If both non-units and coprime: their atom supports are disjoint, so
      factorizations split uniquely based on atom membership -/
theorem uabfail_CFI : CFI UABFailMonoid := by
  intro x y hxy
  by_cases hx : x = 1
  · -- Case x = 1: The map is essentially projection onto second component
    subst hx
    constructor
    · -- Injective
      intro ⟨f1, g1⟩ ⟨f2, g2⟩ h
      simp only [labeledFactorizationMul, Subtype.mk.injEq] at h
      have hf1_eq := labeledFact_one_unique f1
      have hf2_eq := labeledFact_one_unique f2
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
      have hgy : Finset.univ.prod g.1 = y := by
        have h := g.2
        simp only [LabeledFactorizations, Set.mem_setOf_eq, one_mul] at h
        exact h
      refine ⟨(⟨constOne, constOne_prod⟩, ⟨g.1, hgy⟩), ?_⟩
      apply Subtype.ext
      funext i
      simp only [labeledFactorizationMul, Pi.mul_apply, constOne, one_mul]
  · by_cases hy : y = 1
    · -- Case y = 1: symmetric to x = 1
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
        have hfx : Finset.univ.prod f.1 = x := by
          have h := f.2
          simp only [LabeledFactorizations, Set.mem_setOf_eq, mul_one] at h
          exact h
        refine ⟨(⟨f.1, hfx⟩, ⟨constOne, constOne_prod⟩), ?_⟩
        apply Subtype.ext
        funext i
        simp only [labeledFactorizationMul, Pi.mul_apply, constOne, mul_one]
    · -- Case both x ≠ 1 and y ≠ 1: Use coprimality structure
      -- For coprime non-units, their atom supports are disjoint.
      --
      -- **Proof strategy for CFI:**
      -- For coprime x, y, every element z can be uniquely decomposed as z = zx * zy
      -- where zx contains only "x-atoms" (atoms that divide x) and zy contains only
      -- "y-atoms" (atoms that divide y). This is because:
      -- 1. For "others" at index j: at most one of pn(j) | x or pn(j) | y (coprimality)
      -- 2. For p1/p2: coprimality ensures disjoint ownership
      --
      -- Injectivity: If f(i) * g(i) = f'(i) * g'(i), then since f(i), f'(i) factor x
      -- and g(i), g'(i) factor y, the coprime decomposition gives f(i) = f'(i) and
      -- g(i) = g'(i).
      --
      -- Surjectivity: Given h with h(0) * h(1) = x * y, we split each h(i) into
      -- f(i) * g(i) using the coprime decomposition.
      --
      -- The full proof requires significant infrastructure for the quotient structure
      -- (the p₁² = p₂² relation complicates the exp_p1/exp_p2 analysis).
      -- The key mathematical insight is correct: coprime elements have disjoint
      -- atom supports, which implies unique coprime decomposition.
      constructor
      · -- Injectivity: show f = f' and g = g' from f(i) * g(i) = f'(i) * g'(i)
        -- The key insight is that coprime x, y have disjoint atom supports,
        -- so the "x-part" of a product is uniquely determined.
        intro ⟨f, g⟩ ⟨f', g'⟩ heq
        simp only [labeledFactorizationMul, Subtype.mk.injEq] at heq
        have hf_eq : f = f' := by
          apply Subtype.ext
          funext i
          have hi := congr_fun heq i
          -- Get representatives (without rfl substitution)
          obtain ⟨fi, hfi⟩ := Quotient.exists_rep (f.1 i)
          obtain ⟨gi, hgi⟩ := Quotient.exists_rep (g.1 i)
          obtain ⟨fi', hfi'⟩ := Quotient.exists_rep (f'.1 i)
          obtain ⟨gi', hgi'⟩ := Quotient.exists_rep (g'.1 i)
          obtain ⟨x', hx'⟩ := Quotient.exists_rep x
          obtain ⟨y', hy'⟩ := Quotient.exists_rep y
          rw [quot_mk_eq_mk] at hfi hgi hfi' hgi' hx' hy'
          -- Rewrite the goal using representatives
          rw [← hfi, ← hfi']
          -- f.1 i divides x
          have hfi_dvd : mk fi ∣ x := by
            have hprod : f.1 0 * f.1 1 = x := by
              have h := f.2
              simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at h
              exact h
            rw [hfi]
            fin_cases i
            · exact ⟨f.1 1, hprod.symm⟩
            · exact ⟨f.1 0, by rw [mul_comm]; exact hprod.symm⟩
          -- g.1 i divides y
          have hgi_dvd : mk gi ∣ y := by
            have hprod : g.1 0 * g.1 1 = y := by
              have h := g.2
              simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at h
              exact h
            rw [hgi]
            fin_cases i
            · exact ⟨g.1 1, hprod.symm⟩
            · exact ⟨g.1 0, by rw [mul_comm]; exact hprod.symm⟩
          -- f'.1 i divides x
          have hfi'_dvd : mk fi' ∣ x := by
            have hprod : f'.1 0 * f'.1 1 = x := by
              have h := f'.2
              simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at h
              exact h
            rw [hfi']
            fin_cases i
            · exact ⟨f'.1 1, hprod.symm⟩
            · exact ⟨f'.1 0, by rw [mul_comm]; exact hprod.symm⟩
          -- g'.1 i divides y
          have hgi'_dvd : mk gi' ∣ y := by
            have hprod : g'.1 0 * g'.1 1 = y := by
              have h := g'.2
              simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at h
              exact h
            rw [hgi']
            fin_cases i
            · exact ⟨g'.1 1, hprod.symm⟩
            · exact ⟨g'.1 0, by rw [mul_comm]; exact hprod.symm⟩
          -- Rewrite hi using representatives
          simp only [Pi.mul_apply] at hi
          rw [← hfi, ← hgi, ← hfi', ← hgi'] at hi
          -- The "others" components are equal by coprime_dvd_others_eq
          have hothers_eq : fi.others = fi'.others :=
            coprime_dvd_others_eq x y (mk fi) (mk gi) (mk fi') (mk gi') hxy
              hi hfi_dvd hgi_dvd hfi'_dvd hgi'_dvd
              fi gi fi' gi' x' y' rfl rfl rfl rfl hx' hy'
          -- Now work on the p1/p2 components
          rw [mk_mul, mk_mul] at hi
          have heq_prod := Quotient.exact hi
          obtain ⟨h_others_prod, h_total_prod, h_parity_prod⟩ := heq_prod
          simp only [PreUABMonoid.mul_others, PreUABMonoid.mul_exp_p1,
                     PreUABMonoid.mul_exp_p2] at h_others_prod h_total_prod h_parity_prod
          -- Get the "others" equality for gi and gi'
          have hgi_others : gi.others = gi'.others := by
            have h := DFunLike.ext_iff.mp h_others_prod
            ext j
            have hj := h j
            simp only [Finsupp.coe_add, Pi.add_apply] at hj
            have hfij : fi.others j = fi'.others j := DFunLike.congr_fun hothers_eq j
            omega
          -- Get divisibility constraints on p1/p2 components
          have hdisjoint := coprime_others_disjoint x y hxy x' y' hx' hy'
          -- Coprimality tells us at most one of x, y has p1/p2 atoms
          -- Use this to determine the total and parity
          apply Quotient.sound
          refine ⟨hothers_eq, ?_, ?_⟩
          · -- Total: fi.exp_p1 + fi.exp_p2 = fi'.exp_p1 + fi'.exp_p2
            -- Key: coprimality means divisors of x and y have constrained p1/p2 totals
            -- From the product equation and gi.others = gi'.others, we can derive this
            -- Use dvd_others_support to get support containment
            have hfi_support := dvd_others_support (mk fi) x hfi_dvd fi x' rfl hx'
            have hgi_support := dvd_others_support (mk gi) y hgi_dvd gi y' rfl hy'
            have hfi'_support := dvd_others_support (mk fi') x hfi'_dvd fi' x' rfl hx'
            have hgi'_support := dvd_others_support (mk gi') y hgi'_dvd gi' y' rfl hy'
            -- For the p1/p2 total, analyze based on which of x, y has p1/p2 atoms
            by_cases hp1x : atomP1 ∣ x
            · have hp1y := areCoprime_p1 x y hxy
              push_neg at hp1y
              have hp1_not_y := hp1y hp1x
              -- y has no p1-divisibility, so divisors of y have 0 p1+p2 total (relative to y)
              -- Actually, we need a more direct argument
              -- From coprimality: gi and gi' divide y which is coprime to x
              -- The key is that the total is determined by the product equation
              by_cases hp2x : atomP2 ∣ x
              · have hp2y := areCoprime_p2 x y hxy
                push_neg at hp2y
                have hp2_not_y := hp2y hp2x
                -- y has neither p1 nor p2, so y's p1/p2 total is 0
                -- This means gi and gi' have 0 total (in the y-contribution sense)
                -- From h_total_prod: fi.total + gi.total = fi'.total + gi'.total
                -- We need to show fi.total = fi'.total
                -- Use that y has no p1/p2: any divisor of y has 0 p1/p2 contribution
                rw [← hy'] at hp1_not_y hp2_not_y
                have hy'_no_p1 : ¬(∃ yr : PreUABMonoid, mk yr = mk y' ∧ yr.exp_p1 ≥ 1) :=
                  fun h => hp1_not_y ((atomP1_dvd_iff (mk y')).mpr h)
                have hy'_no_p2 : ¬(∃ yr : PreUABMonoid, mk yr = mk y' ∧ yr.exp_p2 ≥ 1) :=
                  fun h => hp2_not_y ((atomP2_dvd_iff (mk y')).mpr h)
                push_neg at hy'_no_p1 hy'_no_p2
                have hy'_p1 := hy'_no_p1 y' rfl
                have hy'_p2 := hy'_no_p2 y' rfl
                simp only [not_le, Nat.lt_one_iff] at hy'_p1 hy'_p2
                -- y' has exp_p1 = 0 and exp_p2 = 0
                -- gi divides y = mk y', so gi * c ~ y' for some c
                -- This means gi.total + c.total = y'.total = 0, so gi.total = 0
                obtain ⟨cgi, hcgi⟩ := hgi_dvd
                obtain ⟨cgir, rfl⟩ := Quotient.exists_rep cgi
                rw [quot_mk_eq_mk, mk_mul, ← hy'] at hcgi
                have heq_gi := Quotient.exact hcgi
                obtain ⟨_, htot_gi, _⟩ := heq_gi
                simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htot_gi
                obtain ⟨cgi', hcgi'⟩ := hgi'_dvd
                obtain ⟨cgi'r, rfl⟩ := Quotient.exists_rep cgi'
                rw [quot_mk_eq_mk, mk_mul, ← hy'] at hcgi'
                have heq_gi' := Quotient.exact hcgi'
                obtain ⟨_, htot_gi', _⟩ := heq_gi'
                simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htot_gi'
                omega
              · -- x has p1 but not p2: x has total = 1, parity = 1
                -- So fi, fi' have exp_p1 ∈ {0, 1} and exp_p2 = 0
                -- Parity constraint determines equality
                -- atomP2 ∤ x, so fi.exp_p2 = 0 = fi'.exp_p2
                have hfi_no_p2 := not_dvd_of_dvd atomP2 x (mk fi) hp2x hfi_dvd
                have hfi'_no_p2 := not_dvd_of_dvd atomP2 x (mk fi') hp2x hfi'_dvd
                have hfi_no_p2' : ¬∃ r, mk r = mk fi ∧ r.exp_p2 ≥ 1 :=
                  fun h => hfi_no_p2 ((atomP2_dvd_iff (mk fi)).mpr h)
                have hfi'_no_p2' : ¬∃ r, mk r = mk fi' ∧ r.exp_p2 ≥ 1 :=
                  fun h => hfi'_no_p2 ((atomP2_dvd_iff (mk fi')).mpr h)
                push_neg at hfi_no_p2' hfi'_no_p2'
                have hfi_p2 := hfi_no_p2' fi rfl
                have hfi'_p2 := hfi'_no_p2' fi' rfl
                simp only [not_le, Nat.lt_one_iff] at hfi_p2 hfi'_p2
                -- atomP1 ∤ y, so gi.exp_p1 = 0 = gi'.exp_p1
                have hgi_no_p1 := not_dvd_of_dvd atomP1 y (mk gi) hp1_not_y hgi_dvd
                have hgi'_no_p1 := not_dvd_of_dvd atomP1 y (mk gi') hp1_not_y hgi'_dvd
                have hgi_no_p1' : ¬∃ r, mk r = mk gi ∧ r.exp_p1 ≥ 1 :=
                  fun h => hgi_no_p1 ((atomP1_dvd_iff (mk gi)).mpr h)
                have hgi'_no_p1' : ¬∃ r, mk r = mk gi' ∧ r.exp_p1 ≥ 1 :=
                  fun h => hgi'_no_p1 ((atomP1_dvd_iff (mk gi')).mpr h)
                push_neg at hgi_no_p1' hgi'_no_p1'
                have hgi_p1 := hgi_no_p1' gi rfl
                have hgi'_p1 := hgi'_no_p1' gi' rfl
                simp only [not_le, Nat.lt_one_iff] at hgi_p1 hgi'_p1
                -- fi.exp_p2 = 0, fi'.exp_p2 = 0, gi.exp_p1 = 0, gi'.exp_p1 = 0
                -- Total: fi.exp_p1 + gi.exp_p2 = fi'.exp_p1 + gi'.exp_p2
                -- Parity: fi.exp_p1 % 2 = fi'.exp_p1 % 2
                -- Combined with the constraint that fi.exp_p1 ∈ {0,1} (from x's structure),
                -- parity determines equality
                -- Use helper lemma: atomP2 ∤ mk fi and fi.exp_p2 = 0 implies fi.exp_p1 < 2
                have hfi_exp_p1_lt : fi.exp_p1 < 2 := exp_p1_lt_two_of_not_dvd_p2 fi hfi_no_p2 hfi_p2
                have hfi'_exp_p1_lt : fi'.exp_p1 < 2 := exp_p1_lt_two_of_not_dvd_p2 fi' hfi'_no_p2 hfi'_p2
                -- fi.exp_p1, fi'.exp_p1 ∈ {0, 1}, same parity → equal
                have hfi_parity : fi.exp_p1 % 2 = fi'.exp_p1 % 2 := by
                  simp only [hgi_p1, hgi'_p1, add_zero] at h_parity_prod
                  exact h_parity_prod
                -- Both < 2 and same parity means equal
                interval_cases fi.exp_p1 <;> interval_cases fi'.exp_p1 <;> simp_all
            · by_cases hp2x : atomP2 ∣ x
              · -- x has p2 but not p1: symmetric to above
                have hp2y := areCoprime_p2 x y hxy
                push_neg at hp2y
                have hp2_not_y := hp2y hp2x
                -- atomP1 ∤ x, so fi.exp_p1 = 0 = fi'.exp_p1
                have hfi_no_p1 := not_dvd_of_dvd atomP1 x (mk fi) hp1x hfi_dvd
                have hfi'_no_p1 := not_dvd_of_dvd atomP1 x (mk fi') hp1x hfi'_dvd
                have hfi_no_p1' : ¬∃ r, mk r = mk fi ∧ r.exp_p1 ≥ 1 :=
                  fun h => hfi_no_p1 ((atomP1_dvd_iff (mk fi)).mpr h)
                have hfi'_no_p1' : ¬∃ r, mk r = mk fi' ∧ r.exp_p1 ≥ 1 :=
                  fun h => hfi'_no_p1 ((atomP1_dvd_iff (mk fi')).mpr h)
                push_neg at hfi_no_p1' hfi'_no_p1'
                have hfi_p1 := hfi_no_p1' fi rfl
                have hfi'_p1 := hfi'_no_p1' fi' rfl
                simp only [not_le, Nat.lt_one_iff] at hfi_p1 hfi'_p1
                -- atomP2 ∤ y, so gi.exp_p2 = 0 = gi'.exp_p2
                have hgi_no_p2 := not_dvd_of_dvd atomP2 y (mk gi) hp2_not_y hgi_dvd
                have hgi'_no_p2 := not_dvd_of_dvd atomP2 y (mk gi') hp2_not_y hgi'_dvd
                have hgi_no_p2' : ¬∃ r, mk r = mk gi ∧ r.exp_p2 ≥ 1 :=
                  fun h => hgi_no_p2 ((atomP2_dvd_iff (mk gi)).mpr h)
                have hgi'_no_p2' : ¬∃ r, mk r = mk gi' ∧ r.exp_p2 ≥ 1 :=
                  fun h => hgi'_no_p2 ((atomP2_dvd_iff (mk gi')).mpr h)
                push_neg at hgi_no_p2' hgi'_no_p2'
                have hgi_p2 := hgi_no_p2' gi rfl
                have hgi'_p2 := hgi'_no_p2' gi' rfl
                simp only [not_le, Nat.lt_one_iff] at hgi_p2 hgi'_p2
                -- Symmetric case: fi.exp_p1 = fi'.exp_p1 = 0, gi.exp_p2 = gi'.exp_p2 = 0
                -- Use helper lemma: atomP2 ∤ mk gi and gi.exp_p2 = 0 implies gi.exp_p1 < 2
                have hgi_exp_p1_lt : gi.exp_p1 < 2 := exp_p1_lt_two_of_not_dvd_p2 gi hgi_no_p2 hgi_p2
                have hgi'_exp_p1_lt : gi'.exp_p1 < 2 := exp_p1_lt_two_of_not_dvd_p2 gi' hgi'_no_p2 hgi'_p2
                -- Parity constraint after substitution: gi.exp_p1 % 2 = gi'.exp_p1 % 2
                have hgi_parity : gi.exp_p1 % 2 = gi'.exp_p1 % 2 := by
                  simp only [hfi_p1, hfi'_p1, zero_add] at h_parity_prod
                  exact h_parity_prod
                -- Both < 2 and same parity means gi.exp_p1 = gi'.exp_p1
                have hgi_exp_eq : gi.exp_p1 = gi'.exp_p1 := by
                  interval_cases gi.exp_p1 <;> interval_cases gi'.exp_p1 <;> simp_all
                -- Now from total constraint: gi.exp_p1 + fi.exp_p2 = gi'.exp_p1 + fi'.exp_p2
                -- Since gi.exp_p1 = gi'.exp_p1, we get fi.exp_p2 = fi'.exp_p2
                simp only [hfi_p1, hfi'_p1, hgi_p2, hgi'_p2, zero_add, add_zero] at h_total_prod
                omega
              · -- x has neither p1 nor p2
                rw [← hx'] at hp1x hp2x
                have hx'_no_p1 : ¬(∃ xr : PreUABMonoid, mk xr = mk x' ∧ xr.exp_p1 ≥ 1) :=
                  fun h => hp1x ((atomP1_dvd_iff (mk x')).mpr h)
                have hx'_no_p2 : ¬(∃ xr : PreUABMonoid, mk xr = mk x' ∧ xr.exp_p2 ≥ 1) :=
                  fun h => hp2x ((atomP2_dvd_iff (mk x')).mpr h)
                push_neg at hx'_no_p1 hx'_no_p2
                have hx'_p1 := hx'_no_p1 x' rfl
                have hx'_p2 := hx'_no_p2 x' rfl
                simp only [not_le, Nat.lt_one_iff] at hx'_p1 hx'_p2
                -- x' has exp_p1 = 0 and exp_p2 = 0
                obtain ⟨cfi, hcfi⟩ := hfi_dvd
                obtain ⟨cfir, rfl⟩ := Quotient.exists_rep cfi
                rw [quot_mk_eq_mk, mk_mul, ← hx'] at hcfi
                have heq_fi := Quotient.exact hcfi
                obtain ⟨_, htot_fi, _⟩ := heq_fi
                simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htot_fi
                obtain ⟨cfi', hcfi'⟩ := hfi'_dvd
                obtain ⟨cfi'r, rfl⟩ := Quotient.exists_rep cfi'
                rw [quot_mk_eq_mk, mk_mul, ← hx'] at hcfi'
                have heq_fi' := Quotient.exact hcfi'
                obtain ⟨_, htot_fi', _⟩ := heq_fi'
                simp only [PreUABMonoid.mul_exp_p1, PreUABMonoid.mul_exp_p2] at htot_fi'
                omega
          · -- Parity: fi.exp_p1 % 2 = fi'.exp_p1 % 2
            by_cases hp1x : atomP1 ∣ x
            · have hp1y := areCoprime_p1 x y hxy
              push_neg at hp1y
              have hp1_not_y := hp1y hp1x
              -- Save original before rewriting for later use
              have hp1_not_y_orig : ¬atomP1 ∣ y := hp1_not_y
              rw [← hy'] at hp1_not_y
              have hy'_no_p1 : ¬(∃ yr : PreUABMonoid, mk yr = mk y' ∧ yr.exp_p1 ≥ 1) :=
                fun h => hp1_not_y ((atomP1_dvd_iff (mk y')).mpr h)
              push_neg at hy'_no_p1
              have hy'_p1 := hy'_no_p1 y' rfl
              simp only [not_le, Nat.lt_one_iff] at hy'_p1
              -- y' has exp_p1 = 0, so gi, gi' have exp_p1 = 0
              -- Key insight: atomP1 ∤ y, and gi | y, so atomP1 ∤ mk gi
              -- This means ALL representatives of mk gi have exp_p1 = 0
              have hgi_no_p1 := not_dvd_of_dvd atomP1 y (mk gi) hp1_not_y_orig hgi_dvd
              have hgi'_no_p1 := not_dvd_of_dvd atomP1 y (mk gi') hp1_not_y_orig hgi'_dvd
              have hgi_no_p1' : ¬∃ r, mk r = mk gi ∧ r.exp_p1 ≥ 1 :=
                fun h => hgi_no_p1 ((atomP1_dvd_iff (mk gi)).mpr h)
              have hgi'_no_p1' : ¬∃ r, mk r = mk gi' ∧ r.exp_p1 ≥ 1 :=
                fun h => hgi'_no_p1 ((atomP1_dvd_iff (mk gi')).mpr h)
              push_neg at hgi_no_p1' hgi'_no_p1'
              have hgi_p1 := hgi_no_p1' gi rfl
              have hgi'_p1 := hgi'_no_p1' gi' rfl
              simp only [not_le, Nat.lt_one_iff] at hgi_p1 hgi'_p1
              -- Now gi.exp_p1 = gi'.exp_p1 = 0, so h_parity_prod gives fi.exp_p1 % 2 = fi'.exp_p1 % 2
              simp only [hgi_p1, hgi'_p1, add_zero] at h_parity_prod
              exact h_parity_prod
            · -- Save original before rewriting for later use
              have hp1x_orig : ¬atomP1 ∣ x := hp1x
              rw [← hx'] at hp1x
              have hx'_no_p1 : ¬(∃ xr : PreUABMonoid, mk xr = mk x' ∧ xr.exp_p1 ≥ 1) :=
                fun h => hp1x ((atomP1_dvd_iff (mk x')).mpr h)
              push_neg at hx'_no_p1
              have hx'_p1 := hx'_no_p1 x' rfl
              simp only [not_le, Nat.lt_one_iff] at hx'_p1
              -- x' has exp_p1 = 0, so fi, fi' have exp_p1 = 0
              -- Key insight: atomP1 ∤ x, and fi | x, so atomP1 ∤ mk fi
              -- This means ALL representatives of mk fi have exp_p1 = 0
              have hfi_no_p1 := not_dvd_of_dvd atomP1 x (mk fi) hp1x_orig hfi_dvd
              have hfi'_no_p1 := not_dvd_of_dvd atomP1 x (mk fi') hp1x_orig hfi'_dvd
              have hfi_no_p1' : ¬∃ r, mk r = mk fi ∧ r.exp_p1 ≥ 1 :=
                fun h => hfi_no_p1 ((atomP1_dvd_iff (mk fi)).mpr h)
              have hfi'_no_p1' : ¬∃ r, mk r = mk fi' ∧ r.exp_p1 ≥ 1 :=
                fun h => hfi'_no_p1 ((atomP1_dvd_iff (mk fi')).mpr h)
              push_neg at hfi_no_p1' hfi'_no_p1'
              have hfi_p1 := hfi_no_p1' fi rfl
              have hfi'_p1 := hfi'_no_p1' fi' rfl
              simp only [not_le, Nat.lt_one_iff] at hfi_p1 hfi'_p1
              -- Now fi.exp_p1 = fi'.exp_p1 = 0, so parity constraint is satisfied trivially
              simp only [hfi_p1, hfi'_p1]
        have hg_eq : g = g' := by
          apply Subtype.ext
          funext i
          have hi := congr_fun heq i
          rw [hf_eq] at hi
          exact mul_left_cancel (f'.1 i) (g.1 i) (g'.1 i) hi
        simp only [Prod.mk.injEq]
        exact ⟨hf_eq, hg_eq⟩
      · -- Surjectivity
        intro h
        -- h(0) * h(1) = x * y
        have hprod_xy : h.1 0 * h.1 1 = x * y := by
          have := h.2; simp only [LabeledFactorizations, Set.mem_setOf_eq,
            Fin.prod_univ_two] at this; exact this
        -- h(0) ∣ x * y
        have h0_dvd : h.1 0 ∣ x * y := ⟨h.1 1, hprod_xy.symm⟩
        -- Split h(0) = f₀ * g₀ with f₀ ∣ x, g₀ ∣ y
        obtain ⟨f₀, g₀, hf₀, hg₀, hfg₀⟩ := coprime_split_exists x y (h.1 0) hxy h0_dvd
        -- Get cofactors: x = f₀ * x₁, y = g₀ * y₁
        obtain ⟨x₁, hx₁⟩ := hf₀
        obtain ⟨y₁, hy₁⟩ := hg₀
        -- Show h(1) = x₁ * y₁ by cancellation
        have h1_eq : h.1 1 = x₁ * y₁ := by
          apply mul_left_cancel (f₀ * g₀)
          calc (f₀ * g₀) * h.1 1 = h.1 0 * h.1 1 := by rw [hfg₀]
            _ = x * y := hprod_xy
            _ = (f₀ * x₁) * (g₀ * y₁) := by rw [hx₁, hy₁]
            _ = (f₀ * g₀) * (x₁ * y₁) := mul_mul_mul_comm f₀ x₁ g₀ y₁
        -- Construct preimage
        let fv : Fin 2 → UABFailMonoid := ![f₀, x₁]
        let gv : Fin 2 → UABFailMonoid := ![g₀, y₁]
        have hfv_prod : Finset.univ.prod fv = x := by
          simp [Fin.prod_univ_two, fv, hx₁]
        have hgv_prod : Finset.univ.prod gv = y := by
          simp [Fin.prod_univ_two, gv, hy₁]
        refine ⟨(⟨fv, hfv_prod⟩, ⟨gv, hgv_prod⟩), ?_⟩
        apply Subtype.ext; funext i; fin_cases i <;>
          simp [labeledFactorizationMul, fv, gv, hfg₀, h1_eq]

/-- CPL holds: atoms p₃, p₄, ... give arbitrarily long coprime tuples. -/
theorem uabfail_CPL : CPL UABFailMonoid := by
  intro r
  use List.ofFn (fun i : Fin r => atomPn i.val)
  constructor
  · simp
  constructor
  · intro x hx
    simp at hx
    obtain ⟨i, rfl⟩ := hx
    exact atomPn_not_isUnit i.val
  · rw [List.pairwise_iff_get]
    intro i j hij
    simp
    intro p hp hdvd_i hdvd_j
    rw [atoms_eq] at hp
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq] at hp
    rcases hp with (rfl | rfl) | ⟨m, rfl⟩
    · -- p = atomP1
      have ⟨c', hc', hexp⟩ := (atomP1_dvd_iff _).mp hdvd_i
      have hequiv := Quotient.exact hc'
      obtain ⟨hothers, htotal, _⟩ := hequiv
      simp only [PreUABMonoid.pn_others, PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2] at hothers htotal
      omega
    · -- p = atomP2
      have ⟨c', hc', hexp⟩ := (atomP2_dvd_iff _).mp hdvd_i
      have hequiv := Quotient.exact hc'
      obtain ⟨hothers, htotal, _⟩ := hequiv
      simp only [PreUABMonoid.pn_others, PreUABMonoid.pn_exp_p1, PreUABMonoid.pn_exp_p2] at hothers htotal
      omega
    · -- p = atomPn m
      have ⟨c1', hc1', hexp1⟩ := (atomPn_dvd_iff m _).mp hdvd_i
      have ⟨c2', hc2', hexp2⟩ := (atomPn_dvd_iff m _).mp hdvd_j
      have hequiv1 := Quotient.exact hc1'
      have hequiv2 := Quotient.exact hc2'
      obtain ⟨hothers1, _, _⟩ := hequiv1
      obtain ⟨hothers2, _, _⟩ := hequiv2
      simp only [PreUABMonoid.pn_others] at hothers1 hothers2
      have hm_i : m = i.val := by
        by_contra hmi
        have := DFunLike.congr_fun hothers1 m
        simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hmi] at this
        omega
      have hm_j : m = j.val := by
        by_contra hmj
        have := DFunLike.congr_fun hothers2 m
        simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hmj] at this
        omega
      have hcontra : i.val = j.val := hm_i.symm.trans hm_j
      omega

end UABFailMonoid

end
