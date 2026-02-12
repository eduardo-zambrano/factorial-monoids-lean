/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d37149b9-f4ab-4268-854d-ccb02751c22f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem collapsing_CFI : CFI CollapsingMonoid
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Example 4: The Collapsing Monoid (Failure of PP-D only)

This file formalizes a REVISED version of Example 10.2 from Section 10 of the paper.

The original example used p₁² = p₁, but this makes p₁ idempotent and thus NOT irreducible
(since p₁ = p₁ * p₁ with neither factor a unit).

**Revised construction:** Use the relation p₁² = p₁³ instead.
- This keeps p₁ irreducible (p₁ has exponent 1, any non-trivial factorization would need exponent ≥ 2)
- PP-D fails: p₁² = p₁³ violates injectivity of the power map
- The monoid is atomic: every element has finite atomic factorization
- APD, CFI, CPL hold for the other atoms p₂, p₃, ...

## Main Results

- `CollapsingMonoid`: The collapsing monoid with p₁² = p₁³
- `collapsing_reduced`: The monoid is reduced
- `collapsing_atomic`: The monoid is atomic
- `collapsing_APD`: The monoid satisfies APD
- `collapsing_not_PPD`: The monoid does NOT satisfy PP-D
- `collapsing_CFI`: The monoid satisfies CFI
- `collapsing_CPL`: The monoid satisfies CPL
-/

import MultiplicationProject.Basic
import Mathlib.Data.Finsupp.Basic


open scoped Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## The Collapsing Monoid Structure

Elements are pairs (e₁, f) where:
- e₁ ∈ {0, 1, 2} is the canonical exponent of p₁ (all higher powers collapse to 2)
- f : ℕ →₀ ℕ tracks exponents of atoms p₂, p₃, ... (index n corresponds to p_{n+2})

Multiplication: (e₁, f₁) * (e₂, f₂) = (min(e₁ + e₂, 2), f₁ + f₂)
Identity: (0, 0)

The relation p₁² = p₁³ is encoded by capping e₁ at 2.
-/

/-- The collapsing monoid with relation p₁² = p₁³. -/
structure CollapsingMonoid where
  /-- Canonical exponent of p₁: 0, 1, or 2 (higher powers collapse to 2) -/
  exp_p1 : Fin 3
  /-- Exponents of atoms p₂, p₃, ... -/
  exponents : ℕ →₀ ℕ
  deriving DecidableEq

namespace CollapsingMonoid

/-- Extensionality. -/
@[ext]
lemma ext {x y : CollapsingMonoid} (h1 : x.exp_p1 = y.exp_p1)
    (h2 : x.exponents = y.exponents) : x = y := by
  cases x; cases y; simp at h1 h2; simp [h1, h2]

/-- Extensionality via values. -/
lemma ext' {x y : CollapsingMonoid} (h1 : x.exp_p1.val = y.exp_p1.val)
    (h2 : x.exponents = y.exponents) : x = y := by
  apply ext
  · exact Fin.ext h1
  · exact h2

/-- The identity element. -/
protected def one : CollapsingMonoid := ⟨0, 0⟩

/-- Multiplication: add exponents, capping p₁ exponent at 2. -/
protected def mul (x y : CollapsingMonoid) : CollapsingMonoid :=
  ⟨⟨min (x.exp_p1.val + y.exp_p1.val) 2, by omega⟩, x.exponents + y.exponents⟩

instance : One CollapsingMonoid := ⟨CollapsingMonoid.one⟩

instance : Mul CollapsingMonoid := ⟨CollapsingMonoid.mul⟩

@[simp]
lemma one_exp_p1 : (1 : CollapsingMonoid).exp_p1 = 0 := rfl

@[simp]
lemma one_exp_p1_val : (1 : CollapsingMonoid).exp_p1.val = 0 := rfl

@[simp]
lemma one_exponents : (1 : CollapsingMonoid).exponents = 0 := rfl

@[simp]
lemma mul_exp_p1 (x y : CollapsingMonoid) :
    (x * y).exp_p1.val = min (x.exp_p1.val + y.exp_p1.val) 2 := rfl

@[simp]
lemma mul_exponents (x y : CollapsingMonoid) :
    (x * y).exponents = x.exponents + y.exponents := rfl

/-- The collapsing monoid is a commutative monoid. -/
instance : CommMonoid CollapsingMonoid where
  mul := (· * ·)
  mul_assoc := by
    intros a b c
    apply ext'
    · simp only [mul_exp_p1]; omega
    · simp only [mul_exponents, add_assoc]
  one := 1
  one_mul := by
    intro a
    apply ext'
    · simp only [mul_exp_p1, one_exp_p1_val, zero_add, min_eq_left_iff]
      exact Nat.le_of_lt_succ a.exp_p1.isLt
    · simp only [mul_exponents, one_exponents, zero_add]
  mul_one := by
    intro a
    apply ext'
    · simp only [mul_exp_p1, one_exp_p1_val, add_zero, min_eq_left_iff]
      exact Nat.le_of_lt_succ a.exp_p1.isLt
    · simp only [mul_exponents, one_exponents, add_zero]
  mul_comm := by
    intros a b
    apply ext'
    · simp only [mul_exp_p1]; omega
    · simp only [mul_exponents, add_comm]

/-!
## Atoms

- p₁ = ⟨1, 0⟩ (the collapsing atom)
- p_{n+2} = ⟨0, Finsupp.single n 1⟩ for n ∈ ℕ
-/

/-- The collapsing atom p₁. -/
def p1 : CollapsingMonoid := ⟨1, 0⟩

/-- The regular atom p_{n+2}. -/
def pn (n : ℕ) : CollapsingMonoid := ⟨0, Finsupp.single n 1⟩

@[simp] lemma p1_exp_p1 : p1.exp_p1 = 1 := rfl

@[simp] lemma p1_exp_p1_val : p1.exp_p1.val = 1 := rfl

@[simp] lemma p1_exponents : p1.exponents = 0 := rfl

@[simp] lemma pn_exp_p1 (n : ℕ) : (pn n).exp_p1 = 0 := rfl

@[simp] lemma pn_exp_p1_val (n : ℕ) : (pn n).exp_p1.val = 0 := rfl

@[simp] lemma pn_exponents (n : ℕ) : (pn n).exponents = Finsupp.single n 1 := rfl

/-- The key relation: p₁² = p₁³. -/
lemma p1_sq_eq_p1_cubed : p1 * p1 = p1 * p1 * p1 := by
  apply ext' <;> simp

/-- Powers of p₁: p₁^n = ⟨min(n, 2), 0⟩. -/
lemma pow_p1 (n : ℕ) : p1 ^ n = ⟨⟨min n 2, by omega⟩, 0⟩ := by
  induction n with
  | zero => apply ext' <;> simp [pow_zero]
  | succ m ih =>
    rw [pow_succ, ih]
    apply ext'
    · simp only [mul_exp_p1, p1_exp_p1_val, Fin.val_mk]; omega
    · simp only [mul_exponents, p1_exponents, add_zero]

/-- Powers of pn: pn(m)^k = ⟨0, Finsupp.single m k⟩. -/
lemma pow_pn (m k : ℕ) : pn m ^ k = ⟨0, Finsupp.single m k⟩ := by
  induction k with
  | zero =>
    apply ext'
    · simp [pow_zero]
    · simp [pow_zero, Finsupp.single_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    apply ext'
    · simp
    · simp only [mul_exponents, pn_exponents, ← Finsupp.single_add, add_comm]

/-!
## Units
-/

/-- Helper lemma for Finsupp. -/
lemma finsupp_add_eq_zero_iff {a b : ℕ →₀ ℕ} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · ext i
      have hi : a i + b i = 0 := DFunLike.congr_fun h i
      have : a i = 0 := Nat.eq_zero_of_add_eq_zero_right hi
      exact this
    · ext i
      have hi : a i + b i = 0 := DFunLike.congr_fun h i
      have : b i = 0 := Nat.eq_zero_of_add_eq_zero_left hi
      exact this
  · intro ⟨ha, hb⟩
    simp [ha, hb]

/-- Only 1 is a unit. -/
lemma isUnit_iff (x : CollapsingMonoid) : IsUnit x ↔ x = 1 := by
  constructor
  · intro ⟨u, hu⟩
    have h := u.val_inv
    have h1_val : (u.val * u.inv).exp_p1.val = 0 := by rw [h]; rfl
    have h2 : (u.val * u.inv).exponents = 0 := by rw [h]; rfl
    simp only [mul_exp_p1, mul_exponents] at h1_val h2
    have hval_exp : u.val.exp_p1.val = 0 := by omega
    have hval_f : u.val.exponents = 0 := (finsupp_add_eq_zero_iff.mp h2).1
    rw [← hu]
    apply ext' hval_exp hval_f
  · intro hx
    rw [hx]
    exact isUnit_one

/-- The collapsing monoid is reduced. -/
theorem collapsing_reduced : Reduced CollapsingMonoid := by
  intro x hx
  exact (isUnit_iff x).mp hx

/-!
## Irreducibility
-/

/-- p₁ is not a unit. -/
lemma p1_not_isUnit : ¬IsUnit p1 := by
  intro h
  have := (isUnit_iff p1).mp h
  have hcontra : (1 : Fin 3) = 0 := congrArg exp_p1 this
  simp at hcontra

/-- pn(m) is not a unit. -/
lemma pn_not_isUnit (m : ℕ) : ¬IsUnit (pn m) := by
  intro h
  have := (isUnit_iff (pn m)).mp h
  have hexp : Finsupp.single m 1 = (0 : ℕ →₀ ℕ) := congrArg exponents this
  have hcontra : (Finsupp.single m 1) m = 0 := DFunLike.congr_fun hexp m
  simp at hcontra

/-- p₁ is irreducible. -/
lemma p1_irreducible : Irreducible p1 := by
  constructor
  · exact p1_not_isUnit
  · intros a b hab
    have h1 : (a * b).exp_p1 = 1 := hab ▸ rfl
    have h2 : (a * b).exponents = 0 := hab ▸ rfl
    simp only [mul_exp_p1, mul_exponents] at h1 h2
    have ⟨ha_f, hb_f⟩ := finsupp_add_eq_zero_iff.mp h2
    have hsum : min (a.exp_p1.val + b.exp_p1.val) 2 = 1 := by
      have := congrArg (fun x => x.val) h1
      simp at this
      exact this
    have hab_sum : a.exp_p1.val + b.exp_p1.val = 1 := by omega
    cases Nat.eq_zero_or_pos a.exp_p1.val with
    | inl ha =>
      left
      rw [isUnit_iff]
      apply ext' ha ha_f
    | inr ha =>
      have hb : b.exp_p1.val = 0 := by omega
      right
      rw [isUnit_iff]
      apply ext' hb hb_f

/-- pn(m) is irreducible. -/
lemma pn_irreducible (m : ℕ) : Irreducible (pn m) := by
  constructor
  · exact pn_not_isUnit m
  · intros a b hab
    have h1 : (a * b).exp_p1 = 0 := hab ▸ rfl
    have h2 : (a * b).exponents = Finsupp.single m 1 := hab ▸ rfl
    simp only [mul_exp_p1, mul_exponents] at h1 h2
    have ha_exp : a.exp_p1.val = 0 := by
      have := congrArg (fun x => x.val) h1
      simp at this; omega
    have hb_exp : b.exp_p1.val = 0 := by
      have := congrArg (fun x => x.val) h1
      simp at this; omega
    by_cases ha_zero : a.exponents = 0
    · left
      rw [isUnit_iff]
      apply ext' ha_exp ha_zero
    · by_cases hb_zero : b.exponents = 0
      · right
        rw [isUnit_iff]
        apply ext' hb_exp hb_zero
      · exfalso
        have ha_supp := Finsupp.support_nonempty_iff.mpr ha_zero
        obtain ⟨i, hi⟩ := ha_supp
        have hi_pos : 0 < a.exponents i := Finsupp.mem_support_iff.mp hi |> Nat.pos_of_ne_zero
        have hsum_i : a.exponents i + b.exponents i = (Finsupp.single m 1) i :=
          DFunLike.congr_fun h2 i
        by_cases him : i = m
        · subst him
          simp only [Finsupp.single_eq_same] at hsum_i
          have hb_supp := Finsupp.support_nonempty_iff.mpr hb_zero
          obtain ⟨j, hj⟩ := hb_supp
          have hj_pos : 0 < b.exponents j := Finsupp.mem_support_iff.mp hj |> Nat.pos_of_ne_zero
          by_cases hjm : j = i
          · subst hjm; omega
          · have hsum_j : a.exponents j + b.exponents j = 0 := by
              have := DFunLike.congr_fun h2 j
              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hjm] at this
              exact this
            omega
        · simp only [Finsupp.single_eq_of_ne him] at hsum_i
          omega

/-- The atoms are p₁ and {pn(m) : m ∈ ℕ}. -/
lemma atoms_eq : Atoms CollapsingMonoid = {p1} ∪ { x | ∃ m, x = pn m } := by
  ext x
  simp only [Atoms, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases h1 : x.exp_p1.val ≥ 1
    · by_cases hf : x.exponents = 0
      · by_cases h1' : x.exp_p1.val = 1
        · left
          apply ext' h1' hf
        · have h2 : x.exp_p1.val = 2 := by have := x.exp_p1.isLt; omega
          exfalso
          have hx_eq : x = p1 * p1 := by
            apply ext'
            · simp only [mul_exp_p1, p1_exp_p1_val]; omega
            · simp only [mul_exponents, p1_exponents, add_zero]; exact hf
          have h := hx.isUnit_or_isUnit hx_eq
          cases h with
          | inl h => exact p1_not_isUnit h
          | inr h => exact p1_not_isUnit h
      · exfalso
        have hx_eq : x = p1 * ⟨⟨x.exp_p1.val - 1, by have := x.exp_p1.isLt; omega⟩, x.exponents⟩ := by
          apply ext'
          · simp only [mul_exp_p1, p1_exp_p1_val, Fin.val_mk]
            have := x.exp_p1.isLt; omega
          · simp only [mul_exponents, p1_exponents, zero_add]
        have hy_not_unit : ¬IsUnit (⟨⟨x.exp_p1.val - 1, by have := x.exp_p1.isLt; omega⟩, x.exponents⟩ : CollapsingMonoid) := by
          intro hu
          have heq := (isUnit_iff _).mp hu
          have := congrArg exponents heq
          simp at this
          exact hf this
        have h := hx.isUnit_or_isUnit hx_eq
        cases h with
        | inl h => exact p1_not_isUnit h
        | inr h => exact hy_not_unit h
    · push_neg at h1
      have h0 : x.exp_p1.val = 0 := by omega
      by_cases hf : x.exponents = 0
      · exfalso
        have hx_eq : x = 1 := by apply ext' h0 hf
        rw [hx_eq] at hx
        exact hx.not_isUnit isUnit_one
      · right
        have hsupp := Finsupp.support_nonempty_iff.mpr hf
        obtain ⟨i, hi⟩ := hsupp
        by_contra h_not_pn
        push_neg at h_not_pn
        by_cases h_single : x.exponents = Finsupp.single i 1
        · have hxi : x = pn i := by apply ext' h0 h_single
          exact h_not_pn i hxi
        · exfalso
          by_cases hi_val : x.exponents i = 1
          · have h_other : ∃ j ≠ i, j ∈ x.exponents.support := by
              by_contra h_no
              push_neg at h_no
              have hsingle : x.exponents = Finsupp.single i 1 := by
                ext k
                by_cases hki : k = i
                · simp [hki, hi_val]
                · have := h_no k hki
                  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at this
                  simp [hki, this]
              exact h_single hsingle
            obtain ⟨j, hji, hj⟩ := h_other
            have hj_pos : 0 < x.exponents j := Finsupp.mem_support_iff.mp hj |> Nat.pos_of_ne_zero
            have hx_eq : x = pn i * ⟨0, x.exponents - Finsupp.single i 1⟩ := by
              apply ext'
              · simp [h0]
              · ext k
                simp only [mul_exponents, pn_exponents, Finsupp.coe_add, Finsupp.coe_tsub,
                           Pi.add_apply, Pi.sub_apply]
                by_cases hki : k = i
                · simp [hki, hi_val]
                · simp [Finsupp.single_eq_of_ne hki]
            have h := hx.isUnit_or_isUnit hx_eq
            cases h with
            | inl h => exact pn_not_isUnit i h
            | inr h =>
              have heq := (isUnit_iff _).mp h
              have hj_exp := congrArg exponents heq
              simp only [one_exponents] at hj_exp
              have hj' := DFunLike.congr_fun hj_exp j
              simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at hj'
              have hsingle_j : (Finsupp.single i (1 : ℕ)) j = 0 := by
                rw [Finsupp.single_apply]
                simp [hji.symm]
              simp only [hsingle_j, tsub_zero] at hj'
              omega
          · have hi_ge2 : x.exponents i ≥ 2 := by
              have hi_pos : 0 < x.exponents i := Finsupp.mem_support_iff.mp hi |> Nat.pos_of_ne_zero
              omega
            have hx_eq : x = pn i * ⟨0, x.exponents - Finsupp.single i 1⟩ := by
              apply ext'
              · simp [h0]
              · ext k
                simp only [mul_exponents, pn_exponents, Finsupp.coe_add, Finsupp.coe_tsub,
                           Pi.add_apply, Pi.sub_apply]
                by_cases hki : k = i
                · simp only [hki, Finsupp.single_eq_same]; omega
                · simp [Finsupp.single_eq_of_ne hki]
            have h := hx.isUnit_or_isUnit hx_eq
            cases h with
            | inl h => exact pn_not_isUnit i h
            | inr h =>
              have heq := (isUnit_iff _).mp h
              have hi' : x.exponents i - 1 = 0 := by
                have := congrArg exponents heq
                simp at this
                have := DFunLike.congr_fun this i
                simp at this
                exact this
              omega
  · intro hx
    rcases hx with rfl | ⟨m, rfl⟩
    · exact p1_irreducible
    · exact pn_irreducible m

/-- Product of replicate n copies of p1 has exp_p1 = min n 2. -/
lemma prod_replicate_p1 (n : ℕ) :
    (Multiset.replicate n p1).prod = ⟨⟨min n 2, by omega⟩, 0⟩ := by
  induction n with
  | zero => apply ext' <;> simp
  | succ m ih =>
    simp only [Multiset.replicate_succ, Multiset.prod_cons, ih]
    apply ext'
    · simp only [mul_exp_p1, p1_exp_p1_val, Fin.val_mk]; omega
    · simp only [mul_exponents, p1_exponents, zero_add]

/-- Product of replicate k copies of pn(i) has exponents = single i k. -/
lemma prod_replicate_pn (i k : ℕ) :
    (Multiset.replicate k (pn i)).prod = ⟨0, Finsupp.single i k⟩ := by
  induction k with
  | zero => apply ext' <;> simp [Finsupp.single_zero]
  | succ n ih =>
    simp only [Multiset.replicate_succ, Multiset.prod_cons, ih]
    apply ext'
    · simp
    · simp only [mul_exponents, pn_exponents, ← Finsupp.single_add, add_comm]

/-- Size function for well-founded induction: sum of exp_p1 and all exponents. -/
private def collapsingSize (x : CollapsingMonoid) : ℕ :=
  x.exp_p1.val + x.exponents.sum (fun _ v => v)

/-- The collapsing monoid is atomic.
    Every non-unit factors into atoms p₁ and {pn i : i ∈ ℕ}.
    The factorization of x = ⟨e₁, f⟩ is: e₁ copies of p₁ (if e₁ ≤ 2),
    plus for each i ∈ supp(f), f(i) copies of pn(i).
    The proof uses well-founded induction on element size. -/
theorem collapsing_atomic : Atomic CollapsingMonoid := by
  intro x
  have h : ∀ n (y : CollapsingMonoid), collapsingSize y = n → ¬IsUnit y →
      ∃ L : List CollapsingMonoid, (∀ a ∈ L, a ∈ Atoms CollapsingMonoid) ∧ L.prod = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hsize hy_not_unit
      have h_exp_le : y.exp_p1.val ≤ 2 := Nat.le_of_lt_succ y.exp_p1.isLt
      by_cases hy_atom : y ∈ Atoms CollapsingMonoid
      · exact ⟨[y], by simp [hy_atom], by simp⟩
      · by_cases hp : y.exp_p1.val ≥ 1
        · -- Factor out p1
          let z : CollapsingMonoid := ⟨⟨y.exp_p1.val - 1, by omega⟩, y.exponents⟩
          have hz_exp : z.exp_p1.val = y.exp_p1.val - 1 := rfl
          have hz_exponents : z.exponents = y.exponents := rfl
          have hz_size : collapsingSize z < collapsingSize y := by
            unfold collapsingSize
            rw [hz_exponents]
            omega
          by_cases hz_unit : IsUnit z
          · have heq := (isUnit_iff z).mp hz_unit
            have hexp1 : y.exp_p1.val = 1 := by
              have := congrArg (fun x => x.exp_p1.val) heq
              simp at this
              omega
            have hf0 : y.exponents = 0 := congrArg exponents heq
            exfalso
            have hy_is_p1 : y = p1 := by apply ext' hexp1 hf0
            rw [hy_is_p1] at hy_atom
            exact hy_atom p1_irreducible
          · have ⟨Lz, hLz_atoms, hLz_prod⟩ := ih (collapsingSize z) (hsize ▸ hz_size) z rfl hz_unit
            refine ⟨p1 :: Lz, ?_, ?_⟩
            · intro a ha
              simp at ha
              rcases ha with rfl | ha
              · exact p1_irreducible
              · exact hLz_atoms a ha
            · simp only [List.prod_cons, hLz_prod]
              apply ext'
              · simp only [mul_exp_p1, p1_exp_p1_val, hz_exp, Fin.val_mk]
                omega
              · simp only [mul_exponents, p1_exponents, zero_add, hz_exponents]
        · push_neg at hp
          have hp0 : y.exp_p1.val = 0 := by omega
          by_cases hf : y.exponents = 0
          · exfalso
            have hy1 : y = 1 := by apply ext' hp0 hf
            rw [hy1] at hy_not_unit
            exact hy_not_unit isUnit_one
          · -- Factor out some pn(i)
            have hsupp := Finsupp.support_nonempty_iff.mpr hf
            obtain ⟨i, hi⟩ := hsupp
            have hi_pos : y.exponents i ≥ 1 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
            let z : CollapsingMonoid := ⟨0, y.exponents - Finsupp.single i 1⟩
            have hz_exp_val : z.exp_p1.val = 0 := rfl
            have hz_size : collapsingSize z < collapsingSize y := by
              -- collapsingSize z = 0 + z.exponents.sum (id)
              -- collapsingSize y = 0 + y.exponents.sum (id)
              -- z.exponents = y.exponents - single i 1
              -- Need: z.exponents.sum < y.exponents.sum
              unfold collapsingSize
              simp only [hz_exp_val, hp0, zero_add]
              -- Goal: z.exponents.sum (fun _ v => v) < y.exponents.sum (fun _ v => v)
              -- Key idea: the sum over z.exponents equals sum over y.exponents minus 1
              have hz_exp_def : z.exponents = y.exponents - Finsupp.single i 1 := rfl
              -- Express sum in terms of support
              have hsum_y : y.exponents.sum (fun _ v => v) =
                  y.exponents.support.sum (fun j => y.exponents j) := by
                rw [Finsupp.sum]
              have hsum_z : z.exponents.sum (fun _ v => v) =
                  z.exponents.support.sum (fun j => z.exponents j) := by
                rw [Finsupp.sum]
              rw [hsum_y, hsum_z]
              -- z.exponents j = y.exponents j for j ≠ i
              -- z.exponents i = y.exponents i - 1
              -- y.exponents i ≥ 1, so z.exponents.support ⊆ y.exponents.support
              have hz_supp_sub : z.exponents.support ⊆ y.exponents.support := by
                intro j hj
                rw [Finsupp.mem_support_iff] at hj ⊢
                rw [hz_exp_def] at hj
                simp only [Finsupp.coe_tsub, Pi.sub_apply] at hj
                by_contra hy_j
                simp only [hy_j, tsub_zero] at hj
                by_cases hji : j = i
                · subst hji; simp only [Finsupp.single_eq_same] at hj; omega
                · simp only [Finsupp.single_eq_of_ne hji] at hj; exact hj rfl
              -- Show strict inequality
              calc z.exponents.support.sum (fun j => z.exponents j)
                  ≤ y.exponents.support.sum (fun j => z.exponents j) := by
                      apply Finset.sum_le_sum_of_subset hz_supp_sub
                _ < y.exponents.support.sum (fun j => y.exponents j) := by
                      apply Finset.sum_lt_sum
                      · intro j _
                        rw [hz_exp_def]
                        simp only [Finsupp.coe_tsub, Pi.sub_apply]
                        exact Nat.sub_le _ _
                      · use i, hi
                        rw [hz_exp_def]
                        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
                        omega
            by_cases hz_unit : IsUnit z
            · have heq := (isUnit_iff z).mp hz_unit
              have hf1 : y.exponents = Finsupp.single i 1 := by
                have hz_zero := congrArg exponents heq
                simp only [one_exponents] at hz_zero
                -- hz_zero : z.exponents = 0
                -- z.exponents = y.exponents - Finsupp.single i 1
                ext k
                have hk := DFunLike.congr_fun hz_zero k
                -- hk : z.exponents k = 0
                -- z.exponents k = (y.exponents - Finsupp.single i 1) k = y.exponents k - (Finsupp.single i 1) k
                have hz_k : z.exponents k = y.exponents k - (Finsupp.single i 1) k := rfl
                rw [hz_k] at hk
                by_cases hki : k = i
                · rw [hki] at hk ⊢
                  simp only [Finsupp.single_eq_same] at hk ⊢
                  -- hk : y.exponents i - 1 = 0
                  have hi_bound : y.exponents i ≤ 1 := Nat.sub_eq_zero_iff_le.mp hk
                  exact Nat.le_antisymm hi_bound hi_pos
                · simp only [Finsupp.single_eq_of_ne hki] at hk ⊢
                  -- hk : y.exponents k - 0 = 0
                  simp at hk
                  exact hk
              exfalso
              have hy_is_pn : y = pn i := by apply ext' hp0 hf1
              rw [hy_is_pn] at hy_atom
              exact hy_atom (pn_irreducible i)
            · have ⟨Lz, hLz_atoms, hLz_prod⟩ := ih (collapsingSize z) (hsize ▸ hz_size) z rfl hz_unit
              refine ⟨pn i :: Lz, ?_, ?_⟩
              · intro a ha
                simp at ha
                rcases ha with rfl | ha
                · exact pn_irreducible i
                · exact hLz_atoms a ha
              · simp only [List.prod_cons, hLz_prod]
                apply ext'
                · simp only [mul_exp_p1, pn_exp_p1_val, Fin.val_mk]
                  -- Need: min (0 + 0) 2 = y.exp_p1.val
                  have hz_exp0 : z.exp_p1.val = 0 := hz_exp_val
                  rw [hz_exp0, add_zero]
                  simp only [Nat.min_eq_left (by omega : 0 ≤ 2)]
                  exact hp0.symm
                · ext k
                  simp only [mul_exponents, pn_exponents, Finsupp.coe_add, Finsupp.coe_tsub,
                             Pi.add_apply, Pi.sub_apply]
                  by_cases hki : k = i
                  · rw [hki]
                    simp only [Finsupp.single_eq_same]
                    -- Goal: 1 + z.exponents i = y.exponents i
                    -- z is defined as ⟨0, y.exponents - Finsupp.single i 1⟩
                    -- So z.exponents = y.exponents - Finsupp.single i 1
                    have hz_exp : z.exponents = y.exponents - Finsupp.single i 1 := rfl
                    have hz_i_def : z.exponents i = y.exponents i - 1 := by
                      rw [hz_exp]
                      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
                    rw [hz_i_def, add_comm]
                    exact Nat.sub_add_cancel hi_pos
                  · simp only [Finsupp.single_eq_of_ne hki, zero_add, tsub_zero]
                    -- Goal: z.exponents k = y.exponents k
                    -- z.exponents k = y.exponents k - (Finsupp.single i 1) k = y.exponents k - 0 = y.exponents k
                    have hz_exp : z.exponents = y.exponents - Finsupp.single i 1 := rfl
                    rw [hz_exp]
                    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hki, tsub_zero]
  intro hx_not_unit
  obtain ⟨L, hL_atoms, hL_prod⟩ := h (collapsingSize x) x rfl hx_not_unit
  use L
  constructor
  · intro a ha; exact hL_atoms a ha
  · simp only [Multiset.prod_coe, hL_prod]

/-!
## The Four Axioms
-/

/-- APD holds. -/
theorem collapsing_APD : APD CollapsingMonoid := by
  intro p q hp hq k hdvd
  rw [atoms_eq] at hp hq
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with rfl | ⟨n, rfl⟩
  · rcases hq with rfl | ⟨m, rfl⟩
    · rfl
    · exfalso
      rw [pow_p1] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h := congrArg exponents hc
      simp only [mul_exponents, pn_exponents] at h
      have hm := DFunLike.congr_fun h m
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.coe_zero,
                 Pi.zero_apply] at hm
      omega
  · rcases hq with rfl | ⟨m, rfl⟩
    · exfalso
      rw [pow_pn] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h := congrArg (fun x => x.exp_p1.val) hc
      simp only [mul_exp_p1, p1_exp_p1_val, Fin.val_zero] at h
      omega
    · rw [pow_pn] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h := congrArg exponents hc
      simp only [mul_exponents, pn_exponents] at h
      have hm_eq_n : m = n := by
        by_contra hmn
        have := DFunLike.congr_fun h m
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
                   Finsupp.single_eq_of_ne hmn] at this
        omega
      simp [hm_eq_n]

/-- UAB holds: If p^k = q^m for atoms p, q with k, m ≥ 1, then p = q.
    The collapsing relation p₁² = p₁³ is within a single tower, not across atoms. -/
theorem collapsing_UAB : UAB CollapsingMonoid := by
  intro p q hp hq k m hk hm hpow
  rw [atoms_eq] at hp hq
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with rfl | ⟨n, rfl⟩
  · -- p = p1
    rcases hq with rfl | ⟨m', rfl⟩
    · -- q = p1: trivially p = q
      rfl
    · -- q = pn m': p1^k = (pn m')^m, impossible since exp_p1 differ
      exfalso
      rw [pow_p1, pow_pn] at hpow
      have h := congrArg (fun x => x.exp_p1.val) hpow
      simp only [Fin.val_mk, pn_exp_p1_val] at h
      omega
  · -- p = pn n
    rcases hq with rfl | ⟨m', rfl⟩
    · -- q = p1: (pn n)^k = p1^m, impossible since exp_p1 differ
      exfalso
      rw [pow_p1, pow_pn] at hpow
      have h := congrArg (fun x => x.exp_p1.val) hpow
      simp only [Fin.val_mk, pn_exp_p1_val] at h
      omega
    · -- q = pn m': (pn n)^k = (pn m')^m implies n = m'
      rw [pow_pn, pow_pn] at hpow
      have h := congrArg exponents hpow
      simp only at h
      have hn := DFunLike.congr_fun h n
      simp only [Finsupp.single_eq_same] at hn
      by_cases hnm : n = m'
      · simp [hnm]
      · simp only [Finsupp.single_eq_of_ne hnm] at hn
        omega

/-- PP-D fails: p₁² = p₁³. -/
theorem collapsing_not_PPD : ¬ PP_D CollapsingMonoid := by
  intro hppd
  have hp1_atom : p1 ∈ Atoms CollapsingMonoid := by rw [atoms_eq]; simp
  have h := hppd p1 hp1_atom
  have h23 : p1 ^ 2 = p1 ^ 3 := by
    rw [pow_p1, pow_p1]
    apply ext' <;> simp
  have := h h23
  omega

/-- p₁ divides x iff x.exp_p1 ≥ 1. -/
lemma p1_dvd_iff (x : CollapsingMonoid) : p1 ∣ x ↔ x.exp_p1.val ≥ 1 := by
  constructor
  · intro ⟨c, hc⟩
    have h := congrArg (fun y => y.exp_p1.val) hc
    simp only [mul_exp_p1, p1_exp_p1_val] at h
    omega
  · intro h
    use ⟨⟨x.exp_p1.val - 1, by have := x.exp_p1.isLt; omega⟩, x.exponents⟩
    apply ext'
    · simp only [mul_exp_p1, p1_exp_p1_val, Fin.val_mk]
      have := x.exp_p1.isLt; omega
    · simp only [mul_exponents, p1_exponents, zero_add]

/-- pn(i) divides x iff x.exponents(i) ≥ 1. -/
lemma pn_dvd_iff (i : ℕ) (x : CollapsingMonoid) : pn i ∣ x ↔ x.exponents i ≥ 1 := by
  constructor
  · intro ⟨c, hc⟩
    have h := congrArg exponents hc
    simp only [mul_exponents, pn_exponents] at h
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hi
    omega
  · intro h
    use ⟨x.exp_p1, x.exponents - Finsupp.single i 1⟩
    apply ext'
    · simp only [mul_exp_p1, pn_exp_p1_val, zero_add]
      exact (Nat.min_eq_left (Nat.le_of_lt_succ x.exp_p1.isLt)).symm
    · ext j
      simp only [mul_exponents, pn_exponents, Finsupp.coe_add, Pi.add_apply,
                 Finsupp.coe_tsub, Pi.sub_apply]
      by_cases hji : j = i
      · subst hji; simp only [Finsupp.single_eq_same]; omega
      · simp only [Finsupp.single_eq_of_ne hji, zero_add, tsub_zero]

/-- Coprimality in CollapsingMonoid means disjoint atom support. -/
lemma areCoprime_iff (x y : CollapsingMonoid) :
    AreCoprime x y ↔ (x.exp_p1.val = 0 ∨ y.exp_p1.val = 0) ∧
                      (∀ i, x.exponents i = 0 ∨ y.exponents i = 0) := by
  constructor
  · intro h
    constructor
    · by_contra h'
      push_neg at h'
      have hp1x : p1 ∣ x := p1_dvd_iff x |>.mpr (Nat.one_le_iff_ne_zero.mpr h'.1)
      have hp1y : p1 ∣ y := p1_dvd_iff y |>.mpr (Nat.one_le_iff_ne_zero.mpr h'.2)
      have hp1_atom : p1 ∈ Atoms CollapsingMonoid := by rw [atoms_eq]; simp
      exact h p1 hp1_atom hp1x hp1y
    · intro i
      by_contra h'
      push_neg at h'
      have hpnx : pn i ∣ x := pn_dvd_iff i x |>.mpr (Nat.one_le_iff_ne_zero.mpr h'.1)
      have hpny : pn i ∣ y := pn_dvd_iff i y |>.mpr (Nat.one_le_iff_ne_zero.mpr h'.2)
      have hpn_atom : pn i ∈ Atoms CollapsingMonoid := by rw [atoms_eq]; right; exact ⟨i, rfl⟩
      exact h (pn i) hpn_atom hpnx hpny
  · intro ⟨h_exp, h_f⟩ p hp hdvd_x hdvd_y
    rw [atoms_eq] at hp
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    rcases hp with rfl | ⟨m, rfl⟩
    · have hx := p1_dvd_iff x |>.mp hdvd_x
      have hy := p1_dvd_iff y |>.mp hdvd_y
      cases h_exp with
      | inl h => omega
      | inr h => omega
    · have hx := pn_dvd_iff m x |>.mp hdvd_x
      have hy := pn_dvd_iff m y |>.mp hdvd_y
      cases h_f m with
      | inl h => omega
      | inr h => omega

/- CFI holds: factorizations of coprime products split.
    For coprime x, y, the map (f, g) ↦ f * g (coordinatewise) is a bijection
    from F_2(x) × F_2(y) to F_2(x * y).

    The proof follows from the disjoint support characterization:
    - Coprime x, y means their atom supports are disjoint
    - Any factorization of x*y can be uniquely split into x and y parts
    - The exp_p1 component goes entirely to x or y (whichever has exp_p1 > 0)
    - Each exponents(i) goes entirely to x or y based on support membership -/
noncomputable section AristotleLemmas

/-
Splits a divisor z of x*y into parts dividing x and y, assuming x and y are coprime.
If x has p1 component, z's p1 goes to x (since y has none). Otherwise it goes to y.
For other exponents, we take the part of z bounded by x as x's share, and the rest as y's share.
-/
noncomputable def CollapsingMonoid.coprimeSplit (x y z : CollapsingMonoid) : CollapsingMonoid × CollapsingMonoid :=
  let e_split : Fin 3 × Fin 3 :=
    if x.exp_p1.val = 0 then (0, z.exp_p1) else (z.exp_p1, 0)
  let f_split : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) :=
    (z.exponents ⊓ x.exponents, z.exponents - (z.exponents ⊓ x.exponents))
  (⟨e_split.1, f_split.1⟩, ⟨e_split.2, f_split.2⟩)

/-
Antisymmetry of divisibility in CollapsingMonoid.
Proof:
1. `x ∣ y` implies `x.exponents ≤ y.exponents`.
   `y = x * k` => `y.exponents = x.exponents + k.exponents` => `x.exponents ≤ y.exponents`.
   Similarly `y ∣ x` implies `y.exponents ≤ x.exponents`.
   So `x.exponents = y.exponents`.
2. `x ∣ y` implies `x.exp_p1 ≤ y.exp_p1`.
   If `y.exp_p1 < 2`, `x.exp_p1 + k.exp_p1 = y.exp_p1`, so `x.exp_p1 ≤ y.exp_p1`.
   If `y.exp_p1 = 2`, `x.exp_p1 ≤ 2` is trivial.
   Similarly `y ∣ x` implies `y.exp_p1 ≤ x.exp_p1`.
   So `x.exp_p1 = y.exp_p1`.
3. By extensionality, `x = y`.
-/
lemma CollapsingMonoid.associated_eq {x y : CollapsingMonoid} (h1 : x ∣ y) (h2 : y ∣ x) : x = y := by
  -- By definition of divisibility in CollapsingMonoid, we have that if x ∣ y, then x.exp_p1 ≤ y.exp_p1 and x.exponents ≤ y.exponents.
  have h_div_exp_p1 : x.exp_p1.val ≤ y.exp_p1.val := by
    rcases h1 with ⟨ k, rfl ⟩;
    exact le_min ( Nat.le_add_right _ _ ) ( by linarith [ Fin.is_lt x.exp_p1 ] )
  have h_div_exponents : x.exponents ≤ y.exponents := by
    cases h1 ; aesop;
  -- By definition of divisibility in CollapsingMonoid, if y ∣ x, then y.exp_p1 ≤ x.exp_p1 and y.exponents ≤ x.exponents.
  have h_div_exp_p1' : y.exp_p1.val ≤ x.exp_p1.val := by
    obtain ⟨ k, hk ⟩ := h2;
    rw [ hk, CollapsingMonoid.mul_exp_p1 ];
    exact le_min ( Nat.le_add_right _ _ ) ( Fin.is_le _ )
  have h_div_exponents' : y.exponents ≤ x.exponents := by
    cases h2 ; aesop;
  exact CollapsingMonoid.ext ( Fin.ext <| le_antisymm h_div_exp_p1 h_div_exp_p1' ) ( le_antisymm h_div_exponents h_div_exponents' )

/-
Properties of coprimeSplit:
1. u * v = z:
   - Exponents of pn: (z ⊓ x) + (z - (z ⊓ x)) = z (lattice property in ℕ).
   - Exponent of p1:
     - If x.exp_p1 = 0, u.exp_p1 = 0, v.exp_p1 = z.exp_p1. Sum is z.exp_p1.
     - If x.exp_p1 ≠ 0, u.exp_p1 = z.exp_p1, v.exp_p1 = 0. Sum is z.exp_p1.
     - Multiplication caps at 2, but z.exp_p1 ∈ Fin 3, so min(z.exp_p1, 2) = z.exp_p1.
2. u ∣ x:
   - pn: u.exponents = z ⊓ x ≤ x.
   - p1:
     - If x.exp_p1 = 0, u.exp_p1 = 0 ≤ x.exp_p1.
     - If x.exp_p1 ≠ 0, y.exp_p1 = 0 (coprime). z ∣ x*y => z.exp_p1 ≤ min(x.exp_p1, 2) ≤ x.exp_p1.
3. v ∣ y:
   - pn: Since x, y coprime, their supports are disjoint.
     - If x_i > 0, y_i = 0. z_i ≤ x_i. u_i = z_i, v_i = 0 ≤ y_i.
     - If x_i = 0, u_i = 0, v_i = z_i. z_i ≤ y_i.
   - p1:
     - If x.exp_p1 = 0, v.exp_p1 = z.exp_p1. z ∣ x*y => z.exp_p1 ≤ y.exp_p1.
     - If x.exp_p1 ≠ 0, v.exp_p1 = 0 ≤ y.exp_p1.
-/
lemma CollapsingMonoid.coprimeSplit_spec {x y z : CollapsingMonoid} (hxy : AreCoprime x y) (hz : z ∣ x * y) :
    let (u, v) := CollapsingMonoid.coprimeSplit x y z
    u * v = z ∧ u ∣ x ∧ v ∣ y := by
      refine' ⟨ _, _, _ ⟩;
      · refine' CollapsingMonoid.ext' _ _ <;> simp_all +decide [ CollapsingMonoid.mul ];
        split_ifs <;> simp +decide [ * ];
        · exact Nat.le_of_lt_succ ( Fin.is_lt _ );
        · exact Nat.le_of_lt_succ ( Fin.is_lt _ );
      · by_cases h : x.exp_p1.val = 0 <;> simp +decide [ h ];
        · exact ⟨ ⟨ x.exp_p1, x.exponents - ( z.exponents ⊓ x.exponents ) ⟩, by ext <;> aesop ⟩;
        · -- Since $x$ and $y$ are coprime, their exponents for $p_1$ are disjoint. Therefore, $z.exp_p1 \leq x.exp_p1$.
          have h_exp_p1 : z.exp_p1.val ≤ x.exp_p1.val := by
            have h_exp_p1 : z.exp_p1.val ≤ (x * y).exp_p1.val := by
              obtain ⟨ k, hk ⟩ := hz;
              simp +decide [ hk, CollapsingMonoid.mul_exp_p1 ];
              exact Nat.le_of_lt_succ ( Fin.is_lt _ );
            have := hxy; rw [ areCoprime_iff ] at this; aesop;
          exact ⟨ ⟨ ⟨ x.exp_p1.val - z.exp_p1.val, by omega ⟩, x.exponents - ( z.exponents ⊓ x.exponents ) ⟩, by
            ext <;> simp +decide [ *, Fin.ext_iff, Fin.val_add, Fin.val_mul ];
            exact Nat.le_of_lt_succ x.exp_p1.2 ⟩;
      · -- By definition of coprimeSplit, we know that v divides y.
        have hv_div_y : (z.exponents - (z.exponents ⊓ x.exponents)) ≤ y.exponents ∧ (if x.exp_p1.val = 0 then z.exp_p1 else 0) ≤ y.exp_p1 := by
          constructor;
          · -- Since $x$ and $y$ are coprime, their exponents are disjoint. Therefore, $z.exponents \cap x.exponents$ is a subset of $x.exponents$.
            have h_disjoint : ∀ i, z.exponents i ≤ x.exponents i + y.exponents i := by
              -- Since $z \mid x * y$, we have $z.exponents i \leq (x * y).exponents i$ for all $i$.
              have h_div : ∀ i, z.exponents i ≤ (x * y).exponents i := by
                obtain ⟨ k, hk ⟩ := hz;
                simp +decide [ hk, CollapsingMonoid.mul ];
              convert h_div using 1;
            intro i; specialize h_disjoint i; simp_all +decide [ Nat.sub_le_iff_le_add ] ;
            cases min_cases ( z.exponents i ) ( x.exponents i ) <;> linarith;
          · obtain ⟨ k, hk ⟩ := hz;
            have := congr_arg ( fun m : CollapsingMonoid => m.exp_p1.val ) hk; norm_num at this;
            grind;
        refine' ⟨ ⟨ y.exp_p1 - ( if x.exp_p1.val = 0 then z.exp_p1 else 0 ), y.exponents - ( z.exponents - z.exponents ⊓ x.exponents ) ⟩, _ ⟩;
        refine' CollapsingMonoid.ext' _ _ <;> simp_all +decide [ CollapsingMonoid.mul ];
        grind

/-
If x, y are coprime and u|x, v|y, then splitting u*v gives back (u, v).
Proof:
1. Exponents of pn:
   u|x => u.exponents ≤ x.exponents.
   v|y => v.exponents ≤ y.exponents.
   x, y coprime => x.exponents and y.exponents are disjoint.
   So v.exponents is disjoint from x.exponents.
   (u*v).exponents ⊓ x.exponents = (u.exponents + v.exponents) ⊓ x.exponents
   = (u.exponents ⊓ x.exponents) + (v.exponents ⊓ x.exponents)
   = u.exponents + 0 = u.exponents.
   The second component is (u*v).exponents - u.exponents = v.exponents.
2. Exponent of p1:
   x, y coprime => x.exp_p1 = 0 or y.exp_p1 = 0.
   Case 1: x.exp_p1 = 0.
     u|x => u.exp_p1 = 0.
     coprimeSplit returns (0, (u*v).exp_p1).
     (u*v).exp_p1 = min(u.exp_p1 + v.exp_p1, 2) = min(0 + v.exp_p1, 2) = v.exp_p1.
     So we get (u, v).
   Case 2: x.exp_p1 ≠ 0.
     Then y.exp_p1 = 0.
     v|y => v.exp_p1 = 0.
     coprimeSplit returns ((u*v).exp_p1, 0).
     (u*v).exp_p1 = min(u.exp_p1 + 0, 2) = u.exp_p1.
     So we get (u, v).
-/
lemma CollapsingMonoid.coprimeSplit_eq_of_mul {x y u v : CollapsingMonoid} (hxy : AreCoprime x y)
    (hu : u ∣ x) (hv : v ∣ y) : CollapsingMonoid.coprimeSplit x y (u * v) = (u, v) := by
      apply Classical.byContradiction
      intro h_contra;
      -- By definition of coprimeSplit, we know that (u * v).exponents ⊓ x.exponents = u.exponents and (u * v).exponents - u.exponents = v.exponents.
      have h_split : (u * v).exponents ⊓ x.exponents = u.exponents ∧ (u * v).exponents - u.exponents = v.exponents := by
        -- Since $u \mid x$ and $v \mid y$, we have $u.exponents \leq x.exponents$ and $v.exponents \leq y.exponents$.
        have h_u_le_x : u.exponents ≤ x.exponents := by
          cases hu ; aesop
        have h_v_le_y : v.exponents ≤ y.exponents := by
          obtain ⟨ k, rfl ⟩ := hv;
          exact le_add_right le_rfl;
        -- Since $x$ and $y$ are coprime, their supports are disjoint.
        have h_disjoint : ∀ i, x.exponents i = 0 ∨ y.exponents i = 0 := by
          have := areCoprime_iff x y; aesop;
        simp_all +decide [ Finsupp.le_def ];
        ext i; specialize h_u_le_x i; specialize h_v_le_y i; specialize h_disjoint i; aesop;
      -- By definition of coprimeSplit, we know that (u * v).exp_p1 = u.exp_p1 + v.exp_p1.
      have h_exp_p1 : (u * v).exp_p1.val = u.exp_p1.val + v.exp_p1.val := by
        have h_exp_p1 : (u * v).exp_p1.val = min (u.exp_p1.val + v.exp_p1.val) 2 := by
          exact?;
        have h_exp_p1 : u.exp_p1.val ≤ x.exp_p1.val ∧ v.exp_p1.val ≤ y.exp_p1.val := by
          have h_exp_p1 : ∀ {a b : CollapsingMonoid}, a ∣ b → a.exp_p1.val ≤ b.exp_p1.val := by
            intros a b hab; obtain ⟨ c, rfl ⟩ := hab; simp +decide [ CollapsingMonoid.mul ] ;
            exact Nat.le_of_lt_succ a.exp_p1.2;
          exact ⟨ h_exp_p1 hu, h_exp_p1 hv ⟩;
        have h_exp_p1 : x.exp_p1.val = 0 ∨ y.exp_p1.val = 0 := by
          specialize hxy p1 ; simp_all +decide [ Atoms ];
          by_cases hx : CollapsingMonoid.p1 ∣ x <;> by_cases hy : CollapsingMonoid.p1 ∣ y <;> simp_all +decide [ CollapsingMonoid.p1_dvd_iff ];
          exact False.elim <| hxy <| CollapsingMonoid.p1_irreducible;
        grind;
      unfold CollapsingMonoid.CollapsingMonoid.coprimeSplit at h_contra;
      split_ifs at h_contra <;> simp_all +decide [ CollapsingMonoid.ext_iff ];
      · -- Since $u \mid x$ and $x.exp_p1 = 0$, it follows that $u.exp_p1 = 0$.
        have h_u_exp_p1 : u.exp_p1 = 0 := by
          obtain ⟨ k, hk ⟩ := hu;
          erw [ Fin.ext_iff ] at * ; aesop;
        simp_all +decide [ CollapsingMonoid.mul ];
        exact h_contra ( by rw [ show ( u * v ).exp_p1 = v.exp_p1 from by rw [ show ( u * v ).exp_p1 = ⟨ min ( u.exp_p1.val + v.exp_p1.val ) 2, by omega ⟩ from by rfl ] ; aesop ] );
      · have h_exp_p1_zero : x.exp_p1.val = 0 ∨ y.exp_p1.val = 0 := by
          have := hxy p1; simp_all +decide [ CollapsingMonoid.ext_iff ] ;
          exact Classical.not_not.1 fun h => this ( by exact CollapsingMonoid.p1_irreducible ) ( by exact CollapsingMonoid.p1_dvd_iff _ |>.2 <| Nat.pos_of_ne_zero <| by aesop ) ( by exact CollapsingMonoid.p1_dvd_iff _ |>.2 <| Nat.pos_of_ne_zero <| by aesop );
        obtain ⟨ k, hk ⟩ := hv;
        erw [ Fin.ext_iff ] at * ; aesop

/-
Distributivity of inf over add for Finsupps bounded by disjoint elements.
If `x` and `y` are disjoint (pointwise min is 0), and `a + b ≤ x + y`, then the part of `a + b` "belonging" to `x` is the sum of the parts of `a` and `b` belonging to `x`.
Proof:
Pointwise for each `i`:
If `x i = 0`, then `LHS = (a i + b i) ⊓ 0 = 0`. `RHS = (a i ⊓ 0) + (b i ⊓ 0) = 0`.
If `x i > 0`, then `y i = 0` (by disjointness).
`a i + b i ≤ x i + y i = x i`.
So `a i + b i ≤ x i`.
This implies `a i ≤ x i` and `b i ≤ x i`.
`LHS = (a i + b i) ⊓ x i = a i + b i`.
`RHS = (a i ⊓ x i) + (b i ⊓ x i) = a i + b i`.
QED.
-/
lemma finsupp_inf_add_eq_inf_add_inf {x y a b : ℕ →₀ ℕ} (hxy : Disjoint x y) (hab : a + b ≤ x + y) :
    (a + b) ⊓ x = (a ⊓ x) + (b ⊓ x) := by
      -- Since $x$ and $y$ are disjoint, for any $i$, either $x i = 0$ or $y i = 0$.
      have h_disjoint : ∀ i, x i = 0 ∨ y i = 0 := by
        simp_all +decide [ Finsupp.ext_iff, disjoint_iff_inf_le ];
        exact fun i => by cases le_total ( x i ) ( y i ) <;> specialize hxy i <;> aesop;
      ext i;
      cases h_disjoint i <;> simp_all +decide [ inf_eq_right.mpr, Finsupp.le_def ];
      cases min_cases ( a i + b i ) ( x i ) <;> cases min_cases ( a i ) ( x i ) <;> cases min_cases ( b i ) ( x i ) <;> linarith [ hab i ]

/-
Subtraction distributes over addition if the subtrahends are smaller than the minuends.
`(a + b) - (c + d) = (a - c) + (b - d)` given `c ≤ a` and `d ≤ b`.
Proof: `(a - c) + (b - d) = a - c + b - d = a + b - c - d = a + b - (c + d)`.
Using `Nat.sub_add_comm` and `Nat.add_sub_assoc`.
-/
lemma nat_add_sub_add_eq_sub_add_sub {a b c d : ℕ} (hc : c ≤ a) (hd : d ≤ b) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
      omega

/-
Subtraction distributes over addition for Finsupps if subtrahends are smaller.
`(a + b) - (c + d) = (a - c) + (b - d)` given `c ≤ a` and `d ≤ b`.
Proof: Extensionality + `nat_add_sub_add_eq_sub_add_sub`.
-/
lemma finsupp_add_sub_add_eq_sub_add_sub {a b c d : ℕ →₀ ℕ} (hc : c ≤ a) (hd : d ≤ b) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
      ext x; simp +decide [ *, Finsupp.sub_apply, Finsupp.add_apply ] ;
      rw [ tsub_add_tsub_comm ( hc x ) ( hd x ) ]

/-
Distributivity of inf over add for Finsupps under a specific condition.
If for every `i`, either `x i = 0` or `a i + b i ≤ x i`, then `(a + b) ⊓ x = (a ⊓ x) + (b ⊓ x)`.
Proof:
Pointwise:
If `x i = 0`: LHS = 0, RHS = 0 + 0 = 0.
If `a i + b i ≤ x i`:
LHS = `a i + b i`.
`a i ≤ a i + b i ≤ x i`, so `a i ⊓ x i = a i`.
`b i ≤ a i + b i ≤ x i`, so `b i ⊓ x i = b i`.
RHS = `a i + b i`.
Matches.
-/
lemma finsupp_inf_add_eq_add_inf_of_le_or_eq_zero {a b x : ℕ →₀ ℕ} (h : ∀ i, x i = 0 ∨ a i + b i ≤ x i) :
    (a + b) ⊓ x = (a ⊓ x) + (b ⊓ x) := by
      -- By checking each case, we can conclude that the equality holds for all i.
      ext i
      cases h i <;> simp [*, Finsupp.single_apply];
      cases min_cases ( a i ) ( x i ) <;> cases min_cases ( b i ) ( x i ) <;> linarith

/-
The first component of `coprimeSplit` distributes over multiplication.
Proof:
1. Exponents:
   LHS exponents: `(a * b).exponents ⊓ x.exponents`.
   RHS exponents: `(a.exponents ⊓ x.exponents) + (b.exponents ⊓ x.exponents)`.
   Equality holds by `finsupp_inf_add_eq_add_inf_of_le_or_eq_zero`.
   Condition `∀ i, x i = 0 ∨ a i + b i ≤ x i` holds because `a * b ∣ x * y` and `x, y` coprime implies `a i + b i ≤ x i` whenever `x i > 0`.
2. Exp_p1:
   If `x.exp_p1 = 0`: LHS = 0, RHS = `min(0 + 0, 2) = 0`.
   If `x.exp_p1 ≠ 0`: LHS = `(a * b).exp_p1`, RHS = `min(a.exp_p1 + b.exp_p1, 2)`.
   Matches by definition of multiplication.
-/
lemma CollapsingMonoid.coprimeSplit_mul_fst {x y a b : CollapsingMonoid} (hxy : AreCoprime x y)
    (hab : a * b ∣ x * y) :
    (CollapsingMonoid.coprimeSplit x y (a * b)).1 =
    (CollapsingMonoid.coprimeSplit x y a).1 * (CollapsingMonoid.coprimeSplit x y b).1 := by
      have h_split_dist : (a * b).exponents ⊓ x.exponents = (a.exponents ⊓ x.exponents) + (b.exponents ⊓ x.exponents) := by
        have h_cond : ∀ i, x.exponents i = 0 ∨ (a.exponents i + b.exponents i) ≤ x.exponents i := by
          obtain ⟨ z, hz ⟩ := hab;
          intro i
          by_cases hxi : x.exponents i = 0 ; simp_all +decide [ CollapsingMonoid.mul_exp_p1, CollapsingMonoid.mul_exponents ];
          have := hxy ( pn i ) ; simp_all +decide [ CollapsingMonoid.pn_irreducible ] ;
          contrapose! this; simp_all +decide [ CollapsingMonoid.pn_irreducible, CollapsingMonoid.pn_dvd_iff ] ;
          replace hz := congr_arg ( fun m => m.exponents i ) hz ; simp_all +decide [ CollapsingMonoid.mul_exp_p1, CollapsingMonoid.mul_exponents ];
          exact ⟨ CollapsingMonoid.pn_irreducible i, Nat.pos_of_ne_zero hxi, by linarith ⟩
        convert finsupp_inf_add_eq_add_inf_of_le_or_eq_zero h_cond using 1;
      unfold CollapsingMonoid.CollapsingMonoid.coprimeSplit; aesop;

/-
The second component of `coprimeSplit` distributes over multiplication.
Proof:
1. Exponents:
   LHS: `(a * b).exponents - ((a * b).exponents ⊓ x.exponents)`.
   RHS: `(a.exponents - (a.exponents ⊓ x.exponents)) + (b.exponents - (b.exponents ⊓ x.exponents))`.
   Using `finsupp_inf_add_eq_add_inf_of_le_or_eq_zero` (condition holds as before), LHS becomes `(a + b) - ((a ⊓ x) + (b ⊓ x))`.
   Using `finsupp_add_sub_add_eq_sub_add_sub` with `c = a ⊓ x` and `d = b ⊓ x`, this equals RHS.
   Note `a ⊓ x ≤ a` and `b ⊓ x ≤ b` holds.
2. Exp_p1:
   If `x.exp_p1 = 0`:
     LHS: `(a * b).exp_p1`.
     RHS: `a.exp_p1 + b.exp_p1` (capped at 2).
     Matches.
   If `x.exp_p1 ≠ 0`:
     LHS: 0.
     RHS: `0 + 0 = 0`.
     Matches.
-/
lemma CollapsingMonoid.coprimeSplit_mul_snd {x y a b : CollapsingMonoid} (hxy : AreCoprime x y)
    (hab : a * b ∣ x * y) :
    (CollapsingMonoid.coprimeSplit x y (a * b)).2 =
    (CollapsingMonoid.coprimeSplit x y a).2 * (CollapsingMonoid.coprimeSplit x y b).2 := by
      unfold CollapsingMonoid.CollapsingMonoid.coprimeSplit;
      simp +zetaDelta at *;
      congr 1;
      · cases eq_or_ne x.exp_p1 0 <;> aesop;
      · convert finsupp_add_sub_add_eq_sub_add_sub _ _ using 1;
        · have h_inf_add : ∀ i, x.exponents i = 0 ∨ a.exponents i + b.exponents i ≤ x.exponents i := by
            -- Since $a * b \mid x * y$, we have $a.exponents i + b.exponents i \leq x.exponents i + y.exponents i$ for all $i$.
            have h_div : ∀ i, a.exponents i + b.exponents i ≤ x.exponents i + y.exponents i := by
              intro i
              have h_le : (a * b).exponents i ≤ (x * y).exponents i := by
                obtain ⟨ c, hc ⟩ := hab;
                norm_num [ hc, CollapsingMonoid.mul_exponents ];
              convert h_le using 1;
            intros i
            by_cases hxi : x.exponents i = 0;
            · exact Or.inl hxi;
            · have := hxy (pn i) ; simp_all +decide [ pn_dvd_iff ];
              exact le_trans ( h_div i ) ( by rw [ this ( by exact CollapsingMonoid.pn_irreducible i ) ( Nat.pos_of_ne_zero hxi ) ] ; simp +decide );
          exact congr_arg _ ( finsupp_inf_add_eq_add_inf_of_le_or_eq_zero h_inf_add );
        · exact inf_le_left;
        · exact inf_le_left

/-
`coprimeSplit` distributes over multiplication.
Proof:
Combine `coprimeSplit_mul_fst` and `coprimeSplit_mul_snd`.
`fst`: `(coprimeSplit x y (a * b)).1 = (coprimeSplit x y a).1 * (coprimeSplit x y b).1`.
`snd`: `(coprimeSplit x y (a * b)).2 = (coprimeSplit x y a).2 * (coprimeSplit x y b).2`.
So the pair equals `(ua * ub, va * vb)`.
-/
lemma CollapsingMonoid.coprimeSplit_mul {x y a b : CollapsingMonoid} (hxy : AreCoprime x y)
    (hab : a * b ∣ x * y) :
    CollapsingMonoid.coprimeSplit x y (a * b) =
    let (ua, va) := CollapsingMonoid.coprimeSplit x y a
    let (ub, vb) := CollapsingMonoid.coprimeSplit x y b
    (ua * ub, va * vb) := by
      convert congr_arg₂ Prod.mk ( CollapsingMonoid.coprimeSplit_mul_fst hxy hab ) ( CollapsingMonoid.coprimeSplit_mul_snd hxy hab ) using 1

end AristotleLemmas

theorem collapsing_CFI : CFI CollapsingMonoid := by
  intro x y hxy
  rw [areCoprime_iff] at hxy
  obtain ⟨h_exp_coprime, h_f_coprime⟩ := hxy
  constructor
  · -- Injectivity
    intro p1 p2 heq
    obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := p1
    obtain ⟨⟨f', hf'⟩, ⟨g', hg'⟩⟩ := p2
    simp only [labeledFactorizationMul, Subtype.mk.injEq] at heq
    -- heq : f * g = f' * g' (pointwise)
    -- Since x, y are coprime, the components separate uniquely
    simp_all +decide [ funext_iff, Fin.forall_fin_two ];
    -- Apply the coprimeSplit properties to each pair (f i, g i) and (f' i, g' i).
    have h_split_eq : ∀ i : Fin 2, CollapsingMonoid.coprimeSplit x y (f i * g i) = (f i, g i) ∧ CollapsingMonoid.coprimeSplit x y (f' i * g' i) = (f' i, g' i) := by
      intro i
      have h_coprime : AreCoprime x y := by
        rw [ areCoprime_iff ];
        exact ⟨ by cases h_exp_coprime <;> simp +decide [ * ], h_f_coprime ⟩
      have h_div : f i ∣ x ∧ g i ∣ y ∧ f' i ∣ x ∧ g' i ∣ y := by
        exact ⟨ hf.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), hg.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), hf'.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), hg'.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ⟩
      exact ⟨CollapsingMonoid.coprimeSplit_eq_of_mul h_coprime h_div.left h_div.right.left, CollapsingMonoid.coprimeSplit_eq_of_mul h_coprime h_div.right.right.left h_div.right.right.right⟩;
    grind
  · -- Surjectivity
    intro ⟨h, hh⟩
    -- Construct the unique preimage by projecting onto x and y supports
    -- Define u and v as the component-wise splits of h.
    use (⟨fun i => (CollapsingMonoid.coprimeSplit x y (h i)).1, by
      -- Since $h$ is a labeled factorization of $x * y$, we have $h 0 * h 1 = x * y$.
      have h_prod : (CollapsingMonoid.coprimeSplit x y (h 0)).1 * (CollapsingMonoid.coprimeSplit x y (h 1)).1 = x := by
        have h_prod : (CollapsingMonoid.coprimeSplit x y (h 0 * h 1)).1 = x := by
          have h_prod : CollapsingMonoid.coprimeSplit x y (x * y) = (x, y) := by
            apply CollapsingMonoid.coprimeSplit_eq_of_mul (by
            rw [areCoprime_iff];
            exact?);
            · exact dvd_rfl;
            · exact dvd_rfl;
          unfold LabeledFactorizations at hh; aesop;
        have h_prod : (CollapsingMonoid.coprimeSplit x y (h 0 * h 1)).1 = (CollapsingMonoid.coprimeSplit x y (h 0)).1 * (CollapsingMonoid.coprimeSplit x y (h 1)).1 := by
          apply CollapsingMonoid.coprimeSplit_mul_fst;
          · rw [ areCoprime_iff ] ; aesop;
          · unfold LabeledFactorizations at hh; aesop;
        exact h_prod.symm.trans ‹_›;
      -- By definition of labeled factorization, we need to show that the product of the first components equals x.
      apply Eq.symm; exact (by
        have := hh
        convert h_prod.symm using 1 ; simp +decide [ Fin.prod_univ_two ])⟩, ⟨fun i => (CollapsingMonoid.coprimeSplit x y (h i)).2, by
      have h_prod : (CollapsingMonoid.coprimeSplit x y (h 0)).2 * (CollapsingMonoid.coprimeSplit x y (h 1)).2 = y := by
        have h_prod : (CollapsingMonoid.coprimeSplit x y (h 0)).2 * (CollapsingMonoid.coprimeSplit x y (h 1)).2 = (CollapsingMonoid.coprimeSplit x y (h 0 * h 1)).2 := by
          exact Eq.symm ( CollapsingMonoid.coprimeSplit_mul ( by
            rw [areCoprime_iff];
            exact? ) ( by
            exact hh.symm ▸ by simp +decide [ Fin.prod_univ_two ] ; ) |> congr_arg Prod.snd );
        have h_prod : h 0 * h 1 = x * y := by
          unfold LabeledFactorizations at hh; aesop;
        have := CollapsingMonoid.coprimeSplit_eq_of_mul ( show AreCoprime x y from by
                                                            apply Classical.byContradiction
                                                            intro h_not_coprime;
                                                            exact h_not_coprime <| by rw [ areCoprime_iff ] ; aesop; ) ( show x ∣ x from dvd_rfl ) ( show y ∣ y from dvd_rfl ) ; aesop;
      unfold LabeledFactorizations; aesop;⟩);
    exact Subtype.ext <| funext fun i => CollapsingMonoid.coprimeSplit_spec ( by
      exact ( areCoprime_iff x y ).mpr ⟨ by aesop, by aesop ⟩ ) ( hh ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) |>.1
    skip

/-- CPL holds: atoms p₂, p₃, ... give arbitrarily long coprime tuples. -/
theorem collapsing_CPL : CPL CollapsingMonoid := by
  intro r
  use List.ofFn (fun i : Fin r => pn i.val)
  constructor
  · simp
  constructor
  · intro x hx
    simp at hx
    obtain ⟨i, rfl⟩ := hx
    exact pn_not_isUnit i.val
  · rw [List.pairwise_iff_get]
    intro i j hij
    simp
    intro p hp hdvd_i hdvd_j
    rw [atoms_eq] at hp
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    rcases hp with rfl | ⟨m, rfl⟩
    · exfalso
      obtain ⟨c, hc⟩ := hdvd_i
      have h := congrArg (fun x => x.exp_p1.val) hc
      simp only [mul_exp_p1, p1_exp_p1_val, pn_exp_p1_val] at h
      omega
    · obtain ⟨c1, hc1⟩ := hdvd_i
      obtain ⟨c2, hc2⟩ := hdvd_j
      have h1 := congrArg exponents hc1
      have h2 := congrArg exponents hc2
      simp only [mul_exponents, pn_exponents] at h1 h2
      have hm_i : m = i.val := by
        by_contra hmi
        have := DFunLike.congr_fun h1 m
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
                   Finsupp.single_eq_of_ne hmi] at this
        omega
      have hm_j : m = j.val := by
        by_contra hmj
        have := DFunLike.congr_fun h2 m
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
                   Finsupp.single_eq_of_ne hmj] at this
        omega
      have hcontra : i.val = j.val := hm_i.symm.trans hm_j
      omega

end CollapsingMonoid

end