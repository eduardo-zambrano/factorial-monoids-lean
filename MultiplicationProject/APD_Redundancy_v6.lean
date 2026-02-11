/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Proposition 5.1: CFI + UAB + ACCP implies APD

This file proves Proposition 5.1 from the paper: CFI + UAB + ACCP ⟹ APD.
The paper uses {PP-D, UAB, CFI, CPL} as its four axioms with ACCP as a base
assumption on the monoid. CPL is not needed for this result; it enters only
through the main theorem (Theorem 9.1) to force infinitely many atoms.

ACCP (Ascending Chain Condition on Principal ideals) provides well-foundedness
of strict divisibility. It is a standard condition in commutative algebra,
strictly between "atomic" and "UFD." In cancellative monoids ACCP follows
from atomicity; in our non-cancellative setting it is an additional assumption.

## Proof Strategy (ACCP + WF induction + CFI)

Well-founded induction on elements via ACCP. For an atom-power x = t^j
and an atom s dividing x with s ≠ t:

1. **Extract maximal s-power**: x = s^m * c with s ∤ c (via ACCP).
2. **If c is a unit**: t^j = s^m, so UAB gives t = s, contradiction.
3. **If c is not a unit**: StrictDvd(s^m, t^j), so the WF induction hypothesis
   gives: every atom dividing s^m equals s. Combined with s ∤ c (maximality),
   this gives AreCoprime(s^m, c). Then CFI + irreducibility of t yields s = t,
   contradiction.
-/

import MultiplicationProject.Basic

open scoped Classical

set_option maxHeartbeats 0

noncomputable section

variable {M : Type*} [CommMonoid M]

/-! ## Preliminary Lemmas -/

/-- In a reduced monoid, the only divisors of an atom are 1 and itself. -/
lemma atom_divisors_eq (h_reduced : Reduced M) {a : M} (ha : a ∈ Atoms M) (x : M) (hx : x ∣ a) :
    x = 1 ∨ x = a := by
  obtain ⟨y, hy⟩ := hx
  have hirr := ha
  rw [Atoms, Set.mem_setOf_eq] at hirr
  have h := hirr.isUnit_or_isUnit hy
  cases h with
  | inl hxu => left; exact h_reduced x hxu
  | inr hyu => right; have hy1 := h_reduced y hyu; rw [hy1, mul_one] at hy; exact hy.symm

/-- The only atom dividing an atom a is a itself. -/
lemma atom_dvd_atom_eq (h_reduced : Reduced M) {a b : M} (ha : a ∈ Atoms M) (hb : b ∈ Atoms M)
    (hdvd : b ∣ a) : b = a := by
  have h := atom_divisors_eq h_reduced ha b hdvd
  cases h with
  | inl hb1 =>
    exfalso
    rw [Atoms, Set.mem_setOf_eq] at hb
    rw [hb1] at hb
    exact hb.not_isUnit isUnit_one
  | inr hba => exact hba

/-- Two distinct atoms are coprime. -/
theorem distinct_atoms_coprime (h_reduced : Reduced M) {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M)
    (hne : p ≠ q) : AreCoprime p q := by
  intro a ha hdvd_p hdvd_q
  have hap : a = p := atom_dvd_atom_eq h_reduced hp ha hdvd_p
  have haq : a = q := atom_dvd_atom_eq h_reduced hq ha hdvd_q
  rw [hap] at haq
  exact hne haq

/-- If q is an atom and (q, c) are not coprime, then q | c. -/
lemma atom_dvd_of_not_coprime (h_reduced : Reduced M) {q c : M}
    (hq : q ∈ Atoms M) (hnotcop : ¬ AreCoprime q c) : q ∣ c := by
  rw [AreCoprime] at hnotcop
  push_neg at hnotcop
  obtain ⟨r, hr, hr_dvd_q, hr_dvd_c⟩ := hnotcop
  have hrq : r = q := atom_dvd_atom_eq h_reduced hq hr hr_dvd_q
  rw [← hrq]
  exact hr_dvd_c

/-! ## Maximal atom-power extraction via ACCP -/

/-- In a reduced monoid with ACCP, if atom s divides x, we can extract a
    maximal s-power: x = s^m * c where s ∤ c and m ≥ 1.
    The extraction terminates by well-foundedness of StrictDvd. -/
lemma maximal_atom_power_extraction (_h_reduced : Reduced M) (haccp : ACCP M)
    {s x : M} (hs : s ∈ Atoms M) (h_dvd : s ∣ x) :
    ∃ (m : ℕ) (c : M), m ≥ 1 ∧ x = s ^ m * c ∧ ¬(s ∣ c) := by
  -- We induct on x using the well-founded StrictDvd relation
  induction x using haccp.induction with
  | h x ih =>
  obtain ⟨c₀, hc₀⟩ := h_dvd  -- x = s * c₀
  by_cases h_s_c₀ : s ∣ c₀
  · -- s | c₀: write c₀ = s * c₁, so x = s² * c₁. Recurse on c₀.
    -- First show StrictDvd c₀ x
    have h_strict : StrictDvd c₀ x := by
      refine ⟨s, ?_, ?_⟩
      · rw [Atoms, Set.mem_setOf_eq] at hs; exact hs.not_isUnit
      · rw [hc₀, mul_comm]
    obtain ⟨m', c', hm', hc₀_eq, hndvd⟩ := ih c₀ h_strict h_s_c₀
    refine ⟨m' + 1, c', by omega, ?_, hndvd⟩
    rw [hc₀, hc₀_eq, pow_succ']
    rw [mul_assoc]
  · -- s ∤ c₀: done with m = 1
    exact ⟨1, c₀, le_refl 1, by rw [hc₀, pow_one], h_s_c₀⟩

/-! ## Main Theorem -/

/-- The only atomic divisor of t^j (for t an atom) is t itself,
    assuming CFI + UAB + ACCP (Proposition 5.1 in the paper).

    Proof by well-founded induction on elements (via ACCP).
    For x = t^j with atom s | x and s ≠ t:
    - Extract maximal s-power: t^j = s^m * c with s ∤ c.
    - If c is a unit: t^j = s^m → UAB → t = s, contradiction.
    - If c is not a unit: StrictDvd(s^m, t^j), so the WF IH on s^m gives
      every atom dividing s^m equals s. Combined with s ∤ c (maximality),
      AreCoprime(s^m, c). Then CFI + irreducibility of t yields s = t,
      contradiction. -/
lemma atom_dvd_pow_eq_with_UAB (h_reduced : Reduced M)
    (hcfi : CFI M) (huab : UAB M) (haccp : ACCP M)
    {q : M} (hq : q ∈ Atoms M) {r : M} (hr : r ∈ Atoms M) :
    ∀ m : ℕ, m ≥ 1 → r ∣ q ^ m → r = q := by
  -- Reformulate: for every element x, if x = t^j (t atom, j ≥ 1) and
  -- s is an atom dividing x, then s = t.
  -- We prove this by well-founded induction on x (via ACCP).
  suffices key : ∀ x : M,
      (∀ (t : M), t ∈ Atoms M → ∀ (j : ℕ), j ≥ 1 → x = t ^ j →
        ∀ (s : M), s ∈ Atoms M → s ∣ x → s = t) by
    intro m hm hdvd
    exact key (q ^ m) q hq m hm rfl r hr hdvd
  -- Prove by well-founded induction on x using ACCP
  intro x
  induction x using haccp.induction with
  | h x ih =>
  intro t ht j hj hx s hs h_s_dvd
  -- Base case: j = 1
  by_cases hj1 : j = 1
  · subst hj1; rw [pow_one] at hx; subst hx
    exact atom_dvd_atom_eq h_reduced ht hs h_s_dvd
  -- Now j ≥ 2
  have hj_ge2 : j ≥ 2 := by omega
  by_contra h_neq
  exfalso
  -- Step 1: Extract maximal s-power from x = t^j using ACCP
  obtain ⟨m, c, hm_ge, heq, h_ndvd⟩ :=
    maximal_atom_power_extraction h_reduced haccp hs h_s_dvd
  -- heq : x = s^m * c, s ∤ c
  -- Step 2: Case split on whether c is a unit
  by_cases hc_unit : IsUnit c
  · -- c is a unit, hence = 1 in reduced monoid
    have hc1 : c = 1 := h_reduced c hc_unit
    rw [hc1, mul_one] at heq
    -- x = s^m, i.e. t^j = s^m, so UAB gives t = s, contradiction
    rw [hx] at heq
    -- heq : t^j = s^m, i.e. s^m = t^j by .symm
    exact h_neq (huab t s ht hs j m (by omega) hm_ge heq).symm
  · -- c is not a unit
    -- Step 3: StrictDvd(s^m, x) since x = s^m * c with c non-unit
    have h_strict_sm : StrictDvd (s ^ m) x := ⟨c, hc_unit, heq⟩
    -- Step 4: By WF IH on s^m, every atom dividing s^m equals s
    have h_only_s : ∀ (u : M), u ∈ Atoms M → u ∣ s ^ m → u = s := by
      intro u hu hu_dvd
      exact ih (s ^ m) h_strict_sm s hs m hm_ge rfl u hu hu_dvd
    -- Step 5: AreCoprime(s^m, c) — any atom dividing s^m equals s,
    -- and s ∤ c by maximality
    have h_cop : AreCoprime (s ^ m) c := by
      intro p hp hp_sm hp_c
      have hp_eq_s : p = s := h_only_s p hp hp_sm
      rw [hp_eq_s] at hp_c
      exact h_ndvd hp_c
    -- Step 6: Apply CFI to the coprime pair (s^m, c) with product t^j
    rw [hx] at heq
    have hbij := hcfi (s ^ m) c h_cop
    -- Build the factorization (t, t^{j-1}) ∈ F_2(t^j)
    have hfact : t * t ^ (j - 1) = s ^ m * c := by
      have : t * t ^ (j - 1) = t ^ j := by
        have hj_eq : j = j - 1 + 1 := by omega
        conv_rhs => rw [hj_eq, pow_succ']
      rw [this, heq]
    let ttj : LabeledFactorizations 2 (s ^ m * c) :=
      ⟨![t, t ^ (j - 1)], by simp [LabeledFactorizations, Fin.prod_univ_two, hfact]⟩
    obtain ⟨⟨fsm, fc⟩, hpre⟩ := hbij.surjective ttj
    have hfsm := fsm.property; have hfc := fc.property
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hfsm hfc
    have h0 : fsm.val 0 * fc.val 0 = t := by
      have := congrFun (congrArg Subtype.val hpre) 0
      simp only [labeledFactorizationMul] at this; exact this
    have h1 : fsm.val 1 * fc.val 1 = t ^ (j - 1) := by
      have := congrFun (congrArg Subtype.val hpre) 1
      simp only [labeledFactorizationMul] at this; exact this
    -- t is irreducible, so in fsm.val 0 * fc.val 0 = t, one factor is a unit
    have ht_irr := ht; rw [Atoms, Set.mem_setOf_eq] at ht_irr
    have hor := ht_irr.isUnit_or_isUnit h0.symm
    cases hor with
    | inl hfsm0_unit =>
      -- fsm.val 0 is a unit, hence = 1 (reduced)
      have hfsm0 : fsm.val 0 = 1 := h_reduced _ hfsm0_unit
      rw [hfsm0, one_mul] at hfsm; rw [hfsm] at h1
      -- h1: s^m * fc.val 1 = t^(j-1), so s | t^(j-1)
      have hs_dvd_tj1 : s ∣ t ^ (j - 1) :=
        dvd_trans (dvd_pow_self s (by omega : m ≠ 0)) ⟨fc.val 1, h1.symm⟩
      -- StrictDvd(t^{j-1}, x) since x = t^j = t * t^{j-1} and t is not a unit
      have h_strict_tj1 : StrictDvd (t ^ (j - 1)) x := by
        refine ⟨t, ?_, ?_⟩
        · rw [Atoms, Set.mem_setOf_eq] at ht; exact ht.not_isUnit
        · conv_lhs => rw [hx]
          have : t ^ j = t ^ (j - 1) * t := by
            conv_lhs => rw [show j = j - 1 + 1 from by omega, pow_succ]
          rw [this, mul_comm]
      -- By WF IH on t^{j-1}: s = t, contradiction
      exact h_neq (ih (t ^ (j - 1)) h_strict_tj1 t ht (j - 1) (by omega) rfl s hs hs_dvd_tj1)
    | inr hfc0_unit =>
      -- fc.val 0 is a unit, hence = 1 (reduced)
      have hfc0 : fc.val 0 = 1 := h_reduced _ hfc0_unit
      rw [hfc0, mul_one] at h0
      -- h0: fsm.val 0 = t and hfsm: fsm.val 0 * fsm.val 1 = s^m
      -- So t | s^m
      have ht_dvd_sm : t ∣ s ^ m := ⟨fsm.val 1, by rw [← h0]; exact hfsm.symm⟩
      -- By WF IH on s^m: t = s, contradiction
      exact h_neq (ih (s ^ m) h_strict_sm s hs m hm_ge rfl t ht ht_dvd_sm).symm

/-- Main theorem: CFI + UAB + ACCP implies APD (Proposition 5.1). -/
theorem CFI_UAB_implies_APD (h_reduced : Reduced M) :
    CFI M → UAB M → ACCP M → APD M := by
  intro hcfi huab haccp
  rw [APD]
  intro p q hp hq k hdvd
  cases k with
  | zero =>
    simp at hdvd
    rw [Atoms, Set.mem_setOf_eq] at hq
    exact absurd (isUnit_of_dvd_one hdvd) hq.not_isUnit
  | succ k' =>
    exact atom_dvd_pow_eq_with_UAB h_reduced hcfi huab haccp hp hq (k' + 1) (by omega) hdvd

end
