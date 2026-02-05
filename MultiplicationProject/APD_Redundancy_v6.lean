/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Proposition 5.1: CFI + CPL + UAB implies APD

This file proves that APD follows from CFI, CPL, and UAB.

## Proof Strategy (Nat.find + CFI)

Strong induction on m. For the inductive step m = m'+2 with r | q^(m'+2):

- **Case r^(m'+2) ∤ q^(m'+2)**: Use Nat.find to get the maximal n ≤ m'+1
  with r^n | q^(m'+2). Then AreCoprime(r^n, d) follows from the IH
  (since n < m'+2), and CFI gives the contradiction. (Sorry-free.)

- **Case r^(m'+2) | q^(m'+2)**: If d = 1, UAB gives q = r. If d ≠ 1,
  this is the single remaining sorry — it requires showing that r^(m'+2)
  cannot properly divide q^(m'+2) when r ≠ q. The mathematical argument
  uses atomicity to bound extraction, but formalizing the well-foundedness
  without cancellativity (derived AFTER APD) requires subtle machinery.
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

/-! ## Main Theorem -/

/-- The only atomic divisor of q^m (for q an atom) is q itself, assuming CFI + CPL + UAB.

Proof structure (restructured to use Nat.find for maximal extraction):
- Strong induction on m.
- For m = m'+2: case-split on whether r^(m'+2) | q^(m'+2).
- If NOT: use Nat.find to get maximal n ≤ m'+1 with r^n | q^(m'+2),
  then AreCoprime(r^n, d) by IH, and CFI gives contradiction. (Sorry-free.)
- If YES: UAB handles d = 1; d ≠ 1 is the single remaining sorry. -/
lemma atom_dvd_pow_eq_with_UAB (h_reduced : Reduced M) (h_atomic : Atomic M)
    (hcfi : CFI M) (hcpl : CPL M) (huab : UAB M)
    {q : M} (hq : q ∈ Atoms M) {r : M} (hr : r ∈ Atoms M) :
    ∀ m : ℕ, m ≥ 1 → r ∣ q ^ m → r = q := by
  suffices h_univ : ∀ m : ℕ, ∀ q r : M, q ∈ Atoms M → r ∈ Atoms M →
      m ≥ 1 → r ∣ q ^ m → r = q by
    intro m hm hdvd
    exact h_univ m q r hq hr hm hdvd
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro q r hq hr hm hdvd
  match m with
  | 0 => omega
  | 1 => simp at hdvd; exact atom_dvd_atom_eq h_reduced hq hr hdvd
  | m' + 2 =>
    by_contra hrq
    have hne_rq : r ≠ q := hrq
    exfalso
    by_cases h_high : r ^ (m' + 2) ∣ q ^ (m' + 2)
    · -- Case 1: r^(m'+2) | q^(m'+2)
      obtain ⟨d, hd⟩ := h_high
      by_cases hd1 : d = 1
      · -- q^(m'+2) = r^(m'+2): UAB gives q = r, contradiction
        rw [hd1, mul_one] at hd
        exact hne_rq (huab q r hq hr (m' + 2) (m' + 2) (by omega) (by omega) hd).symm
      · -- q^(m'+2) = r^(m'+2) * d with d ≠ 1
        -- This case requires showing that r^(m'+2) cannot properly divide q^(m'+2)
        -- when r ≠ q are atoms. The mathematical argument uses atomicity to bound
        -- the extraction process, but formalizing well-foundedness without
        -- cancellativity (derived AFTER APD) requires subtle machinery.
        sorry
    · -- Case 2: r^(m'+2) ∤ q^(m'+2) — fully resolved via Nat.find + CFI
      -- Find the first n where r^n ∤ q^(m'+2) using classical well-ordering
      have h_exists : ∃ n, ¬ (r ^ n ∣ q ^ (m' + 2)) := ⟨m' + 2, h_high⟩
      set n₀ := Nat.find h_exists with hn₀_def
      have hn₀_spec : ¬ (r ^ n₀ ∣ q ^ (m' + 2)) := Nat.find_spec h_exists
      -- For all j < n₀, r^j | q^(m'+2) (by minimality of n₀)
      have hn₀_min : ∀ j, j < n₀ → r ^ j ∣ q ^ (m' + 2) := by
        intro j hj
        exact not_not.mp (Nat.find_min h_exists hj)
      -- n₀ ≥ 2: r^0 = 1 divides anything, r^1 = r divides q^(m'+2) by hypothesis
      have hn₀_ge : n₀ ≥ 2 := by
        have h0 : n₀ ≠ 0 := by
          intro h; rw [h, pow_zero] at hn₀_spec; exact hn₀_spec (one_dvd _)
        have h1 : n₀ ≠ 1 := by
          intro h; rw [h, pow_one] at hn₀_spec; exact hn₀_spec hdvd
        omega
      -- n₀ ≤ m'+2: since r^(m'+2) ∤ q^(m'+2) and n₀ is the first such n
      have hn₀_le : n₀ ≤ m' + 2 := by
        by_contra h_gt
        push_neg at h_gt
        exact h_high (hn₀_min (m' + 2) (by omega))
      -- Set n := n₀ - 1 (the maximal power of r dividing q^(m'+2))
      set n := n₀ - 1 with hn_def
      have hn_ge : n ≥ 1 := by omega
      have hn_le : n ≤ m' + 1 := by omega
      have hn_dvd : r ^ n ∣ q ^ (m' + 2) := hn₀_min n (by omega)
      have hn_not_dvd : ¬ (r ^ (n + 1) ∣ q ^ (m' + 2)) := by
        have h_eq : n + 1 = n₀ := by omega
        rw [h_eq]; exact hn₀_spec
      -- Write q^(m'+2) = r^n * d
      obtain ⟨d, heq⟩ := hn_dvd
      -- AreCoprime(r, d): if r | d then r^(n+1) | q^(m'+2), contradicting maximality
      have hrd_cop : AreCoprime r d := by
        intro p hp hp_r hp_d
        have hp_eq_r : p = r := atom_dvd_atom_eq h_reduced hr hp hp_r
        rw [hp_eq_r] at hp_d
        apply hn_not_dvd
        obtain ⟨d', hd'⟩ := hp_d
        exact ⟨d', by rw [heq, hd', ← mul_assoc, ← pow_succ]⟩
      -- AreCoprime(r^n, d): any atom dividing r^n equals r (by IH, since n ≤ m'+1),
      -- and r ∤ d by AreCoprime(r, d)
      have hrn_d_cop : AreCoprime (r ^ n) d := by
        intro s hs hs_rn hs_d
        have hs_eq_r : s = r := ih n (by omega) r s hr hs hn_ge hs_rn
        rw [hs_eq_r] at hs_d
        exact hrd_cop r hr (dvd_refl r) hs_d
      -- Apply CFI to the coprime pair (r^n, d) with product q^(m'+2)
      have hbij := hcfi (r ^ n) d hrn_d_cop
      have hfact : q * q ^ (m' + 1) = r ^ n * d := by
        calc q * q ^ (m' + 1) = q ^ (m' + 2) := by rw [← pow_succ']
          _ = r ^ n * d := heq
      let qqm : LabeledFactorizations 2 (r ^ n * d) :=
        ⟨![q, q ^ (m' + 1)], by simp [LabeledFactorizations, Fin.prod_univ_two, hfact]⟩
      obtain ⟨⟨frn, fd⟩, hpre⟩ := hbij.surjective qqm
      have hfrn := frn.property; have hfd := fd.property
      simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hfrn hfd
      have h0 : frn.val 0 * fd.val 0 = q := by
        have := congrFun (congrArg Subtype.val hpre) 0
        simp only [labeledFactorizationMul] at this; exact this
      have h1 : frn.val 1 * fd.val 1 = q ^ (m' + 1) := by
        have := congrFun (congrArg Subtype.val hpre) 1
        simp only [labeledFactorizationMul] at this; exact this
      -- q is irreducible, so in frn.val 0 * fd.val 0 = q, one factor is a unit
      have hq_irr := hq; rw [Atoms, Set.mem_setOf_eq] at hq_irr
      have hor := hq_irr.isUnit_or_isUnit h0.symm
      cases hor with
      | inl hfrn0_unit =>
        -- frn.val 0 is a unit, hence = 1 (reduced)
        have hfrn0 : frn.val 0 = 1 := h_reduced _ hfrn0_unit
        rw [hfrn0, one_mul] at hfrn; rw [hfrn] at h1
        -- h1: r^n * fd.val 1 = q^(m'+1), so r | q^(m'+1)
        have hr_dvd_qm1 : r ∣ q ^ (m' + 1) :=
          dvd_trans (dvd_pow_self r (by omega : n ≠ 0)) ⟨fd.val 1, h1.symm⟩
        -- By IH (m'+1 < m'+2): r = q, contradiction
        exact hne_rq (ih (m' + 1) (by omega) q r hq hr (by omega) hr_dvd_qm1)
      | inr hfd0_unit =>
        -- fd.val 0 is a unit, hence = 1 (reduced)
        have hfd0 : fd.val 0 = 1 := h_reduced _ hfd0_unit
        rw [hfd0, mul_one] at h0
        -- h0: frn.val 0 = q and hfrn: frn.val 0 * frn.val 1 = r^n
        -- So q | r^n
        have hq_dvd_rn : q ∣ r ^ n := ⟨frn.val 1, by rw [← h0]; exact hfrn.symm⟩
        -- By IH (n ≤ m'+1 < m'+2): q = r, contradiction
        exact hne_rq (ih n (by omega) r q hr hq hn_ge hq_dvd_rn).symm

/-- Main theorem: CFI + CPL + UAB implies APD (Proposition 5.1). -/
theorem CFI_CPL_UAB_implies_APD (h_reduced : Reduced M) (h_atomic : Atomic M) :
    CFI M → CPL M → UAB M → APD M := by
  intro hcfi hcpl huab
  rw [APD]
  intro p q hp hq k hdvd
  cases k with
  | zero =>
    simp at hdvd
    rw [Atoms, Set.mem_setOf_eq] at hq
    exact absurd (isUnit_of_dvd_one hdvd) hq.not_isUnit
  | succ k' =>
    exact atom_dvd_pow_eq_with_UAB h_reduced h_atomic hcfi hcpl huab hp hq (k' + 1) (by omega) hdvd

end
