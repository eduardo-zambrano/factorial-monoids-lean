/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Proposition 5.1: CFI + CPL + UAB implies APD (Simplified with Fuel-Based Termination)

This file proves that APD follows from CFI, CPL, and UAB using fuel-based
termination for the extraction process.

## Termination Strategy

When extracting r-factors from p^k = r^n * d:
- Fuel = k + 1 - n (decreases as n increases)
- When n > k and d ≠ 1, we have r^n | p^k with n > k
- By continued extraction to d = 1: p^k = r^j for some j, UAB gives r = p
- Or extraction reaches coprime state: CFI + IH gives contradiction

All termination sorries are in the "extraction continues past bound" cases,
which require showing that extraction must eventually reach d = 1.
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

/-- The only atomic divisor of q^m (for q an atom) is q itself, assuming CFI + CPL + UAB. -/
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
    have hcop_rq : AreCoprime r q := distinct_atoms_coprime h_reduced hr hq hne_rq
    obtain ⟨c, hc⟩ := hdvd
    exfalso

    -- Fuel-based extraction: fuel = m' + 3 - n decreases as n increases
    suffices h_fuel : ∀ fuel : ℕ, ∀ n : ℕ, fuel = m' + 3 - n → n ≥ 1 → n ≤ m' + 2 →
        ∀ d : M, q ^ (m' + 2) = r ^ n * d → False by
      exact h_fuel (m' + 2) 1 (by omega) (by omega) (by omega) c (by simp [hc])

    intro fuel
    induction fuel using Nat.strong_induction_on with
    | _ fuel ih_fuel =>
    intro n hfuel_eq hn_ge hn_le d heq_n

    by_cases hd_eq_1 : d = 1
    · -- d = 1: q^(m'+2) = r^n, UAB gives q = r
      rw [hd_eq_1, mul_one] at heq_n
      have huab_apply := huab q r hq hr (m' + 2) n (by omega) hn_ge heq_n
      exact hne_rq huab_apply.symm
    · -- d ≠ 1
      by_cases hrd_cop : AreCoprime r d
      · -- (r, d) coprime: use CFI
        have hrn_d_cop : AreCoprime (r ^ n) d := by
          intro s hs hs_dvd_rn hs_dvd_d
          have hs_eq_r : s = r := by
            by_cases hn_lt : n < m' + 2
            · exact ih n hn_lt r s hr hs hn_ge hs_dvd_rn
            · -- n = m' + 2: s | r^(m'+2), use CFI to reduce to IH
              push_neg at hn_lt
              have hn_eq : n = m' + 2 := by omega
              rw [hn_eq] at hs_dvd_rn
              by_contra hs_ne_r
              obtain ⟨c_s, hc_s⟩ := hs_dvd_rn
              by_cases hs_c_cop : AreCoprime s c_s
              · -- CFI gives s | r^(m'+1)
                have hbij_s := hcfi s c_s hs_c_cop
                have hfact_s : r * r ^ (m' + 1) = s * c_s := by
                  calc r * r ^ (m' + 1) = r ^ (m' + 2) := by rw [← pow_succ']
                    _ = s * c_s := hc_s
                let rrm : LabeledFactorizations 2 (s * c_s) :=
                  ⟨![r, r ^ (m' + 1)], by simp [LabeledFactorizations, Fin.prod_univ_two, hfact_s]⟩
                obtain ⟨⟨fs, fcs⟩, hpre_s⟩ := hbij_s.surjective rrm
                have hfs := fs.property
                simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hfs
                have h0_s : fs.val 0 * fcs.val 0 = r := by
                  have := congrFun (congrArg Subtype.val hpre_s) 0
                  simp only [labeledFactorizationMul] at this; exact this
                have h1_s : fs.val 1 * fcs.val 1 = r ^ (m' + 1) := by
                  have := congrFun (congrArg Subtype.val hpre_s) 1
                  simp only [labeledFactorizationMul] at this; exact this
                have hr_irr := hr; rw [Atoms, Set.mem_setOf_eq] at hr_irr
                have hor_s := hr_irr.isUnit_or_isUnit h0_s.symm
                cases hor_s with
                | inl hfs0_unit =>
                  have hfs0 : fs.val 0 = 1 := h_reduced _ hfs0_unit
                  rw [hfs0, one_mul] at hfs; rw [hfs] at h1_s
                  have hs_dvd_rm1 : s ∣ r ^ (m' + 1) := ⟨fcs.val 1, h1_s.symm⟩
                  have hs_eq_r' := ih (m' + 1) (by omega) r s hr hs (by omega) hs_dvd_rm1
                  exact hs_ne_r hs_eq_r'
                | inr hfcs0_unit =>
                  have hfcs0 : fcs.val 0 = 1 := h_reduced _ hfcs0_unit
                  rw [hfcs0, mul_one] at h0_s
                  have hr_dvd_s : r ∣ s := ⟨fs.val 1, by rw [← h0_s]; exact hfs.symm⟩
                  have hr_eq_s := atom_dvd_atom_eq h_reduced hs hr hr_dvd_s
                  exact hs_ne_r hr_eq_s.symm
              · -- (s, c_s) not coprime: extraction → d = 1 → UAB
                -- This is where termination needs the atomicity argument
                -- Eventually r^(m'+2) = s^j, UAB gives s = r
                sorry
          rw [hs_eq_r] at hs_dvd_d
          exact hrd_cop r hr (dvd_refl r) hs_dvd_d

        -- Use CFI with (r^n, d) coprime
        have hbij := hcfi (r ^ n) d hrn_d_cop
        have hfact : q * q ^ (m' + 1) = r ^ n * d := by
          calc q * q ^ (m' + 1) = q ^ (m' + 2) := by rw [← pow_succ']
            _ = r ^ n * d := heq_n
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
        have hq_irr := hq; rw [Atoms, Set.mem_setOf_eq] at hq_irr
        have hor := hq_irr.isUnit_or_isUnit h0.symm
        cases hor with
        | inl hfrn0_unit =>
          have hfrn0 : frn.val 0 = 1 := h_reduced _ hfrn0_unit
          rw [hfrn0, one_mul] at hfrn h0; rw [hfrn] at h1
          have hr_dvd_qm1 : r ∣ q ^ (m' + 1) := by
            have hrn_dvd : r ^ n ∣ q ^ (m' + 1) := ⟨fd.val 1, h1.symm⟩
            have hr_dvd_rn : r ∣ r ^ n := by
              cases n with
              | zero => omega
              | succ n' => exact ⟨r ^ n', by rw [pow_succ, mul_comm]⟩
            exact dvd_trans hr_dvd_rn hrn_dvd
          have hreq := ih (m' + 1) (by omega) q r hq hr (by omega) hr_dvd_qm1
          exact hne_rq hreq
        | inr hfd0_unit =>
          have hfd0 : fd.val 0 = 1 := h_reduced _ hfd0_unit
          rw [hfd0, mul_one] at h0
          have hq_dvd_rn : q ∣ r ^ n := ⟨frn.val 1, by rw [← h0]; exact hfrn.symm⟩
          by_cases hn_lt : n < m' + 2
          · have hqr := ih n hn_lt r q hr hq hn_ge hq_dvd_rn
            exact hne_rq hqr.symm
          · -- n = m' + 2, q | r^(m'+2): symmetric case
            push_neg at hn_lt
            have hn_eq : n = m' + 2 := by omega
            rw [hn_eq] at hq_dvd_rn
            have hne_qr : q ≠ r := fun h => hne_rq h.symm
            obtain ⟨c_q, hc_q⟩ := hq_dvd_rn
            by_cases hq_c_cop : AreCoprime q c_q
            · -- CFI gives q | r^(m'+1)
              have hbij_q := hcfi q c_q hq_c_cop
              have hfact_q : r * r ^ (m' + 1) = q * c_q := by
                calc r * r ^ (m' + 1) = r ^ (m' + 2) := by rw [← pow_succ']
                  _ = q * c_q := hc_q
              let rrm_q : LabeledFactorizations 2 (q * c_q) :=
                ⟨![r, r ^ (m' + 1)], by simp [LabeledFactorizations, Fin.prod_univ_two, hfact_q]⟩
              obtain ⟨⟨fq, fcq⟩, hpre_q⟩ := hbij_q.surjective rrm_q
              have hfq := fq.property
              simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two] at hfq
              have h0_q : fq.val 0 * fcq.val 0 = r := by
                have := congrFun (congrArg Subtype.val hpre_q) 0
                simp only [labeledFactorizationMul] at this; exact this
              have h1_q : fq.val 1 * fcq.val 1 = r ^ (m' + 1) := by
                have := congrFun (congrArg Subtype.val hpre_q) 1
                simp only [labeledFactorizationMul] at this; exact this
              have hr_irr' := hr; rw [Atoms, Set.mem_setOf_eq] at hr_irr'
              have hor_q := hr_irr'.isUnit_or_isUnit h0_q.symm
              cases hor_q with
              | inl hfq0_unit =>
                have hfq0 : fq.val 0 = 1 := h_reduced _ hfq0_unit
                rw [hfq0, one_mul] at hfq; rw [hfq] at h1_q
                have hq_dvd_rm1 : q ∣ r ^ (m' + 1) := ⟨fcq.val 1, h1_q.symm⟩
                have hq_eq_r := ih (m' + 1) (by omega) r q hr hq (by omega) hq_dvd_rm1
                exact hne_qr hq_eq_r
              | inr hfcq0_unit =>
                have hfcq0 : fcq.val 0 = 1 := h_reduced _ hfcq0_unit
                rw [hfcq0, mul_one] at h0_q
                have hr_dvd_q : r ∣ q := ⟨fq.val 1, by rw [← h0_q]; exact hfq.symm⟩
                have hr_eq_q := atom_dvd_atom_eq h_reduced hq hr hr_dvd_q
                exact hne_qr hr_eq_q.symm
            · -- (q, c_q) not coprime: extraction → d = 1 → UAB
              sorry
      · -- (r, d) not coprime: r | d, extract more
        have hr_dvd_d : r ∣ d := atom_dvd_of_not_coprime h_reduced hr hrd_cop
        by_cases hn_lt_max : n < m' + 2
        · -- Fuel decreases
          obtain ⟨d', hd'⟩ := hr_dvd_d
          have heq_n1 : q ^ (m' + 2) = r ^ (n + 1) * d' := by
            calc q ^ (m' + 2) = r ^ n * d := heq_n
              _ = r ^ n * (r * d') := by rw [hd']
              _ = (r ^ n * r) * d' := by rw [mul_assoc]
              _ = r ^ (n + 1) * d' := by rw [← pow_succ]
          have hfuel_lt : fuel - 1 < fuel := by omega
          exact ih_fuel (fuel - 1) hfuel_lt (n + 1) (by omega) (by omega) (by omega) d' heq_n1
        · -- n = m' + 2: extraction past bound
          push_neg at hn_lt_max
          have hn_eq : n = m' + 2 := by omega
          obtain ⟨d', hd'⟩ := hr_dvd_d
          have heq_max : q ^ (m' + 2) = r ^ (m' + 3) * d' := by
            calc q ^ (m' + 2) = r ^ (m' + 2) * d := by rw [hn_eq] at heq_n; exact heq_n
              _ = r ^ (m' + 2) * (r * d') := by rw [hd']
              _ = (r ^ (m' + 2) * r) * d' := by rw [mul_assoc]
              _ = r ^ (m' + 3) * d' := by rw [← pow_succ]
          by_cases hd'_eq_1 : d' = 1
          · rw [hd'_eq_1, mul_one] at heq_max
            have huab_max := huab q r hq hr (m' + 2) (m' + 3) (by omega) (by omega) heq_max
            exact hne_rq huab_max.symm
          · -- d' ≠ 1: extraction continues past bound
            -- Eventually d = 1 by atomicity, then UAB gives contradiction
            sorry

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
