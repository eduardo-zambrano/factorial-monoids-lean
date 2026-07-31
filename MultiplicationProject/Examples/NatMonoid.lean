/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# The multiplicative monoid of positive integers satisfies all four axioms

This file certifies the necessity-direction witness of the characterization
theorem: (ℕ+, ×) — the paper's (ℕ, ×), i.e., the positive integers under
multiplication — satisfies the base assumptions (reduced, atomic, WFD),
is factorial with countably infinite atom set, and therefore (via
`thm_characterization`) satisfies all four axioms tower faithfulness, TD, CFI, CPL⁺.

Strategy: prove Reduced, Atomic, WFD, Factorial by hand (uniqueness via
Mathlib's `UniqueFactorizationMonoid` instance on ℕ), plus countably
infinite atoms (Euclid); the four axioms then come out of the backward
direction of the characterization iff.
-/
import MultiplicationProject.MainTheorem

set_option maxHeartbeats 400000

noncomputable section

namespace NatMonoidExample

/-! ## Base assumptions -/

/-- ℕ+ is reduced: the only unit is 1. -/
theorem pnat_reduced : Reduced ℕ+ := by
  intro u hu
  have h1 : ((u : ℕ)) = 1 := Nat.isUnit_iff.mp (hu.map PNat.coeMonoidHom)
  exact PNat.coe_injective (by simpa using h1)

/-- Irreducibility transfers between ℕ+ and ℕ along the coercion. -/
theorem pnat_irreducible_iff (q : ℕ+) : Irreducible q ↔ Irreducible (q : ℕ) := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · intro hu
      have h1 : (q : ℕ) = 1 := Nat.isUnit_iff.mp hu
      have hq1 : q = 1 := PNat.coe_injective (by simpa using h1)
      exact hq.1 (hq1 ▸ isUnit_one)
    · intro a b hab
      have ha : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · exfalso; rw [h, zero_mul] at hab; exact q.pos.ne' hab
        · exact h
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · exfalso; rw [h, mul_zero] at hab; exact q.pos.ne' hab
        · exact h
      have hq_eq : q = (⟨a, ha⟩ : ℕ+) * (⟨b, hb⟩ : ℕ+) := by
        apply PNat.coe_injective
        rw [PNat.mul_coe]
        exact hab
      rcases hq.isUnit_or_isUnit hq_eq with h | h
      · left
        have h1 : (⟨a, ha⟩ : ℕ+) = 1 := pnat_reduced _ h
        have h2 : a = 1 := congrArg PNat.val h1
        rw [h2]; exact isUnit_one
      · right
        have h1 : (⟨b, hb⟩ : ℕ+) = 1 := pnat_reduced _ h
        have h2 : b = 1 := congrArg PNat.val h1
        rw [h2]; exact isUnit_one
  · intro hq
    refine ⟨?_, ?_⟩
    · intro hu
      have h1 : q = 1 := pnat_reduced q hu
      apply hq.1
      rw [h1]
      exact isUnit_one
    · intro a b hab
      have hval : (q : ℕ) = (a : ℕ) * (b : ℕ) := by
        rw [hab, PNat.mul_coe]
      rcases hq.isUnit_or_isUnit hval with h | h
      · left
        have h1 : (a : ℕ) = 1 := Nat.isUnit_iff.mp h
        have : a = 1 := PNat.coe_injective (by simpa using h1)
        rw [this]; exact isUnit_one
      · right
        have h1 : (b : ℕ) = 1 := Nat.isUnit_iff.mp h
        have : b = 1 := PNat.coe_injective (by simpa using h1)
        rw [this]; exact isUnit_one

/-- ℕ+ is atomic: strong induction on the value. -/
theorem pnat_atomic : Atomic ℕ+ := by
  suffices H : ∀ N : ℕ, ∀ n : ℕ+, (n : ℕ) ≤ N → ¬IsUnit n →
      ∃ s : Multiset ℕ+, (∀ a ∈ s, Irreducible a) ∧ s.prod = n by
    intro n hn
    exact H (n : ℕ) n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro n hle _
    exact absurd hle (by have := n.pos; omega)
  | succ N ih =>
    intro n hle hn
    by_cases hirr : Irreducible n
    · refine ⟨{n}, ?_, by simp⟩
      intro a ha
      rw [Multiset.mem_singleton.mp ha]
      exact hirr
    · -- n is neither a unit nor irreducible: it splits into two non-units
      have hsplit : ∃ a b : ℕ+, n = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
        by_contra hcon
        push_neg at hcon
        refine hirr ⟨hn, fun a b hab => ?_⟩
        by_cases ha : IsUnit a
        · exact Or.inl ha
        · exact Or.inr (hcon a b hab ha)
      obtain ⟨a, b, hab, ha, hb⟩ := hsplit
      have ha2 : 2 ≤ (a : ℕ) := by
        have h1 : (a : ℕ) ≠ 1 := fun h => ha (by
          have h2 : a = 1 := PNat.coe_injective (by simpa using h)
          rw [h2]; exact isUnit_one)
        have := a.pos
        omega
      have hb2 : 2 ≤ (b : ℕ) := by
        have h1 : (b : ℕ) ≠ 1 := fun h => hb (by
          have h2 : b = 1 := PNat.coe_injective (by simpa using h)
          rw [h2]; exact isUnit_one)
        have := b.pos
        omega
      have hval : (n : ℕ) = (a : ℕ) * (b : ℕ) := by rw [hab, PNat.mul_coe]
      have haN : (a : ℕ) ≤ N := by
        have h2 : (a : ℕ) * 2 ≤ (a : ℕ) * (b : ℕ) := Nat.mul_le_mul_left _ hb2
        have := a.pos
        omega
      have hbN : (b : ℕ) ≤ N := by
        have h2 : 2 * (b : ℕ) ≤ (a : ℕ) * (b : ℕ) := Nat.mul_le_mul_right _ ha2
        have := b.pos
        omega
      obtain ⟨sa, hsa_atoms, hsa_prod⟩ := ih a haN ha
      obtain ⟨sb, hsb_atoms, hsb_prod⟩ := ih b hbN hb
      refine ⟨sa + sb, ?_, ?_⟩
      · intro x hx
        rcases Multiset.mem_add.mp hx with h | h
        · exact hsa_atoms x h
        · exact hsb_atoms x h
      · rw [Multiset.prod_add, hsa_prod, hsb_prod, hab]

/-- ℕ+ satisfies WFD: strict divisibility strictly increases the value. -/
theorem pnat_wfd : WFD ℕ+ := by
  have hsub : Subrelation (fun a b : ℕ+ => StrictDvd a b)
      (InvImage (· < ·) (fun a : ℕ+ => (a : ℕ))) := by
    intro a b hab
    obtain ⟨c, hc_unit, rfl⟩ := hab
    have hc2 : 2 ≤ (c : ℕ) := by
      have h1 : (c : ℕ) ≠ 1 := fun h => hc_unit (by
        have h2 : c = 1 := PNat.coe_injective (by simpa using h)
        rw [h2]; exact isUnit_one)
      have := c.pos
      omega
    show (a : ℕ) < ((a * c : ℕ+) : ℕ)
    rw [PNat.mul_coe]
    have h2 : (a : ℕ) * 2 ≤ (a : ℕ) * (c : ℕ) := Nat.mul_le_mul_left _ hc2
    have := a.pos
    omega
  exact Subrelation.wf hsub (InvImage.wf _ Nat.lt_wfRel.wf)

/-! ## Factorial structure -/

/-- Coercion turns a ℕ+ multiset product into a ℕ multiset product. -/
lemma val_prod (t : Multiset ℕ+) :
    ((t.prod : ℕ+) : ℕ) = (t.map (fun x : ℕ+ => (x : ℕ))).prod := by
  have h := Multiset.prod_hom t PNat.coeMonoidHom
  simpa using h.symm

/-- ℕ+ is factorial: existence from atomicity, uniqueness via the unique
    factorization structure of ℕ. -/
theorem pnat_factorial : Factorial ℕ+ := by
  intro n hn
  obtain ⟨s, hs_atoms, hs_prod⟩ := pnat_atomic n hn
  refine ⟨s, ⟨hs_atoms, hs_prod⟩, ?_⟩
  rintro t ⟨ht_atoms, ht_prod⟩
  -- push both multisets into ℕ and use uniqueness of factorization there
  have hs_irr : ∀ x ∈ s.map (fun q : ℕ+ => (q : ℕ)), Irreducible x := by
    intro x hx
    obtain ⟨q, hq_mem, rfl⟩ := Multiset.mem_map.mp hx
    exact (pnat_irreducible_iff q).mp (hs_atoms q hq_mem)
  have ht_irr : ∀ x ∈ t.map (fun q : ℕ+ => (q : ℕ)), Irreducible x := by
    intro x hx
    obtain ⟨q, hq_mem, rfl⟩ := Multiset.mem_map.mp hx
    exact (pnat_irreducible_iff q).mp (ht_atoms q hq_mem)
  have hprod_eq : (t.map (fun q : ℕ+ => (q : ℕ))).prod
                = (s.map (fun q : ℕ+ => (q : ℕ))).prod := by
    rw [← val_prod, ← val_prod, hs_prod, ht_prod]
  have hrel := UniqueFactorizationMonoid.factors_unique ht_irr hs_irr
    (by rw [hprod_eq]; exact Associated.refl _)

  have heq : t.map (fun q : ℕ+ => (q : ℕ)) = s.map (fun q : ℕ+ => (q : ℕ)) :=
    Multiset.rel_eq.mp (hrel.mono fun a _ b _ h => associated_iff_eq.mp h)
  exact Multiset.map_injective (fun a b hab => PNat.coe_injective hab) heq

/-! ## The atom set is countably infinite -/

/-- The primes are an infinite subset of ℕ (Euclid). -/
lemma infinite_primes : Set.Infinite {p : ℕ | Nat.Prime p} := by
  intro hfin
  exact Nat.not_bddAbove_setOf_prime hfin.bddAbove

theorem pnat_atoms_infinite : Set.Infinite (Atoms ℕ+) := by
  haveI := infinite_primes.to_subtype
  apply Set.infinite_of_injective_forall_mem
    (f := fun p : {p : ℕ | Nat.Prime p} => (⟨p.1, p.2.pos⟩ : ℕ+))
  · intro p q hpq
    apply Subtype.ext
    exact congrArg PNat.val hpq
  · intro p
    show Irreducible _
    exact (pnat_irreducible_iff _).mpr p.2

theorem pnat_atoms_countable : (Atoms ℕ+).Countable :=
  Set.to_countable _

/-! ## Main result: (ℕ+, ×) satisfies everything -/

/-- (ℕ+, ×) satisfies all four axioms — obtained from the backward direction
    of the characterization theorem applied to its factorial structure. -/
theorem pnat_satisfies_axioms : TowerFaithful ℕ+ ∧ TD ℕ+ ∧ CFI ℕ+ ∧ CCA ℕ+ :=
  (thm_characterization pnat_reduced pnat_atomic pnat_wfd).mpr
    ⟨pnat_factorial, pnat_atoms_countable, pnat_atoms_infinite⟩

/-- Summary: (ℕ+, ×) satisfies the base assumptions and all four axioms. -/
theorem pnat_satisfies_all :
    Reduced ℕ+ ∧ Atomic ℕ+ ∧ WFD ℕ+ ∧
    TowerFaithful ℕ+ ∧ TD ℕ+ ∧ CFI ℕ+ ∧ CCA ℕ+ :=
  ⟨pnat_reduced, pnat_atomic, pnat_wfd,
   pnat_satisfies_axioms.1, pnat_satisfies_axioms.2.1,
   pnat_satisfies_axioms.2.2.1, pnat_satisfies_axioms.2.2.2⟩

end NatMonoidExample
