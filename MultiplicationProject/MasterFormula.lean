/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 8: Master Formula and Structural Consequences

This file contains:
- Helper lemmas for the master formula (from Aristotle)
- Placeholders for the main Section 8 results (still in progress)

Main results (when complete):
- `lem_primewise`: Primewise decomposition m = ∏ p^{v_p(m)} (Lemma 8.1)
- `thm_master`: Master formula F_k(m) = ∏ C(v_p(m)+k-1, k-1) (Theorem 8.2)
- `prop_val_additive`: v_p(x·y) = v_p(x) + v_p(y) (Proposition 8.3)
- `cor_factorial`: M ≅ ⊕ℕ₀ (Corollary 8.4)

Also includes Corollary 7.3 (squarefree diagnostic), deferred from Section 7
so that h_prime_atoms can be derived rather than assumed.

Formalized with assistance from Aristotle (uuids: 26ea4588..., b300d104...)
-/

import MultiplicationProject.GlobalMultiplicativity

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Helper Lemmas from Section 8 Aristotle Outputs
-/

/-- If p and q are atoms, and p^k divides q, then k ≤ 1. -/
lemma lemma_pow_dvd_atom {M : Type*} [CommMonoid M] (h_red : Reduced M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : p ^ k ∣ q) :
    k ≤ 1 := by
  unfold Atoms at hq
  cases' h_dvd with a ha
  rcases k with (_ | _ | k) <;> simp_all +decide [pow_succ, mul_assoc]
  rw [irreducible_mul_iff] at hq
  aesop
  · exact hp.1 left_1
  · rw [irreducible_mul_iff] at left
    aesop
    · exact left.not_isUnit left_1
    · exact hp.1 right_1

/-- If an atom q divides a power of an atom p, then q = p.
    This is key for proving that atoms are prime. -/
lemma lemma_atom_dvd_pow {M : Type*} [CommMonoid M] (h_red : Reduced M) (h_ppp : PP_P M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : q ∣ p ^ k) :
    q = p := by
  -- Since q ∣ p^k, we have p^k = q · x for some x
  obtain ⟨x, hx⟩ : ∃ x, p^k = q * x := h_dvd
  -- Since q divides p^k, we have q ∈ powers(p)
  have hq_pow : q ∈ Submonoid.powers p := by
    have := h_ppp p hp q x
    exact this ⟨k, hx⟩ |>.1
  cases hq_pow
  aesop
  rcases w with (_ | _ | w) <;> simp_all +decide [pow_succ]
  · exact absurd hq (by unfold Atoms; aesop)
  · have := hq.isUnit_or_isUnit rfl
    aesop
    · cases hp; aesop
    · cases hp; aesop

/-!
## Recurrence for Factorization Counts

This is used in the inductive proof of coprime multiplicativity.
-/

/-- Recurrence relation: F_{k+1}(m) = ∑_{(u,v) ∈ F_2(m)} F_k(v). -/
lemma count_recurrence {M : Type*} [CommMonoid M] (k : ℕ) (m : M)
    (h_finite_2 : (LabeledFactorizations 2 m).Finite)
    (h_finite_k : ∀ f ∈ LabeledFactorizations 2 m, (LabeledFactorizations k (f 1)).Finite) :
    LabeledFactorizationCount (k + 1) m = ∑ f ∈ h_finite_2.toFinset, LabeledFactorizationCount k (f 1) := by
  unfold LabeledFactorizationCount at *
  have h_recurrence : Set.ncard (LabeledFactorizations (k + 1) m) =
      Set.ncard (⋃ f ∈ h_finite_2.toFinset,
        {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g}) := by
    congr with w
    simp +decide [LabeledFactorizations]
    bound
    · refine' ⟨Fin.cons (w 0) (Fin.cons (Finset.univ.prod (Fin.tail w)) Fin.elim0), _, Fin.tail w, _, _⟩ <;>
        simp +decide [Fin.univ_succ]
      rfl
    · simp +decide [Fin.prod_univ_succ, left_1]
  have h_disjoint : ∀ f g : Fin 2 → M, f ∈ LabeledFactorizations 2 m → g ∈ LabeledFactorizations 2 m → f ≠ g →
      Disjoint {w : Fin (k + 1) → M | ∃ h ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) h}
               {w : Fin (k + 1) → M | ∃ h ∈ LabeledFactorizations k (g 1), w = Fin.cons (g 0) h} := by
    intro f g hf hg hfg
    rw [Set.disjoint_left]
    contrapose! hfg
    aesop
    ext i
    fin_cases i <;> simp_all +decide [LabeledFactorizations]
  have h_card_union : ∀ {S : Finset (Fin 2 → M)}, (∀ f ∈ S, f ∈ LabeledFactorizations 2 m) →
      Set.ncard (⋃ f ∈ S, {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g}) =
      ∑ f ∈ S, Set.ncard {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g} := by
    intro S hS
    induction S using Finset.induction <;> aesop
    rw [← a_2, @Set.ncard_union_eq]
    · exact Set.disjoint_left.mpr fun x hx hx' => by
        rcases Set.mem_iUnion₂.mp hx' with ⟨f, hf, hxf⟩
        exact Set.disjoint_left.mp (h_disjoint a f left (right f hf) (by aesop)) hx hxf
    · exact Set.Finite.subset (Set.Finite.image (fun g => Fin.cons (a 0) g) (h_finite_k a left)) fun x hx => by aesop
    · exact Set.Finite.biUnion (Finset.finite_toSet s) fun f hf =>
        Set.Finite.subset (Set.Finite.image (fun g => Fin.cons (f 0) g) (h_finite_k f (right f hf))) fun x hx => by aesop
  rw [h_recurrence, h_card_union]
  · refine' Finset.sum_congr rfl fun f hf => _
    rw [show {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g} =
            Set.image (fun g : Fin k → M => Fin.cons (f 0) g) (LabeledFactorizations k (f 1)) by ext; aesop]
    rw [Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy]
  · norm_num +zetaDelta at *

/-- Sum reindexing lemma using CFI bijection. -/
lemma sum_split_by_CFI {M : Type*} [CommMonoid M]
    (h_cfi : ∀ x y : M, AreCoprime x y → Function.Bijective
      (fun (p : LabeledFactorizations 2 x × LabeledFactorizations 2 y) => labeledFactorizationMul p.1 p.2))
    (h_finite : ∀ (n : ℕ) (z : M), (LabeledFactorizations n z).Finite)
    (k : ℕ) (x y : M) (h_coprime : AreCoprime x y) :
    ∑ f ∈ (h_finite 2 (x * y)).toFinset, LabeledFactorizationCount k (f 1) =
    ∑ g ∈ (h_finite 2 x).toFinset, ∑ h ∈ (h_finite 2 y).toFinset, LabeledFactorizationCount k (g 1 * h 1) := by
  have := h_cfi x y h_coprime
  rcases this with ⟨h₁, h₂⟩
  have h_bij : Finset.image (fun (p : (Fin 2 → M) × (Fin 2 → M)) => p.1 * p.2)
      ((h_finite 2 x).toFinset ×ˢ (h_finite 2 y).toFinset) = (h_finite 2 (x * y)).toFinset := by
    ext
    constructor
    · simp +decide [LabeledFactorizations]
      aesop
      ac_rfl
    · simp +zetaDelta at *
      intro h
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := h₂ ⟨_, h⟩
      exact ⟨_, _, ⟨a.2, ha.2⟩, rfl⟩
  rw [← h_bij, Finset.sum_image]
  · simp +decide [Finset.sum_product]
  · intro p hp q hq h_eq
    simp_all +decide [Function.Injective, Set.mem_setOf_eq]
    specialize h₁ _ hp.1 _ hp.2 _ hq.1 _ hq.2
    aesop
    · exact h₁ (Subtype.ext h_eq) |>.1
    · exact h₁ (Subtype.ext h_eq) |>.2

/-!
## Corollary 7.3: Squarefree Diagnostic (Deferred from Section 7)

This corollary uses h_prime_atoms, which we can now derive from CFI.
-/

/-- Under PP-D + CFI, atoms are prime: if p ∣ a·b then p ∣ a or p ∣ b. -/
lemma atoms_are_prime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p hp a b h_dvd
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  -- Strategy: Use PP-P to show that the "p-part" of a*b comes from a or b.
  -- If p ∤ a and p ∤ b, we derive a contradiction.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨h_not_a, h_not_b⟩ := h_neg
  -- p | a*b means a*b = p * m for some m
  obtain ⟨m, hm⟩ := h_dvd
  -- Key: use `power_coprime_of_not_in_support` to show p is coprime to a and b
  -- p ∤ a means p ∉ Support a (since if p ∈ Support a, then p | a)
  have hp_not_supp_a : p ∉ Support a := by
    intro h_in
    exact h_not_a h_in.2
  have hp_not_supp_b : p ∉ Support b := by
    intro h_in
    exact h_not_b h_in.2
  -- By power_coprime_of_not_in_support, p^1 = p and a are coprime, similarly for b
  have h_cop_pa : AreCoprime (p ^ 1) a := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_a 1
  have h_cop_pb : AreCoprime (p ^ 1) b := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_b 1
  simp only [pow_one] at h_cop_pa h_cop_pb
  -- Now we need: if p coprime to a and p coprime to b, then p coprime to a*b
  -- This follows because AreCoprime means no common atom divisor
  -- If p | a*b and p coprime to a and p coprime to b, we get a contradiction
  -- p | a*b and p is an atom means p ∈ Support(a*b)
  -- We need to show this contradicts p being coprime to both a and b
  -- The key insight: use CFI on (a, b) if they're coprime, or decompose otherwise
  -- For the general case, we use that p being coprime to a means p ∤ a (for atoms)
  -- Since p is coprime to a: any atom dividing both p and a leads to contradiction
  -- p | p, so if p | a, then p is a common atom divisor, contradicting coprimality
  -- But we already know p ∤ a from h_not_a
  -- The issue is showing p ∤ a*b from p ∤ a and p ∤ b
  -- This requires the "primality" property we're trying to prove!
  -- Alternative: use PP-P directly on the p-power structure
  -- If a*b = p * m, consider the p-adic structure
  -- By PP-P, if p^k | a*b for some k ≥ 1, then the p-power part must come from somewhere
  -- Since p ∤ a means v_p(a) = 0, and p ∤ b means v_p(b) = 0
  -- We should have v_p(a*b) = 0, contradicting p | a*b
  -- The formal proof of v_p additivity requires more machinery
  -- For now, we note this is where PP-P enters: prime powers are factorially closed
  -- means the p-content cannot "appear from nowhere"
  sorry

/-- **Corollary 7.3**: Squarefree diagnostic.

    If m is a product of distinct atoms (squarefree), then F_k(m) = k^ω(m),
    where ω(m) is the number of distinct prime factors.

    Proof: F_k(p) = k for each atom, and coprime multiplicativity gives the product. -/
theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (h_atomic : Atomic M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : ∀ x y : M, AreCoprime x y → Function.Bijective (Function.uncurry (labeledFactorizationMul (k := 2) (x := x) (y := y))))
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length := by
  -- We need atoms_are_prime, which requires finishing the sorry above
  sorry

/-!
## Main Section 8 Results (Placeholders)

These theorems represent the core of Section 8. Aristotle made partial progress
but did not complete them. They will be proven in future Aristotle sessions.
-/

/-- **Lemma 8.1**: Primewise decomposition.

    Under (PP-D), (PP-P), and atomicity, every m ∈ M can be written as
    m = ∏_{p ∈ S} p^{v_p(m)} where S is the support of m. -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_ppd : PP_D M) (h_ppp : PP_P M) (h_atomic : Atomic M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  sorry

/-- **Theorem 8.2**: Master counting formula.

    Under (PP-D) and (CFI), for any m ∈ M and k ≥ 1:
    F_k(m) = ∏_{p ∈ P} C(v_p(m) + k - 1, k - 1) -/
theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1)) := by
  sorry

/-- **Proposition 8.3**: Additivity of valuations.

    Under (PP-D) and (CFI), for every atom p and all x, y ∈ M:
    v_p(x · y) = v_p(x) + v_p(y) -/
theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y := by
  sorry

/-- **Corollary 8.4**: Factorial structure.

    Under (PP-D) and (CFI), the monoid M is isomorphic to ⊕_{p ∈ P} ℕ₀,
    and hence is factorial. -/
theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) :
    Factorial M := by
  sorry

end
