/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 8: Master Formula and Structural Consequences (v2)

This version imports the proven `atoms_are_prime` lemma from AtomsArePrime_v2_aristotle.lean
to avoid re-proving it.

Main results to prove:
- `cor_squarefree`: F_k(squarefree) = k^ω(m) (Corollary 7.3)
- `lem_primewise`: Primewise decomposition m = ∏ p^{v_p(m)} (Lemma 8.1)
- `thm_master`: Master formula F_k(m) = ∏ C(v_p(m)+k-1, k-1) (Theorem 8.2)
- `prop_val_additive`: v_p(x·y) = v_p(x) + v_p(y) (Proposition 8.3)
- `cor_factorial`: M ≅ ⊕ℕ₀ (Corollary 8.4)
-/

import MultiplicationProject.GlobalMultiplicativity
import MultiplicationProject.AtomsArePrime_v2_aristotle

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Helper Lemmas (already proven in original MasterFormula.lean)
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

/-- If an atom q divides a power of an atom p, then q = p. -/
lemma lemma_atom_dvd_pow {M : Type*} [CommMonoid M] (h_red : Reduced M) (h_ppp : PP_P M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : q ∣ p ^ k) :
    q = p := by
  obtain ⟨x, hx⟩ : ∃ x, p^k = q * x := h_dvd
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
## Corollary 7.3: Squarefree Diagnostic

Now using the PROVEN atoms_are_prime from AtomsArePrime_v2_aristotle.lean!
-/

/-- **Corollary 7.3**: Squarefree diagnostic.

    If m is a product of distinct atoms (squarefree), then F_k(m) = k^ω(m),
    where ω(m) is the number of distinct prime factors.

    Proof: F_k(p) = k for each atom, and coprime multiplicativity gives the product. -/
theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (h_atomic : Atomic M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : CFI M)
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length := by
  -- Now we can use the proven atoms_are_prime!
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  -- The rest of the proof uses coprime multiplicativity and induction on L
  sorry

/-!
## Main Section 8 Results

These theorems can now use the proven atoms_are_prime lemma.
-/

/-- **Lemma 8.1**: Primewise decomposition.

    Under (PP-D), (PP-P), and atomicity, every m ∈ M can be written as
    m = ∏_{p ∈ S} p^{v_p(m)} where S is the support of m. -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
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
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  sorry

/-- **Proposition 8.3**: Additivity of valuations.

    Under (PP-D) and (CFI), for every atom p and all x, y ∈ M:
    v_p(x · y) = v_p(x) + v_p(y)

    This is the KEY result that establishes M is factorial.
    The proof uses CFI + PP-P + atoms_are_prime. -/
theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  -- The proof follows the paper:
  -- 1. Write x = p^a * x' and y = p^b * y' where x', y' are p-free
  -- 2. Show v_p(x*y) = a + b using CFI and the fact that atoms are prime
  sorry

/-- **Corollary 8.4**: Factorial structure.

    Under (PP-D) and (CFI), the monoid M is isomorphic to ⊕_{p ∈ P} ℕ₀,
    and hence is factorial. -/
theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) :
    Factorial M := by
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime h_reduced h_atomic h_cfi
  -- The proof:
  -- 1. By prop_val_additive, each v_p is a monoid homomorphism
  -- 2. The map Φ: m ↦ (v_p(m))_p is a monoid homomorphism to ⊕ℕ₀
  -- 3. By lem_primewise, Φ is surjective
  -- 4. By PP-D, Φ is injective
  -- 5. Hence M ≅ ⊕ℕ₀, which is factorial
  sorry

end
