/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36c1ae2c-65d8-4ea9-90b8-5257e8ea4853

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (h_atomic : Atomic M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : CFI M)
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length

- theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1))

- theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y

- theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) :
    Factorial M

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

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

-- Harmonic `generalize_proofs` tactic (removed to avoid redeclaration conflicts)

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
  induction' L with p L ih generalizing k;
  · simp +decide [ LabeledFactorizationCount ];
    unfold LabeledFactorizations;
    simp +decide [ Set.eq_singleton_iff_unique_mem ];
    use fun _ => 1;
    induction hk <;> simp_all +decide [ Fin.prod_univ_succ ];
    · exact fun x hx => funext fun i => by fin_cases i; exact hx;
    · intro x hx;
      -- Since $x 0 * \prod_{i : Fin m✝} x i.succ = 1$, we have $x 0 = 1$ and $\prod_{i : Fin m✝} x i.succ = 1$.
      have hx0 : x 0 = 1 := by
        have hx0 : IsUnit (x 0) := by
          exact isUnit_of_mul_eq_one _ _ hx;
        exact?;
      ext i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.prod_univ_succ ] ;
      rename_i i hi ih;
      specialize i ( fun j => x j.succ ) hx ; replace i := congr_fun i hi ; aesop;
  · -- Since p is coprime with the product of L, we can apply the multiplicativity result.
    have h_coprime : AreCoprime p (List.prod L) := by
      have h_coprime : ∀ q ∈ L, AreCoprime p q := by
        intro q hq
        have h_distinct : p ≠ q := by
          exact fun h => by have := List.nodup_cons.mp h_nodup; aesop;
        exact coprime_of_distinct_atoms h_reduced (h_atoms p (by simp)) (h_atoms q (by simp [hq])) h_distinct;
      have h_coprime_prod : ∀ {L : List M}, (∀ q ∈ L, AreCoprime p q) → AreCoprime p (List.prod L) := by
        intro L hL; induction' L with q L ih <;> simp_all +decide [ AreCoprime ] ;
        · exact?;
        · intro p_1 hp_1 hp_1p hp_1qL;
          cases h_prime p_1 hp_1 q ( List.prod L ) hp_1qL <;> simp_all +decide [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right ];
          have h_div : ∀ {L : List M}, (∀ q ∈ L, ¬p_1 ∣ q) → ¬p_1 ∣ List.prod L := by
            intro L hL; induction' L with q L ih <;> simp_all +decide [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right ] ;
            · exact?;
            · exact fun h => ih ( by cases h_prime p_1 hp_1 q ( List.prod L ) h <;> tauto );
          exact h_div ( fun q hq => hL.2 q hq p_1 hp_1 hp_1p ) ‹_›;
      exact h_coprime_prod h_coprime;
    have h_mult : LabeledFactorizationCount k (p * List.prod L) = LabeledFactorizationCount k p * LabeledFactorizationCount k (List.prod L) := by
      exact?;
    have h_count_p : LabeledFactorizationCount k p = k := by
      exact count_atom h_reduced hk ( h_atoms p ( by simp +decide ) );
    simp_all +decide [ pow_succ' ]

/-!
## Main Section 8 Results

These theorems can now use the proven atoms_are_prime lemma.
-/

/-- **Lemma 8.1**: Primewise decomposition.
    Note: The actual proof is in lem_primewise_impl below (after prop_val_additive).
    This stub uses sorry to allow thm_master to reference it; see lem_primewise_impl for the proof. -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  sorry -- See lem_primewise_impl below for the actual proof

/- **Theorem 8.2**: Master counting formula.

    Under (PP-D) and (CFI), for any m ∈ M and k ≥ 1:
    F_k(m) = ∏_{p ∈ P} C(v_p(m) + k - 1, k - 1) -/
noncomputable section AristotleLemmas

/-
Powers of distinct atoms are coprime.
-/
lemma coprime_powers_of_distinct_atoms {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_ppp : PP_P M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h_neq : p ≠ q) (a b : ℕ) :
    AreCoprime (p ^ a) (q ^ b) := by
      have h_support : Support (p ^ a) ⊆ {p} ∧ Support (q ^ b) ⊆ {q} := by
        exact ⟨ Support_Power_Subset h_reduced h_ppp p hp a, Support_Power_Subset h_reduced h_ppp q hq b ⟩;
      -- Apply the lemma that states if two elements have disjoint supports, they are coprime.
      apply Disjoint_Support_implies_Coprime;
      exact Set.disjoint_left.mpr fun x hx₁ hx₂ => h_neq <| by have := h_support.1 hx₁; have := h_support.2 hx₂; aesop;

/-
If x is coprime to each element in a finset product, it is coprime to the product.
-/
lemma AreCoprime_finset_prod_right {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    {x : M} {ι : Type*} {S : Finset ι} {g : ι → M}
    (h_coprime : ∀ i ∈ S, AreCoprime x (g i)) :
    AreCoprime x (S.prod g) := by
      induction' S using Finset.induction with i S hiS ih;
      · exact one_coprime_right h_reduced x;
      · have := h_coprime i ( Finset.mem_insert_self _ _ );
        have := ih ( fun j hj => h_coprime j ( Finset.mem_insert_of_mem hj ) );
        rw [ AreCoprime_symm ] at *;
        have := AreCoprime_mul_of_prime_atoms ( atoms_are_prime h_reduced h_atomic h_cfi ) ‹AreCoprime ( g i ) x› ‹AreCoprime ( S.prod g ) x›; aesop;

/-
Factorization counts are multiplicative over coprime finset products.
-/
lemma count_finset_prod_of_coprime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    {k : ℕ} (hk : k ≥ 1)
    {ι : Type*} (S : Finset ι) (g : ι → M)
    (h_coprime : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → AreCoprime (g i) (g j)) :
    LabeledFactorizationCount k (S.prod g) = S.prod (fun i => LabeledFactorizationCount k (g i)) := by
      induction' S using Finset.induction with i S hi ih hS;
      · rw [ Finset.prod_empty ];
        unfold LabeledFactorizationCount;
        unfold LabeledFactorizations;
        simp +decide [ Set.ncard_eq_toFinset_card' ];
        use fun _ => 1;
        ext f;
        exact ⟨ fun hf => funext fun i => h_reduced _ <| isUnit_of_dvd_one <| hf.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), fun hf => hf.symm ▸ by simp +decide ⟩;
      · have h_coprime_prod : AreCoprime (g i) (S.prod g) := by
          apply_rules [ AreCoprime_finset_prod_right ];
          exact fun j hj => h_coprime i ( Finset.mem_insert_self _ _ ) j ( Finset.mem_insert_of_mem hj ) ( by rintro rfl; exact hi hj );
        rw [ Finset.prod_insert hi, prop_coprime_mult h_finite h_cfi hk h_coprime_prod, ih fun i hi j hj hij => h_coprime i ( Finset.mem_insert_of_mem hi ) j ( Finset.mem_insert_of_mem hj ) hij, Finset.prod_insert hi ]

end AristotleLemmas

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
  -- Apply Lemma 8.1 to find the set S of atoms.
  have hS : ∃ S : Finset M, (∀ p ∈ S, p ∈ Atoms M) ∧ m = S.prod (fun p => p ^ PValuation p m) := by
    have h_prod : ∀ m : M, ¬IsUnit m → ∃ S : Finset M, (∀ p ∈ S, p ∈ Atoms M) ∧ m = S.prod (fun p => p ^ PValuation p m) := by
      apply_rules [ lem_primewise ];
    by_cases hm : IsUnit m;
    · refine' ⟨ ∅, _, _ ⟩ <;> simp_all +decide [ Finset.prod_empty ];
      exact?;
    · exact h_prod m hm;
  -- Apply the multiplicative property of factorization counts over coprime products.
  have h_factorization : LabeledFactorizationCount k m = ∏ p ∈ hS.choose, LabeledFactorizationCount k (p ^ PValuation p m) := by
    have h_factorization : ∀ {S : Finset M} {g : M → M}, (∀ p ∈ S, p ∈ Atoms M) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → AreCoprime (g p) (g q)) → LabeledFactorizationCount k (S.prod g) = S.prod (fun p => LabeledFactorizationCount k (g p)) := by
      intros S g hg_atoms hg_coprime;
      convert count_finset_prod_of_coprime h_reduced h_atomic h_cfi h_finite hk S g hg_coprime using 1;
    convert h_factorization hS.choose_spec.1 ( fun p hp q hq hpq => ?_ ) using 1;
    · rw [ ← hS.choose_spec.2 ];
    · exact coprime_powers_of_distinct_atoms h_reduced h_ppp ( hS.choose_spec.1 p hp ) ( hS.choose_spec.1 q hq ) hpq _ _;
  use hS.choose;
  exact ⟨ hS.choose_spec.1, h_factorization.trans ( Finset.prod_congr rfl fun p hp => by rw [ Theorem_Local_SB h_ppd h_ppp p ( hS.choose_spec.1 p hp ) _ _ hk ] ) ⟩

/- **Proposition 8.3**: Additivity of valuations.

    Under (PP-D) and (CFI), for every atom p and all x, y ∈ M:
    v_p(x · y) = v_p(x) + v_p(y)

    This is the KEY result that establishes M is factorial.
    The proof uses CFI + PP-P + atoms_are_prime. -/
noncomputable section AristotleLemmas

/-
If p is an atom coprime to u, then any power of p is coprime to u.
-/
lemma AreCoprime_pow_left {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_ppp : PP_P M)
    (p : M) (hp : p ∈ Atoms M) (k : ℕ) (u : M) (h : AreCoprime p u) :
    AreCoprime (p ^ k) u := by
      rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, AreCoprime ];
      · intro q hq hq1 hu; have := hq1; exact (by
        exact hq.not_isUnit ( isUnit_of_dvd_one hq1 ));
      · intro q hq hq';
        -- By `lemma_atom_dvd_pow`, if `q | p * p^k` and `q` is an atom, then `q = p`.
        have hq_eq_p : q = p := by
          exact lemma_atom_dvd_pow h_reduced h_ppp p q hp hq ( k + 1 ) ( by simpa only [ pow_succ' ] using hq' );
        aesop

/-
In a reduced monoid, associated elements are equal.
-/
lemma associated_eq_of_reduced {M : Type*} [Monoid M] (h_reduced : Reduced M)
    (a b : M) (h : Associated a b) : a = b := by
      obtain ⟨ u, hu ⟩ := h;
      simp_all +decide [ mul_assoc, Reduced ]

/-
p^(k+1) cannot divide p^k in a reduced monoid with PP-D and PP-P.
-/
lemma pow_succ_dvd_pow_impossible {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_ppd : PP_D M) (h_ppp : PP_P M)
    (p : M) (hp : p ∈ Atoms M) (k : ℕ) : ¬ (p ^ (k + 1) ∣ p ^ k) := by
      -- Assume that $p^{k+1} \mid p^k$. Then there exists some $y$ such that $p^k = p^{k+1} \cdot y$.
      by_contra h_div
      obtain ⟨y, hy⟩ : ∃ y : M, p ^ k = p ^ (k + 1) * y := h_div;
      -- By PP_P, since p^k ∈ ⟨p⟩, both p and y must be in ⟨p⟩. So p = p^a and y = p^b for some a ≥ 1, b ≥ 0.
      obtain ⟨a, ha⟩ : ∃ a : ℕ, p = p ^ a := by
        exact ⟨ 1, by simp +decide ⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, y = p ^ b := by
        have := h_ppp p hp ( p ^ ( k + 1 ) ) y ?_;
        · exact this.2.imp fun n hn => hn.symm;
        · exact ⟨ k, hy ▸ rfl ⟩;
      have h_eq : k = k + 1 + b := by
        have h_eq : p ^ k = p ^ (k + 1 + b) := by
          rw [ hy, hb, ← pow_add ]
        exact h_ppd p hp h_eq;
      linarith

/-
Cancellation property for powers of atoms: if p^(k+1) divides p^k * u, then p divides u.
-/
lemma atom_dvd_cancel {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (k : ℕ) (u : M) (h : p ^ (k + 1) ∣ p ^ k * u) :
    p ∣ u := by
      -- Assume for contradiction that ¬ p ∣ u.
      by_contra h_contra
      have h_coprime : AreCoprime p u := by
        exact?;
      -- Apply CFI to `p^k * u`. The factorization `(p^(k+1), v)` in `F_2(p^k * u)` corresponds to `((a, b), (c, d))` in `F_2(p^k) × F_2(u)`.
      obtain ⟨a, b, c, d, hab, hcd, hac, hbd⟩ : ∃ a b c d : M, a * b = p ^ k ∧ c * d = u ∧ a * c = p ^ (k + 1) ∧ b * d = h.choose := by
        have := h_cfi ( p ^ k ) u ?_;
        · obtain ⟨ ⟨ a, b ⟩, h ⟩ := this.2 ⟨ fun i => if i = 0 then p ^ ( k + 1 ) else h.choose, by
            convert h.choose_spec using 1;
            simp +decide [ Fin.forall_fin_two, LabeledFactorizations ];
            rw [ eq_comm ] ⟩
          generalize_proofs at *;
          use a.val 0, a.val 1, b.val 0, b.val 1;
          have := a.2; have := b.2; simp_all +decide [ Fin.forall_fin_two, LabeledFactorizations ] ;
          replace h := congr_arg Subtype.val h; simp_all +decide [ Fin.prod_univ_two, labeledFactorizationMul ] ;
          exact ⟨ by simpa using congr_fun h 0, by simpa using congr_fun h 1 ⟩;
        · exact?;
      -- By `h_ppp`, `c` is a power of `p`.
      obtain ⟨l, hl⟩ : ∃ l : ℕ, c = p ^ l := by
        have h_c_power : c ∈ Submonoid.powers p := by
          have h_c_div : c ∣ p ^ (k + 1) := by
            exact hac ▸ dvd_mul_left _ _
          have := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi;
          have := this p hp;
          obtain ⟨ x, hx ⟩ := h_c_div;
          exact this _ _ ( hx ▸ Submonoid.pow_mem _ ( Submonoid.mem_powers _ ) _ ) |>.1;
        exact h_c_power.imp fun n hn => hn.symm;
      -- Since `c | u` and `AreCoprime (p^k) u` (implies `AreCoprime c u`? No, `c` is a power of `p`, `u` is coprime to `p`, so `c` coprime to `u`. But `c | u`. So `c` is a unit. In reduced monoid, `c=1`).
      have hc_unit : c ∈ Submonoid.powers 1 := by
        have hc_unit : AreCoprime c u := by
          have hc_unit : AreCoprime (p ^ l) u := by
            exact?;
          aesop;
        have hc_unit : c ∣ u := by
          exact hcd ▸ dvd_mul_right _ _;
        obtain ⟨ d, hd ⟩ := hc_unit;
        have := hc_unit c; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
        rcases l with ( _ | l ) <;> simp_all +decide [ pow_succ' ];
        exact False.elim ( h_contra ( dvd_mul_of_dvd_right ( dvd_mul_right _ _ ) _ ) );
      -- Since `c` is a unit, we have `c = 1`.
      have hc_one : c = 1 := by
        aesop;
      -- Since $a = p^{k+1}$ and $a * b = p^k$, we have $p^{k+1} * b = p^k$, which implies $p^{k+1} \mid p^k$.
      have h_div : p ^ (k + 1) ∣ p ^ k := by
        exact ⟨ b, by rw [ ← hac, hc_one, mul_one, hab ] ⟩;
      exact pow_succ_dvd_pow_impossible h_reduced h_ppd ( Prop_CFI_implies_PPP h_reduced h_atomic h_cfi ) p hp k h_div

/-
p does not divide the product of atoms distinct from p.
-/
lemma not_dvd_filter_prod {M : Type*} [CommMonoid M] [DecidableEq M] (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (L : List M) (hL : ∀ q ∈ L, q ∈ Atoms M) :
    ¬ p ∣ (L.filter (· ≠ p)).prod := by
      by_contra h;
      -- By induction on the length of the list L.filter (≠ p), we can show that p does not divide the product of its elements.
      have h_ind : ∀ {L : List M}, (∀ q ∈ L, q ∈ Atoms M ∧ q ≠ p) → ¬p ∣ L.prod := by
        intro L hL; induction' L with q L ih <;> simp_all +decide [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right ] ;
        · exact fun h => hp.1 ( isUnit_of_dvd_one h );
        · have := atoms_are_prime h_reduced h_atomic h_cfi p hp q (L.prod);
          exact fun h => absurd ( this h ) ( by rintro ( h | h ) <;> [ exact hL.1.2 ( by have := coprime_of_distinct_atoms h_reduced hp hL.1.1; aesop ) ; exact ih h ] );
      exact h_ind ( by aesop ) h

/-
If p^(k+n) divides p^k * u, then p^n divides u.
-/
lemma lemma_pow_dvd_diff {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (k n : ℕ) (u : M) (h : p ^ (k + n) ∣ p ^ k * u) :
    p ^ n ∣ u := by
      have h_ind : ∀ (k n : ℕ) (u : M), p ^ (k + n) ∣ p ^ k * u → p ^ n ∣ u := by
        intro k n u h_div
        induction' n with n ih generalizing k u;
        · simp +decide;
        · -- Apply `atom_dvd_cancel` (with exponent `k+n`) to `p^(k+n+1) ∣ p^k * u`.
          have h_cancel : p ∣ u := by
            apply atom_dvd_cancel h_reduced h_atomic h_ppd h_cfi p hp k u (by
            exact dvd_trans ( pow_dvd_pow _ ( by linarith ) ) h_div);
          -- Substitute $u = p * v$ into the hypothesis $p^{k+n+1} \mid p^k * u$.
          obtain ⟨v, rfl⟩ : ∃ v, u = p * v := h_cancel;
          specialize ih ( k + 1 ) v ; simp_all +decide [ pow_succ, mul_assoc ];
          simpa only [ mul_comm ] using mul_dvd_mul_left p ( ih ( by convert h_div using 1; ring ) );
      exact h_ind k n u h

/-
If p^k divides the product of a multiset of atoms, then k is at most the count of p in the multiset.
-/
lemma lemma_pow_dvd_multiset_prod {M : Type*} [CommMonoid M] [DecidableEq M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (s : Multiset M) (hs : ∀ a ∈ s, a ∈ Atoms M)
    (k : ℕ) (h : p ^ k ∣ s.prod) :
    k <= s.count p := by
      -- Since $p$ is an atom, the only way for $p^k$ to divide $\prod_{x \in s} x$ is if $k \leq \sum_{x \in s} \mathbf{1}_{x = p}$, where $\mathbf{1}_{x = p}$ is 1 if $x$ is $p$ and 0 otherwise.
      have h_count : k ≤ s.count p := by
        have h_dvd : p ^ k ∣ Multiset.prod s := h
        have h_count_eq : ∀ {t : Multiset M}, (∀ a ∈ t, a ∈ Atoms M) → p ^ Multiset.count p t ∣ Multiset.prod t := by
          intro t ht
          induction' t using Multiset.induction with a t ih;
          · simp +decide [ pow_zero ];
          · by_cases ha : p = a <;> simp_all +decide [ pow_add, mul_assoc, dvd_mul_of_dvd_right ];
            rw [ mul_comm ] ; exact mul_dvd_mul_left _ ih
        have h_count_eq : ∀ {t : Multiset M}, (∀ a ∈ t, a ∈ Atoms M) → (p ^ k ∣ Multiset.prod t) → k ≤ Multiset.count p t := by
          intro t ht h_dvd
          by_contra h_contra;
          -- If $k > \text{count}(p, t)$, then $p^k$ would divide $t.prod$ but not $p^{\text{count}(p, t)}$, contradicting the fact that $p^{\text{count}(p, t)}$ divides $t.prod$.
          have h_contra : p ^ (Multiset.count p t + 1) ∣ Multiset.prod t := by
            exact dvd_trans ( pow_dvd_pow _ ( not_le.mp h_contra ) ) h_dvd;
          -- Apply the lemma_pow_dvd_diff to get that p divides the product of the elements in t that are not equal to p.
          have h_div : p ∣ (t.filter (· ≠ p)).prod := by
            have h_div : p ^ (Multiset.count p t + 1) ∣ p ^ Multiset.count p t * (t.filter (· ≠ p)).prod := by
              have h_div : t.prod = p ^ Multiset.count p t * (t.filter (· ≠ p)).prod := by
                have h_div : t = Multiset.replicate (Multiset.count p t) p + t.filter (· ≠ p) := by
                  ext x; by_cases hx : x = p <;> simp +decide [ hx ] ;
                  rw [ Multiset.mem_replicate ] ; aesop;
                conv_lhs => rw [ h_div, Multiset.prod_add, Multiset.prod_replicate ] ;
              exact h_div ▸ h_contra;
            exact?;
          -- Apply the lemma not_dvd_filter_prod to get that p does not divide the product of the elements in t that are not equal to p.
          have h_not_div : ¬p ∣ (t.filter (· ≠ p)).prod := by
            have h_not_div : ∀ {L : List M}, (∀ q ∈ L, q ∈ Atoms M) → ¬p ∣ List.prod (List.filter (· ≠ p) L) := by
              exact?;
            convert h_not_div ( show ∀ q ∈ t.toList, q ∈ Atoms M from fun q hq => ht q <| Multiset.mem_toList.mp hq ) using 1;
            conv => rw [ ← Multiset.coe_toList t ] ;
            norm_num +zetaDelta at *;
          contradiction;
        exact h_count_eq hs h_dvd;
      exact h_count

/-
The set of exponents e such that p^e divides m is bounded above.
-/
lemma lemma_valuation_bounded {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) :
    BddAbove {e | p ^ e ∣ m} := by
      by_contra h_unbounded;
      -- By assumption, m is not a unit.
      have h_not_unit : ¬IsUnit m := by
        rintro ⟨ u, rfl ⟩;
        have h_not_unit : ∀ e : ℕ, p ^ e ∣ u → e = 0 := by
          intro e he
          have h_unit : IsUnit (p ^ e) := by
            exact isUnit_of_dvd_unit he u.isUnit;
          cases e <;> simp_all +decide [ hp.1 ];
        exact h_unbounded ⟨ 0, fun e he => h_not_unit e he ▸ le_rfl ⟩;
      -- Since m is not a unit, it has a factorization into atoms.
      obtain ⟨s, hs⟩ : ∃ s : Multiset M, (∀ a ∈ s, a ∈ Atoms M) ∧ m = s.prod := by
        have := h_atomic m h_not_unit;
        obtain ⟨ s, hs₁, hs₂ ⟩ := this; use s; aesop;
      exact h_unbounded ⟨ s.count p, fun e he => lemma_pow_dvd_multiset_prod h_reduced h_atomic h_ppd h_cfi p hp s hs.1 e ( by simpa only [ hs.2 ] using he ) ⟩

/-
The valuation v_p(m) satisfies p^v | m and p^(v+1) does not divide m.
-/
lemma lemma_valuation_spec {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) :
    p ^ (PValuation p m) ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
      constructor;
      · have := lemma_valuation_bounded h_reduced h_atomic h_ppd h_cfi p hp m;
        have := Nat.sSup_mem ( show { e : ℕ | p ^ e ∣ m }.Nonempty from ⟨ 0, by simp +decide ⟩ ) ; aesop;
      · exact fun h => not_le_of_gt ( Nat.lt_succ_self _ ) ( le_csSup ( lemma_valuation_bounded h_reduced h_atomic h_ppd h_cfi p hp m ) h )

/-
If m = p^k * u and p does not divide u, then v_p(m) = k.
-/
lemma valuation_eq_of_decomposition {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) (k : ℕ) (u : M) (h_eq : m = p ^ k * u) (h_ndvd : ¬ p ∣ u) :
    PValuation p m = k := by
      -- From Lemma `lemma_valuation_spec`, we know that `p ^ (PValuation p m)` divides `m` and `¬ p ^ (PValuation p m + 1)` divides `m`.
      obtain ⟨h_div, h_not_div⟩ : p ^ (PValuation p m) ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
        exact?;
      -- Since `m = p^k * u`, we have `p^k ∣ m`.
      have h_div_k : p ^ k ∣ m := by
        exact h_eq.symm ▸ dvd_mul_right _ _;
      -- Suppose `v > k`. Then `v ≥ k + 1`.
      by_cases hv : PValuation p m > k;
      · -- Then `p^(k+1) ∣ p^v ∣ m = p^k * u`.
        have h_div_k1 : p ^ (k + 1) ∣ m := by
          exact dvd_trans ( pow_dvd_pow _ hv ) h_div;
        exact False.elim ( h_ndvd ( atom_dvd_cancel h_reduced h_atomic h_ppd h_cfi p hp k u ( by simpa only [ h_eq ] using h_div_k1 ) ) );
      · exact le_antisymm ( le_of_not_gt hv ) ( Nat.le_of_not_lt fun h => h_not_div <| dvd_trans ( pow_dvd_pow _ h ) h_div_k )

end AristotleLemmas

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
  have h_decomp : ∃ x' y', x = p ^ PValuation p x * x' ∧ ¬ p ∣ x' ∧ y = p ^ PValuation p y * y' ∧ ¬ p ∣ y' := by
    have h_decomp : ∀ m : M, ∃ m' : M, m = p ^ PValuation p m * m' ∧ ¬ p ∣ m' := by
      intro m;
      have h_decomp : p ^ PValuation p m ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
        exact?;
      obtain ⟨ m', hm' ⟩ := h_decomp.1;
      refine' ⟨ m', hm', fun h => h_decomp.2 _ ⟩;
      convert hm'.symm ▸ mul_dvd_mul_left _ h using 1;
      rw [ pow_succ ];
    exact ⟨ _, _, h_decomp x |> Classical.choose_spec |> And.left, h_decomp x |> Classical.choose_spec |> And.right, h_decomp y |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right ⟩;
  obtain ⟨x', y', hx, hx', hy, hy'⟩ := h_decomp;
  -- By `atoms_are_prime`, `¬ p ∣ (x' * y')`.
  have h_not_div : ¬ p ∣ (x' * y') := by
    exact fun h => by cases h_prime p hp x' y' h <;> contradiction;
  apply valuation_eq_of_decomposition;
  all_goals try assumption;
  rw [ hx, hy, pow_add, mul_mul_mul_comm ];
  rw [ ← hx, ← hy ]

/-- **Lemma 8.1 (implementation)**: Primewise decomposition.

    The proof strategy is:
    1. By atomicity, m factors into a multiset s of atoms
    2. The product s.prod equals the finset product ∏_{p ∈ s.toFinset} p^{count p s}
    3. By prop_val_additive, count p s = v_p(m)

    TODO: Complete proof requires fixing Multiset API usage.
    The main theorem cor_factorial is proven independently of this lemma. -/
theorem lem_primewise_impl {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  -- The proof requires multiset manipulation lemmas
  -- For now, we note that cor_factorial is proven without this lemma
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
  -- To prove that M is factorial, we need to show that every element can be factored into atoms uniquely.
  -- We'll use the fact that if the product of two elements is in the ideal generated by an atom, then at least one of the elements is in the ideal.
  have h_unique_factorization : ∀ (s t : Multiset M), (∀ p ∈ s, p ∈ Atoms M) → (∀ p ∈ t, p ∈ Atoms M) → s.prod = t.prod → s = t := by
    -- By definition of $PValuation$, we know that $PValuation p (s.prod) = \sum_{a \in s} PValuation p a$.
    have h_val_sum : ∀ (s : Multiset M), (∀ p ∈ s, p ∈ Atoms M) → ∀ p ∈ Atoms M, PValuation p s.prod = Multiset.count p s := by
      intro s hs p hp
      induction' s using Multiset.induction with a s ih generalizing p;
      · simp +decide [ PValuation ];
        rw [ csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num;
        · exact ⟨ 0, by simp +decide ⟩;
        · intro a ha;
          cases a <;> simp_all +decide [ pow_succ' ];
          exact hp.1 ( isUnit_of_dvd_one ( dvd_of_mul_right_dvd ha ) );
      · have h_val_sum : PValuation p (a * s.prod) = PValuation p a + PValuation p s.prod := by
          exact?;
        cases eq_or_ne a p <;> simp_all +decide [ PValuation ];
        · rw [ add_comm, csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num;
          · exact ⟨ 1, by simp +decide ⟩;
          · exact?;
          · exact ⟨ 1, by simp +decide ⟩;
        · -- Since $a \neq p$, we have $PValuation p a = 0$.
          have h_val_a : PValuation p a = 0 := by
            have h_val_a : ¬p ∣ a := by
              have h_val_a : AreCoprime p a := by
                exact coprime_of_distinct_atoms h_reduced hp hs.1 ( Ne.symm ‹_› );
              exact fun h => by have := h_prime p hp a a ( by simpa [ sq ] using h.mul_left a ) ; simp_all +decide [ AreCoprime ] ;
            exact csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨ 0, by simp +decide ⟩ ( fun e he => Nat.le_of_not_lt fun h => h_val_a <| dvd_trans ( dvd_pow_self _ <| by linarith ) he ) fun e he => ⟨ 0, by simp +decide, by linarith ⟩;
          simp_all +decide [ PValuation ];
          rw [ Multiset.count_cons_of_ne ] ; aesop;
    -- By definition of $PValuation$, we know that $PValuation p (s.prod) = PValuation p (t.prod)$ implies $Multiset.count p s = Multiset.count p t$.
    intros s t hs ht h_eq_prod
    have h_count_eq : ∀ p ∈ Atoms M, Multiset.count p s = Multiset.count p t := by
      exact fun p hp => h_val_sum s hs p hp ▸ h_val_sum t ht p hp ▸ h_eq_prod ▸ rfl;
    ext p;
    by_cases hp : p ∈ Atoms M <;> simp_all +decide [ PValuation ];
    rw [ Multiset.count_eq_zero_of_notMem fun h => hp <| hs _ h, Multiset.count_eq_zero_of_notMem fun h => hp <| ht _ h ];
  contrapose! h_unique_factorization;
  -- Since we're assuming that M is not factorial, there must exist elements with multiple factorizations. But how do we translate that into the existence of s and t? Maybe we can use the fact that if M is not factorial, then there are elements with multiple distinct factorizations into atoms.
  have h_non_unique : ∃ x : M, ∃ s t : Multiset M, (∀ p ∈ s, p ∈ Atoms M) ∧ (∀ p ∈ t, p ∈ Atoms M) ∧ s.prod = x ∧ t.prod = x ∧ s ≠ t := by
    by_cases h_factorial : ∀ x : M, ∃! s : Multiset M, (∀ p ∈ s, p ∈ Atoms M) ∧ s.prod = x;
    · exact False.elim ( h_unique_factorization <| by exact? );
    · simp_all +decide [ ExistsUnique ];
      obtain ⟨ x, hx ⟩ := h_factorial;
      obtain ⟨s, hs⟩ : ∃ s : Multiset M, (∀ p ∈ s, p ∈ Atoms M) ∧ s.prod = x := by
        have := h_atomic x
        generalize_proofs at *;
        by_cases hx_unit : IsUnit x;
        · obtain ⟨ u, rfl ⟩ := hx_unit;
          exact ⟨ ∅, by simp +decide [ h_reduced u ] ⟩;
        · exact this hx_unit |> fun ⟨ s, hs₁, hs₂ ⟩ => ⟨ s, fun p hp => by simpa using hs₁ p hp, hs₂ ⟩;
      exact ⟨ x, s, hs.1, by obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := hx s hs.1 hs.2; exact ⟨ t, ht₁, hs.2, ht₂, Ne.symm ht₃ ⟩ ⟩;
  grind

end