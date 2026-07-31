/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36c1ae2c-65d8-4ea9-90b8-5257e8ea4853

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following results originated in the Aristotle-assisted development
(updated for the System B / APD-based approach):

- theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : CFI M)
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length

- theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M)
    (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1))
  (finiteness of the factorization sets is derived via cor_factorial +
   finite_labeledFactorizations_of_factorial, not assumed; the auxiliary
   thm_master_of_finite carries the explicit h_finite hypothesis)

- theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M)
    (h_tf : TowerFaithful M) (h_cfi : CFI M) :
    Factorial M

- theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M)
    (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Multiplicity Rigidity, Factoriality, and Counting Consequences

This version imports the proven `atoms_are_prime` lemma from AtomsArePrime.lean
to avoid re-proving it.

The structural proof is deliberately ordered as follows:
- `multiplicity_rigidity`: the valuation of a product of atoms is
  its multiplicity in the multiset;
- `cor_factorial`: multiplicity rigidity gives unique factorization immediately;
- `prop_val_additive`: additivity is then a consequence of concatenating atomic
  factorizations;
- `lem_primewise_full`: primewise decomposition with its complete support clauses.

The file also retains the earlier counting consequences:
- `cor_squarefree`: F_k(squarefree) = k^ω(m) (Corollary 7.3)
- `lem_primewise`: Primewise decomposition m = ∏ p^{v_p(m)}
- `thm_master`: Master formula F_k(m) = ∏ C(v_p(m)+k-1, k-1) (Theorem 8.2)
-/

import MultiplicationProject.CoprimeAssembly

-- Harmonic `generalize_proofs` tactic (removed to avoid redeclaration conflicts)

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Helper Lemmas (proven earlier in this file's development)
-/

/-- If p and q are atoms, and p^k divides q, then k ≤ 1. -/
lemma lemma_pow_dvd_atom {M : Type*} [CommMonoid M] (_h_red : Reduced M)
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
lemma lemma_atom_dvd_pow {M : Type*} [CommMonoid M] (_h_red : Reduced M) (h_ppp : TowersFactoriallyClosed M)
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
    simp_all +decide [Function.Injective]
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
    (h_apd : APD M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : CFI M)
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length := by
  -- Now we can use the proven atoms_are_prime!
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime_APD h_reduced h_atomic h_apd h_cfi
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
      ext i; induction i using Fin.inductionOn <;> simp_all +decide;
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
          cases h_prime p_1 hp_1 q ( List.prod L ) hp_1qL <;> simp_all +decide [ dvd_mul_of_dvd_right ];
          have h_div : ∀ {L : List M}, (∀ q ∈ L, ¬p_1 ∣ q) → ¬p_1 ∣ List.prod L := by
            intro L hL; induction' L with q L ih <;> simp_all +decide;
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
## Structural Results and Counting Consequences

These theorems can now use the proven atoms_are_prime lemma.
-/

/- **Theorem 8.2**: Master counting formula.

    Under (tower faithfulness) and (CFI), for any m ∈ M and k ≥ 1:
    F_k(m) = ∏_{p ∈ P} C(v_p(m) + k - 1, k - 1) -/
noncomputable section AristotleLemmas

/-
Powers of distinct atoms are coprime.
-/
lemma coprime_powers_of_distinct_atoms {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_ppp : TowersFactoriallyClosed M)
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
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_cfi : CFI M)
    {x : M} {ι : Type*} {S : Finset ι} {g : ι → M}
    (h_coprime : ∀ i ∈ S, AreCoprime x (g i)) :
    AreCoprime x (S.prod g) := by
      induction' S using Finset.induction with i S hiS ih;
      · exact one_coprime_right h_reduced x;
      · have := h_coprime i ( Finset.mem_insert_self _ _ );
        have := ih ( fun j hj => h_coprime j ( Finset.mem_insert_of_mem hj ) );
        rw [ AreCoprime_symm ] at *;
        have := AreCoprime_mul_of_prime_atoms ( atoms_are_prime_APD h_reduced h_atomic h_apd h_cfi ) ‹AreCoprime ( g i ) x› ‹AreCoprime ( S.prod g ) x›; aesop;

/-
Factorization counts are multiplicative over coprime finset products.
-/
lemma count_finset_prod_of_coprime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    {k : ℕ} (hk : k ≥ 1)
    {ι : Type*} (S : Finset ι) (g : ι → M)
    (h_coprime : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → AreCoprime (g i) (g j)) :
    LabeledFactorizationCount k (S.prod g) = S.prod (fun i => LabeledFactorizationCount k (g i)) := by
      induction' S using Finset.induction with i S hi ih hS;
      · rw [ Finset.prod_empty ];
        unfold LabeledFactorizationCount;
        unfold LabeledFactorizations;
        simp +decide;
        use fun _ => 1;
        ext f;
        exact ⟨ fun hf => funext fun i => h_reduced _ <| isUnit_of_dvd_one <| hf.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ), fun hf => hf.symm ▸ by simp +decide ⟩;
      · have h_coprime_prod : AreCoprime (g i) (S.prod g) := by
          apply_rules [ AreCoprime_finset_prod_right ];
          exact fun j hj => h_coprime i ( Finset.mem_insert_self _ _ ) j ( Finset.mem_insert_of_mem hj ) ( by rintro rfl; exact hi hj );
        rw [ Finset.prod_insert hi, prop_coprime_mult h_finite h_cfi hk h_coprime_prod, ih fun i hi j hj hij => h_coprime i ( Finset.mem_insert_of_mem hi ) j ( Finset.mem_insert_of_mem hj ) hij, Finset.prod_insert hi ]

end AristotleLemmas

/- **Proposition 8.3**: Additivity of valuations.

    Under (tower faithfulness) and (CFI), for every atom p and all x, y ∈ M:
    v_p(x · y) = v_p(x) + v_p(y)

    This is the KEY result that establishes M is factorial.
    The proof uses CFI + PP-P + atoms_are_prime. -/
noncomputable section AristotleLemmas

/-
If p is an atom coprime to u, then any power of p is coprime to u.
-/
lemma AreCoprime_pow_left {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_ppp : TowersFactoriallyClosed M)
    (p : M) (hp : p ∈ Atoms M) (k : ℕ) (u : M) (h : AreCoprime p u) :
    AreCoprime (p ^ k) u := by
      rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ', AreCoprime ];
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
      simp_all +decide [ Reduced ]

/-
p^(k+1) cannot divide p^k in a reduced monoid with tower faithfulness and PP-P.
-/
lemma pow_succ_dvd_pow_impossible {M : Type*} [CommMonoid M] (_h_reduced : Reduced M) (h_tf : TowerFaithful M) (h_ppp : TowersFactoriallyClosed M)
    (p : M) (hp : p ∈ Atoms M) (k : ℕ) : ¬ (p ^ (k + 1) ∣ p ^ k) := by
      -- Assume that $p^{k+1} \mid p^k$. Then there exists some $y$ such that $p^k = p^{k+1} \cdot y$.
      by_contra h_div
      obtain ⟨y, hy⟩ : ∃ y : M, p ^ k = p ^ (k + 1) * y := h_div;
      -- By TowersFactoriallyClosed, since p^k ∈ ⟨p⟩, both p and y must be in ⟨p⟩. So p = p^a and y = p^b for some a ≥ 1, b ≥ 0.
      obtain ⟨a, ha⟩ : ∃ a : ℕ, p = p ^ a := by
        exact ⟨ 1, by simp +decide ⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, y = p ^ b := by
        have := h_ppp p hp ( p ^ ( k + 1 ) ) y ?_;
        · exact this.2.imp fun n hn => hn.symm;
        · exact ⟨ k, hy ▸ rfl ⟩;
      have h_eq : k = k + 1 + b := by
        have h_eq : p ^ k = p ^ (k + 1 + b) := by
          rw [ hy, hb, ← pow_add ]
        exact h_tf p hp h_eq;
      linarith

/-
Cancellation property for powers of atoms: if p^(k+1) divides p^k * u, then p divides u.
-/
lemma atom_dvd_cancel {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
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
            simp +decide [ LabeledFactorizations ];
            rw [ eq_comm ] ⟩
          generalize_proofs at *;
          use a.val 0, a.val 1, b.val 0, b.val 1;
          have := a.2; have := b.2; simp_all +decide [ LabeledFactorizations ] ;
          replace h := congr_arg Subtype.val h; simp_all +decide [ labeledFactorizationMul ] ;
          exact ⟨ by simpa using congr_fun h 0, by simpa using congr_fun h 1 ⟩;
        · -- Need: AreCoprime (p ^ k) u. Use power_coprime_of_not_in_support.
          have h_not_in_supp : p ∉ Support u := by
            simp only [Support, Set.mem_setOf_eq, not_and]
            intro _ h_dvd
            exact h_coprime p hp (dvd_refl p) h_dvd
          exact power_coprime_of_not_in_support_APD h_reduced h_apd hp h_not_in_supp k;
      -- By `h_ppp`, `c` is a power of `p`.
      obtain ⟨l, hl⟩ : ∃ l : ℕ, c = p ^ l := by
        have h_c_power : c ∈ Submonoid.powers p := by
          have h_c_div : c ∣ p ^ (k + 1) := by
            exact hac ▸ dvd_mul_left _ _
          have := APD_implies_towers_factorially_closed h_reduced h_atomic h_apd;
          have := this p hp;
          obtain ⟨ x, hx ⟩ := h_c_div;
          exact this _ _ ( hx ▸ Submonoid.pow_mem _ ( Submonoid.mem_powers _ ) _ ) |>.1;
        exact h_c_power.imp fun n hn => hn.symm;
      -- Since `c | u` and `AreCoprime (p^k) u` (implies `AreCoprime c u`? No, `c` is a power of `p`, `u` is coprime to `p`, so `c` coprime to `u`. But `c | u`. So `c` is a unit. In reduced monoid, `c=1`).
      have hc_unit : c ∈ Submonoid.powers 1 := by
        have hc_unit : AreCoprime c u := by
          have hc_unit : AreCoprime (p ^ l) u := by
            -- Use power_coprime_of_not_in_support with h_coprime : AreCoprime p u
            have h_not_in_supp : p ∉ Support u := by
              simp only [Support, Set.mem_setOf_eq, not_and]
              intro _ h_dvd
              exact h_coprime p hp (dvd_refl p) h_dvd
            exact power_coprime_of_not_in_support_APD h_reduced h_apd hp h_not_in_supp l;
          aesop;
        have hc_unit : c ∣ u := by
          exact hcd ▸ dvd_mul_right _ _;
        obtain ⟨ d, hd ⟩ := hc_unit;
        have := hc_unit c; simp_all +decide [ mul_comm, mul_left_comm ] ;
        rcases l with ( _ | l ) <;> simp_all +decide [ pow_succ' ];
        exact False.elim ( h_contra ( dvd_mul_of_dvd_right ( dvd_mul_right _ _ ) _ ) );
      -- Since `c` is a unit, we have `c = 1`.
      have hc_one : c = 1 := by
        aesop;
      -- Since $a = p^{k+1}$ and $a * b = p^k$, we have $p^{k+1} * b = p^k$, which implies $p^{k+1} \mid p^k$.
      have h_div : p ^ (k + 1) ∣ p ^ k := by
        exact ⟨ b, by rw [ ← hac, hc_one, mul_one, hab ] ⟩;
      exact pow_succ_dvd_pow_impossible h_reduced h_tf ( APD_implies_towers_factorially_closed h_reduced h_atomic h_apd ) p hp k h_div

/-
p does not divide the product of atoms distinct from p.
-/
lemma not_dvd_filter_prod {M : Type*} [CommMonoid M] [DecidableEq M] (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (L : List M) (hL : ∀ q ∈ L, q ∈ Atoms M) :
    ¬ p ∣ (L.filter (· ≠ p)).prod := by
      by_contra h;
      -- By induction on the length of the list L.filter (≠ p), we can show that p does not divide the product of its elements.
      have h_ind : ∀ {L : List M}, (∀ q ∈ L, q ∈ Atoms M ∧ q ≠ p) → ¬p ∣ L.prod := by
        intro L hL; induction' L with q L ih <;> simp_all +decide;
        · exact fun h => hp.1 ( isUnit_of_dvd_one h );
        · have := atoms_are_prime_APD h_reduced h_atomic h_apd h_cfi p hp q (L.prod);
          exact fun h => absurd ( this h ) ( by rintro ( h | h ) <;> [ exact hL.1.2 ( by have := coprime_of_distinct_atoms h_reduced hp hL.1.1; aesop ) ; exact ih h ] );
      exact h_ind ( by aesop ) h

/-
If p^(k+n) divides p^k * u, then p^n divides u.
-/
lemma lemma_pow_dvd_diff {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (k n : ℕ) (u : M) (h : p ^ (k + n) ∣ p ^ k * u) :
    p ^ n ∣ u := by
      have h_ind : ∀ (k n : ℕ) (u : M), p ^ (k + n) ∣ p ^ k * u → p ^ n ∣ u := by
        intro k n u h_div
        induction' n with n ih generalizing k u;
        · simp +decide;
        · -- Apply `atom_dvd_cancel` (with exponent `k+n`) to `p^(k+n+1) ∣ p^k * u`.
          have h_cancel : p ∣ u := by
            apply atom_dvd_cancel h_reduced h_atomic h_apd h_tf h_cfi p hp k u (by
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
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
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
          · by_cases ha : p = a <;> simp_all +decide [ pow_add, dvd_mul_of_dvd_right ];
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
            exact atom_dvd_cancel h_reduced h_atomic h_apd h_tf h_cfi p hp (Multiset.count p t)
                  (Multiset.filter (fun x => x ≠ p) t).prod h_div
          -- Apply the lemma not_dvd_filter_prod to get that p does not divide the product of the elements in t that are not equal to p.
          have h_not_div : ¬p ∣ (t.filter (· ≠ p)).prod := by
            have h_not_div : ∀ {L : List M}, (∀ q ∈ L, q ∈ Atoms M) → ¬p ∣ List.prod (List.filter (· ≠ p) L) := by
              exact fun {L} a => not_dvd_filter_prod h_reduced h_atomic h_apd h_cfi p hp L a
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
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
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
      exact h_unbounded ⟨ s.count p, fun e he => lemma_pow_dvd_multiset_prod h_reduced h_atomic h_apd h_tf h_cfi p hp s hs.1 e ( by simpa only [ hs.2 ] using he ) ⟩

/-
The valuation v_p(m) satisfies p^v | m and p^(v+1) does not divide m.
-/
lemma lemma_valuation_spec {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) :
    p ^ (PValuation p m) ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
      constructor;
      · have := lemma_valuation_bounded h_reduced h_atomic h_apd h_tf h_cfi p hp m;
        have := Nat.sSup_mem ( show { e : ℕ | p ^ e ∣ m }.Nonempty from ⟨ 0, by simp +decide ⟩ ) ; aesop;
      · exact fun h => not_le_of_gt ( Nat.lt_succ_self _ ) ( le_csSup ( lemma_valuation_bounded h_reduced h_atomic h_apd h_tf h_cfi p hp m ) h )

/-
If m = p^k * u and p does not divide u, then v_p(m) = k.
-/
lemma valuation_eq_of_decomposition {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (m : M) (k : ℕ) (u : M) (h_eq : m = p ^ k * u) (h_ndvd : ¬ p ∣ u) :
    PValuation p m = k := by
      -- From Lemma `lemma_valuation_spec`, we know that `p ^ (PValuation p m)` divides `m` and `¬ p ^ (PValuation p m + 1)` divides `m`.
      obtain ⟨h_div, h_not_div⟩ : p ^ (PValuation p m) ∣ m ∧ ¬ p ^ (PValuation p m + 1) ∣ m := by
        exact lemma_valuation_spec h_reduced h_atomic h_apd h_tf h_cfi p hp m
      -- Since `m = p^k * u`, we have `p^k ∣ m`.
      have h_div_k : p ^ k ∣ m := by
        exact h_eq.symm ▸ dvd_mul_right _ _;
      -- Suppose `v > k`. Then `v ≥ k + 1`.
      by_cases hv : PValuation p m > k;
      · -- Then `p^(k+1) ∣ p^v ∣ m = p^k * u`.
        have h_div_k1 : p ^ (k + 1) ∣ m := by
          exact dvd_trans ( pow_dvd_pow _ hv ) h_div;
        exact False.elim ( h_ndvd ( atom_dvd_cancel h_reduced h_atomic h_apd h_tf h_cfi p hp k u ( by simpa only [ h_eq ] using h_div_k1 ) ) );
      · exact le_antisymm ( le_of_not_gt hv ) ( Nat.le_of_not_lt fun h => h_not_div <| dvd_trans ( pow_dvd_pow _ h ) h_div_k )

end AristotleLemmas

/-- For a multiset of atoms, the p-valuation of the product equals the count of p.
    This is the multiplicity-rigidity statement: the valuation is intrinsic
    to the element and therefore independent of the chosen atomic factorization. -/
lemma multiplicity_rigidity {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (s : Multiset M) (hs : ∀ a ∈ s, a ∈ Atoms M) (p : M) (hp : p ∈ Atoms M) :
    PValuation p s.prod = Multiset.count p s := by
  classical
  obtain ⟨h_val_dvd, _⟩ :=
    lemma_valuation_spec h_reduced h_atomic h_apd h_tf h_cfi p hp s.prod
  have h_upper : PValuation p s.prod ≤ Multiset.count p s :=
    lemma_pow_dvd_multiset_prod h_reduced h_atomic h_apd h_tf h_cfi
      p hp s hs (PValuation p s.prod) h_val_dvd
  have h_count_dvd : ∀ t : Multiset M, p ^ Multiset.count p t ∣ t.prod := by
    intro t
    induction' t using Multiset.induction with a t ih
    · simp
    · by_cases ha : p = a
      · subst a
        simpa [pow_succ, mul_comm] using mul_dvd_mul_left p ih
      · rw [Multiset.count_cons_of_ne ha, Multiset.prod_cons]
        exact dvd_mul_of_dvd_right ih a
  have h_lower : Multiset.count p s ≤ PValuation p s.prod :=
    le_csSup
      (lemma_valuation_bounded h_reduced h_atomic h_apd h_tf h_cfi p hp s.prod)
      (h_count_dvd s)
  exact le_antisymm h_upper h_lower

/-- Factoriality follows immediately from multiplicity rigidity:
    atomicity gives existence, and the intrinsic p-multiplicities give uniqueness. -/
theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M) :
    Factorial M := by
  classical
  intro x hx
  obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic x hx
  refine ⟨s, ⟨hs_atoms, hs_prod⟩, ?_⟩
  intro t ht
  rcases ht with ⟨ht_atoms, ht_prod⟩
  apply Multiset.ext.mpr
  intro p
  by_cases hp : p ∈ Atoms M
  · calc
      Multiset.count p t = PValuation p t.prod :=
        (multiplicity_rigidity
          h_reduced h_atomic h_apd h_tf h_cfi t ht_atoms p hp).symm
      _ = PValuation p s.prod := by rw [ht_prod, hs_prod]
      _ = Multiset.count p s :=
        multiplicity_rigidity
          h_reduced h_atomic h_apd h_tf h_cfi s hs_atoms p hp
  · rw [
      Multiset.count_eq_zero_of_notMem (fun hpt => hp (ht_atoms p hpt)),
      Multiset.count_eq_zero_of_notMem (fun hps => hp (hs_atoms p hps))
    ]

/-- Once multiplicities are intrinsic, valuations add under multiplication
    because atomic factorizations concatenate. -/
theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y := by
  classical
  have h_factorization :
      ∀ m : M, ∃ s : Multiset M, (∀ a ∈ s, a ∈ Atoms M) ∧ s.prod = m := by
    intro m
    by_cases hm : IsUnit m
    · exact ⟨0, by simp [h_reduced m hm]⟩
    · exact h_atomic m hm
  obtain ⟨sx, hsx_atoms, hsx_prod⟩ := h_factorization x
  obtain ⟨sy, hsy_atoms, hsy_prod⟩ := h_factorization y
  have hxy_atoms : ∀ a ∈ sx + sy, a ∈ Atoms M := by
    intro a ha
    rcases Multiset.mem_add.mp ha with ha | ha
    · exact hsx_atoms a ha
    · exact hsy_atoms a ha
  calc
    PValuation p (x * y) = PValuation p (sx + sy).prod := by
      rw [Multiset.prod_add, hsx_prod, hsy_prod]
    _ = Multiset.count p (sx + sy) :=
      multiplicity_rigidity
        h_reduced h_atomic h_apd h_tf h_cfi (sx + sy) hxy_atoms p hp
    _ = Multiset.count p sx + Multiset.count p sy := Multiset.count_add p sx sy
    _ = PValuation p sx.prod + PValuation p sy.prod := by
      rw [
        multiplicity_rigidity
          h_reduced h_atomic h_apd h_tf h_cfi sx hsx_atoms p hp,
        multiplicity_rigidity
          h_reduced h_atomic h_apd h_tf h_cfi sy hsy_atoms p hp
      ]
    _ = PValuation p x + PValuation p y := by rw [hsx_prod, hsy_prod]

/-- Primewise decomposition.

    The proof strategy is:
    1. By atomicity, m factors into a multiset s of atoms
    2. The product s.prod equals the finset product ∏_{p ∈ s.toFinset} p^{count p s}
    3. By multiplicity_rigidity, count p s = v_p(m) -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  -- Step 1: By atomicity, get multiset s of atoms with m = s.prod
  obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
  -- Step 2: Take S = s.toFinset
  use s.toFinset
  constructor
  · -- All elements of s.toFinset are atoms
    intro p hp
    exact hs_atoms p (Multiset.mem_toFinset.mp hp)
  · -- m = S.prod (fun p => p ^ PValuation p m)
    -- First show that s.count p = PValuation p m for each atom p
    have h_count_eq : ∀ p ∈ s.toFinset, Multiset.count p s = PValuation p m := by
      intro p hp
      have hp_atom : p ∈ Atoms M := hs_atoms p (Multiset.mem_toFinset.mp hp)
      rw [← hs_prod]
      exact (multiplicity_rigidity h_reduced h_atomic h_apd h_tf h_cfi s hs_atoms p hp_atom).symm
    -- Use Finset.prod_multiset_count and substitute
    calc m = s.prod := hs_prod.symm
      _ = ∏ p ∈ s.toFinset, p ^ Multiset.count p s := Finset.prod_multiset_count s
      _ = ∏ p ∈ s.toFinset, p ^ PValuation p m := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [h_count_eq p hp]

/-- The atom-divisor support of an element is exactly the finite set of atoms
    occurring in any atomic factorization. -/
theorem support_eq_atomic_factorization {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_apd : APD M) (h_cfi : CFI M)
    (m : M) (s : Multiset M) (hs_atoms : ∀ p ∈ s, p ∈ Atoms M)
    (hs_prod : s.prod = m) :
    (↑s.toFinset : Set M) = Support m := by
  classical
  ext p
  simp only [Support, Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · intro hp
    have hp_mem : p ∈ s := Multiset.mem_toFinset.mp hp
    exact ⟨hs_atoms p hp_mem, by
      rw [← hs_prod]
      exact Multiset.dvd_prod hp_mem⟩
  · rintro ⟨hp_atom, hp_dvd⟩
    apply Multiset.mem_toFinset.mpr
    apply atom_dvd_multiset_prod_APD h_reduced h_apd h_cfi s hs_atoms p hp_atom
    simpa only [hs_prod] using hp_dvd

/-- Full primewise decomposition, including the support clauses printed in the paper.
    The finite indexing set is the atom-divisor support, and valuations vanish
    on atoms outside it. -/
theorem lem_primewise_full {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (m : M) (hm : ¬ IsUnit m) :
    ∃ S : Finset M,
      (∀ p ∈ S, p ∈ Atoms M) ∧
      (↑S : Set M) = Support m ∧
      m = S.prod (fun p => p ^ PValuation p m) ∧
      ∀ p, p ∈ Atoms M → p ∉ S → PValuation p m = 0 := by
  classical
  obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic m hm
  refine ⟨s.toFinset, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hs_atoms p (Multiset.mem_toFinset.mp hp)
  · exact support_eq_atomic_factorization
      h_reduced h_apd h_cfi m s hs_atoms hs_prod
  · have h_count_eq :
        ∀ p ∈ s.toFinset, Multiset.count p s = PValuation p m := by
      intro p hp
      have hp_atom : p ∈ Atoms M := hs_atoms p (Multiset.mem_toFinset.mp hp)
      rw [← hs_prod]
      exact (multiplicity_rigidity
        h_reduced h_atomic h_apd h_tf h_cfi s hs_atoms p hp_atom).symm
    calc
      m = s.prod := hs_prod.symm
      _ = ∏ p ∈ s.toFinset, p ^ Multiset.count p s := Finset.prod_multiset_count s
      _ = ∏ p ∈ s.toFinset, p ^ PValuation p m := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [h_count_eq p hp]
  · intro p hp_atom hp_not_mem
    rw [← hs_prod]
    rw [multiplicity_rigidity
      h_reduced h_atomic h_apd h_tf h_cfi s hs_atoms p hp_atom]
    exact Multiset.count_eq_zero_of_notMem fun hp_mem =>
      hp_not_mem (Multiset.mem_toFinset.mpr hp_mem)

/-- Under the structural hypotheses, every element has finite atom-divisor support. -/
theorem support_finite {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (m : M) (hm : ¬ IsUnit m) :
    (Support m).Finite := by
  obtain ⟨S, _, hS_support, _, _⟩ :=
    lem_primewise_full h_reduced h_atomic h_apd h_tf h_cfi m hm
  rw [← hS_support]
  exact S.finite_toSet

/-- Master counting formula, auxiliary version carrying an explicit
    finiteness hypothesis on the factorization sets. The public `thm_master`
    (below, after `cor_factorial`) discharges `h_finite` via
    `finite_labeledFactorizations_of_factorial`. -/
theorem thm_master_of_finite {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1)) := by
  have h_ppp : TowersFactoriallyClosed M := APD_implies_towers_factorially_closed h_reduced h_atomic h_apd
  have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b :=
    atoms_are_prime_APD h_reduced h_atomic h_apd h_cfi
  -- Apply Lemma 8.1 to find the set S of atoms.
  have hS : ∃ S : Finset M, (∀ p ∈ S, p ∈ Atoms M) ∧ m = S.prod (fun p => p ^ PValuation p m) := by
    by_cases hm : IsUnit m
    · refine' ⟨ ∅, _, _ ⟩ <;> simp_all +decide [ Finset.prod_empty ]
      exact?
    · exact lem_primewise h_reduced h_atomic h_apd h_tf h_cfi m hm
  -- Apply the multiplicative property of factorization counts over coprime products.
  have h_factorization : LabeledFactorizationCount k m = ∏ p ∈ hS.choose, LabeledFactorizationCount k (p ^ PValuation p m) := by
    have h_factorization : ∀ {S : Finset M} {g : M → M}, (∀ p ∈ S, p ∈ Atoms M) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → AreCoprime (g p) (g q)) → LabeledFactorizationCount k (S.prod g) = S.prod (fun p => LabeledFactorizationCount k (g p)) := by
      intros S g hg_atoms hg_coprime
      convert count_finset_prod_of_coprime h_reduced h_atomic h_apd h_cfi h_finite hk S g hg_coprime using 1
    convert h_factorization hS.choose_spec.1 ( fun p hp q hq hpq => ?_ ) using 1
    · rw [ ← hS.choose_spec.2 ]
    · exact coprime_powers_of_distinct_atoms h_reduced h_ppp ( hS.choose_spec.1 p hp ) ( hS.choose_spec.1 q hq ) hpq _ _
  use hS.choose
  exact ⟨ hS.choose_spec.1, h_factorization.trans ( Finset.prod_congr rfl fun p hp => by rw [ Theorem_Local_SB h_tf h_ppp p ( hS.choose_spec.1 p hp ) _ _ hk ] ) ⟩

/-!
## Finiteness of factorization sets, and the master formula proper

`cor_factorial` needs no finiteness hypothesis; from factoriality we now
DERIVE that all labeled factorization sets are finite, and use that to
discharge the `h_finite` hypothesis of `thm_master_of_finite`. This makes
the formal statement of the master formula match the paper's Theorem 8.2.
-/

/-- In a reduced factorial monoid, every element has finitely many divisors:
    each divisor is the product of a sub-multiset of the (unique) atomic
    factorization. -/
lemma divisors_finite_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    {d : M | d ∣ m}.Finite := by
  by_cases hm : IsUnit m
  · -- m = 1, and the only divisor of 1 in a reduced monoid is 1
    have hm1 : m = 1 := h_reduced m hm
    subst hm1
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    simp [h_reduced d (isUnit_of_dvd_one hd)]
  · obtain ⟨s, hs, hs_uniq⟩ := h_fact m hm
    obtain ⟨hs_atoms, hs_prod⟩ := hs
    -- every divisor is the product of some sub-multiset of s
    refine Set.Finite.subset ((s.powerset.finite_toSet).image Multiset.prod) ?_
    intro d hd
    obtain ⟨c, hc⟩ := hd
    by_cases hd_unit : IsUnit d
    · exact ⟨0, by simp, by simp [h_reduced d hd_unit]⟩
    · by_cases hc_unit : IsUnit c
      · -- c = 1, so d = m: witness is s itself
        have hc1 : c = 1 := h_reduced c hc_unit
        exact ⟨s, by simp, by rw [hs_prod, hc, hc1, mul_one]⟩
      · -- factor d and c into atoms; uniqueness at m forces t_d + t_c = s
        obtain ⟨td, htd_atoms, htd_prod⟩ := (h_fact d hd_unit).exists
        obtain ⟨tc, htc_atoms, htc_prod⟩ := (h_fact c hc_unit).exists
        have hsum : td + tc = s := by
          apply hs_uniq
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases Multiset.mem_add.mp ha with h | h
            exacts [htd_atoms a h, htc_atoms a h]
          · rw [Multiset.prod_add, htd_prod, htc_prod]
            exact hc.symm
        refine ⟨td, ?_, htd_prod⟩
        have h_le : td ≤ s := hsum ▸ Multiset.le_add_right td tc
        simpa [Multiset.mem_powerset] using h_le

/-- In a reduced factorial monoid, all labeled factorization sets are finite:
    each slot of a factorization of m divides m, and m has finitely many
    divisors. This discharges the finiteness hypothesis of
    `thm_master_of_finite`. -/
lemma finite_labeledFactorizations_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M) (k : ℕ) (m : M) :
    (LabeledFactorizations k m).Finite := by
  have hdiv := divisors_finite_of_factorial h_reduced h_fact m
  have hsub : LabeledFactorizations k m ⊆
      Set.univ.pi (fun _ : Fin k => {d : M | d ∣ m}) := by
    intro f hf i _
    simp only [LabeledFactorizations, Set.mem_setOf_eq] at hf
    exact hf ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  exact (Set.Finite.pi fun _ => hdiv).subset hsub

/-- **Theorem 8.2**: Master counting formula.

    Under (APD), (tower faithfulness), and (CFI), for any m ∈ M and k ≥ 1:
    F_k(m) = ∏_{p ∈ S} C(v_p(m) + k - 1, k - 1) for a finite set S of atoms.
    Finiteness of the factorization sets is DERIVED (via `cor_factorial` and
    `finite_labeledFactorizations_of_factorial`), not assumed — matching the
    paper's statement. -/
theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m =
        S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1)) :=
  thm_master_of_finite h_reduced h_atomic h_apd h_tf h_cfi
    (fun k' m' => finite_labeledFactorizations_of_factorial h_reduced
      (cor_factorial h_reduced h_atomic h_apd h_tf h_cfi) k' m')
    m k hk

/-!
## Equivalence of Cancellativity and tower faithfulness under CFI

Under the CFI axiom, cancellativity and tower faithfulness are equivalent properties
in a reduced atomic commutative monoid.
-/

/-- Under APD + tower faithfulness + CFI, the monoid is cancellative (via Factorial).

    The proof chain is: APD + tower faithfulness + CFI → Factorial → Cancellative.
    This is the System B version. -/
theorem cancellative_of_structural {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    {a b c : M} (h : a * b = a * c) : b = c :=
  Factorial_implies_mul_left_cancel h_reduced h_atomic
    (cor_factorial h_reduced h_atomic h_apd h_tf h_cfi) h

/- Note: The following theorems from System A (cancellativity ↔ tower faithfulness under CFI)
   are not directly applicable in System B, where we assume APD as an independent
   axiom rather than deriving it from cancellativity.

   In System B:
   - We assume APD, tower faithfulness, CFI, CPL as four independent axioms
   - Cancellativity is derived from Factorial (which follows from the axioms)
   - The relationship to System A is: CancelCommMonoid implies APD (but has sorries) -/

end
