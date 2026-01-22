/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a9417ddc-e500-4608-9c18-13792c0cf41f

The following was proved by Aristotle:

- lemma MulEquiv.irreducible_iff' {M N : Type*} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) (x : M) :
    Irreducible (e x) ↔ Irreducible x

- theorem Factorial.of_mulEquiv {M N : Type*} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) (h : Factorial N) : Factorial M
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Utility Lemmas

This file contains helper lemmas for:
- Transferring properties across monoid isomorphisms
- Relating disjoint supports to coprimality
- Blockwise disjointness properties
-/

import MultiplicationProject.Basic


noncomputable section

open scoped Classical

/-!
## Isomorphism Transfer Lemmas

These lemmas show how properties (being an atom, being factorial, being a unit)
transfer across multiplicative equivalences (isomorphisms).
-/

/-- Being a unit is preserved under multiplicative equivalence. -/
lemma MulEquiv.isUnit_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (x : M) :
    IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [this]
    exact h.map e.symm.toMonoidHom
  · intro h
    exact h.map e.toMonoidHom

/-- Irreducibility is preserved under multiplicative equivalence. -/
lemma MulEquiv.irreducible_iff' {M N : Type*} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) (x : M) :
    Irreducible (e x) ↔ Irreducible x := by
  constructor <;> intro h <;> rw [ irreducible_iff ] at * <;> aesop

/-- Atoms (irreducible elements) are preserved under multiplicative equivalence. -/
lemma Atoms_map {M N : Type*} [CommMonoid M] [CommMonoid N] (e : M ≃* N) (x : M) :
    e x ∈ Atoms N ↔ x ∈ Atoms M := by
  simp only [Atoms, Set.mem_setOf_eq]
  exact e.irreducible_iff' x

/-- Helper: product of mapped multiset equals map of product -/
lemma MulEquiv.multiset_prod_map {M N : Type*} [CommMonoid M] [CommMonoid N] 
    (e : M ≃* N) (s : Multiset M) :
    (s.map e).prod = e s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.map_cons, Multiset.prod_cons, ih]

/-- Helper: product of mapped multiset equals map of product (symm version) -/
lemma MulEquiv.multiset_prod_map_symm {M N : Type*} [CommMonoid M] [CommMonoid N] 
    (e : M ≃* N) (s : Multiset N) :
    (s.map e.symm).prod = e.symm s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.map_cons, Multiset.prod_cons, ih]

/-- The factorial property transfers across multiplicative equivalences.
    If N is factorial and M ≃* N, then M is also factorial. -/
theorem Factorial.of_mulEquiv {M N : Type*} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) (h : Factorial N) : Factorial M := by
  intro x hx
  have h_factorization : ∃! s : Multiset N, (∀ a ∈ s, Irreducible a) ∧ s.prod = e x := by
    aesop;
  obtain ⟨ s, hs₁, hs₂ ⟩ := h_factorization.exists;
  refine' ⟨ s.map e.symm, _, _ ⟩;
  · exact ⟨ fun a ha => by obtain ⟨ b, hb, rfl ⟩ := Multiset.mem_map.mp ha; exact MulEquiv.irreducible_iff' e.symm b |>.2 ( hs₁ _ hb ), by rw [ Multiset.prod_hom ] ; aesop ⟩;
  · intro y hy
    have hy_prod : (y.map e).prod = e x := by
      rw [ ← hy.2, Multiset.prod_hom ];
    have := h_factorization.unique ⟨ fun a ha => ?_, hy_prod ⟩ ⟨ hs₁, hs₂ ⟩;
    · aesop;
    · rw [ Multiset.mem_map ] at ha; obtain ⟨ b, hb, rfl ⟩ := ha; exact ( MulEquiv.irreducible_iff' e b ) |>.2 ( hy.1 b hb ) ;

/-- The reduced property transfers across multiplicative equivalences.
    If N is reduced and M ≃* N, then M is also reduced. -/
theorem Reduced.of_mulEquiv {M N : Type*} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) (h : Reduced N) : Reduced M := by
  intro x hx
  have : e x = 1 := h (e x) (e.isUnit_iff x |>.mpr hx)
  exact e.injective (this.trans (map_one e).symm)

/-!
## Support and Coprimality Lemmas
-/

/-- If the supports of x and y are disjoint, then x and y are coprime. -/
lemma Disjoint_Support_implies_Coprime {M : Type*} [Monoid M] (x y : M)
    (h : Disjoint (Support x) (Support y)) : AreCoprime x y := by
  intro p hp hpx
  have : p ∈ Support x := by simp [Support, hp, hpx]
  have : p ∉ Support y := by
    apply Set.disjoint_left.mp h this
  simp [Support, hp] at this
  exact this

/-- Restriction of a blockwise disjoint family preserves blockwise disjointness. -/
lemma Lemma_Blockwise_Restrict {M : Type*} [CommMonoid M] {m : ℕ}
    (x y : Fin (m + 1) → M)
    (h_disjoint : BlockwiseDisjoint x y) :
    BlockwiseDisjoint (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) := by
  intro i j hij
  specialize h_disjoint (Fin.castSucc i) (Fin.castSucc j)
  aesop

end