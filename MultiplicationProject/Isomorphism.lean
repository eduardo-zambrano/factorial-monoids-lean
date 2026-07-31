/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# The isomorphism with (ℕ, ×): part (C) of the main theorem

This file formalizes the equivalence (B) ⟺ (C) of the paper's Theorem 4.1:
a reduced commutative monoid is factorial with countably infinite atom set
IF AND ONLY IF it is isomorphic (as a monoid) to ℕ+, the multiplicative
monoid of positive integers.

- Forward: `factorialMulEquiv` builds M ≃* N for any two reduced factorial
  monoids with equivalent atom sets, by transporting canonical atomic
  multisets (the classification of free commutative monoids by rank, in the
  special case needed); `mulEquiv_pnat_of_factorial` specializes N := ℕ+.
- `factorialCoordinateEquiv` gives the explicit free-coordinate isomorphism
  Multiplicative ((Atoms M) →₀ ℕ) ≃* M, whose forward map is
  e ↦ ∏ p, p ^ e(p).
- Backward: `factorial_countable_atoms_of_mulEquiv` transports factoriality
  and the atom-set cardinality along a monoid isomorphism.
- `thm_B_iff_C` is the equivalence, and `thm_A_iff_C` chains it with
  `thm_A_iff_B` to give (A) ⟺ (C):
  {WFD, TD, CFI, CPL⁺} ⟺ M ≃* ℕ+, over reducedness alone.
-/
import MultiplicationProject.Examples.NatMonoid

set_option maxHeartbeats 800000

noncomputable section

/-! ## Transport along a monoid isomorphism -/

section Transport

variable {M N : Type*} [CommMonoid M] [CommMonoid N]

lemma isUnit_map_equiv (e : M ≃* N) {a : M} : IsUnit (e a) ↔ IsUnit a := by
  constructor
  · intro h
    have h2 := h.map e.symm.toMonoidHom
    simpa using h2
  · intro h
    exact h.map e.toMonoidHom

lemma irreducible_map_equiv (e : M ≃* N) {a : M} :
    Irreducible (e a) ↔ Irreducible a := by
  constructor
  · intro h
    constructor
    · intro hu
      exact h.not_isUnit ((isUnit_map_equiv e).mpr hu)
    · intro b c hbc
      have h2 : e a = e b * e c := by rw [hbc, map_mul]
      rcases h.isUnit_or_isUnit h2 with h3 | h3
      · exact Or.inl ((isUnit_map_equiv e).mp h3)
      · exact Or.inr ((isUnit_map_equiv e).mp h3)
  · intro h
    constructor
    · intro hu
      exact h.not_isUnit ((isUnit_map_equiv e).mp (by simpa using hu))
    · intro b c hbc
      have h2 : a = e.symm b * e.symm c := by
        have h3 := congrArg e.symm hbc
        simpa [map_mul] using h3
      rcases h.isUnit_or_isUnit h2 with h3 | h3
      · exact Or.inl ((isUnit_map_equiv e.symm).mp h3)
      · exact Or.inr ((isUnit_map_equiv e.symm).mp h3)

/-- The atom sets of isomorphic monoids are equivalent. -/
def atomsEquiv (e : M ≃* N) : ↥(Atoms M) ≃ ↥(Atoms N) where
  toFun a := ⟨e a.1, (irreducible_map_equiv e).mpr a.2⟩
  invFun b := ⟨e.symm b.1, (irreducible_map_equiv e.symm).mpr b.2⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv b := by
    apply Subtype.ext
    simp

/-- Factoriality transports along a monoid isomorphism. -/
lemma factorial_of_mulEquiv (e : M ≃* N) (hN : Factorial N) : Factorial M := by
  intro x hx
  have hex : ¬IsUnit (e x) := fun h => hx ((isUnit_map_equiv e).mp h)
  obtain ⟨t, ⟨ht_atoms, ht_prod⟩, ht_uniq⟩ := hN (e x) hex
  refine ⟨t.map e.symm, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨b, hb_mem, rfl⟩ := Multiset.mem_map.mp ha
    exact (irreducible_map_equiv e.symm).mpr (ht_atoms b hb_mem)
  · apply e.injective
    rw [map_multiset_prod]
    simp only [Multiset.map_map]
    rw [show Multiset.map (⇑e ∘ ⇑e.symm) t = Multiset.map id t from
      Multiset.map_congr rfl (fun b _ => by simp), Multiset.map_id]
    exact ht_prod
  · rintro s ⟨hs_atoms, hs_prod⟩
    have h1 : ∀ b ∈ s.map e, Irreducible b := by
      intro b hb
      obtain ⟨a, ha_mem, rfl⟩ := Multiset.mem_map.mp hb
      exact (irreducible_map_equiv e).mpr (hs_atoms a ha_mem)
    have h2 : (s.map e).prod = e x := by
      rw [← map_multiset_prod, hs_prod]
    have h3 := ht_uniq (s.map e) ⟨h1, h2⟩
    rw [← h3]
    simp only [Multiset.map_map]
    rw [show Multiset.map (⇑e.symm ∘ ⇑e) s = Multiset.map id s from
      Multiset.map_congr rfl (fun a _ => by simp), Multiset.map_id]

end Transport

/-! ## The isomorphism between reduced factorial monoids with equivalent atoms -/

section Construction

variable {M N : Type*} [CommMonoid M] [CommMonoid N]

open Classical in
/-- Transport of a single element along an atom correspondence, extended by 1
    on non-atoms. -/
def atomMap (eA : ↥(Atoms M) ≃ ↥(Atoms N)) : M → N :=
  fun a => if h : Irreducible a then (eA ⟨a, h⟩ : N) else 1

lemma atomMap_irreducible (eA : ↥(Atoms M) ≃ ↥(Atoms N)) {a : M}
    (h : Irreducible a) : Irreducible (atomMap eA a) := by
  rw [atomMap, dif_pos h]
  exact (eA ⟨a, h⟩).2

lemma atomMap_leftInv (eA : ↥(Atoms M) ≃ ↥(Atoms N)) {a : M}
    (h : Irreducible a) : atomMap eA.symm (atomMap eA a) = a := by
  have hinner : atomMap eA a = ((eA ⟨a, h⟩ : ↥(Atoms N)) : N) := by
    rw [atomMap, dif_pos h]
  rw [hinner]
  have h2 : Irreducible ((eA ⟨a, h⟩ : ↥(Atoms N)) : N) := (eA ⟨a, h⟩).2
  rw [atomMap, dif_pos h2]
  have h3 : (⟨((eA ⟨a, h⟩ : ↥(Atoms N)) : N), h2⟩ : ↥(Atoms N)) = eA ⟨a, h⟩ :=
    Subtype.ext rfl
  rw [h3, Equiv.symm_apply_apply]

/-- The transported element: map the canonical atomic multiset and multiply. -/
def transportFn (h_factM : Factorial M) (eA : ↥(Atoms M) ≃ ↥(Atoms N)) :
    M → N :=
  fun m => ((factorMS h_factM m).map (atomMap eA)).prod

lemma transportFn_mul (h_redM : Reduced M) (h_factM : Factorial M)
    (eA : ↥(Atoms M) ≃ ↥(Atoms N)) (a b : M) :
    transportFn h_factM eA (a * b)
      = transportFn h_factM eA a * transportFn h_factM eA b := by
  unfold transportFn
  rw [factorMS_mul h_redM h_factM, Multiset.map_add, Multiset.prod_add]

/-- The canonical multiset of a transported element is the transported
    multiset. -/
lemma factorMS_transportFn (h_redM : Reduced M) (h_factM : Factorial M)
    (h_redN : Reduced N) (h_factN : Factorial N)
    (eA : ↥(Atoms M) ≃ ↥(Atoms N)) (m : M) :
    factorMS h_factN (transportFn h_factM eA m)
      = (factorMS h_factM m).map (atomMap eA) := by
  refine (factorMS_eq h_redN h_factN ?_ rfl).symm
  intro b hb
  obtain ⟨a, ha_mem, rfl⟩ := Multiset.mem_map.mp hb
  exact atomMap_irreducible eA (factorMS_atoms h_redM h_factM m a ha_mem)

lemma transportFn_leftInv (h_redM : Reduced M) (h_factM : Factorial M)
    (h_redN : Reduced N) (h_factN : Factorial N)
    (eA : ↥(Atoms M) ≃ ↥(Atoms N)) (m : M) :
    transportFn h_factN eA.symm (transportFn h_factM eA m) = m := by
  show ((factorMS h_factN (transportFn h_factM eA m)).map (atomMap eA.symm)).prod = m
  rw [factorMS_transportFn h_redM h_factM h_redN h_factN eA m]
  simp only [Multiset.map_map]
  rw [show Multiset.map (atomMap eA.symm ∘ atomMap eA) (factorMS h_factM m)
      = Multiset.map id (factorMS h_factM m) from
    Multiset.map_congr rfl (fun a ha =>
      atomMap_leftInv eA (factorMS_atoms h_redM h_factM m a ha)),
    Multiset.map_id]
  exact factorMS_prod h_redM h_factM m

/-- **Classification, special case**: two reduced factorial monoids with
    equivalent atom sets are isomorphic. -/
noncomputable def factorialMulEquiv (h_redM : Reduced M) (h_factM : Factorial M)
    (h_redN : Reduced N) (h_factN : Factorial N)
    (eA : ↥(Atoms M) ≃ ↥(Atoms N)) : M ≃* N where
  toFun := transportFn h_factM eA
  invFun := transportFn h_factN eA.symm
  left_inv m := transportFn_leftInv h_redM h_factM h_redN h_factN eA m
  right_inv n := by
    have h := transportFn_leftInv h_redN h_factN h_redM h_factM eA.symm n
    rwa [Equiv.symm_symm] at h
  map_mul' a b := transportFn_mul h_redM h_factM eA a b

end Construction

/-! ## Explicit free coordinates -/

section ExplicitCoordinates

open scoped Classical

variable {M : Type*} [CommMonoid M]

/-- The multiplicative form of the direct sum `⊕ p : Atoms M, ℕ`.
    Multiplication corresponds to coordinatewise addition of exponents. -/
abbrev FactorialCoordinates (M : Type*) [CommMonoid M] :=
  Multiplicative ((Atoms M) →₀ ℕ)

/-- The canonical atomic factorization, with every entry bundled with its
    proof of being an atom. -/
def atomFactorMultiset (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    Multiset (Atoms M) :=
  (factorMS h_fact m).pmap
    (fun a ha => (⟨a, ha⟩ : Atoms M))
    (factorMS_atoms h_reduced h_fact m)

lemma atomFactorMultiset_map_val (h_reduced : Reduced M) (h_fact : Factorial M)
    (m : M) :
    (atomFactorMultiset h_reduced h_fact m).map ((↑) : Atoms M → M) =
      factorMS h_fact m := by
  simp [atomFactorMultiset, Multiset.map_pmap, Multiset.pmap_eq_map]

/-- Evaluate finite-support exponent data by multiplying the corresponding
    powers of atoms. This is the displayed coordinate map in Corollary 7.7. -/
def realizeFactorialCoordinates (e : FactorialCoordinates M) : M :=
  (e.toAdd.toMultiset.map ((↑) : Atoms M → M)).prod

/-- The multiset implementation of the coordinate map is exactly the finite
    product `∏ p, p ^ e(p)`. -/
theorem realizeFactorialCoordinates_eq_prod (e : FactorialCoordinates M) :
    realizeFactorialCoordinates e =
      e.toAdd.prod (fun p n => (p : M) ^ n) := by
  change (e.toAdd.toMultiset.map ((↑) : Atoms M → M)).prod =
    e.toAdd.prod (fun p n => (p : M) ^ n)
  induction e.toAdd using Finsupp.induction with
  | zero => simp
  | @single_add a n f ha hn ih =>
      simp [Finsupp.prod_add_index', pow_add, ih, Multiset.map_nsmul,
        Multiset.prod_nsmul]

/-- The inverse coordinate map records the multiplicity of every atom in the
    canonical factorization multiset. -/
def factorialCoordinates (h_reduced : Reduced M) (h_fact : Factorial M) (m : M) :
    FactorialCoordinates M :=
  Multiplicative.ofAdd
    (Multiset.toFinsupp (atomFactorMultiset h_reduced h_fact m))

lemma realize_factorialCoordinates (h_reduced : Reduced M) (h_fact : Factorial M)
    (m : M) :
    realizeFactorialCoordinates (factorialCoordinates h_reduced h_fact m) = m := by
  simp [realizeFactorialCoordinates, factorialCoordinates,
    atomFactorMultiset_map_val, factorMS_prod h_reduced h_fact]

lemma factorMS_realizeFactorialCoordinates (h_reduced : Reduced M)
    (h_fact : Factorial M) (e : FactorialCoordinates M) :
    factorMS h_fact (realizeFactorialCoordinates e) =
      e.toAdd.toMultiset.map ((↑) : Atoms M → M) := by
  symm
  apply factorMS_eq h_reduced h_fact
  · intro a ha
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp ha
    exact p.2
  · rfl

lemma atomFactorMultiset_realizeFactorialCoordinates (h_reduced : Reduced M)
    (h_fact : Factorial M) (e : FactorialCoordinates M) :
    atomFactorMultiset h_reduced h_fact (realizeFactorialCoordinates e) =
      e.toAdd.toMultiset := by
  apply Multiset.map_injective Subtype.val_injective
  rw [atomFactorMultiset_map_val h_reduced h_fact,
    factorMS_realizeFactorialCoordinates h_reduced h_fact]

lemma factorialCoordinates_realize (h_reduced : Reduced M) (h_fact : Factorial M)
    (e : FactorialCoordinates M) :
    factorialCoordinates h_reduced h_fact (realizeFactorialCoordinates e) = e := by
  apply Multiplicative.toAdd.injective
  change Multiset.toFinsupp
      (atomFactorMultiset h_reduced h_fact (realizeFactorialCoordinates e)) = e.toAdd
  rw [atomFactorMultiset_realizeFactorialCoordinates]
  exact Multiset.toFinsupp.apply_symm_apply e.toAdd

lemma realizeFactorialCoordinates_mul (e f : FactorialCoordinates M) :
    realizeFactorialCoordinates (e * f) =
      realizeFactorialCoordinates e * realizeFactorialCoordinates f := by
  change (((e.toAdd + f.toAdd).toMultiset.map ((↑) : Atoms M → M)).prod) = _
  rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add]
  rfl

/-- **Explicit free-coordinate classification.** A reduced factorial monoid
    is canonically isomorphic to the free commutative monoid on its atoms.
    The forward map sends finitely supported exponent data `e` to
    `∏ p, p ^ e p`. -/
def factorialCoordinateEquiv (h_reduced : Reduced M) (h_fact : Factorial M) :
    FactorialCoordinates M ≃* M where
  toFun := realizeFactorialCoordinates
  invFun := factorialCoordinates h_reduced h_fact
  left_inv := factorialCoordinates_realize h_reduced h_fact
  right_inv := realize_factorialCoordinates h_reduced h_fact
  map_mul' := realizeFactorialCoordinates_mul

/-- The explicit coordinate isomorphism evaluates by the formula printed in
    Corollary 7.7. -/
theorem factorialCoordinateEquiv_apply (h_reduced : Reduced M) (h_fact : Factorial M)
    (e : FactorialCoordinates M) :
    factorialCoordinateEquiv h_reduced h_fact e =
      e.toAdd.prod (fun p n => (p : M) ^ n) :=
  realizeFactorialCoordinates_eq_prod e

end ExplicitCoordinates

/-! ## Part (C): the equivalence with ℕ+ -/

/-- **(B) ⟹ (C)**: a reduced factorial monoid with countably infinite atom
    set is isomorphic to (ℕ, ×), represented as ℕ+. -/
theorem mulEquiv_pnat_of_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_fact : Factorial M)
    (hc : (Atoms M).Countable) (hi : Set.Infinite (Atoms M)) :
    Nonempty (M ≃* ℕ+) := by
  haveI : Countable ↥(Atoms M) := hc.to_subtype
  haveI : Infinite ↥(Atoms M) := hi.to_subtype
  obtain ⟨dM⟩ := nonempty_denumerable ↥(Atoms M)
  haveI : Countable ↥(Atoms ℕ+) := NatMonoidExample.pnat_atoms_countable.to_subtype
  haveI : Infinite ↥(Atoms ℕ+) := NatMonoidExample.pnat_atoms_infinite.to_subtype
  obtain ⟨dP⟩ := nonempty_denumerable ↥(Atoms ℕ+)
  exact ⟨factorialMulEquiv h_reduced h_fact
    NatMonoidExample.pnat_reduced NatMonoidExample.pnat_factorial
    ((Denumerable.eqv ↥(Atoms M)).trans (Denumerable.eqv ↥(Atoms ℕ+)).symm)⟩

/-- **(C) ⟹ (B)**: factoriality and the atom-set cardinality transport along
    a monoid isomorphism with ℕ+. -/
theorem factorial_countable_atoms_of_mulEquiv {M : Type*} [CommMonoid M]
    (e : M ≃* ℕ+) :
    Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M) := by
  refine ⟨factorial_of_mulEquiv e NatMonoidExample.pnat_factorial, ?_, ?_⟩
  · haveI : Countable M := Countable.of_equiv ℕ+ e.toEquiv.symm
    exact Set.to_countable _
  · haveI : Infinite ↥(Atoms ℕ+) := NatMonoidExample.pnat_atoms_infinite.to_subtype
    have h := Infinite.of_injective (atomsEquiv e).symm (atomsEquiv e).symm.injective
    exact Set.infinite_coe_iff.mp h

/-- **(B) ⟺ (C)** of the paper's Theorem 4.1. -/
theorem thm_B_iff_C {M : Type*} [CommMonoid M] (h_reduced : Reduced M) :
    (Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M)) ↔
    Nonempty (M ≃* ℕ+) := by
  constructor
  · rintro ⟨hf, hc, hi⟩
    exact mulEquiv_pnat_of_factorial h_reduced hf hc hi
  · rintro ⟨e⟩
    exact factorial_countable_atoms_of_mulEquiv e

/-- **The main theorem, (A) ⟺ (C)**: over a reduced commutative monoid, the
    four axioms hold iff M is isomorphic to the multiplicative monoid of
    positive integers. -/
theorem thm_A_iff_C {M : Type*} [CommMonoid M] (h_reduced : Reduced M) :
    (WFD M ∧ TD M ∧ CFI M ∧ CCA M) ↔ Nonempty (M ≃* ℕ+) :=
  (thm_A_iff_B h_reduced).trans (thm_B_iff_C h_reduced)

end
