/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Sections 2-3: Basic Definitions and Axioms

This file contains the fundamental definitions for characterizing
factorial monoids via labeled factorization counts.

Based on the paper "Characterizing Factorial Monoids via Labeled Factorization Counts"
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
## Core Definitions
-/

/-- A monoid M is reduced if 1 is the only unit. -/
def Reduced (M : Type*) [Monoid M] : Prop :=
  ∀ u : M, IsUnit u → u = 1

/-- M is atomic if every non-unit can be written as a finite product of atoms. -/
def Atomic (M : Type*) [CommMonoid M] : Prop :=
  ∀ x : M, ¬ IsUnit x → ∃ (s : Multiset M), (∀ a ∈ s, Irreducible a) ∧ s.prod = x

/-- M is factorial if every non-unit has a unique factorization into atoms, up to order. -/
def Factorial (M : Type*) [CommMonoid M] : Prop :=
  ∀ x : M, ¬ IsUnit x → ∃! s : Multiset M, (∀ a ∈ s, Irreducible a) ∧ s.prod = x

/-- The set of atoms (irreducible elements) in M. -/
def Atoms (M : Type*) [Monoid M] : Set M := { x | Irreducible x }

/-- The set of labeled k-factorizations of m.
    These are ordered k-tuples (m₁, ..., mₖ) with m₁ · ... · mₖ = m. -/
def LabeledFactorizations {M : Type*} [CommMonoid M] (k : ℕ) (m : M) : Set (Fin k → M) :=
  { f | (Finset.univ.prod f) = m }

/-- The labeled k-factorization count F_k(m) is the cardinality of the set of
    labeled k-factorizations. -/
noncomputable def LabeledFactorizationCount {M : Type*} [CommMonoid M] (k : ℕ) (m : M) : ℕ :=
  Set.ncard (LabeledFactorizations k m)

/-- Two elements are coprime if no atom divides both. -/
def AreCoprime {M : Type*} [Monoid M] (x y : M) : Prop :=
  ∀ p ∈ Atoms M, p ∣ x → ¬ p ∣ y

/-- The support of m is the set of atoms dividing m. -/
def Support {M : Type*} [Monoid M] (m : M) : Set M :=
  { p ∈ Atoms M | p ∣ m }

/-!
## The Three Axioms

These axioms characterize when a reduced atomic commutative monoid is factorial.
-/

/-- **Axiom PP-D**: Powers of atoms are distinct.
    For every atom p, the map e ↦ p^e is injective. -/
def PP_D (M : Type*) [Monoid M] : Prop :=
  ∀ p ∈ Atoms M, Function.Injective (fun (e : ℕ) => p ^ e)

/-- **Property PP-P**: Prime powers are factorially closed.
    For every atom p, if x * y is a power of p, then x and y are powers of p. -/
def PP_P (M : Type*) [Monoid M] : Prop :=
  ∀ p ∈ Atoms M, ∀ x y : M, x * y ∈ Submonoid.powers p →
    x ∈ Submonoid.powers p ∧ y ∈ Submonoid.powers p

/-- Helper: The coordinatewise product of a k-factorization of x and a k-factorization of y
    is a k-factorization of x*y. -/
def labeledFactorizationMul {M : Type*} [CommMonoid M] {k : ℕ} {x y : M}
    (f : LabeledFactorizations k x) (g : LabeledFactorizations k y) :
    LabeledFactorizations k (x * y) :=
  ⟨f.1 * g.1, by
    convert congr_arg₂ ( · * · ) f.2 g.2 using 1
    simp [LabeledFactorizations]
    rw [Finset.prod_mul_distrib]⟩

/-- **Axiom CFI**: Coprime parts factor independently.
    If x, y are coprime, then the coordinatewise multiplication map
    from F_2(x) × F_2(y) to F_2(x * y) is a bijection. -/
def CFI (M : Type*) [CommMonoid M] : Prop :=
  ∀ x y : M, AreCoprime x y →
    Function.Bijective (fun p : LabeledFactorizations 2 x × LabeledFactorizations 2 y =>
                          labeledFactorizationMul p.1 p.2)

/-- **Axiom CPL**: Coprime tuples come in every length.
    For every r, there exist r pairwise coprime non-units. -/
def CPL (M : Type*) [Monoid M] : Prop :=
  ∀ r : ℕ, ∃ (L : List M), L.length = r ∧ (∀ x ∈ L, ¬ IsUnit x) ∧ L.Pairwise AreCoprime

/-!
## Helper Definitions
-/

/-- A family of pairs (x_i, y_i) is blockwise disjoint if the supports of distinct blocks
    are disjoint. -/
def BlockwiseDisjoint {M : Type*} [Monoid M] {n : ℕ} (x y : Fin n → M) : Prop :=
  ∀ i j, i ≠ j → Disjoint (Support (x i) ∪ Support (y i)) (Support (x j) ∪ Support (y j))

/-- The p-adic valuation v_p(m) = max{e ≥ 0 : p^e | m} -/
def PValuation {M : Type*} [CommMonoid M] (p : M) (m : M) : ℕ :=
  sSup {e | p ^ e ∣ m}

end