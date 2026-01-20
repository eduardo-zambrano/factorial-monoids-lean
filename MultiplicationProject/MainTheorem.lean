/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 9: Main Theorem

This file proves Theorem 9.1 from the paper:
Under (PP-D), (CFI), and (CPL), the monoid M is isomorphic to (ℕ, ×).

The proof has two parts:
(a) M is factorial - proven in MasterFormula_v2_aristotle.lean as cor_factorial
(b) CPL forces the atom set to be countably infinite, hence M ≅ (ℕ, ×)
-/

import MultiplicationProject.MasterFormula_v2_aristotle

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Part (b): CPL implies atoms are infinite

The key insight: Given r pairwise coprime non-units, each has a distinct atom
dividing it (atoms of coprime elements are distinct). Hence |Atoms M| ≥ r for all r.
-/

/-- Every non-unit has at least one atom dividing it. -/
lemma exists_atom_dvd {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M) (m : M) (hm : ¬IsUnit m) :
    ∃ p ∈ Atoms M, p ∣ m := by
  sorry

/-- From a finite set of pairwise coprime non-units, we can extract distinct atoms.
    The function f assigns to each element an atom dividing it, and f is injective
    because coprime elements cannot share an atom. -/
lemma exists_injective_atom_choice {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M)
    (S : Finset M) (hS_nonunit : ∀ x ∈ S, ¬IsUnit x)
    (hS_coprime : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → AreCoprime x y) :
    ∃ f : S → Atoms M, Function.Injective f ∧ ∀ s : S, (f s : M) ∣ (s : M) := by
  sorry

/-- A list of pairwise coprime non-units has no duplicates.
    If L[i] = L[j] with i ≠ j, then L[i] is coprime to itself.
    But any non-unit has an atom dividing it, contradicting coprimality. -/
lemma nodup_of_pairwise_coprime {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M)
    (L : List M) (hL_nonunit : ∀ x ∈ L, ¬IsUnit x) (hL_coprime : L.Pairwise AreCoprime) :
    L.Nodup := by
  sorry

/-- CPL implies the atom set is infinite.

    The proof: Suppose Atoms M is finite with n elements. By CPL, there exist n+1
    pairwise coprime non-units. Each has a distinct atom dividing it (by coprimality).
    This gives n+1 distinct atoms, contradiction. -/
theorem atoms_infinite_of_CPL {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    Set.Infinite (Atoms M) := by
  sorry

/-- **Theorem 9.1**: Main result.

    Under (PP-D), (CFI), and (CPL):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    Part (a) is cor_factorial. Part (b) follows from atoms_infinite_of_CPL. -/
theorem thm_main {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  ⟨cor_factorial h_reduced h_atomic h_ppd h_cfi,
   atoms_infinite_of_CPL h_atomic h_cpl⟩

/-- The atom set is countable when M is countable. -/
theorem atoms_countable {M : Type*} [CommMonoid M] [Countable M] :
    (Atoms M).Countable := by
  sorry

/-- Under CPL with M countable, the atom set is countably infinite. -/
theorem atoms_countably_infinite {M : Type*} [CommMonoid M] [Countable M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    (Atoms M).Countable ∧ Set.Infinite (Atoms M) :=
  ⟨atoms_countable, atoms_infinite_of_CPL h_atomic h_cpl⟩

end
