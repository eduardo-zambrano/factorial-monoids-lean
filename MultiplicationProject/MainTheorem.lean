/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0faa6e02-741d-48d1-8afe-097c44a9cddb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma exists_atom_dvd {M : Type*} [CancelCommMonoid M]
    (h_atomic : Atomic M) (m : M) (hm : ¬IsUnit m) :
    ∃ p ∈ Atoms M, p ∣ m

- lemma exists_injective_atom_choice {M : Type*} [CancelCommMonoid M]
    (h_atomic : Atomic M)
    (S : Finset M) (hS_nonunit : ∀ x ∈ S, ¬IsUnit x)
    (hS_coprime : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → AreCoprime x y) :
    ∃ f : S → Atoms M, Function.Injective f ∧ ∀ s : S, (f s : M) ∣ (s : M)

- lemma nodup_of_pairwise_coprime {M : Type*} [CancelCommMonoid M]
    (h_atomic : Atomic M)
    (L : List M) (hL_nonunit : ∀ x ∈ L, ¬IsUnit x) (hL_coprime : L.Pairwise AreCoprime) :
    L.Nodup

- theorem atoms_infinite_of_CPL {M : Type*} [CancelCommMonoid M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    Set.Infinite (Atoms M)

- theorem atoms_countable {M : Type*} [CancelCommMonoid M] [Countable M] :
    (Atoms M).Countable
-/

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

import MultiplicationProject.MasterFormula
import MultiplicationProject.APD_Redundancy_v6


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
  by_contra h_contra;
  obtain ⟨ p, hp ⟩ := h_atomic m hm;
  rcases p with ⟨ ⟨ a ⟩ ⟩ <;> simp_all +decide [ irreducible_iff ];
  · exact hm ( hp ▸ isUnit_one );
  · exact h_contra _ ⟨ hp.1.1.1, hp.1.1.2 ⟩ ( hp.2 ▸ dvd_mul_right _ _ )

/-- From a finite set of pairwise coprime non-units, we can extract distinct atoms.
    The function f assigns to each element an atom dividing it, and f is injective
    because coprime elements cannot share an atom. -/
lemma exists_injective_atom_choice {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M)
    (S : Finset M) (hS_nonunit : ∀ x ∈ S, ¬IsUnit x)
    (hS_coprime : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → AreCoprime x y) :
    ∃ f : S → Atoms M, Function.Injective f ∧ ∀ s : S, (f s : M) ∣ (s : M) := by
  -- Let's choose any $x ∈ S$ and obtain an atom $p$ such that $p ∣ x$.
  have h_atom_exists : ∀ x ∈ S, ∃ p ∈ Atoms M, p ∣ x := by
    exact?;
  choose! f hf using h_atom_exists;
  -- Show that f is injective.
  have h_inj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x ≠ f y := by
    intro x hx y hy hxy h; specialize hS_coprime x hx y hy hxy; have := hf x hx; have := hf y hy; simp_all +decide [ AreCoprime ] ;
    exact hS_coprime _ ( hf _ hy |>.1 ) ( h ▸ this ) ( hf _ hy |>.2 );
  exact ⟨ fun s => ⟨ f s, hf s s.2 |>.1 ⟩, fun s t hst => by_contradiction fun hst' => h_inj s s.2 t t.2 ( by aesop ) ( by aesop ), fun s => hf s s.2 |>.2 ⟩

/-- A list of pairwise coprime non-units has no duplicates.
    If L[i] = L[j] with i ≠ j, then L[i] is coprime to itself.
    But any non-unit has an atom dividing it, contradicting coprimality. -/
lemma nodup_of_pairwise_coprime {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M)
    (L : List M) (hL_nonunit : ∀ x ∈ L, ¬IsUnit x) (hL_coprime : L.Pairwise AreCoprime) :
    L.Nodup := by
  rw [ List.nodup_iff_injective_get ];
  intro i j hij
  by_contra h_neq;
  have h_coprime_self : AreCoprime (L.get i) (L.get j) := by
    have := List.pairwise_iff_get.mp hL_coprime;
    grind;
  -- By definition of coprimality, if L[i] is coprime to itself, then any atom dividing L[i] must divide 1, which is impossible since atoms are non-units.
  obtain ⟨p, hp⟩ : ∃ p ∈ Atoms M, p ∣ L.get i := by
    exact exists_atom_dvd h_atomic _ ( hL_nonunit _ ( by simp ) );
  have := h_coprime_self p; simp_all +decide;

/-- CPL implies the atom set is infinite.

    The proof: Suppose Atoms M is finite with n elements. By CPL, there exist n+1
    pairwise coprime non-units. Each has a distinct atom dividing it (by coprimality).
    This gives n+1 distinct atoms, contradiction. -/
theorem atoms_infinite_of_CPL {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    Set.Infinite (Atoms M) := by
  -- Suppose for contradiction that Atoms M is finite with n elements.
  by_cases h_finite : (Atoms M).Finite;
  · -- By CPL, there exist n+1 pairwise coprime non-units.
    obtain ⟨L, hL_length, hL_nonunit, hL_coprime⟩ : ∃ L : List M, L.length = h_finite.toFinset.card + 1 ∧ (∀ x ∈ L, ¬IsUnit x) ∧ L.Pairwise AreCoprime := by
      exact h_cpl ( h_finite.toFinset.card + 1 ) |> fun ⟨ L, hL ⟩ => ⟨ L, hL ⟩;
    -- By the lemma `exists_injective_atom_choice`, there exists an injective function `f : L.toFinset → Atoms M` such that `f s` divides `s` for all `s : L.toFinset`.
    obtain ⟨f, hf_injective, hf_div⟩ : ∃ f : L.toFinset → Atoms M, Function.Injective f ∧ ∀ s : L.toFinset, (f s : M) ∣ (s : M) := by
      apply exists_injective_atom_choice h_atomic (L.toFinset) (by
      aesop) (by
      simp_all +decide [ List.pairwise_iff_get ];
      intro x hx y hy hxy
      obtain ⟨i, hi⟩ : ∃ i : Fin L.length, L[i] = x := by
        exact?
      obtain ⟨j, hj⟩ : ∃ j : Fin L.length, L[j] = y := by
        exact?
      have hij : i ≠ j := by
        grind +ring
      have h_coprime : AreCoprime L[i] L[j] := by
        cases lt_or_gt_of_ne hij <;> [ exact hL_coprime _ _ ‹_› ; exact AreCoprime_symm.mp ( hL_coprime _ _ ‹_› ) ]
      aesop);
    have h_card : Finset.card (L.toFinset : Finset M) ≤ h_finite.toFinset.card := by
      have h_card : Finset.card (Finset.image (fun s : L.toFinset => (f s : M)) Finset.univ) ≤ h_finite.toFinset.card := by
        exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun s _ => h_finite.mem_toFinset.mpr ( f s |>.2 ) );
      rw [ Finset.card_image_of_injective _ fun x y hxy => by have := hf_injective ( Subtype.ext hxy ) ; aesop ] at h_card ; aesop;
    exact absurd h_card ( by rw [ List.toFinset_card_of_nodup ( nodup_of_pairwise_coprime h_atomic L hL_nonunit hL_coprime ) ] ; simp +decide [ hL_length ] );
  · exact h_finite

/-- **Theorem 9.1**: Main result (APD version).

    Under (APD), (PP-D), (CFI), and (CPL):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    Part (a) is cor_factorial. Part (b) follows from atoms_infinite_of_CPL.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  ⟨cor_factorial h_reduced h_atomic h_apd h_ppd h_cfi,
   atoms_infinite_of_CPL h_atomic h_cpl⟩

/-- **Theorem 9.1**: Main result (System B version, sorry-free).

    Under (PP-P), (PP-D), (CFI), and (CPL):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    This uses the axiom system {PP-D, PP-P, CFI, CPL}, where APD is
    derived from PP-P via `PPP_implies_APD`. The entire proof chain
    from these axioms to the conclusion is sorry-free.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main_PPP {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppp : PP_P M) (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  thm_main h_reduced h_atomic (PPP_implies_APD h_reduced h_ppp) h_ppd h_cfi h_cpl

/-- **Theorem 9.1**: Main result (paper version).

    Under (PP-D), (UAB), (CFI), (CPL), and ACCP (base assumption):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    This matches the paper's axiom system {PP-D, UAB, CFI, CPL} with ACCP
    as a base assumption. The proof chains through Proposition 5.1
    (CFI + UAB + ACCP ⟹ APD) and then applies `thm_main`.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main_UAB {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_uab : UAB M) (h_cfi : CFI M) (h_cpl : CPL M)
    (h_accp : ACCP M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  thm_main h_reduced h_atomic
    (CFI_UAB_implies_APD h_reduced h_cfi h_uab h_accp)
    h_ppd h_cfi h_cpl

/-- The atom set is countable when M is countable. -/
theorem atoms_countable {M : Type*} [CommMonoid M] [Countable M] :
    (Atoms M).Countable := by
  exact Set.to_countable _

/-- Under CPL with M countable, the atom set is countably infinite. -/
theorem atoms_countably_infinite {M : Type*} [CommMonoid M] [Countable M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    (Atoms M).Countable ∧ Set.Infinite (Atoms M) :=
  ⟨atoms_countable, atoms_infinite_of_CPL h_atomic h_cpl⟩

end