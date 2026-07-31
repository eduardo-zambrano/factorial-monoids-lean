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
Under (tower faithfulness), (CFI), and (CPL), the monoid M is isomorphic to (ℕ, ×).

The proof has two parts:
(a) M is factorial - proven in FactorialStructure.lean as cor_factorial
(b) CPL forces the atom set to be countably infinite, hence M ≅ (ℕ, ×)
-/

import MultiplicationProject.FactorialStructure
import MultiplicationProject.APDRedundancy
import MultiplicationProject.AxiomsNecessity


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

    Under (APD), (tower faithfulness), (CFI), and (CPL):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    Part (a) is cor_factorial. Part (b) follows from atoms_infinite_of_CPL.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  ⟨cor_factorial h_reduced h_atomic h_apd h_tf h_cfi,
   atoms_infinite_of_CPL h_atomic h_cpl⟩

/-- **Theorem 9.1**: Main result (System B version, sorry-free).

    Under (PP-P), (tower faithfulness), (CFI), and (CPL):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    This uses the axiom system {tower faithfulness, PP-P, CFI, CPL}, where APD is
    derived from PP-P via `towers_factorially_closed_implies_APD`. The entire proof chain
    from these axioms to the conclusion is sorry-free.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main_towers_factorially_closed {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppp : TowersFactoriallyClosed M) (h_tf : TowerFaithful M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  thm_main h_reduced h_atomic (towers_factorially_closed_implies_APD h_reduced h_ppp) h_tf h_cfi h_cpl

/-- **Theorem 9.1**: Main result (paper version).

    Under (tower faithfulness), (TD), (CFI), (CPL), and WFD (base assumption):
    (a) M is factorial (isomorphic to ⊕_{p ∈ P} ℕ₀)
    (b) The atom set P is countably infinite, hence M ≅ (ℕ, ×)

    This matches the paper's axiom system {tower faithfulness, TD, CFI, CPL} with WFD
    as a base assumption. The proof chains through Proposition 5.1
    (CFI + TD + WFD ⟹ APD) and then applies `thm_main`.

    Note: This uses CommMonoid (not CancelCommMonoid) since cancellativity
    is derived from the axioms via Factorial. -/
theorem thm_main_TD {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_tf : TowerFaithful M) (h_td : TD M) (h_cfi : CFI M) (h_cpl : CPL M)
    (h_wfd : WFD M) :
    Factorial M ∧ Set.Infinite (Atoms M) :=
  thm_main h_reduced h_atomic
    (CFI_TD_implies_APD h_reduced h_cfi h_td h_wfd)
    h_tf h_cfi h_cpl

/-- The atom set is countable when M is countable. -/
theorem atoms_countable {M : Type*} [CommMonoid M] [Countable M] :
    (Atoms M).Countable := by
  exact Set.to_countable _

/-- Under CPL with M countable, the atom set is countably infinite. -/
theorem atoms_countably_infinite {M : Type*} [CommMonoid M] [Countable M]
    (h_atomic : Atomic M) (h_cpl : CPL M) :
    (Atoms M).Countable ∧ Set.Infinite (Atoms M) :=
  ⟨atoms_countable, atoms_infinite_of_CPL h_atomic h_cpl⟩

/-! ## CPL⁺: the strengthened axiom

CPL⁺ (`CCA`, defined in Basic.lean) supplies both halves of "the atom
set is countably infinite" with NO countability assumption on M:
- the lower bound (infinitude) via `CCA_implies_CPL`;
- the upper bound (countability) because every atom divides some member of
  the coprime basis, hence lies in its finite support (`support_finite`,
  the primewise-support lemma — paper Lemma 7.6).

Note the firing order: countability needs the other axioms' machinery
(finite supports); CPL⁺ is the last axiom to fire. -/

/-- CPL⁺ implies the atom set is infinite (lower bound half). -/
theorem atoms_infinite_of_CCA {M : Type*} [CommMonoid M]
    (h_atomic : Atomic M) (h : CCA M) :
    Set.Infinite (Atoms M) :=
  atoms_infinite_of_CPL h_atomic (CCA_implies_CPL h)

/-- CPL⁺ implies the atom set is countable (upper bound half) — with no
    countability assumption on M. Every atom divides some basis element mᵢ,
    hence lies in Support(mᵢ), which is finite (`support_finite`, the
    primewise-support lemma); so the atoms are covered by countably many
    finite sets. This is the paper's §8 upper-bound argument verbatim. -/
theorem atoms_countable_of_CCA {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (h : CCA M) :
    (Atoms M).Countable := by
  obtain ⟨m, hm_nonunit, -, hm_cover⟩ := h
  have hsub : Atoms M ⊆ ⋃ i, Support (m i) := by
    intro p hp
    obtain ⟨i, hi⟩ := hm_cover p hp
    exact Set.mem_iUnion.mpr ⟨i, hp, hi⟩
  exact Set.Countable.mono hsub
    (Set.countable_iUnion fun i =>
      (support_finite h_reduced h_atomic h_apd h_tf h_cfi (m i)
        (hm_nonunit i)).countable)

/-- Under Reduced + Atomic + APD + CFI, the axiom CPL⁺ makes the atom set
    countably infinite — no countability hypothesis on M. -/
theorem atoms_countably_infinite_of_CCA {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (h : CCA M) :
    (Atoms M).Countable ∧ Set.Infinite (Atoms M) :=
  ⟨atoms_countable_of_CCA h_reduced h_atomic h_apd h_tf h_cfi h,
   atoms_infinite_of_CCA h_atomic h⟩

/-- **Theorem 9.1, revised (CPL⁺ version)**: Under the axiom system
    {tower faithfulness, TD, CFI, CPL⁺} with base assumptions (reduced, atomic, WFD):
    (a) M is factorial;
    (b) the atom set is countably infinite.
    Hence M is the free commutative monoid on countably many generators,
    i.e., M ≅ (ℕ, ×). No countability of M is assumed — CPL⁺ provides it. -/
theorem thm_A_implies_B {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_tf : TowerFaithful M) (h_td : TD M) (h_cfi : CFI M) (h_cca : CCA M)
    (h_wfd : WFD M) :
    Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M) := by
  have h_apd : APD M := CFI_TD_implies_APD h_reduced h_cfi h_td h_wfd
  exact ⟨cor_factorial h_reduced h_atomic h_apd h_tf h_cfi,
    atoms_countable_of_CCA h_reduced h_atomic h_apd h_tf h_cfi h_cca,
    atoms_infinite_of_CCA h_atomic h_cca⟩

/-- **The characterization theorem**: over the base assumptions (reduced,
    atomic, WFD), the axiom system {tower faithfulness, TD, CFI, CPL⁺} holds IF AND ONLY
    IF M is factorial with countably infinite atom set — i.e., iff M is the
    free commutative monoid on countably many generators, i.e., M ≅ (ℕ, ×).

    Forward direction: `thm_A_implies_B` (uses WFD via Prop 5.1).
    Backward direction: `tower_faithful_of_factorial`, `TD_of_factorial`,
    `CFI_of_factorial`, `CCA_of_atoms_countably_infinite`
    (needs only reducedness). -/
theorem thm_characterization {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_wfd : WFD M) :
    (TowerFaithful M ∧ TD M ∧ CFI M ∧ CCA M) ↔
    (Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M)) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact thm_A_implies_B h_reduced h_atomic h1 h2 h3 h4 h_wfd
  · rintro ⟨hf, hc, hi⟩
    exact ⟨tower_faithful_of_factorial h_reduced hf, TD_of_factorial h_reduced hf,
           CFI_of_factorial h_reduced hf,
           CCA_of_atoms_countably_infinite h_reduced hc hi⟩

/-- **The characterization theorem, three-axiom form**: since WFD already
    implies tower faithfulness (`WFD_implies_tower_faithful`), the axiom tower faithfulness can be dropped.
    Over the base assumptions (reduced, atomic, WFD):
    {TD, CFI, CPL⁺} ⟺ factorial with countably infinite atom set.
    This is the form of the main theorem stated in the paper (Theorem 4.1);
    the backward direction uses only reducedness. -/
theorem thm_characterization_three_axioms {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_wfd : WFD M) :
    (TD M ∧ CFI M ∧ CCA M) ↔
    (Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M)) := by
  constructor
  · rintro ⟨h2, h3, h4⟩
    exact thm_A_implies_B h_reduced h_atomic
      (WFD_implies_tower_faithful h_reduced h_wfd) h2 h3 h4 h_wfd
  · rintro ⟨hf, hc, hi⟩
    exact ⟨TD_of_factorial h_reduced hf, CFI_of_factorial h_reduced hf,
           CCA_of_atoms_countably_infinite h_reduced hc hi⟩

/-- **The cardinality-free characterization** (the first display of the
    paper's Theorem 4.1): over a reduced commutative monoid — nothing else
    assumed — the three structural axioms {WFD, TD, CFI} (paper names:
    {WFD, TD, CFI}) hold iff M is factorial. Forward: atomicity and tower faithfulness
    from WFD, APD from CFI + TD + WFD, then factoriality; backward:
    each axiom from factoriality, using only reducedness. -/
theorem thm_structural_characterization {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) :
    (WFD M ∧ TD M ∧ CFI M) ↔ Factorial M := by
  constructor
  · rintro ⟨h_wfd, h_td, h_cfi⟩
    exact cor_factorial h_reduced (Atomic_of_WFD h_wfd)
      (CFI_TD_implies_APD h_reduced h_cfi h_td h_wfd)
      (WFD_implies_tower_faithful h_reduced h_wfd) h_cfi
  · intro hf
    exact ⟨WFD_of_factorial h_reduced hf, TD_of_factorial h_reduced hf,
           CFI_of_factorial h_reduced hf⟩

/-- **The characterization theorem, final form**: over a reduced commutative
    monoid — with no atomicity or chain condition assumed — the four axioms
    {WFD, TD, CFI, CPL⁺} hold iff M is factorial with countably infinite
    atom set, i.e., iff M ≅ (ℕ, ×). Atomicity and tower faithfulness are derived from
    WFD (`Atomic_of_WFD`, `WFD_implies_tower_faithful`); the backward direction
    supplies WFD from factoriality (`WFD_of_factorial`). -/
theorem thm_A_iff_B {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) :
    (WFD M ∧ TD M ∧ CFI M ∧ CCA M) ↔
    (Factorial M ∧ (Atoms M).Countable ∧ Set.Infinite (Atoms M)) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact thm_A_implies_B h_reduced (Atomic_of_WFD h1)
      (WFD_implies_tower_faithful h_reduced h1) h2 h3 h4 h1
  · rintro ⟨hf, hc, hi⟩
    exact ⟨WFD_of_factorial h_reduced hf, TD_of_factorial h_reduced hf,
           CFI_of_factorial h_reduced hf,
           CCA_of_atoms_countably_infinite h_reduced hc hi⟩

end