# Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Overview

This project formalizes a characterization of ordinary multiplication on natural numbers using only counting properties of labeled factorizations. The main theorem (Theorem 9.1) shows that a reduced atomic commutative monoid satisfying WFD and four simple axioms is factorial with infinitely many atoms, hence isomorphic to (N, x).

## Base Assumptions

Throughout, (M, ·, 1) is a monoid satisfying the following base assumptions:

| Base Assumption | Description |
|-----------------|-------------|
| **Commutative** | The monoid operation is commutative (a · b = b · a) |
| **Reduced** | The only unit is the identity element |
| **Atomic** | Every non-unit can be written as a finite product of atoms |
| **WFD** | Ascending chain condition on principal ideals: there is no infinite sequence m₁, m₂, … in M such that each mᵢ₊₁ strictly divides mᵢ |

We do *not* assume cancellativity. Instead, cancellativity is *derived* as a consequence of factorial structure (Corollary 8.4).

## The Four Axioms

The paper characterizes factorial monoids using four axioms on top of the base assumptions:

| Axiom | Name | Description |
|-------|------|-------------|
| **tower faithfulness** | Prime-Powers-Distinct | For each atom p, p^a = p^b implies a = b |
| **TD** | Tower Disjointness | If p^k = q^m (atoms p, q; k, m >= 1), then p = q |
| **CFI** | Coprime-Factor-Independence | Coprime parts factor independently (bijection condition) |
| **CPL** | Coprime-Products-at-every-Length | Pairwise coprime non-units exist in every length |

### Derived Properties

| Property | Name | Description |
|----------|------|-------------|
| **APD** | Atom-Power-Divisibility | If atom q divides p^k (p an atom), then q = p |
| **PP-P** | Prime-Powers-Pure | Prime-power submonoid ⟨p⟩ is factorially closed |

**Key equivalences**: PP-P ⟺ APD ⟺ TD (given CFI + WFD). Specifically: PP-P ⟹ APD (`towers_factorially_closed_implies_APD`), APD ⟹ TD (`APD_implies_TD`), APD ⟹ PP-P (`APD_implies_towers_factorially_closed`), and CFI + TD + WFD ⟹ APD (`CFI_TD_implies_APD`).

## Main Results

### Main Theorem (Theorem 9.1)

The main theorem matches the paper's axiom set {tower faithfulness, TD, CFI, CPL} with WFD as a base assumption:

```lean
theorem thm_main_TD {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_tf : TowerFaithful M) (h_td : TD M) (h_cfi : CFI M) (h_cpl : CPL M)
    (h_wfd : WFD M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

This chains through Proposition 5.1 (`CFI_TD_implies_APD`) to derive APD from CFI + TD + WFD, then feeds into the main proof. The code also contains an internal variant `thm_main_towers_factorially_closed` that takes the derived property PP-P directly; this is a stepping stone in the proof chain, not a separate axiom system.

### Master Counting Formula (Theorem 8.2)

```lean
theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_tf : TowerFaithful M) (h_cfi : CFI M)
    (h_finite : forall (k : N) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : N) (hk : k >= 1) :
    exists (S : Finset M), (forall p in S, p in Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1))
```

This establishes the explicit counting formula F_k(m) = prod_p C(v_p(m)+k-1, k-1).

## Complete List of Formalized Results

| Paper Ref | Name | Lean Name | Status |
|-----------|------|-----------|--------|
| **Section 5: Deriving APD and Local Purity** |
| Prop 5.1 | CFI + TD + WFD => APD | `CFI_TD_implies_APD` | Complete |
| Prop 5.2 | APD => PP-P | `APD_implies_towers_factorially_closed` | Complete |
| -- | PP-P => APD | `towers_factorially_closed_implies_APD` | Complete |
| -- | APD => TD | `APD_implies_TD` | Complete |
| **Section 6: Local Characterization** |
| Lemma 6.1 | Unique factorization in prime powers | `pp_unique` | Complete |
| Thm 6.2 | Local stars-and-bars | `Theorem_Local_SB` | Complete |
| **Section 7: Global Multiplicativity** |
| Lemma 7.1 | CFI extends to all k | (built into `prop_coprime_mult`) | Complete |
| Prop 7.2 | Coprime multiplicativity | `prop_coprime_mult` | Complete |
| Cor 7.3 | Squarefree diagnostic | `cor_squarefree` | Complete |
| **Structural spine and counting consequences** |
| -- | Multiplicity rigidity | `multiplicity_rigidity` | Complete |
| -- | Factorial structure from multiplicity rigidity | `cor_factorial` | Complete |
| -- | Valuation additivity | `prop_val_additive` | Complete |
| -- | Primewise decomposition | `lem_primewise` | Complete |
| -- | Primewise decomposition with support clauses | `lem_primewise_full` | Complete |
| -- | Finiteness of atom-divisor support | `support_finite` | Complete |
| **Thm 8.2** | **Master counting formula** | `thm_master` | Complete |
| **Section 9: Main Theorem** |
| **Thm 9.1** | **Main result: M isomorphic to (N, x)** | `thm_main_TD` | Complete |
| **Section 10: Independence of the Axioms** |
| Ex 10.1 | tower faithfulness fails (collapsing monoid) | `collapsing_not_tower_faithful` | Complete |
| Ex 10.2 | TD fails (p₁² = p₂² monoid) | `tdfail_not_TD` | Complete |
| Ex 10.3 | CFI fails (pq = uv monoid) | `cfifail_not_CFI` | Complete |
| Ex 10.4 | CPL fails (Peano monoid) | `peano_not_CPL` | Complete |
| **Additional Results** |
| -- | Atoms are prime under APD + CFI | `atoms_are_prime_APD` | Complete |
| -- | CPL implies atoms are infinite | `atoms_infinite_of_CPL` | Complete |
| -- | Factorial implies cancellative | `Factorial_implies_mul_left_cancel` | Complete |

### Note on Proposition 5.1

`APDRedundancy.lean` proves Proposition 5.1 from the paper: CFI + TD + WFD ⟹ APD. The proof uses well-founded induction on elements (via WFD).

WFD (Ascending Chain Condition on Principal ideals) provides well-foundedness of strict divisibility. In cancellative monoids, WFD follows from atomicity; in the non-cancellative setting, it is an additional assumption.

## Logical Structure of the Proof

```
  tower faithfulness  TD                 CFI      CPL
    |    |                   |        |
    |    +                   |        |
    |    |                   |        |
    | CFI_TD_implies_APD    |        |
    |    |  (Prop 5.1)       |        |
    |    v                   |        |
    |   APD                  |        |
    |    |                   |        |
    |    v                   |        |
    | APD_implies_towers_factorially_closed        |        |
    |  (Prop 5.2)            |        |
    |    |                   |        |
    |    v                   |        |
    |  PP-P                  |        |
    |    |                   |        |
    |    v                   |        |
    +----+                   |        |
         |                   |        |
         v                   v        |
  pp_unique  prop_coprime_mult  |
    (Lemma 6.1)      (Prop 7.2)       |
         |                |           |
         +-------+--------+           |
                 |                    |
                 v                    |
 multiplicity_rigidity    |
       (multiplicity rigidity)        |
                 |                    |
                 v                    |
           cor_factorial              |
                 |                    |
       +---------+---------+          |
       |                   |          |
       v                   v          |
 prop_val_additive   lem_primewise_full
       |              support_finite  |
       +---------+---------+          |
                 |                    |
                 v                    |
            thm_master (Thm 8.2)      |
                 |                    |
                 +--------------------+
                 |
                 v
          thm_main_TD (Thm 9.1)
          Factorial M ∧ Set.Infinite (Atoms M)
```

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | Sections 2-3 | Core definitions (tower faithfulness, TD, CFI, CPL, PP-P, APD), towers_factorially_closed_implies_APD, APD_implies_TD, APD_implies_towers_factorially_closed, StrictDvd, WFD |
| `APDRedundancy.lean` | Section 5 | CFI + TD + WFD => APD (Prop 5.1) |
| `Utilities.lean` | -- | Transfer lemmas, support properties |
| `TowersFactoriallyClosed.lean` | Section 5 | Helper lemmas for coprimality and blockwise CFI |
| `LocalCounting.lean` | Section 6 | Local stars-and-bars (Theorem 6.2) |
| `CoprimeAssembly.lean` | Section 7 | Coprime multiplicativity (Proposition 7.2) |
| `FactorialStructure.lean` | Structural spine and counting consequences | Multiplicity rigidity, factoriality, valuation additivity, primewise support, master formula |
| `MainTheorem.lean` | Section 9 | Main theorem (Theorem 9.1): `thm_main_TD` |
| `Examples/CollapsingMonoid.lean` | Section 10 | Ex 10.1: tower faithfulness fails, TD+CFI+CPL hold |
| `Examples/TDFailMonoid.lean` | Section 10 | Ex 10.2: TD fails, tower faithfulness+CFI+CPL hold |
| `Examples/CFIFailMonoid.lean` | Section 10 | Ex 10.3: CFI fails, tower faithfulness+TD+CPL hold |
| `Examples/PeanoMonoid.lean` | Section 10 | Ex 10.4: CPL fails, tower faithfulness+TD+CFI hold |

### Dependency Chain

```
Basic.lean (tower faithfulness, TD, CFI, CPL, PP-P, APD definitions; towers_factorially_closed_implies_APD, APD_implies_TD, APD_implies_towers_factorially_closed; StrictDvd, WFD)
  |
  +-- APDRedundancy.lean (Prop 5.1: CFI + TD + WFD => APD)
  |
  +-- Utilities.lean
       +-- TowersFactoriallyClosed.lean (Section 5 helper lemmas)
            +-- LocalCounting.lean (Section 6: Theorem_Local_SB)
                 +-- CoprimeAssembly.lean (Section 7: prop_coprime_mult)
                      +-- FactorialStructure.lean (multiplicity rigidity -> factoriality; structural and counting consequences)
                           +-- MainTheorem.lean (Section 9: thm_main_TD)
```

## Necessity of Each Axiom

The paper (Section 10) constructs explicit counterexamples showing each axiom is necessary. All four are formalized in Lean and verified sorry-free:

| Axiom that fails | Monoid | Lean file | Key theorem |
|------------------|--------|-----------|-------------|
| **tower faithfulness** | Collapsing towers (p^2 = p^3) | `Examples/CollapsingMonoid.lean` | `collapsing_not_tower_faithful` |
| **TD** | Cross-atom identification (p₁² = p₂²) | `Examples/TDFailMonoid.lean` | `tdfail_not_TD` |
| **CFI** | Spurious coprime factorizations (pq = uv) | `Examples/CFIFailMonoid.lean` | `cfifail_not_CFI` |
| **CPL** | Peano monoid (single atom) | `Examples/PeanoMonoid.lean` | `peano_not_CPL` |

Each example also formally verifies that the other three axioms hold (e.g., `collapsing_TD`, `collapsing_CFI`, `collapsing_CPL` for the tower faithfulness counterexample).

## Building

Requires Lean 4 v4.24.0 and Mathlib.

```bash
lake exe cache get   # Get Mathlib cache (required before first build)
lake build           # Build the project
```

## Author

Eduardo Zambrano

## License

Apache 2.0

## Acknowledgments

Some proofs were completed with assistance from [Aristotle](https://harmonic.fun/) (Harmonic's AI theorem prover).
