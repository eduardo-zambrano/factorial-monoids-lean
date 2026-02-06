# Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Overview

This project formalizes a characterization of ordinary multiplication on natural numbers using only counting properties of labeled factorizations. The main theorem (Theorem 9.1) shows that a reduced atomic commutative monoid satisfying four simple axioms is factorial with infinitely many atoms, hence isomorphic to (N, x).

## The Four Axioms

The formalization uses four axioms to characterize factorial monoids:

| Axiom | Name | Description |
|-------|------|-------------|
| **PP-D** | Prime-Powers-Distinct | For each atom p, p^a = p^b implies a = b |
| **PP-P** | Prime-Powers-Pure | Prime-power submonoid ⟨p⟩ is factorially closed |
| **CFI** | Coprime-Factor-Independence | Coprime parts factor independently (bijection condition) |
| **CPL** | Coprime-Products-at-every-Length | Pairwise coprime non-units exist in every length |

### Derived Properties

| Property | Name | Description |
|----------|------|-------------|
| **APD** | Atom-Power-Divisibility | If atom q divides p^k (p an atom), then q = p |
| **UAB** | Unique-Atomic-Base | If p^k = q^m (atoms p, q; k, m >= 1), then p = q |

**Key implications**: PP-P ⟹ APD (`PPP_implies_APD`), APD ⟹ UAB (`APD_implies_UAB`), and APD ⟹ PP-P (`APD_implies_PPP`).

We were not able to prove that the four axioms are logically independent (CFI may imply PP-P). The main theorem chain is sorry-free.

We do *not* assume cancellativity. Instead, cancellativity is *derived* as a consequence of factorial structure (Corollary 8.4).

## Main Results

### Main Theorem (Theorem 9.1)

```lean
theorem thm_main_PPP {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppp : PP_P M) (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

Under the four axioms {PP-D, PP-P, CFI, CPL}, a reduced atomic commutative monoid M is factorial with infinitely many atoms, hence isomorphic to (N, x). The entire proof chain is sorry-free.

### Master Counting Formula (Theorem 8.2)

```lean
theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_ppd : PP_D M) (h_cfi : CFI M)
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
| -- | PP-P => APD | `PPP_implies_APD` | Complete |
| -- | APD => UAB | `APD_implies_UAB` | Complete |
| Prop 5.1 | CFI + CPL + UAB + ACCP => APD | `CFI_CPL_UAB_implies_APD` | Complete (supplementary, uses ACCP) |
| Prop 5.2 | APD => PP-P | `APD_implies_PPP` | Complete |
| **Section 6: Local Characterization** |
| Lemma 6.1 | Unique factorization in prime powers | `Lemma_PP_Unique` | Complete |
| Thm 6.2 | Local stars-and-bars | `Theorem_Local_SB` | Complete |
| **Section 7: Global Multiplicativity** |
| Lemma 7.1 | CFI extends to all k | (built into `prop_coprime_mult`) | Complete |
| Prop 7.2 | Coprime multiplicativity | `prop_coprime_mult` | Complete |
| Cor 7.3 | Squarefree diagnostic | `cor_squarefree` | Complete |
| **Section 8: Master Formula** |
| Lemma 8.1 | Primewise decomposition | `lem_primewise` | Complete |
| **Thm 8.2** | **Master counting formula** | `thm_master` | Complete |
| Prop 8.3 | Valuation additivity | `prop_val_additive` | Complete |
| Cor 8.4 | Factorial structure | `cor_factorial` | Complete |
| **Section 9: Main Theorem** |
| **Thm 9.1** | **Main result: M isomorphic to (N, x)** | `thm_main` / `thm_main_PPP` | Complete |
| **Additional Results** |
| -- | Atoms are prime under APD + CFI | `atoms_are_prime_APD` | Complete |
| -- | CPL implies atoms are infinite | `atoms_infinite_of_CPL` | Complete |
| -- | Factorial implies cancellative | `Factorial_implies_mul_left_cancel` | Complete |

### Note on Proposition 5.1 (Supplementary)

`APD_Redundancy_v6.lean` is a **supplementary** file proving APD from the alternative axiom system {PP-D, UAB, CFI, CPL} plus ACCP (Ascending Chain Condition on Principal ideals — well-foundedness of strict divisibility). ACCP is a standard condition in commutative algebra, strictly between "atomic" and "UFD." In cancellative monoids, ACCP follows from atomicity; in the non-cancellative setting, it is an additional assumption.

The main theorem chain uses {PP-D, PP-P, CFI, CPL} and is **sorry-free**: PP-P ⟹ APD is proven directly in `PPP_implies_APD` (Basic.lean), and all downstream results follow without any sorry. The entire formalization is sorry-free.

## Logical Structure of the Proof

```
                              AXIOMS
                                |
        +----------+----------+----------+
        |          |          |          |
      PP-D       PP-P        CFI        CPL
        |          |          |          |
        |          v          |          |
        |    PPP_implies_APD  |          |
        |          |          |          |
        |          v          |          |
        |         APD---------+          |
        |          |          |          |
        |          v          |          |
        |   APD_implies_PPP   |          |
        |     (Prop 5.2)      |          |
        |          |          |          |
        |          v          |          |
        |        PP-P         |          |
        |          |          |          |
        +----+-----+         |          |
             |                |          |
             v                |          |
      Lemma_PP_Unique         |          |
        (Lemma 6.1)           |          |
             |                |          |
             v                v          |
      Theorem_Local_SB  prop_coprime_mult|
        (Thm 6.2)         (Prop 7.2)    |
             |                |          |
             +-------+--------+          |
                     |                   |
                     v                   |
                thm_master               |
                 (Thm 8.2)               |
                     |                   |
                     v                   |
             prop_val_additive           |
               (Prop 8.3)               |
                     |                   |
                     v                   |
               cor_factorial             |
                 (Cor 8.4)               |
                     |                   |
                     +--------+----------+
                              |
                              v
                        thm_main_PPP
                          (Thm 9.1)
                         Factorial M
                             AND
                    Set.Infinite (Atoms M)
```

The entire chain from {PP-D, PP-P, CFI, CPL} to the conclusion is sorry-free.

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | Sections 2-3 | Core definitions, axioms (PP-D, PP-P, CFI, CPL), PPP_implies_APD, APD_implies_UAB, APD_implies_PPP, StrictDvd, ACCP |
| `APD_Redundancy_v6.lean` | Section 5 | CFI + CPL + UAB + ACCP => APD (supplementary) |
| `Utilities.lean` | -- | Transfer lemmas, support properties |
| `LocalPurity.lean` | Section 5 | Helper lemmas for coprimality and blockwise CFI |
| `LocalCharacterization.lean` | Section 6 | Local stars-and-bars (Theorem 6.2) |
| `GlobalMultiplicativity.lean` | Section 7 | Coprime multiplicativity (Proposition 7.2) |
| `MasterFormula.lean` | Section 8 | Master formula, valuation additivity, factorial structure |
| `MainTheorem.lean` | Section 9 | Main theorem (Theorem 9.1) |

### Dependency Chain

```
Basic.lean (PP-D, PP-P, CFI, CPL definitions; PPP_implies_APD, APD_implies_UAB, APD_implies_PPP; StrictDvd, ACCP)
  |
  +-- APD_Redundancy_v6.lean (supplementary: CFI + CPL + UAB + ACCP => APD)
  |
  +-- Utilities.lean
       +-- LocalPurity.lean (Section 5 helper lemmas)
            +-- LocalCharacterization.lean (Section 6: Theorem_Local_SB)
                 +-- GlobalMultiplicativity.lean (Section 7: prop_coprime_mult)
                      +-- MasterFormula.lean (Section 8: thm_master, cor_factorial)
                           +-- MainTheorem.lean (Section 9: thm_main, thm_main_PPP)
```

## Necessity of Each Axiom

The paper (Section 10) constructs explicit counterexamples showing each axiom is necessary:
- **Failure of PP-D only**: Collapsing prime-power towers (e.g., p^2 = p^3)
- **Failure of PP-P only**: Distinct atoms with equal powers (e.g., p^2 = q^2)
- **Failure of CFI only**: Spurious coprime factorizations
- **Failure of CPL only**: Finite atom sets (e.g., Peano monoid)

We were not able to prove that the four axioms are logically independent (CFI may imply PP-P).

These counterexamples are not formalized in this repository (they are on a separate branch `section-10-examples`).

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
