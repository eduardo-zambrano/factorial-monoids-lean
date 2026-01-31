# Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Overview

This project formalizes a characterization of ordinary multiplication on natural numbers using only counting properties of labeled factorizations. The main theorem (Theorem 9.1) shows that a reduced atomic commutative monoid satisfying four simple axioms is factorial with infinitely many atoms, hence isomorphic to (N, x).

**Formalization Status:**
- Main theorems (Sections 5-9): Fully formalized with no sorries
- Axiom redundancy (Proposition 5.1): CFI + CPL + UAB implies APD, with 3 sorries related to extraction termination

## The Four Axioms (System B)

The formalization uses four independent axioms to characterize factorial monoids:

| Axiom | Name | Description |
|-------|------|-------------|
| **PP-D** | Prime-Powers-Distinct | For each atom p, the map e -> p^e is injective |
| **UAB** | Unique-Atomic-Base | If p^k = q^m (atoms p, q; k, m >= 1), then p = q |
| **CFI** | Coprime-Factor-Independence | Coprime parts factor independently (bijection condition) |
| **CPL** | Coprime-Products-at-every-Length | Pairwise coprime non-units exist in every length |

### Derived Property

| Property | Name | Description |
|----------|------|-------------|
| **APD** | Atom-Power-Divisibility | If atom q divides p^k (p an atom), then q = p |

**Proposition 5.1**: CFI + CPL + UAB implies APD.

We do *not* assume cancellativity. Instead, cancellativity is *derived* as a consequence of factorial structure (Corollary 8.4).

## Main Results

### Main Theorem (Theorem 9.1)

```lean
theorem thm_main {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

Under the four axioms, a reduced atomic commutative monoid M is factorial with infinitely many atoms, hence isomorphic to (N, x).

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
| Prop 5.1 | CFI + CPL + UAB => APD | `CFI_CPL_UAB_implies_APD` | 3 sorries* |
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
| **Thm 9.1** | **Main result: M isomorphic to (N, x)** | `thm_main` | Complete |
| **Additional Results** |
| -- | Atoms are prime under APD + CFI | `atoms_are_prime_APD` | Complete |
| -- | CPL implies atoms are infinite | `atoms_infinite_of_CPL` | Complete |
| -- | Factorial implies cancellative | `Factorial_implies_mul_left_cancel` | Complete |

### *Note on Proposition 5.1 (3 sorries)

The 3 sorries in `APD_Redundancy_v6.lean` all represent the same termination issue:

**Mathematical situation:** The proof extracts copies of an atom r from an element d, writing d = r^n × d' where d' = 1 or (r, d') coprime. This extraction terminates because atomic monoids have finite factorizations.

**Formalization gap:** Lean requires explicit well-founded measures for recursive definitions. Constructing such a measure without cancellativity (which we derive *after* proving APD) requires subtle machinery for factorization length in non-UFM monoids.

**Key point:** The mathematical argument is complete. The sorries are proof engineering gaps, not logical gaps. The paper's proof of Proposition 5.1 is valid; we simply haven't fully translated the termination argument into Lean's type theory.

## Logical Structure of the Proof

```
                              AXIOMS
                                |
        +----------+----------+----------+----------+
        |          |          |          |          |
      PP-D        UAB        CFI        CPL        |
        |          |          |          |          |
        |          +----+-----+----+-----+          |
        |               |          |                |
        |               v          |                |
        |   CFI_CPL_UAB_implies_APD|                |
        |        (Prop 5.1)*       |                |
        |               |          |                |
        |               v          |                |
        |              APD         |                |
        |               |          |                |
        |               v          |                |
        |       APD_implies_PPP    |                |
        |         (Prop 5.2)       |                |
        |               |          |                |
        |               v          |                |
        |             PP-P         |                |
        |               |          |                |
        +-------+-------+          |                |
                |                  |                |
                v                  |                |
        Lemma_PP_Unique            |                |
          (Lemma 6.1)              |                |
                |                  |                |
                v                  v                |
        Theorem_Local_SB   prop_coprime_mult        |
          (Thm 6.2)          (Prop 7.2)             |
                |                  |                |
                +--------+---------+                |
                         |                          |
                         v                          |
                    thm_master                      |
                     (Thm 8.2)                      |
                         |                          |
                         v                          |
                 prop_val_additive                  |
                   (Prop 8.3)                       |
                         |                          |
                         v                          |
                   cor_factorial                    |
                     (Cor 8.4)                      |
                         |                          |
                         +-------------+------------+
                                       |
                                       v
                                   thm_main
                                  (Thm 9.1)
                                 Factorial M
                                     AND
                             Set.Infinite (Atoms M)
```

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | Sections 2-3 | Core definitions, axioms (PP-D, UAB, CFI, CPL), APD definition, APD_implies_PPP |
| `APD_Redundancy_v6.lean` | Section 3 | Proves CFI + CPL + UAB => APD (with 3 sorries) |
| `Utilities.lean` | -- | Transfer lemmas, support properties |
| `LocalPurity.lean` | Section 5 | Helper lemmas for coprimality and blockwise CFI |
| `LocalCharacterization.lean` | Section 6 | Local stars-and-bars (Theorem 6.2) |
| `GlobalMultiplicativity.lean` | Section 7 | Coprime multiplicativity (Proposition 7.2) |
| `MasterFormula.lean` | Section 8 | Master formula, valuation additivity, factorial structure |
| `MainTheorem.lean` | Section 9 | Main theorem (Theorem 9.1) |

### Dependency Chain

```
Basic.lean (PP-D, UAB, CFI, CPL definitions; APD_implies_PPP)
  |
  +-- APD_Redundancy_v6.lean (CFI + CPL + UAB => APD)
  |
  +-- Utilities.lean
       +-- LocalPurity.lean (Section 5 helper lemmas)
            +-- LocalCharacterization.lean (Section 6: Theorem_Local_SB)
                 +-- GlobalMultiplicativity.lean (Section 7: prop_coprime_mult)
                      +-- MasterFormula.lean (Section 8: thm_master, cor_factorial)
                           +-- MainTheorem.lean (Section 9: thm_main)
```

## The Four Axioms Are Independent

The paper (Section 10) constructs explicit counterexamples showing each axiom is necessary:
- **Failure of PP-D only**: Collapsing prime-power towers (e.g., p^2 = p^3)
- **Failure of UAB only**: Distinct atoms with equal powers (e.g., p^2 = q^2)
- **Failure of CFI only**: Spurious coprime factorizations
- **Failure of CPL only**: Finite atom sets (e.g., Peano monoid)

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
