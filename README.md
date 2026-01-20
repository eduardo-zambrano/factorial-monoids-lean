# Lean 4 Formalization: Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Overview

This project proves Theorem 9.1 from the paper: under axioms PP-D (powers distinct), CFI (coprime parts factor independently), and CPL (coprime products exist at every level), a reduced atomic commutative monoid M is isomorphic to (ℕ, ×). The main result is `thm_main` in `MainTheorem.lean`.

## Logical Structure of the Proof

```
                                    AXIOMS
              ┌───────────────────────┼───────────────────────┐
              │                       │                       │
            PP-D                     CFI                     CPL
              │                       │                       │
              │     ┌─────────────────┼───────────────┐       │
              │     │                 │               │       │
              │     ▼                 │               ▼       │
              │   Prop_CFI_implies_PPP│       atoms_are_prime │
              │   (Prop 5.3)          │                       │
              │     │                 │               │       │
              │     ▼                 │               │       │
              │   PP-P                │               │       │
              │     │                 │               │       │
              └─────┴────────┬────────┴───────────────┘       │
                             │                                │
                             ▼                                │
                    prop_val_additive                         │
                    (Prop 8.3)                                │
                             │                                │
                             ▼                                ▼
                      cor_factorial              atoms_infinite_of_CPL
                      (Corollary 8.4)
                             │                                │
                             └───────────────┬────────────────┘
                                             │
                                             ▼
                                         thm_main
                                       (Theorem 9.1)
                                        M ≅ (ℕ, ×)
```

## Proof Structure in the Lean Files

### thm_main (Theorem 9.1)
**File:** `MainTheorem.lean:157`
**Statement:** Under PP-D, CFI, and CPL, M is factorial with infinitely many atoms, hence M ≅ (ℕ, ×).
**Proof uses:**
- `cor_factorial` for the factorial structure (part a)
- `atoms_infinite_of_CPL` for infinite atoms (part b)

### atoms_infinite_of_CPL
**File:** `MainTheorem.lean:120`
**Statement:** Under CPL, the atom set is infinite.
**Proof uses:**
- `exists_injective_atom_choice` to extract distinct atoms from coprime non-units
- `nodup_of_pairwise_coprime` to show coprime non-units have no duplicates
- Pigeonhole argument: n+1 coprime non-units require n+1 distinct atoms

### cor_factorial (Corollary 8.4)
**File:** `MasterFormula_v2_aristotle.lean:656`
**Statement:** Under PP-D and CFI, M is factorial.
**Proof uses:**
- `Prop_CFI_implies_PPP` to derive PP-P from CFI
- `atoms_are_prime` to show atoms satisfy the prime property
- Proves unique factorization by showing that if two multisets of atoms have the same product, they must be equal (via valuation counts)

### atoms_are_prime
**File:** `AtomsArePrime_v2_aristotle.lean:223`
**Statement:** Under CFI, atoms are prime: if p | a*b then p | a or p | b.
**Proof uses:**
- `atoms_are_prime_coprime` for the coprime case (uses CFI bijection directly)
- `atom_dvd_multiset_prod` to handle the general case via atomic factorizations
- `atom_dvd_power_eq_of_CFI` to show atoms dividing p^k must equal p

### prop_val_additive (Proposition 8.3)
**File:** `MasterFormula_v2_aristotle.lean:604`
**Statement:** v_p(x*y) = v_p(x) + v_p(y) for all atoms p.
**Proof uses:**
- `Prop_CFI_implies_PPP` and `atoms_are_prime`
- `lemma_valuation_spec` to characterize valuations
- CFI structure to show p cannot divide both p-free parts

### Prop_CFI_implies_PPP (Proposition 5.3)
**File:** `LocalPurity.lean:612`
**Statement:** CFI implies PP-P (prime powers are factorially closed).
**Proof uses:**
- Shows that if x*y divides p^e, any atom dividing x or y must equal p
- Uses divisibility chain and atomic factorizations

## File Dependency Chain

```
Basic.lean                        -- Definitions: Reduced, Atomic, CFI, PP-D, PP-P, CPL, F_k
  └─ Utilities.lean               -- Transfer lemmas, Disjoint_Support_implies_Coprime
       └─ AtomDvdPower.lean       -- atom_dvd_power_eq_of_CFI
            └─ LocalPurity.lean   -- Prop_CFI_implies_PPP (Prop 5.3)
                 └─ LocalCharacterization.lean
                      └─ GlobalMultiplicativity.lean
                           └─ AtomsArePrime_v2_aristotle.lean  -- atoms_are_prime
                                └─ MasterFormula_v2_aristotle.lean  -- cor_factorial (Cor 8.4)
                                     └─ MainTheorem.lean  -- thm_main (Thm 9.1)
```

## Proven Results

| Lean Name | Paper Ref | Description |
|-----------|-----------|-------------|
| `thm_main` | Theorem 9.1 | PP-D + CFI + CPL implies M ≅ (ℕ, ×) |
| `atoms_infinite_of_CPL` | — | CPL implies infinitely many atoms |
| `cor_factorial` | Corollary 8.4 | PP-D + CFI implies M is factorial |
| `prop_val_additive` | Proposition 8.3 | Additivity of p-adic valuations |
| `Prop_CFI_implies_PPP` | Proposition 5.3 | CFI implies PP-P |
| `atoms_are_prime` | — | Atoms are prime under CFI |

## Building

Requires Lean 4 v4.24.0 and Mathlib.

```bash
lake exe cache get   # Get Mathlib cache
lake build           # Build the project
```

## Author

Eduardo Zambrano

## License

Apache 2.0

## Acknowledgments

Some proofs were completed with assistance from [Aristotle](https://harmonic.fun/) (Harmonic's AI theorem prover).
