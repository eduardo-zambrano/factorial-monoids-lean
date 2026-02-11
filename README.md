# Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Overview

This project formalizes a characterization of ordinary multiplication on natural numbers using only counting properties of labeled factorizations. The main theorem (Theorem 9.1) shows that a reduced atomic commutative monoid satisfying ACCP and four simple axioms is factorial with infinitely many atoms, hence isomorphic to (N, x).

## Base Assumptions

Throughout, (M, ·, 1) is a monoid satisfying the following base assumptions:

| Base Assumption | Description |
|-----------------|-------------|
| **Commutative** | The monoid operation is commutative (a · b = b · a) |
| **Reduced** | The only unit is the identity element |
| **Atomic** | Every non-unit can be written as a finite product of atoms |
| **ACCP** | Ascending chain condition on principal ideals: there is no infinite sequence m₁, m₂, … in M such that each mᵢ₊₁ strictly divides mᵢ |

We do *not* assume cancellativity. Instead, cancellativity is *derived* as a consequence of factorial structure (Corollary 8.4).

## The Four Axioms

The paper characterizes factorial monoids using four axioms on top of the base assumptions:

| Axiom | Name | Description |
|-------|------|-------------|
| **PP-D** | Prime-Powers-Distinct | For each atom p, p^a = p^b implies a = b |
| **UAB** | Unique-Atomic-Base | If p^k = q^m (atoms p, q; k, m >= 1), then p = q |
| **CFI** | Coprime-Factor-Independence | Coprime parts factor independently (bijection condition) |
| **CPL** | Coprime-Products-at-every-Length | Pairwise coprime non-units exist in every length |

### Derived Properties

| Property | Name | Description |
|----------|------|-------------|
| **APD** | Atom-Power-Divisibility | If atom q divides p^k (p an atom), then q = p |
| **PP-P** | Prime-Powers-Pure | Prime-power submonoid ⟨p⟩ is factorially closed |

**Key equivalences**: PP-P ⟺ APD ⟺ UAB (given CFI + ACCP). Specifically: PP-P ⟹ APD (`PPP_implies_APD`), APD ⟹ UAB (`APD_implies_UAB`), APD ⟹ PP-P (`APD_implies_PPP`), and CFI + UAB + ACCP ⟹ APD (`CFI_UAB_implies_APD`).

## Main Results

### Main Theorem (Theorem 9.1)

The main theorem matches the paper's axiom set {PP-D, UAB, CFI, CPL} with ACCP as a base assumption:

```lean
theorem thm_main_UAB {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_uab : UAB M) (h_cfi : CFI M) (h_cpl : CPL M)
    (h_accp : ACCP M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

This chains through Proposition 5.1 (`CFI_UAB_implies_APD`) to derive APD from CFI + UAB + ACCP, then feeds into the main proof. The code also contains an internal variant `thm_main_PPP` that takes the derived property PP-P directly; this is a stepping stone in the proof chain, not a separate axiom system.

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
| Prop 5.1 | CFI + UAB + ACCP => APD | `CFI_UAB_implies_APD` | Complete |
| Prop 5.2 | APD => PP-P | `APD_implies_PPP` | Complete |
| -- | PP-P => APD | `PPP_implies_APD` | Complete |
| -- | APD => UAB | `APD_implies_UAB` | Complete |
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
| **Thm 9.1** | **Main result: M isomorphic to (N, x)** | `thm_main_UAB` | Complete |
| **Additional Results** |
| -- | Atoms are prime under APD + CFI | `atoms_are_prime_APD` | Complete |
| -- | CPL implies atoms are infinite | `atoms_infinite_of_CPL` | Complete |
| -- | Factorial implies cancellative | `Factorial_implies_mul_left_cancel` | Complete |

### Note on Proposition 5.1

`APD_Redundancy_v6.lean` proves Proposition 5.1 from the paper: CFI + UAB + ACCP ⟹ APD. The proof uses well-founded induction on elements (via ACCP).

ACCP (Ascending Chain Condition on Principal ideals) provides well-foundedness of strict divisibility. It is a standard condition in commutative algebra, strictly between "atomic" and "UFD." In cancellative monoids, ACCP follows from atomicity; in the non-cancellative setting, it is an additional assumption. In the paper, ACCP is a base assumption on the monoid.

## Logical Structure of the Proof

```
  PP-D  UAB                 CFI      CPL
    |    |                   |        |
    |    +                   |        |
    |    |                   |        |
    | CFI_UAB_implies_APD    |        |
    |    |  (Prop 5.1)       |        |
    |    v                   |        |
    |   APD                  |        |
    |    |                   |        |
    |    v                   |        |
    | APD_implies_PPP        |        |
    |  (Prop 5.2)            |        |
    |    |                   |        |
    |    v                   |        |
    |  PP-P                  |        |
    |    |                   |        |
    |    v                   |        |
    +----+                   |        |
         |                   |        |
         v                   v        |
  Lemma_PP_Unique  prop_coprime_mult  |
    (Lemma 6.1)      (Prop 7.2)       |
         |                |           |
         +-------+--------+           |
                 |                    |
                 v                    |
            thm_master (Thm 8.2)      |
                 |                    |
                 v                    |
         prop_val_additive (Prop 8.3) |
                 |                    |
                 v                    |
           cor_factorial (Cor 8.4)    |
                 |                    |
                 +--------------------+
                 |
                 v
          thm_main_UAB (Thm 9.1)
          Factorial M ∧ Set.Infinite (Atoms M)
```

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | Sections 2-3 | Core definitions (PP-D, UAB, CFI, CPL, PP-P, APD), PPP_implies_APD, APD_implies_UAB, APD_implies_PPP, StrictDvd, ACCP |
| `APD_Redundancy_v6.lean` | Section 5 | CFI + UAB + ACCP => APD (Prop 5.1) |
| `Utilities.lean` | -- | Transfer lemmas, support properties |
| `LocalPurity.lean` | Section 5 | Helper lemmas for coprimality and blockwise CFI |
| `LocalCharacterization.lean` | Section 6 | Local stars-and-bars (Theorem 6.2) |
| `GlobalMultiplicativity.lean` | Section 7 | Coprime multiplicativity (Proposition 7.2) |
| `MasterFormula.lean` | Section 8 | Master formula, valuation additivity, factorial structure |
| `MainTheorem.lean` | Section 9 | Main theorem (Theorem 9.1): `thm_main_UAB` |

### Dependency Chain

```
Basic.lean (PP-D, UAB, CFI, CPL, PP-P, APD definitions; PPP_implies_APD, APD_implies_UAB, APD_implies_PPP; StrictDvd, ACCP)
  |
  +-- APD_Redundancy_v6.lean (Prop 5.1: CFI + UAB + ACCP => APD)
  |
  +-- Utilities.lean
       +-- LocalPurity.lean (Section 5 helper lemmas)
            +-- LocalCharacterization.lean (Section 6: Theorem_Local_SB)
                 +-- GlobalMultiplicativity.lean (Section 7: prop_coprime_mult)
                      +-- MasterFormula.lean (Section 8: thm_master, cor_factorial)
                           +-- MainTheorem.lean (Section 9: thm_main_UAB)
```

## Necessity of Each Axiom

The paper (Section 10) constructs explicit counterexamples showing each axiom is necessary. Each example satisfies ACCP:
- **Failure of PP-D only**: Collapsing prime-power towers (e.g., p^2 = p^3)
- **Failure of UAB only**: Distinct atoms with equal powers (e.g., p^2 = q^2)
- **Failure of CFI only**: Spurious coprime factorizations
- **Failure of CPL only**: Finite atom sets (e.g., Peano monoid)

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
