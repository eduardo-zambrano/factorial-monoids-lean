# Lean 4 Formalization: Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

**All main theorems from the paper (§5–§9) are fully formalized with no sorries.**

## The Four Axioms (System B)

The formalization uses four independent axioms to characterize factorial monoids:

| Axiom | Name | Description |
|-------|------|-------------|
| **APD** | Atom-Power-Divisibility | If atom q divides p^k (p an atom), then q = p |
| **PP-D** | Prime-Powers-Distinct | For each atom p, the map e ↦ p^e is injective |
| **CFI** | Coprime-Factor-Independence | Coprime parts factor independently (bijection condition) |
| **CPL** | Coprime-Products-at-every-Length | Pairwise coprime non-units exist in every length |

**Key innovation**: We do *not* assume cancellativity. Instead, cancellativity is *derived* as a consequence of factorial structure (Corollary 8.4).

### Main Theorem (Theorem 9.1)

```lean
theorem thm_main {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

Under the four axioms, a reduced atomic commutative monoid M is factorial with infinitely many atoms, hence isomorphic to (ℕ, ×).

### Master Counting Formula (Theorem 8.2)

```lean
theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_apd : APD M) (h_ppd : PP_D M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1))
```

This establishes the explicit counting formula F_k(m) = ∏_p C(v_p(m)+k-1, k-1).

## Complete List of Formalized Results

| Paper Ref | Name | Lean Name | Status |
|-----------|------|-----------|--------|
| **§5 Local Purity** |
| Prop 5.1 | APD ⟹ PP-P | `APD_implies_PPP` | ✅ |
| **§6 Local Characterization** |
| Lemma 6.1 | Unique factorization in prime powers | `Lemma_PP_Unique` | ✅ |
| Thm 6.2 | Local stars-and-bars | `Theorem_Local_SB` | ✅ |
| **§7 Global Multiplicativity** |
| Lemma 7.1 | CFI extends to all k | (built into `prop_coprime_mult`) | ✅ |
| Prop 7.2 | Coprime multiplicativity | `prop_coprime_mult` | ✅ |
| Cor 7.3 | Squarefree diagnostic | `cor_squarefree` | ✅ |
| **§8 Master Formula** |
| Lemma 8.1 | Primewise decomposition | `lem_primewise` | ✅ |
| **Thm 8.2** | **Master counting formula** | `thm_master` | ✅ |
| Prop 8.3 | Valuation additivity | `prop_val_additive` | ✅ |
| Cor 8.4 | Factorial structure | `cor_factorial` | ✅ |
| **§9 Main Theorem** |
| **Thm 9.1** | **Main result: M ≅ (ℕ,×)** | `thm_main` | ✅ |
| **Additional results** |
| — | Atoms are prime under APD + CFI | `atoms_are_prime_APD` | ✅ |
| — | CPL implies atoms are infinite | `atoms_infinite_of_CPL` | ✅ |
| — | Factorial implies cancellative | `Factorial_implies_mul_left_cancel` | ✅ |

**Summary: All main theorems formalized (100%), no sorries**

The appendix lemmas (A.1, A.2) providing sufficient conditions for verifying CFI are not formalized, as they are outside the main proof chain.

## Logical Structure of the Proof

```
                              AXIOMS
    ┌────────────┬────────────┬────────────┬────────────┐
    │            │            │            │            │
   APD         PP-D         CFI          CPL
    │            │            │            │
    │            │            │            │
    ▼            │            │            │
APD_implies_PPP  │            │            │
 (Prop 5.1)      │            │            │
    │            │            │            │
    ▼            │            │            │
  PP-P           │            │            │
    │            │            │            │
    │   ┌────────┘            │            │
    │   │                     │            │
    │   │    ┌────────────────┘            │
    │   │    │                             │
    │   │    ▼                             │
    │   │  atoms_are_prime_APD             │
    │   │    │                             │
    ▼   ▼    ▼                             │
  Lemma_PP_Unique ◄──────────┐             │
  (Lemma 6.1)                │             │
    │                        │             │
    ▼                        │             │
  Theorem_Local_SB           │             │
  (Theorem 6.2)              │             │
    │                        │             │
    │                        │             │
    │   prop_coprime_mult ◄──┘             │
    │   (Prop 7.2)                         │
    │         │                            │
    └────┬────┘                            │
         │                                 │
         ▼                                 │
    prop_val_additive                      │
    (Prop 8.3)                             │
         │                                 │
         ▼                                 │
    cor_factorial                          │
    (Cor 8.4)                              │
         │                                 │
         │    ┌────────────────────────────┘
         │    │
         │    ▼
         │  atoms_infinite_of_CPL
         │    │
         └────┴────────┐
                       │
                       ▼
                   thm_main
                 (Theorem 9.1)
                  Factorial M
                      ∧
              Set.Infinite (Atoms M)
```

### Key Intermediate Results

1. **`APD_implies_PPP`** (Basic.lean): The axiom APD implies property PP-P (prime-power towers are factorially closed). This is the foundation for local analysis.

2. **`atoms_are_prime_APD`** (Basic.lean): Under APD and CFI, atoms satisfy the prime property: if p | a·b then p | a or p | b. This is crucial for proving valuation additivity.

3. **`atoms_infinite_of_CPL`** (MainTheorem.lean): CPL forces the atom set to be infinite by a pigeonhole argument on pairwise coprime non-units.

4. **`Factorial_implies_mul_left_cancel`** (Basic.lean): Factorial monoids are cancellative. Combined with `cor_factorial`, this shows cancellativity is a *consequence* of our axioms.

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | §2-3 | Core definitions, axioms, APD_implies_PPP, atoms_are_prime_APD |
| `Utilities.lean` | — | Transfer lemmas, support properties |
| `LocalPurity.lean` | §5 | Helper lemmas for coprimality and blockwise CFI |
| `LocalCharacterization.lean` | §6 | Local stars-and-bars (Theorem 6.2) |
| `GlobalMultiplicativity.lean` | §7 | Coprime multiplicativity (Proposition 7.2) |
| `MasterFormula.lean` | §8 | Master formula, valuation additivity, factorial structure |
| `MainTheorem.lean` | §9 | Main theorem (Theorem 9.1) |

### Dependency Chain

```
Basic.lean (APD_implies_PPP, atoms_are_prime_APD)
  └─ Utilities.lean
       └─ LocalPurity.lean (§5 helper lemmas)
            └─ LocalCharacterization.lean (§6: Theorem_Local_SB)
                 └─ GlobalMultiplicativity.lean (§7: prop_coprime_mult)
                      └─ MasterFormula.lean (§8: thm_master, cor_factorial)
                           └─ MainTheorem.lean (§9: thm_main)
```

## Technical Notes

### Why CommMonoid, Not CancelCommMonoid?

Previous versions of this formalization assumed `CancelCommMonoid` (cancellative commutative monoid). The current version (System B) uses only `CommMonoid` and takes APD and PP-D as explicit axioms.

**Advantage**: This makes the axiom system more transparent. Cancellativity is not an independent assumption but rather a *theorem*: factorial monoids are automatically cancellative, so we prove cancellativity rather than assume it.

**Relationship to cancellativity**: In a reduced cancellative atomic monoid:
- PP-D follows automatically (if p^a = p^b, cancellativity gives 1 = p^{b-a}, contradiction)
- APD can be derived from cancellativity + CFI (though this requires more work)

The System B approach with four explicit axioms is cleaner for formalization because it makes all assumptions explicit and derives all consequences.

### The Four Axioms Are Independent

The paper (§10) constructs explicit counterexamples showing each axiom is necessary:
- Failure of APD only: allows cross-prime divisibility
- Failure of PP-D only: collapsing prime-power towers
- Failure of CFI only: spurious coprime factorizations
- Failure of CPL only: finite atom sets (e.g., Peano monoid)

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
