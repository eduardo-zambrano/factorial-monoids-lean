# Lean 4 Formalization: Factorial Monoids via Labeled Factorization Counts

A Lean 4 formalization of the paper "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano.

## Formalization Status: COMPLETE

**All main theorems from the paper (§5–§9) are fully formalized with no sorries.**

### Main Theorem (Theorem 9.1)

```lean
theorem thm_main {M : Type*} [CancelCommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) (h_cpl : CPL M) :
    Factorial M ∧ Set.Infinite (Atoms M)
```

Under axioms PP-D (powers distinct), CFI (coprime parts factor independently), and CPL (coprime products exist at every level), a reduced atomic cancellative commutative monoid M is factorial with infinitely many atoms, hence isomorphic to (ℕ, ×).

### Master Counting Formula (Theorem 8.2)

```lean
theorem thm_master {M : Type*} [CancelCommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
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
| Prop 5.3 | CFI ⟹ PP-P | `Prop_CFI_implies_PPP` | ✅ |
| **§6 Local Characterization** |
| Lemma 6.1 | Unique factorization in prime powers | `Lemma_PP_Unique` | ✅ |
| Thm 6.2 | Local stars-and-bars | `Theorem_Local_SB` | ✅ |
| **§7 Global Multiplicativity** |
| Lemma 7.1 | CFI extends to all k | `splitFactorization` | ✅ |
| Prop 7.2 | Coprime multiplicativity | `prop_coprime_mult` | ✅ |
| Cor 7.3 | Squarefree diagnostic | `cor_squarefree` | ✅ |
| **§8 Master Formula** |
| Lemma 8.1 | Primewise decomposition | `lem_primewise` | ✅ |
| **Thm 8.2** | **Master counting formula** | `thm_master` | ✅ |
| Prop 8.3 | Valuation additivity | `prop_val_additive` | ✅ |
| Cor 8.4 | Factorial structure | `cor_factorial` | ✅ |
| **§9 Main Theorem** |
| **Thm 9.1** | **Main result: M ≅ (ℕ,×)** | `thm_main` | ✅ |
| — | Atoms infinite under CPL | `atoms_infinite_of_CPL` | ✅ |
| — | Atoms are prime under CFI | `atoms_are_prime` | ✅ |

**Summary: 11/11 main theorems formalized (100%)**

The appendix lemmas (A.1, A.2) providing sufficient conditions for verifying CFI are not formalized, as they are outside the main proof chain.

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

## File Structure

| File | Paper Section | Description |
|------|---------------|-------------|
| `Basic.lean` | §2-3 | Core definitions and axioms |
| `Utilities.lean` | — | Transfer lemmas for monoid isomorphisms |
| `AtomDvdPower.lean` | §5 | Key lemma: atom dividing p^k equals p |
| `LocalPurity.lean` | §5 | CFI implies PP-P (Proposition 5.3) |
| `LocalCharacterization.lean` | §6 | Local stars-and-bars (Theorem 6.2) |
| `GlobalMultiplicativity.lean` | §7 | Coprime multiplicativity (Proposition 7.2) |
| `AtomsArePrime.lean` | §8 | Atoms are prime under CFI |
| `MasterFormula.lean` | §8 | Master formula and factorial structure |
| `MainTheorem.lean` | §9 | Main theorem (Theorem 9.1) |
| `CFI_implies_PPP_clean.lean` | §5 | Alternative proof (not used by main chain) |

### Dependency Chain

```
Basic.lean
  └─ Utilities.lean
       └─ AtomDvdPower.lean
            └─ LocalPurity.lean (§5: Prop_CFI_implies_PPP)
                 ├─ LocalCharacterization.lean (§6)
                 │    └─ GlobalMultiplicativity.lean (§7)
                 │         └─ MasterFormula.lean (§8)
                 │              └─ MainTheorem.lean (§9: thm_main)
                 └─ AtomsArePrime.lean
                      └─ MasterFormula.lean
```

## Technical Notes

### Cancellativity Assumption

The formalization uses `CancelCommMonoid` (cancellative commutative monoid) rather than just `CommMonoid`. This assumption is mathematically harmless: factorial monoids are automatically cancellative, so we assume something weaker than what we prove. The assumption simplifies several intermediate proofs that require cancellation before factoriality is established.

### Alternative Proof Files

`CFI_implies_PPP_clean.lean` provides an alternative direct proof that CFI + PP-D implies PP-P using strong induction. This file is not part of the main proof chain and contains 2 sorries representing ongoing work on a cleaner approach. These do not affect the main theorems.

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
