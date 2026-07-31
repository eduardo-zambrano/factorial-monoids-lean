# Factorial Monoids and (ℕ, ×): An Axiomatic Characterization — Lean 4 Formalization

This repository contains a complete, sorry-free Lean 4 formalization of the paper

> Eduardo Zambrano, *Factorial Monoids and (ℕ, ×): An Axiomatic Characterization*, under review at Semigroup Forum.

Every numbered statement of the paper — the main theorem in all of its forms, every lemma and proposition on the way to it, and all five independence counterexamples — is machine-checked here. The paper annotates each statement with the name of its Lean counterpart, and the correspondence tables below reproduce that mapping.

**Interactive proof map:** the complete dependency structure of the main theorem — every statement, every "is used in the proof of" arrow, and every Lean identifier — can be explored at

> **<https://eduardo-zambrano.github.io/factorial-monoids-lean/>**

Hover over a node to highlight its proof ancestry; click to pin the highlight. The same map appears as Figure 1 of the paper. Its source is [`docs/index.html`](docs/index.html).

---

## The main theorem

Let (M, ·, 1) be a **reduced commutative monoid** (the only unit is 1). Nothing else is assumed — not atomicity, not cancellativity, and atoms are not assumed prime; all of these are *derived*. Write P for the set of atoms of M.

**Theorem 4.1.** For a reduced commutative monoid M:

> M is factorial ⟺ M satisfies (WFD), (TD), and (CFI).

With the cardinality condition (CCA) included, the following are equivalent:

- **(A)** M satisfies (WFD), (TD), (CFI), and (CCA);
- **(B)** M is factorial and P is countably infinite;
- **(C)** M ≅ (ℕ, ×).

| Equivalence | Lean theorem |
|---|---|
| factorial ⟺ WFD + TD + CFI | `thm_structural_characterization` |
| (A) ⟺ (B) | `thm_A_iff_B` |
| (B) ⟺ (C) | `thm_B_iff_C` |
| (A) ⟺ (C) | `thm_A_iff_C` |
| (A) ⟹ (B) assembly | `thm_A_implies_B` |

All are proved over reducedness alone, with no countability assumption on M. An axiom audit (`#print axioms`) reports that each of these theorems — and `cor_factorial`, `cancellative_of_structural`, `factorialCoordinateEquiv` — depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## The four axioms

| Axiom | Name | Content | Lean |
|-------|------|---------|------|
| **(WFD)** | Well-Founded Divisibility | Strict (cofactor-witnessed) divisibility is well-founded. Equivalent to unit-cancellativity plus the principal-ideal chain condition (paper Remark 3.2) | `WFD` |
| **(TD)** | Tower Disjointness | If p^k = q^m for atoms p, q and k, m ≥ 1, then p = q: the positive-power towers of distinct atoms are disjoint | `TD` |
| **(CFI)** | Coprime Factorization Independence | For coprime x, y the assembly map μ₂ : 𝓕₂(x) × 𝓕₂(y) → 𝓕₂(xy), ((x₁,x₂),(y₁,y₂)) ↦ (x₁y₁, x₂y₂), is a bijection | `CFI` |
| **(CCA)** | Coprime Coverage of the Atoms | There is a sequence of pairwise coprime non-units whose supports cover every atom | `CCA` |

Here 𝓕ₖ(m) is the set of ordered k-tuples with product m (slots may be 1), coprimality means no common atom divisor, and the support of m is the set of atoms dividing m. (CPL), the weak form of (CCA) requiring pairwise coprime tuples of every finite length, is defined in the paper's Section 9 and named `CPL` in Lean.

## The derived structure

The proof is *multiplicity-first*: the structural axioms make the atom-wise multiplicity of every element intrinsic, and factoriality falls out immediately; the familiar valuation calculus is then a set of corollaries, not scaffolding. In paper order:

| Paper | Statement | Lean |
|-------|-----------|------|
| Prop 3.4 | (WFD) implies atomicity | `Atomic_of_WFD` |
| Prop 3.6 | (WFD) implies tower faithfulness (e ↦ p^e injective) | `WFD_implies_tower_faithful` |
| Rem 3.3 | (CFI) extends to all k: μₖ bijective | `CFI_bijective_all_k` |
| Lem 5.1 | Maximal extraction x = s^m·c with s ∤ c | `maximal_atom_power_extraction` |
| Prop 5.2 | (CFI) + (TD) + (WFD) imply (APD): an atom dividing p^k equals p | `CFI_TD_implies_APD` |
| Cor 5.3 | The towers ⟨p⟩ are factorially closed | `APD_implies_towers_factorially_closed` |
| Prop 6.1 | Atoms are prime (Euclid's lemma, without cancellativity) | `atoms_are_prime_coprime`, `atoms_are_prime_APD` |
| Lem 7.1 | Power cancellation: p^(k+1) ∣ p^k·u ⟹ p ∣ u | `atom_dvd_cancel` |
| Def 7.2 | Valuation v_p(m) = max{e : p^e ∣ m} | `PValuation` |
| Lem 7.3 | Multiplicity rigidity: v_p equals the multiplicity of p in *every* atomic factorization | `lemma_valuation_spec`, `multiplicity_rigidity` |
| **Cor 7.4** | **Factoriality** | `cor_factorial` |
| Prop 7.5 | Valuation additivity | `prop_val_additive` |
| Lem 7.6 | Primewise decomposition; exact finite support | `lem_primewise_full`, `support_finite` |
| Cor 7.7 | Free coordinates Φ : ⊕_{p∈P} ℕ₀ ≅ M, and cancellativity | `factorialCoordinateEquiv`, `factorialCoordinateEquiv_apply`, `cancellative_of_structural` |
| §8 lower bound | (CCA) + atomicity ⟹ atom set infinite | `atoms_infinite_of_CCA` |
| §8 upper bound | (CCA) + finite supports ⟹ atom set countable | `atoms_countable_of_CCA` |

The converse direction splits hypothesis (B) by role: factoriality alone recovers the three structural axioms (`WFD_of_factorial`, `TD_of_factorial`, `CFI_of_factorial`, and also `tower_faithful_of_factorial`), while countable infinitude of the atom set alone supplies (CCA) (`CCA_of_atoms_countably_infinite`). Part (C) transports canonical atomic multisets along an atom bijection (`factorialMulEquiv`), with (ℕ, ×) represented as the positive naturals and certified in `Examples/NatMonoid.lean`.

## Sharpness: the axioms are independent

Each axiom fails in a reduced commutative monoid satisfying the other three — with two distinct failure modes for (CCA):

| Paper | Monoid | Fails | File | Key verdicts |
|-------|--------|-------|------|--------------|
| Ex 9.1 | ⟨p₁, p₂, … ∣ p₁² = p₁³⟩ (a collapsing tower) | (WFD) only | `Examples/CollapsingMonoid.lean` | `collapsing_not_WFD`, `collapsing_not_factorial` — atomic yet not factorial |
| Ex 9.2 | ⟨p₁, p₂, … ∣ p₁² = p₂²⟩ (colliding towers) | (TD) only | `Examples/TDFailMonoid.lean` | `tdfail_not_TD` |
| Ex 9.3 | ℕ/(uv ∼ pq) (a coprime exchange) | (CFI) only | `Examples/CFIFailMonoid.lean` | `cfifail_not_CFI` |
| Ex 9.4 | Peano monoid (ℕ, x⋆y = x+y−1): one atom | (CCA) only — too few coprimes; even (CPL) fails | `Examples/PeanoMonoid.lean` | `peano_not_CPL`, `peano_not_CCA` |
| Ex 9.5 | ⊕_ℝ ℕ₀: continuum-many atoms | (CCA) only — too many atoms; (CPL) holds | `Examples/UncountableFreeMonoid.lean` | `R_not_CCA`, `R_cpl` |

Each example file also verifies the base assumption and every *holding* axiom, so the independence claims are machine-checked in both directions. Example 9.5 shows that replacing (CCA) by its weak form (CPL) would make the main theorem false.

## File guide (MultiplicationProject/)

| File | Contents |
|------|----------|
| `Basic.lean` | Core definitions: `WFD`, `TD`, `CFI`, `CCA`, `CPL`, `TowerFaithful`, `TowersFactoriallyClosed`, `APD`, `Atoms`, `Support`, `AreCoprime`, factorization sets; first consequences of (WFD); atoms-are-prime lemmas; the equivalence ladder TD ⟺ APD ⟺ factorially closed towers |
| `APDRedundancy.lean` | Maximal extraction (Lem 5.1) and the well-founded induction proving (APD) (Prop 5.2) |
| `Utilities.lean` | Transfer lemmas and support properties |
| `Coprimality.lean` | Coprimality helper lemmas |
| `LocalCounting.lean` | `pp_unique` (in-tower uniqueness, used by Lem 7.1) and local stars-and-bars counting |
| `CoprimeAssembly.lean` | `CFI_bijective_all_k` (Rem 3.3) and coprime count multiplicativity |
| `FactorialStructure.lean` | The Section 7 chain: power cancellation, valuations, multiplicity rigidity, `cor_factorial`, additivity, primewise decomposition, finite support |
| `MainTheorem.lean` | Cardinality bounds from (CCA); `thm_A_implies_B`; `thm_structural_characterization`; `thm_A_iff_B` |
| `AxiomsNecessity.lean` | The converse: canonical atomic multisets (`factorMS`) and the four `*_of_factorial` theorems; `CCA_of_atoms_countably_infinite` |
| `Isomorphism.lean` | Classification of reduced factorial monoids by atom rank (`factorialMulEquiv`); `thm_B_iff_C`; `thm_A_iff_C`; the explicit coordinate isomorphism `factorialCoordinateEquiv` |
| `Examples/` | The five sharpness examples and the (ℕ, ×) witness (`NatMonoid.lean`, via ℕ+) |

A few counting-theoretic results beyond the paper's needs (`thm_master`, `Theorem_Local_SB`, `cor_squarefree`) are retained in the development; their docstrings carry pre-revision numbering.

## Building

Requires Lean 4 (v4.24.0, pinned in `lean-toolchain`) and Mathlib (commit pinned in `lakefile.lean`).

```bash
lake exe cache get   # fetch Mathlib cache (strongly recommended)
lake build           # builds the entire development
```

The build is the verification: the development contains no `sorry`, and `maxHeartbeats` is raised only to accommodate long-running tactics, never to mask failures.

## Nomenclature note

Lean identifiers follow the revised paper's nomenclature. The initial public version of this repository used the pre-revision names; the mapping is: `ACCP` → `WFD`, `UAB` → `TD`, `CPL_plus` → `CCA`, `PP_D` → `TowerFaithful`, `PP_P` → `TowersFactoriallyClosed`.

## Citation

If you use this formalization, please cite the paper (bibliographic details will be updated upon publication). Zenodo DOIs for the formalization and for the interactive proof map are forthcoming.

## License

Apache 2.0 — see [LICENSE](LICENSE).
