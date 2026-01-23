# Why CFI Implies PP-P: The Independence Question

## The Question

When checking logical independence of the four properties (PP-D, CFI, CPL, PP-P), we need examples where each subset of three holds but the fourth fails.

Specifically: **Can we construct an example where PP-D + CFI + CPL hold but PP-P fails?**

## The Answer: No

After analyzing the paper's examples (7.1, 7.2, 7.3), we verified that **all three satisfy PP-P**:

| Example | Description | PP-P Status |
|---------|-------------|-------------|
| 7.1 | Saturating monoid | ✅ Holds (all elements are powers of the single atom p) |
| 7.2 | Quotient by uv ~ pq | ✅ Holds (powers of atoms remain factorially closed) |
| 7.3 | Peano monoid | ✅ Holds (the only atom is the successor, and its powers are closed) |

## The Fundamental Obstruction

The reason we cannot construct such an example is that **CFI actually implies PP-P** (in reduced atomic cancellative monoids). This is what Proposition 5.3 claims.

### Intuitive Argument

**Suppose PP-P fails:** There exist an atom p and elements x, y such that x · y = pᵉ but x ∉ ⟨p⟩ (x is not a power of p).

**Then:** Since x is not a power of p, by atomicity x has some atomic factor q ≠ p. So q | x | pᵉ, meaning q | pᵉ with q ≠ p.

**Now apply CFI:** Write pᵉ = q · m. If q and m are coprime, CFI gives a bijection:

```
F₂(q) × F₂(m) ≅ F₂(pᵉ)
```

The factorization (p, pᵉ⁻¹) ∈ F₂(pᵉ) must have a preimage. Since F₂(q) = {(1,q), (q,1)} for an atom q, analyzing the preimage forces either:

- q · (something) = p, which means q | p, so q = p (contradiction), or
- q | pᵉ⁻¹, reducing to a smaller exponent

**By induction on e**, we eventually reach q | p¹ = p, forcing q = p. Contradiction!

### The CFI Surjectivity Argument in Detail

Given q | pᵏ with q ≠ p (both atoms), write pᵏ = q · m.

**Case 1: q and m are coprime**

Apply CFI to (q, m):
```
F₂(q) × F₂(m) ≅ F₂(q · m) = F₂(pᵏ)
```

The factorization (p, pᵏ⁻¹) ∈ F₂(pᵏ) has a preimage ((a,b), (c,d)) where:
- a · b = q (so (a,b) ∈ {(1,q), (q,1)} since q is an atom)
- c · d = m
- a · c = p
- b · d = pᵏ⁻¹

If (a,b) = (q,1): Then q · c = p. Since p is irreducible and q is not a unit, c must be a unit, so c = 1 and q = p. Contradiction.

If (a,b) = (1,q): Then c = p and q · d = pᵏ⁻¹. This means q | pᵏ⁻¹.

**Induction:** By strong induction on k, we reduce to smaller exponents until reaching k = 1, where q | p forces q = p.

**Case 2: q | m**

Extract maximal q-power: pᵏ = qʲ · n where q ∤ n. Then qʲ and n are coprime, and we apply CFI to (qʲ, n).

## Implications for Independence

This means **PP-P is not independent of {PP-D, CFI, CPL}** — it's a consequence of CFI.

### The Actual Logical Structure

```
        AXIOMS (Independent)
    ┌────────┼────────┐
    │        │        │
  PP-D      CFI      CPL
    │        │        │
    │        ▼        │
    │      PP-P       │
    │   (derived)     │
    │        │        │
    └────────┼────────┘
             │
             ▼
         Factorial
          M ≅ (ℕ,×)
```

Instead of four independent axioms, we have:
- **Three independent axioms:** PP-D, CFI, CPL
- **One derived property:** PP-P (follows from CFI)

The examples 7.1, 7.2, 7.3 demonstrate independence of PP-D, CFI, and CPL from each other, but a fourth example showing PP-P independent from {PP-D, CFI, CPL} **cannot exist**.

## The Gap in Proposition 5.3

While CFI ⟹ PP-P is true, the paper's *proof* of Proposition 5.3 has a gap.

### The Problem

The proof applies "Blockwise CFI" (Lemma 5.2) to pairs like (pᵃ, pᵇ). However, these pairs are **not coprime** — the atom p divides both — so CFI doesn't directly apply to them.

### The Fix

The clean proof in `CFI_implies_PPP_clean.lean` avoids this by:

1. **Only applying CFI to genuinely coprime pairs** — specifically (qʲ, n) where q ∤ n
2. **Using strong induction on the exponent k** — base cases k = 0, 1, 2; inductive step for k ≥ 3
3. **Carefully extracting the maximal q-power** to ensure coprimality with the cofactor

### Proof Structure

```
atom_dvd_power_eq_of_CFI_PPD: q | pᵏ ⟹ q = p

Strong induction on k:
├── k = 0: q | 1 means q is a unit. Contradiction.
├── k = 1: q | p with both atoms implies q = p directly.
├── k = 2: Base case using PP-D. (atom_dvd_sq_eq')
└── k ≥ 3: Write pᵏ = q · m.
    ├── If q ∤ m: Apply CFI to (q, m), trace preimage, get q | pᵏ⁻¹, use IH.
    └── If q | m: Extract more q's until coprime, then apply CFI.
```

## Summary

| Question | Answer |
|----------|--------|
| Can PP-D + CFI + CPL hold while PP-P fails? | **No** |
| Why? | CFI implies PP-P via the surjectivity argument |
| Is the paper's proof correct? | The result is correct, but the proof has a gap |
| What's the gap? | Applying Blockwise CFI to non-coprime pairs (pᵃ, pᵇ) |
| How to fix? | Use strong induction, only apply CFI to coprime pairs |

## References

- Paper: "Characterizing Factorial Monoids via Labeled Factorization Counts" by Eduardo Zambrano
- Lean formalization: `CFI_implies_PPP_clean.lean`
- Main theorem: `CFI_PPD_implies_PPP`
