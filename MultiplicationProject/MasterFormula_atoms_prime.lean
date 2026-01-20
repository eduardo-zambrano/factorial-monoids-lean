/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bebff1c6-4ffc-4e3f-85fd-21c64bc889e6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (h_atomic : Atomic M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : ∀ x y : M, AreCoprime x y → Function.Bijective (Function.uncurry (labeledFactorizationMul (k

- theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1))

- theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) :
    Factorial M

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 8: Master Formula and Structural Consequences

This file contains:
- Helper lemmas for the master formula (from Aristotle)
- Placeholders for the main Section 8 results (still in progress)

Main results (when complete):
- `lem_primewise`: Primewise decomposition m = ∏ p^{v_p(m)} (Lemma 8.1)
- `thm_master`: Master formula F_k(m) = ∏ C(v_p(m)+k-1, k-1) (Theorem 8.2)
- `prop_val_additive`: v_p(x·y) = v_p(x) + v_p(y) (Proposition 8.3)
- `cor_factorial`: M ≅ ⊕ℕ₀ (Corollary 8.4)

Also includes Corollary 7.3 (squarefree diagnostic), deferred from Section 7
so that h_prime_atoms can be derived rather than assumed.

Formalized with assistance from Aristotle (uuids: 26ea4588..., b300d104...)
-/

import MultiplicationProject.GlobalMultiplicativity


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## Helper Lemmas from Section 8 Aristotle Outputs
-/

/-- If p and q are atoms, and p^k divides q, then k ≤ 1. -/
lemma lemma_pow_dvd_atom {M : Type*} [CommMonoid M] (h_red : Reduced M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : p ^ k ∣ q) :
    k ≤ 1 := by
  unfold Atoms at hq
  cases' h_dvd with a ha
  rcases k with (_ | _ | k) <;> simp_all +decide [pow_succ, mul_assoc]
  rw [irreducible_mul_iff] at hq
  aesop
  · exact hp.1 left_1
  · rw [irreducible_mul_iff] at left
    aesop
    · exact left.not_isUnit left_1
    · exact hp.1 right_1

/-- If an atom q divides a power of an atom p, then q = p.
    This is key for proving that atoms are prime. -/
lemma lemma_atom_dvd_pow {M : Type*} [CommMonoid M] (h_red : Reduced M) (h_ppp : PP_P M)
    (p q : M) (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (k : ℕ) (h_dvd : q ∣ p ^ k) :
    q = p := by
  -- Since q ∣ p^k, we have p^k = q · x for some x
  obtain ⟨x, hx⟩ : ∃ x, p^k = q * x := h_dvd
  -- Since q divides p^k, we have q ∈ powers(p)
  have hq_pow : q ∈ Submonoid.powers p := by
    have := h_ppp p hp q x
    exact this ⟨k, hx⟩ |>.1
  cases hq_pow
  aesop
  rcases w with (_ | _ | w) <;> simp_all +decide [pow_succ]
  · exact absurd hq (by unfold Atoms; aesop)
  · have := hq.isUnit_or_isUnit rfl
    aesop
    · cases hp; aesop
    · cases hp; aesop

/-!
## Recurrence for Factorization Counts

This is used in the inductive proof of coprime multiplicativity.
-/

/-- Recurrence relation: F_{k+1}(m) = ∑_{(u,v) ∈ F_2(m)} F_k(v). -/
lemma count_recurrence {M : Type*} [CommMonoid M] (k : ℕ) (m : M)
    (h_finite_2 : (LabeledFactorizations 2 m).Finite)
    (h_finite_k : ∀ f ∈ LabeledFactorizations 2 m, (LabeledFactorizations k (f 1)).Finite) :
    LabeledFactorizationCount (k + 1) m = ∑ f ∈ h_finite_2.toFinset, LabeledFactorizationCount k (f 1) := by
  unfold LabeledFactorizationCount at *
  have h_recurrence : Set.ncard (LabeledFactorizations (k + 1) m) =
      Set.ncard (⋃ f ∈ h_finite_2.toFinset,
        {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g}) := by
    congr with w
    simp +decide [LabeledFactorizations]
    bound
    · refine' ⟨Fin.cons (w 0) (Fin.cons (Finset.univ.prod (Fin.tail w)) Fin.elim0), _, Fin.tail w, _, _⟩ <;>
        simp +decide [Fin.univ_succ]
      rfl
    · simp +decide [Fin.prod_univ_succ, left_1]
  have h_disjoint : ∀ f g : Fin 2 → M, f ∈ LabeledFactorizations 2 m → g ∈ LabeledFactorizations 2 m → f ≠ g →
      Disjoint {w : Fin (k + 1) → M | ∃ h ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) h}
               {w : Fin (k + 1) → M | ∃ h ∈ LabeledFactorizations k (g 1), w = Fin.cons (g 0) h} := by
    intro f g hf hg hfg
    rw [Set.disjoint_left]
    contrapose! hfg
    aesop
    ext i
    fin_cases i <;> simp_all +decide [LabeledFactorizations]
  have h_card_union : ∀ {S : Finset (Fin 2 → M)}, (∀ f ∈ S, f ∈ LabeledFactorizations 2 m) →
      Set.ncard (⋃ f ∈ S, {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g}) =
      ∑ f ∈ S, Set.ncard {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g} := by
    intro S hS
    induction S using Finset.induction <;> aesop
    rw [← a_2, @Set.ncard_union_eq]
    · exact Set.disjoint_left.mpr fun x hx hx' => by
        rcases Set.mem_iUnion₂.mp hx' with ⟨f, hf, hxf⟩
        exact Set.disjoint_left.mp (h_disjoint a f left (right f hf) (by aesop)) hx hxf
    · exact Set.Finite.subset (Set.Finite.image (fun g => Fin.cons (a 0) g) (h_finite_k a left)) fun x hx => by aesop
    · exact Set.Finite.biUnion (Finset.finite_toSet s) fun f hf =>
        Set.Finite.subset (Set.Finite.image (fun g => Fin.cons (f 0) g) (h_finite_k f (right f hf))) fun x hx => by aesop
  rw [h_recurrence, h_card_union]
  · refine' Finset.sum_congr rfl fun f hf => _
    rw [show {w : Fin (k + 1) → M | ∃ g ∈ LabeledFactorizations k (f 1), w = Fin.cons (f 0) g} =
            Set.image (fun g : Fin k → M => Fin.cons (f 0) g) (LabeledFactorizations k (f 1)) by ext; aesop]
    rw [Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy]
  · norm_num +zetaDelta at *

/-- Sum reindexing lemma using CFI bijection. -/
lemma sum_split_by_CFI {M : Type*} [CommMonoid M]
    (h_cfi : ∀ x y : M, AreCoprime x y → Function.Bijective
      (fun (p : LabeledFactorizations 2 x × LabeledFactorizations 2 y) => labeledFactorizationMul p.1 p.2))
    (h_finite : ∀ (n : ℕ) (z : M), (LabeledFactorizations n z).Finite)
    (k : ℕ) (x y : M) (h_coprime : AreCoprime x y) :
    ∑ f ∈ (h_finite 2 (x * y)).toFinset, LabeledFactorizationCount k (f 1) =
    ∑ g ∈ (h_finite 2 x).toFinset, ∑ h ∈ (h_finite 2 y).toFinset, LabeledFactorizationCount k (g 1 * h 1) := by
  have := h_cfi x y h_coprime
  rcases this with ⟨h₁, h₂⟩
  have h_bij : Finset.image (fun (p : (Fin 2 → M) × (Fin 2 → M)) => p.1 * p.2)
      ((h_finite 2 x).toFinset ×ˢ (h_finite 2 y).toFinset) = (h_finite 2 (x * y)).toFinset := by
    ext
    constructor
    · simp +decide [LabeledFactorizations]
      aesop
      ac_rfl
    · simp +zetaDelta at *
      intro h
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := h₂ ⟨_, h⟩
      exact ⟨_, _, ⟨a.2, ha.2⟩, rfl⟩
  rw [← h_bij, Finset.sum_image]
  · simp +decide [Finset.sum_product]
  · intro p hp q hq h_eq
    simp_all +decide [Function.Injective, Set.mem_setOf_eq]
    specialize h₁ _ hp.1 _ hp.2 _ hq.1 _ hq.2
    aesop
    · exact h₁ (Subtype.ext h_eq) |>.1
    · exact h₁ (Subtype.ext h_eq) |>.2

/-!
## Corollary 7.3: Squarefree Diagnostic (Deferred from Section 7)

This corollary uses h_prime_atoms, which we can now derive from CFI.
-/

/- Aristotle failed to find a proof. -/
/-- Under PP-D + CFI, atoms are prime: if p ∣ a·b then p ∣ a or p ∣ b. -/
lemma atoms_are_prime {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M) :
    ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p hp a b h_dvd
  have h_ppp : PP_P M := Prop_CFI_implies_PPP h_reduced h_atomic h_cfi
  -- Strategy: Use PP-P to show that the "p-part" of a*b comes from a or b.
  -- If p ∤ a and p ∤ b, we derive a contradiction.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨h_not_a, h_not_b⟩ := h_neg
  -- p | a*b means a*b = p * m for some m
  obtain ⟨m, hm⟩ := h_dvd
  -- Key: use `power_coprime_of_not_in_support` to show p is coprime to a and b
  -- p ∤ a means p ∉ Support a (since if p ∈ Support a, then p | a)
  have hp_not_supp_a : p ∉ Support a := by
    intro h_in
    exact h_not_a h_in.2
  have hp_not_supp_b : p ∉ Support b := by
    intro h_in
    exact h_not_b h_in.2
  -- By power_coprime_of_not_in_support, p^1 = p and a are coprime, similarly for b
  have h_cop_pa : AreCoprime (p ^ 1) a := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_a 1
  have h_cop_pb : AreCoprime (p ^ 1) b := power_coprime_of_not_in_support h_reduced h_cfi hp hp_not_supp_b 1
  simp only [pow_one] at h_cop_pa h_cop_pb
  -- Now we need: if p coprime to a and p coprime to b, then p coprime to a*b
  -- This follows because AreCoprime means no common atom divisor
  -- If p | a*b and p coprime to a and p coprime to b, we get a contradiction
  -- p | a*b and p is an atom means p ∈ Support(a*b)
  -- We need to show this contradicts p being coprime to both a and b
  -- The key insight: use CFI on (a, b) if they're coprime, or decompose otherwise
  -- For the general case, we use that p being coprime to a means p ∤ a (for atoms)
  -- Since p is coprime to a: any atom dividing both p and a leads to contradiction
  -- p | p, so if p | a, then p is a common atom divisor, contradicting coprimality
  -- But we already know p ∤ a from h_not_a
  -- The issue is showing p ∤ a*b from p ∤ a and p ∤ b
  -- This requires the "primality" property we're trying to prove!
  -- Alternative: use PP-P directly on the p-power structure
  -- If a*b = p * m, consider the p-adic structure
  -- By PP-P, if p^k | a*b for some k ≥ 1, then the p-power part must come from somewhere
  -- Since p ∤ a means v_p(a) = 0, and p ∤ b means v_p(b) = 0
  -- We should have v_p(a*b) = 0, contradicting p | a*b
  -- The formal proof of v_p additivity requires more machinery
  -- For now, we note this is where PP-P enters: prime powers are factorially closed
  -- means the p-content cannot "appear from nowhere"
  sorry

/-- **Corollary 7.3**: Squarefree diagnostic.

    If m is a product of distinct atoms (squarefree), then F_k(m) = k^ω(m),
    where ω(m) is the number of distinct prime factors.

    Proof: F_k(p) = k for each atom, and coprime multiplicativity gives the product. -/
theorem cor_squarefree {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M)
    (h_atomic : Atomic M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (h_cfi : ∀ x y : M, AreCoprime x y → Function.Bijective (Function.uncurry (labeledFactorizationMul (k := 2) (x := x) (y := y))))
    {k : ℕ} (hk : k ≥ 1)
    (L : List M) (h_atoms : ∀ p ∈ L, p ∈ Atoms M) (h_nodup : L.Nodup) :
    LabeledFactorizationCount k L.prod = k ^ L.length := by
  -- We need atoms_are_prime, which requires finishing the sorry above
  induction' L using List.reverseRecOn with p L ih generalizing k;
  · rcases k with ( _ | _ | k ) <;> simp_all +decide;
    · exact?;
    · simp +decide [ LabeledFactorizationCount ];
      use fun _ => 1;
      ext;
      simp +decide [ LabeledFactorizations ];
      simp +decide [ funext_iff, Fin.prod_univ_succ ];
      constructor;
      · intro h x
        generalize_proofs at *;
        -- Since $x_0 * (x_1 * \prod_{i : Fin k} x_{i+2}) = 1$, each $x_i$ must be a unit.
        have h_unit : IsUnit (‹Fin (k + 1 + 1) → M› x) := by
          have h_unit : IsUnit (∏ i : Fin (k + 2), ‹Fin (k + 2) → M› i) := by
            simp_all +decide [ Fin.prod_univ_succ ];
          exact isUnit_of_dvd_unit ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) h_unit;
        exact?;
      · aesop;
  · -- By Proposition 7.2, we have F_k(m * p) = F_k(m) * F_k(p).
    have h_prop : LabeledFactorizationCount k (p.prod * L) = LabeledFactorizationCount k p.prod * LabeledFactorizationCount k L := by
      apply_rules [ prop_coprime_mult ];
      -- Since $L$ is an atom and $p.prod$ is a product of atoms different from $L$, they are coprime.
      have h_coprime : ∀ {p : List M}, (∀ p_1 ∈ p, p_1 ∈ Atoms M) → (∀ p_1 ∈ p, p_1 ≠ L) → AreCoprime (p.prod) L := by
        intro p hp hL; induction' p with p hp ih <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
        · exact?;
        · -- Since p is coprime with L and the product of the rest is coprime with L, their product is also coprime with L.
          have h_coprime_mul : AreCoprime p L ∧ AreCoprime (List.prod ‹_›) L → AreCoprime (p * List.prod ‹_›) L := by
            have h_prime : ∀ p ∈ Atoms M, ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b := by
              exact?;
            intro h_coprime_mul
            apply AreCoprime_mul_of_prime_atoms h_prime h_coprime_mul.left h_coprime_mul.right;
          exact h_coprime_mul ⟨ coprime_of_distinct_atoms h_reduced hp.1 ( h_atoms L ( Or.inr rfl ) ) hL.1, ih ⟩;
      exact h_coprime ( fun x hx => h_atoms x ( List.mem_append_left _ hx ) ) ( fun x hx => by rw [ List.nodup_append ] at h_nodup; aesop );
    simp_all +decide [ List.nodup_append ];
    rw [ pow_succ, mul_comm ];
    rw [ mul_comm, count_atom h_reduced hk ( h_atoms L ( Or.inr rfl ) ) ]

/-!
## Main Section 8 Results (Placeholders)

These theorems represent the core of Section 8. Aristotle made partial progress
but did not complete them. They will be proven in future Aristotle sessions.
-/

/- Aristotle failed to find a proof. -/
/-- **Lemma 8.1**: Primewise decomposition.

    Under (PP-D), (PP-P), and atomicity, every m ∈ M can be written as
    m = ∏_{p ∈ S} p^{v_p(m)} where S is the support of m. -/
theorem lem_primewise {M : Type*} [CommMonoid M]
    (h_ppd : PP_D M) (h_ppp : PP_P M) (h_atomic : Atomic M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
  sorry

/- **Theorem 8.2**: Master counting formula.

    Under (PP-D) and (CFI), for any m ∈ M and k ≥ 1:
    F_k(m) = ∏_{p ∈ P} C(v_p(m) + k - 1, k - 1) -/
noncomputable section AristotleLemmas

lemma Support_prod_powers_subset {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (S : Finset M) (hS : ∀ p ∈ S, p ∈ Atoms M) (e : M → ℕ) :
    Support (S.prod (fun p => p ^ e p)) ⊆ S := by
      induction' S using Finset.induction with p S hS ih;
      · -- Since 1 is a unit, its support is empty.
        simp [Support];
        exact?;
      · -- The support of a product of coprime elements is contained in the union of their supports.
        have h_support_prod : Support (p ^ e p * ∏ p ∈ S, p ^ e p) ⊆ Support (p ^ e p) ∪ Support (∏ p ∈ S, p ^ e p) := by
          apply_rules [ Support_mul_subset_union_support_of_CFI ];
          apply_rules [ power_coprime_of_not_in_support ];
          · exact Finset.mem_insert_self _ _;
          · exact fun h => ‹p∉S› ( ih ( fun q hq => hS q ( Finset.mem_insert_of_mem hq ) ) h );
        simp_all +decide [ Finset.prod_insert, Set.subset_def ];
        exact fun x hx => Or.imp ( fun hx' => by have := Support_Power_Subset h_reduced ( Prop_CFI_implies_PPP h_reduced h_atomic h_cfi ) p hS.1 ( e p ) ; exact this hx' |> fun hx'' => by aesop ) ( fun hx' => ih x hx' ) ( h_support_prod x hx )

lemma count_one_k {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (k : ℕ) :
    LabeledFactorizationCount k 1 = 1 := by
      unfold LabeledFactorizationCount;
      rw [ show LabeledFactorizations k 1 = { fun _ => 1 } from _ ];
      · rw [ Set.ncard_singleton ];
      · ext f; simp [LabeledFactorizations];
        exact ⟨ fun h => funext h, fun h i => congr_fun h i ⟩

lemma count_prod_powers {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (S : Finset M) (hS : ∀ p ∈ S, p ∈ Atoms M)
    (e : M → ℕ) (k : ℕ) (hk : k ≥ 1) :
    LabeledFactorizationCount k (S.prod (fun p => p ^ e p)) =
    S.prod (fun p => LabeledFactorizationCount k (p ^ e p)) := by
      induction' S using Finset.induction with p S hpS ih;
      · convert h_cfi _ _ _;
        rotate_left;
        exact 1;
        exact 1;
        · exact one_coprime_left h_reduced 1;
        · unfold LabeledFactorizationCount;
          simp +decide [ LabeledFactorizations ];
          constructor <;> intro h;
          · exact h_cfi _ _ ( by exact? );
          · use fun _ => 1;
            ext f; simp +decide [ Finset.prod_eq_one ] ;
            constructor <;> intro h <;> simp_all +decide [ funext_iff, Finset.prod_eq_one ];
            intro i; have := h ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ i ) ; simp_all +decide [ dvd_iff_exists_eq_mul_left ] ;
            obtain ⟨ c, hc ⟩ := this;
            rw [ eq_comm ] at hc;
            -- Since $c * f i = 1$ and $M$ is reduced, $c$ must be a unit.
            have hc_unit : IsUnit c := by
              exact isUnit_of_mul_eq_one _ _ hc;
            exact?;
      · rw [ Finset.prod_insert hpS, Finset.prod_insert hpS ];
        rw [ ← ih ( fun q hq => hS q ( Finset.mem_insert_of_mem hq ) ) ];
        apply_rules [ prop_coprime_mult ];
        apply Disjoint_Support_implies_Coprime;
        refine' Set.disjoint_left.mpr _;
        intro q hq hq'; have := Support_prod_powers_subset h_reduced h_atomic h_cfi S ( fun p hp => hS p ( Finset.mem_insert_of_mem hp ) ) e; simp_all +decide [ Finset.prod_eq_zero_iff, pow_eq_zero_iff' ] ;
        have := Support_Power_Subset h_reduced ( Prop_CFI_implies_PPP h_reduced h_atomic h_cfi ) p hS.1 ( e p ) ; simp_all +decide [ Set.subset_def ] ;
        exact hpS ( this q hq ▸ ‹∀ x ∈ Support ( ∏ p ∈ S, p ^ e p ), x ∈ S› q hq' )

lemma lem_primewise_aux {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M) (h_ppd : PP_D M) (h_ppp : PP_P M)
    (h_cfi : CFI M)
    (m : M) (hm : ¬IsUnit m) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      m = S.prod (fun p => p ^ PValuation p m) := by
        exact?

end AristotleLemmas

theorem thm_master {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (h_finite : ∀ (k : ℕ) (m : M), (LabeledFactorizations k m).Finite)
    (m : M) (k : ℕ) (hk : k ≥ 1) :
    ∃ (S : Finset M), (∀ p ∈ S, p ∈ Atoms M) ∧
      LabeledFactorizationCount k m = S.prod (fun p => Nat.choose (PValuation p m + k - 1) (k - 1)) := by
  have h_count_prod : ∀ (S : Finset M) (hS : ∀ p ∈ S, p ∈ Atoms M), LabeledFactorizationCount k (S.prod (fun p => p ^ (PValuation p m))) = S.prod (fun p => Nat.choose ((PValuation p m) + k - 1) (k - 1)) := by
    intro S hS
    have h_count_prod : LabeledFactorizationCount k (S.prod (fun p => p ^ (PValuation p m))) = S.prod (fun p => LabeledFactorizationCount k (p ^ (PValuation p m))) := by
      exact?;
    convert h_count_prod using 2;
    exact Eq.symm ( Theorem_Local_SB h_ppd ( Prop_CFI_implies_PPP h_reduced h_atomic h_cfi ) _ ( hS _ ‹_› ) _ _ hk );
  by_cases hm : IsUnit m;
  · use ∅;
    have h_m_one : m = 1 := by
      exact?;
    grind;
  · obtain ⟨ S, hS₁, hS₂ ⟩ := lem_primewise_aux h_reduced h_atomic h_ppd ( Prop_CFI_implies_PPP h_reduced h_atomic h_cfi ) h_cfi m hm;
    exact ⟨ S, hS₁, by rw [ ← h_count_prod S hS₁, ← hS₂ ] ⟩

/- Aristotle failed to find a proof. -/
/-- **Proposition 8.3**: Additivity of valuations.

    Under (PP-D) and (CFI), for every atom p and all x, y ∈ M:
    v_p(x · y) = v_p(x) + v_p(y) -/
theorem prop_val_additive {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M)
    (p : M) (hp : p ∈ Atoms M) (x y : M) :
    PValuation p (x * y) = PValuation p x + PValuation p y := by
  sorry

/-- **Corollary 8.4**: Factorial structure.

    Under (PP-D) and (CFI), the monoid M is isomorphic to ⊕_{p ∈ P} ℕ₀,
    and hence is factorial. -/
theorem cor_factorial {M : Type*} [CommMonoid M]
    (h_reduced : Reduced M) (h_atomic : Atomic M)
    (h_ppd : PP_D M) (h_cfi : CFI M) :
    Factorial M := by
  intro x hx;
  -- By the properties of the `PValuation` function, we can show that the count of each atom in the factorization is unique.
  have h_unique : ∀ p : M, p ∈ Atoms M → ∀ s : Multiset M, (∀ a ∈ s, Irreducible a) → s.prod = x → Multiset.count p s = PValuation p x := by
    intro p hp s hs hx
    have h_val : PValuation p x = ∑ a ∈ s.toFinset, Multiset.count a s * PValuation p a := by
      have h_val : ∀ {s : Multiset M}, (∀ a ∈ s, Irreducible a) → PValuation p (s.prod) = ∑ a ∈ s.toFinset, Multiset.count a s * PValuation p a := by
        intro s hs
        induction' s using Multiset.induction with a s ih;
        · simp +decide [ PValuation ];
          rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num;
          · exact ⟨ 0, by simp +decide ⟩;
          · intro a ha
            by_contra ha_nonzero;
            have := dvd_trans ( pow_dvd_pow p ( Nat.pos_of_ne_zero ha_nonzero ) ) ha;
            exact hp.1 ( isUnit_of_dvd_one ( by simpa using this ) );
        · simp_all +decide [ Finset.sum_add_distrib, add_mul, Multiset.count_cons ];
          -- Apply the additivity of the valuation function.
          have h_val_add : ∀ a b : M, PValuation p (a * b) = PValuation p a + PValuation p b := by
            apply prop_val_additive h_reduced h_atomic h_ppd h_cfi p hp;
          rw [ h_val_add, ih, add_comm ];
      rw [ ← hx, h_val hs ];
    -- Since $p$ is an atom, for any $a \in s$, we have $PValuation p a = 1$ if $a = p$ and $PValuation p a = 0$ otherwise.
    have h_val_atom : ∀ a ∈ s.toFinset, PValuation p a = if a = p then 1 else 0 := by
      intro a ha
      by_cases ha_eq_p : a = p;
      · simp [ha_eq_p, PValuation];
        rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · exact ⟨ 1, by simp +decide ⟩;
        · exact?;
        · exact fun w hw => ⟨ 1, by simp, hw ⟩;
      · have h_not_div : ¬p ∣ a := by
          have h_not_div : ∀ {a : M}, Irreducible a → ∀ {p : M}, Irreducible p → a ≠ p → ¬p ∣ a := by
            exact?;
          exact h_not_div ( hs a ( Multiset.mem_toFinset.mp ha ) ) hp ha_eq_p;
        simp [ha_eq_p, h_not_div, PValuation];
        rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · exact ⟨ 0, by simp +decide ⟩;
        · exact fun n hn => Nat.le_of_not_lt fun h => h_not_div <| dvd_trans ( dvd_pow_self _ h.ne' ) hn;
        · exact fun w hw => False.elim <| hw.not_le <| Nat.zero_le _;
    rw [ h_val, Finset.sum_congr rfl fun a ha => by rw [ h_val_atom a ha ] ] ; aesop;
  have h_factor_unique : ∀ s t : Multiset M, (∀ a ∈ s, Irreducible a) → (∀ a ∈ t, Irreducible a) → s.prod = x → t.prod = x → s = t := by
    intro s t hs ht hs' ht'
    ext p;
    by_cases hp : Irreducible p <;> simp_all +decide [ Atoms ];
    rw [ Multiset.count_eq_zero_of_notMem fun h => hp <| hs p h, Multiset.count_eq_zero_of_notMem fun h => hp <| ht p h ];
  obtain ⟨ s, hs ⟩ := h_atomic x hx;
  exact ⟨ s, hs, fun t ht => h_factor_unique t s ht.1 hs.1 ht.2 hs.2 ⟩

end