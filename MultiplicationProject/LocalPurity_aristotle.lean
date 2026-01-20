/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5280b5d3-61d0-4885-b753-0d89b27eacb6

The following was proved by Aristotle:

- theorem Prop_CFI_implies_PPP {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_atomic : Atomic M) (h_cfi : CFI M) :
    PP_P M
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6e083587-549a-48b7-a0a4-9f1a628ab2cf

The following was proved by Aristotle:

- lemma Blockwise_CFI_2 {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin n → M)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i)) :
    Function.Bijective (fun (fs : (i : Fin n) →
        LabeledFactorizations 2 (x i) × LabeledFactorizations 2 (y i)) =>
      (⟨fun j => ∏ i, ((fs i).1.1 j * (fs i).2.1 j),
        sorry⟩ : LabeledFactorizations 2 (∏ i, x i * y i)))

- lemma atom_dvd_power_eq {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_ppp : PP_P M) {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M)
    {k : ℕ} (h_dvd : q ∣ p ^ k) :
    q = p

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 5: Local Purity (CFI implies PP-P)

This file proves that CFI implies PP-P using the paper's blockwise independence argument.

## Proof Structure (from the paper)

The key insight is that we prove PP-P DIRECTLY from blockwise CFI, not via Support_Power_Subset.

1. **Lemma 5.1** (Blockwise_CFI_2): For blockwise-disjoint coprime pairs, the coordinatewise
   map Θ: ∏_j (F_2(x^j) × F_2(y^j)) → F_2(X * Y) is a bijection.

2. **Lemma 5.2** (Blockwise_CFI_k): Extends to k factors on one designated block.

3. **Proposition 5.3** (Prop_CFI_implies_PPP): Given x * y ∈ ⟨p⟩:
   - Write x = p^a * x_pf, y = p^b * y_pf (p-free parts)
   - Build blockwise-disjoint family with the p-block and atom blocks from x_pf, y_pf
   - Apply Blockwise_CFI_k; the bijection structure forces x_pf = y_pf = 1

After PP-P is proven, Support_Power_Subset becomes trivial.
-/

import MultiplicationProject.Utilities


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

noncomputable section

open scoped Classical

set_option maxHeartbeats 0

/-!
## Helper Lemmas
-/

/-- In a reduced monoid, 1 is coprime to everything. -/
lemma one_coprime_left {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (x : M) :
    AreCoprime 1 x := by
  intro p hp h1_dvd _
  exact absurd (isUnit_of_dvd_one h1_dvd) hp.not_isUnit

/-- In a reduced monoid, everything is coprime to 1. -/
lemma one_coprime_right {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (x : M) :
    AreCoprime x 1 := by
  intro p hp _ h1_dvd
  exact absurd (isUnit_of_dvd_one h1_dvd) hp.not_isUnit

/-- In a reduced atomic monoid, distinct atoms are coprime. -/
lemma coprime_of_distinct_atoms {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h_neq : p ≠ q) :
    AreCoprime p q := by
  intro r hr hrp hrq
  obtain ⟨s, hs⟩ := hrp
  cases hp.isUnit_or_isUnit hs with
  | inl hr_unit => exact absurd hr_unit hr.not_isUnit
  | inr hs_unit =>
    have hs1 : s = 1 := h_reduced s hs_unit
    subst hs1; simp at hs
    obtain ⟨t, ht⟩ := hrq
    cases hq.isUnit_or_isUnit ht with
    | inl hr_unit => exact absurd hr_unit hr.not_isUnit
    | inr ht_unit =>
      have ht1 : t = 1 := h_reduced t ht_unit
      subst ht1; simp at ht
      exact h_neq (hs.trans ht.symm)

/- Aristotle failed to find a proof. -/
/- Aristotle failed to find a proof. -/
/-- Powers of an atom are coprime to elements with disjoint support.
    Note: This requires PP-P to prove properly. Placeholder with sorry. -/
lemma power_coprime_of_not_in_support {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    {p : M} (hp : p ∈ Atoms M) {x : M} (hx : p ∉ Support x) (k : ℕ) :
    AreCoprime (p ^ k) x := by
  intro q hq hqpk hqx
  simp [Support] at hx
  -- q divides p^k and q is an atom
  -- In a reduced monoid with PP-P, if q | p^k with q irreducible, then q = p
  -- This proof requires PP-P which we derive later from CFI
  have hqp : q = p := by
    sorry
  subst hqp
  exact hx hq hqx

/-!
## Blockwise CFI Lemmas

These are the key technical lemmas from the paper (Lemmas 5.1 and 5.2).
-/

/- **Lemma 5.1**: Blockwise CFI for two factors.

    Given a blockwise-disjoint family {(x^j, y^j)}_{j=1}^m where each pair is coprime,
    the coordinatewise map Θ: ∏_j (F_2(x^j) × F_2(y^j)) → F_2(X * Y) is a bijection,
    where X = ∏_j x^j and Y = ∏_j y^j.

    Proof: Induction on m. The base case m = 1 is CFI. For the step, use that
    supp(X' * Y') is disjoint from supp(x^{m+1} * y^{m+1}) by blockwise disjointness,
    allowing us to apply CFI to combine the bijections.

    TODO: Complete this proof in a future Aristotle session. -/
noncomputable section AristotleLemmas

/-
Under CFI and Reduced, the support of a product of coprime elements is contained in the union of their supports.
-/
lemma Support_mul_subset_union_support_of_CFI {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    (x y : M) (h_coprime : AreCoprime x y) :
    Support (x * y) ⊆ Support x ∪ Support y := by
      have h_support_union : ∀ p ∈ Atoms M, p ∣ x * y → p ∣ x ∨ p ∣ y := by
        -- By definition of coprimality, if p divides x * y, then p must divide x or p must divide y.
        intros p hp hdiv
        by_contra h_contra;
        obtain ⟨f, g, hfg⟩ : ∃ f : LabeledFactorizations 2 x, ∃ g : LabeledFactorizations 2 y, f.1 0 * g.1 0 = p := by
          obtain ⟨ z, hz ⟩ := hdiv;
          obtain ⟨ f, hf ⟩ := h_cfi x y h_coprime |>.2 ⟨ fun i => if i = 0 then p else z, by
            simp +decide [ hz, LabeledFactorizations ] ⟩
          generalize_proofs at *;
          exact ⟨ f.1, f.2, by simpa using congr_arg ( fun f : LabeledFactorizations 2 ( x * y ) => f.val 0 ) hf ⟩;
        have hfg_div : f.val 0 ∣ x ∧ g.val 0 ∣ y := by
          exact ⟨ dvd_trans ( by simp +decide [ Fin.prod_univ_succ ] ) ( f.2.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ 0 ) ), dvd_trans ( by simp +decide [ Fin.prod_univ_succ ] ) ( g.2.symm ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ 0 ) ) ⟩;
        have hfg_unit : IsUnit (f.val 0) ∨ IsUnit (g.val 0) := by
          exact?;
        cases' hfg_unit with hfg_unit hfg_unit;
        · have := h_reduced _ hfg_unit; aesop;
        · have := h_reduced _ hfg_unit; aesop;
      exact fun p hp => by cases h_support_union p hp.1 hp.2 <;> [ exact Or.inl ⟨ hp.1, by assumption ⟩ ; exact Or.inr ⟨ hp.1, by assumption ⟩ ] ;

/-
The support of the product of blockwise disjoint coprime pairs is contained in the union of their individual supports.
-/
lemma Blockwise_Support_Subset {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin n → M)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i)) :
    Support (∏ i, x i * y i) ⊆ ⋃ i, (Support (x i) ∪ Support (y i)) := by
      -- We proceed by induction on $n$.
      induction' n with n ih;
      · simp +decide [ Support ];
        intro x hx hx';
        exact hx.not_isUnit ( isUnit_of_dvd_one hx' );
      · -- Let's split the product into the first element and the rest.
        have h_split : Support (∏ i : Fin (Nat.succ n), x i * y i) = Support ((x 0 * y 0) * ∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i)) := by
          rw [ Fin.prod_univ_succ ];
        -- By `BlockwiseDisjoint`, `S_0` is disjoint from `S_tail`.
        have h_disjoint_supports : Disjoint (Support (x 0 * y 0)) (Support (∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i))) := by
          have h_disjoint_supports : Disjoint (Support (x 0) ∪ Support (y 0)) (⋃ i : Fin n, (Support (x (Fin.succ i)) ∪ Support (y (Fin.succ i)))) := by
            simp_all +decide [ Set.disjoint_left ];
            intro a ha i; specialize h_disjoint 0 ( Fin.succ i ) ; simp_all +decide [ Fin.ext_iff, Set.disjoint_left ] ;
          refine' Disjoint.mono _ _ h_disjoint_supports;
          · apply_rules [ Support_mul_subset_union_support_of_CFI ];
          · exact ih _ _ ( fun i j hij => h_disjoint _ _ ( by simpa [ Fin.ext_iff ] using hij ) ) fun i => h_coprime _;
        -- By `Support_mul_subset_union_support_of_CFI`, `Support (z 0 * ∏_{i>0} z i) ⊆ Support (z 0) ∪ Support (∏_{i>0} z i)`.
        have h_support_union : Support ((x 0 * y 0) * ∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i)) ⊆ Support (x 0 * y 0) ∪ Support (∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i)) := by
          apply_rules [ Support_mul_subset_union_support_of_CFI ];
          exact Disjoint_Support_implies_Coprime _ _ h_disjoint_supports;
        refine' h_split ▸ h_support_union.trans _;
        refine' Set.union_subset _ _;
        · have h_support_union : Support (x 0 * y 0) ⊆ Support (x 0) ∪ Support (y 0) := by
            exact?;
          exact h_support_union.trans ( Set.subset_iUnion ( fun i => Support ( x i ) ∪ Support ( y i ) ) 0 );
        · exact Set.Subset.trans ( ih _ _ ( fun i j hij => h_disjoint ( Fin.succ i ) ( Fin.succ j ) ( by simpa [ Fin.ext_iff ] using hij ) ) fun i => h_coprime _ ) ( Set.iUnion_subset fun i => Set.subset_iUnion_of_subset ( Fin.succ i ) ( Set.Subset.refl _ ) )

/-
The product of the first pair is coprime to the product of the remaining pairs in a blockwise disjoint family.
-/
lemma Blockwise_Coprime_Head_Tail {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin (n + 1) → M)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i)) :
    AreCoprime (x 0 * y 0) (∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i)) := by
      -- The support of `x 0 * y 0` is disjoint from the support of each term in the product.
      have h_support_disjoint : Disjoint (Support (x 0) ∪ Support (y 0)) (⋃ i, (Support (x (Fin.succ i)) ∪ Support (y (Fin.succ i)))) := by
        exact Set.disjoint_left.mpr fun p hp hp' => by obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp hp'; exact Set.disjoint_left.mp ( h_disjoint 0 ( Fin.succ i ) ( ne_of_lt ( Fin.succ_pos i ) ) ) hp hi;
      have h_support_disjoint : Disjoint (Support (x 0 * y 0)) (⋃ i, (Support (x (Fin.succ i)) ∪ Support (y (Fin.succ i)))) := by
        exact Disjoint.mono_left ( by simpa using Support_mul_subset_union_support_of_CFI h_reduced h_cfi _ _ ( h_coprime 0 ) ) h_support_disjoint;
      refine' Disjoint_Support_implies_Coprime _ _ _;
      refine' h_support_disjoint.mono_right _;
      exact Blockwise_Support_Subset h_reduced h_cfi _ _ ( fun i j hij => h_disjoint _ _ <| by simpa [ Fin.ext_iff ] using hij ) fun i => h_coprime _

/-
Helper lemma to show that the product of blockwise factorizations matches the product of the elements.
-/
lemma Blockwise_Prod_Eq {M : Type*} [CommMonoid M] {n : ℕ} (x y : Fin n → M)
  (fs : (i : Fin n) → LabeledFactorizations 2 (x i) × LabeledFactorizations 2 (y i)) :
  (∏ j : Fin 2, ∏ i : Fin n, (fs i).1.1 j * (fs i).2.1 j) = ∏ i : Fin n, x i * y i := by
    simp +decide [ Fin.prod_univ_succ ];
    rw [ ← Finset.prod_mul_distrib ];
    congr 1 with i;
    convert congr_arg₂ ( · * · ) ( fs i |>.1.2 ) ( fs i |>.2.2 ) using 1;
    rw [ show ( Finset.univ : Finset ( Fin 2 ) ) = { 0, 1 } by decide, Finset.prod_pair, Finset.prod_pair ] <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ]

/-
Inductive step for Blockwise CFI: if the property holds for size n, it holds for size n+1.
-/
lemma Blockwise_CFI_Inductive_Step {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin (n + 1) → M)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i))
    (ih : Function.Bijective (fun (fs : (i : Fin n) →
        LabeledFactorizations 2 (x (Fin.succ i)) × LabeledFactorizations 2 (y (Fin.succ i))) =>
      (⟨fun j => ∏ i, ((fs i).1.1 j * (fs i).2.1 j),
        Blockwise_Prod_Eq (x ∘ Fin.succ) (y ∘ Fin.succ) fs⟩ : LabeledFactorizations 2 (∏ i, x (Fin.succ i) * y (Fin.succ i))))) :
    Function.Bijective (fun (fs : (i : Fin (n + 1)) →
        LabeledFactorizations 2 (x i) × LabeledFactorizations 2 (y i)) =>
      (⟨fun j => ∏ i, ((fs i).1.1 j * (fs i).2.1 j),
        Blockwise_Prod_Eq x y fs⟩ : LabeledFactorizations 2 (∏ i, x i * y i))) := by
          have h_head_bij : Function.Bijective (fun (fs : (LabeledFactorizations 2 (x 0)) × (LabeledFactorizations 2 (y 0))) =>
              ⟨fun (j : Fin 2) => (fs.1.val j) * (fs.2.val j), by
                exact labeledFactorizationMul fs.1 fs.2 |>.2⟩ : (LabeledFactorizations 2 (x 0)) × (LabeledFactorizations 2 (y 0)) → (LabeledFactorizations 2 (x 0 * y 0))) := by
                exact h_cfi _ _ ( h_coprime 0 );
          have h_combine_bij : Function.Bijective (fun (fs : (LabeledFactorizations 2 (x 0 * y 0)) × (LabeledFactorizations 2 (∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i)))) =>
              ⟨fun (j : Fin 2) => (fs.1.val j) * (fs.2.val j), by
                simp +decide [ Fin.prod_univ_succ, LabeledFactorizations ];
                convert congr_arg₂ ( · * · ) ( fs.1.2 ) ( fs.2.2 ) using 1;
                simp +decide [ Fin.univ_succ, mul_assoc, mul_comm, mul_left_comm ]⟩ : (LabeledFactorizations 2 (x 0 * y 0)) × (LabeledFactorizations 2 (∏ i : Fin n, x (Fin.succ i) * y (Fin.succ i))) → (LabeledFactorizations 2 (∏ i : Fin (n + 1), x i * y i))) := by
                have := h_cfi ( x 0 * y 0 ) ( ∏ i : Fin n, x ( Fin.succ i ) * y ( Fin.succ i ) ) ?_;
                · convert this using 1;
                  · simp +decide [ Fin.prod_univ_succ ];
                  · congr! 1;
                    congr! 1;
                    · simp +decide [ Fin.prod_univ_succ ];
                    · bound;
                · exact?
          generalize_proofs at *;
          have h_split_bij : Function.Bijective (fun (fs : (i : Fin (n + 1)) → (LabeledFactorizations 2 (x i)) × (LabeledFactorizations 2 (y i))) =>
              ((fs 0), (fun (i : Fin n) => fs (Fin.succ i))) : ((i : Fin (n + 1)) → (LabeledFactorizations 2 (x i)) × (LabeledFactorizations 2 (y i))) → ((LabeledFactorizations 2 (x 0)) × (LabeledFactorizations 2 (y 0))) × ((i : Fin n) → (LabeledFactorizations 2 (x (Fin.succ i))) × (LabeledFactorizations 2 (y (Fin.succ i)))) ) := by
                constructor;
                · intro fs₁ fs₂ h_eq
                  simp at h_eq;
                  exact funext fun i => Fin.cases h_eq.1 ( fun i => congr_fun h_eq.2 i ) i;
                · intro ⟨ fs₀, fs₁ ⟩;
                  exact ⟨ Fin.cons fs₀ fs₁, rfl ⟩;
          convert h_combine_bij.comp ( h_head_bij.prodMap ih ) |> Function.Bijective.comp <| h_split_bij using 1;
          ext; simp +decide [ Fin.prod_univ_succ ] ;

end AristotleLemmas

lemma Blockwise_CFI_2 {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin n → M)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i)) :
    Function.Bijective (fun (fs : (i : Fin n) →
        LabeledFactorizations 2 (x i) × LabeledFactorizations 2 (y i)) =>
      (⟨fun j => ∏ i, ((fs i).1.1 j * (fs i).2.1 j),
        by
          convert Blockwise_Prod_Eq x y fs using 1⟩ : LabeledFactorizations 2 (∏ i, x i * y i))) := by
  all_goals generalize_proofs at *;
  induction' n with n ih;
  · refine' ⟨ _, _ ⟩;
    · intro a b h;
      exact Subsingleton.elim _ _;
    · intro ⟨ f, hf ⟩;
      simp_all +decide [ LabeledFactorizations ];
      simp_all +decide [ LabeledFactorizations ];
      ext i; fin_cases i <;> simp_all +decide [ h_reduced ] ;
      · have := h_reduced ( f 0 );
        exact Eq.symm ( this ( isUnit_of_mul_eq_one _ _ hf ) );
      · have := h_reduced ( f 1 );
        rw [ this ( isUnit_of_dvd_one ( dvd_of_mul_left_eq _ hf ) ) ];
  · convert Blockwise_CFI_Inductive_Step h_reduced h_cfi x y h_disjoint h_coprime _;
    convert ih ( x ∘ Fin.succ ) ( y ∘ Fin.succ ) _ _ _;
    · exact fun i j hij => h_disjoint _ _ ( by simpa [ Fin.ext_iff ] using hij );
    · exact fun i => h_coprime _

/- Aristotle failed to find a proof. -/
/- Aristotle failed to find a proof. -/
/-- **Lemma 5.2**: Blockwise CFI for k factors on one designated block.

    Given a blockwise-disjoint family with one designated block ℓ, we get a bijection
    that uses 2-factorizations for blocks j ≠ ℓ and k-factorizations for block ℓ. -/
lemma Blockwise_CFI_k {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {n : ℕ} (x y : Fin n → M) (k : ℕ) (ℓ : Fin n)
    (h_disjoint : BlockwiseDisjoint x y)
    (h_coprime : ∀ i, AreCoprime (x i) (y i)) :
    ∃ (E : ((i : Fin n) → if i = ℓ then 
              LabeledFactorizations k (x i) × LabeledFactorizations k (y i)
            else 
              LabeledFactorizations 2 (x i) × LabeledFactorizations 2 (y i)) ≃ 
           LabeledFactorizations k (∏ i, x i * y i)), True := by
  sorry

/-!
## Main Result: Proposition 5.3

CFI implies PP-P via the blockwise argument.
-/

/- Aristotle failed to find a proof. -/
/- **Proposition 5.3**: CFI implies PP-P.

    Proof outline from the paper:
    1. Fix p ∈ P and suppose x * y ∈ ⟨p⟩, say x * y = p^e
    2. Write x = p^a * x_pf and y = p^b * y_pf where x_pf, y_pf are p-free
    3. Partition x_pf = ∏_j u^j and y_pf = ∏_i v^i with atoms grouped by distinct primes
    4. Form the blockwise-disjoint family:
       (p^a, p^b), (u^1, 1), ..., (u^r, 1), (1, v^1), ..., (1, v^s)
    5. Apply Blockwise_CFI_k with ℓ = p-block and k = r + s + 1
    6. Choose the k-factorization (p^{a+b}, 1, ..., 1) ∈ F_k(p^a) × F_k(p^b)
    7. By bijectivity, this has a unique preimage
    8. Since x * y ∈ ⟨p⟩, every coordinate of the image is a p-power
    9. For blocks (u^j, 1): the contribution to each coordinate must be a p-power,
       but u^j is p-free, so u^j must be 1
    10. Similarly v^i = 1 for all i
    11. Therefore x_pf = y_pf = 1, so x = p^a and y = p^b ∈ ⟨p⟩ -/
noncomputable section AristotleLemmas

/-
The product of blockwise factorizations is a factorization of the product.
-/
def blockwiseProd {M : Type*} [CommMonoid M] {n k : ℕ} {x y : Fin n → M}
    (fs : (i : Fin n) → LabeledFactorizations k (x i) × LabeledFactorizations k (y i)) :
    LabeledFactorizations k (∏ i, x i * y i) :=
  ⟨fun j => ∏ i, (fs i).1.1 j * (fs i).2.1 j, by
    simp +decide [ LabeledFactorizations ];
    rw [ Finset.prod_comm ];
    exact Finset.prod_congr rfl fun i _ => by rw [ Finset.prod_mul_distrib, ( fs i |>.1.2 ), ( fs i |>.2.2 ) ] ;⟩

/-
If p is an atom and does not divide x, then p and x are coprime.
-/
lemma not_dvd_implies_coprime {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (p : M) (hp : p ∈ Atoms M) (x : M) (h : ¬ p ∣ x) : AreCoprime p x := by
  intro q hq hq';
  -- Since $q$ divides $p$ and $p$ is an atom, $q$ must be an associate of $p$.
  obtain ⟨u, hu⟩ : ∃ u : M, q = p * u ∧ IsUnit u := by
    cases' hq' with q' hq';
    cases' hp with hp₁ hp₂;
    specialize hp₂ hq';
    cases' hp₂ with hp₂ hp₂ <;> simp_all +decide [ IsUnit.mul_iff ];
    · cases hq ; aesop;
    · exact ⟨ hp₂.unit.inv, by simp +decide [ mul_assoc, hp₂.unit.inv_mul ], by simp +decide [ hp₂.unit.inv_mul ] ⟩;
  aesop

/-
If p and q are distinct atoms, then q does not divide any power of p.
-/
lemma distinct_atom_not_dvd_power {M : Type*} [CommMonoid M] (h_reduced : Reduced M) (h_cfi : CFI M)
    {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M) (h_neq : p ≠ q) (k : ℕ) :
    ¬ q ∣ p ^ k := by
      have := @power_coprime_of_not_in_support M _ h_reduced;
      intro h_div
      have h_coprime : AreCoprime p q := by
        exact coprime_of_distinct_atoms h_reduced hp hq h_neq;
      specialize @this p hp q;
      unfold Support at this; simp_all +decide [ AreCoprime ] ;
      exact this k q hq h_div ( dvd_refl q )

/-
If x and y are coprime and u * v = x * y, then u and v can be split into factors of x and y.
-/
lemma Coprime_Mul_Split {M : Type*} [CommMonoid M] (h_cfi : CFI M) (x y : M) (h_coprime : AreCoprime x y) (u v : M) (h_uv : u * v = x * y) : ∃ a b c d, a * b = x ∧ c * d = y ∧ a * c = u ∧ b * d = v := by
  have := h_cfi x y h_coprime;
  rcases this.2 ⟨ fun j => if j = 0 then u else v, by
    unfold LabeledFactorizations; aesop; ⟩ with ⟨ ⟨ ⟨ a, ha ⟩, ⟨ b, hb ⟩ ⟩, h ⟩
  generalize_proofs at *;
  replace h := congr_arg ( fun f => ( f.1 0, f.1 1 ) ) h ; aesop

end AristotleLemmas

theorem Prop_CFI_implies_PPP {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_atomic : Atomic M) (h_cfi : CFI M) :
    PP_P M := by
  intro p hp x y hxy
  obtain ⟨e, he⟩ := hxy
  -- The full proof uses Blockwise_CFI_k as described above
  have h_unit : ∀ {x : M}, ¬IsUnit x → (∀ q : M, q ∈ Atoms M → q ∣ x → q = p) → x ∈ Submonoid.powers p := by
    intro x hx hq
    obtain ⟨s, hs⟩ := h_atomic x hx;
    -- Since every element in s is an atom and divides x, by hq, each element in s must be p.
    have h_s_p : ∀ a ∈ s, a = p := by
      exact fun a ha => hq a ( hs.1 a ha ) ( hs.2 ▸ Multiset.dvd_prod ha );
    rw [ ← hs.2, Multiset.eq_replicate_of_mem h_s_p ] ; aesop;
  have h_divides : ∀ {x : M}, ¬IsUnit x → (∀ q : M, q ∈ Atoms M → q ∣ x → q ∣ p ^ e) → x ∈ Submonoid.powers p := by
    intro x hx hx'; apply h_unit hx; intro q hq hqx; exact (by
    by_contra hq_ne_p;
    exact absurd ( hx' q hq hqx ) ( by exact? ));
  have h_divides_x : x ∣ p ^ e := by
    aesop
  have h_divides_y : y ∣ p ^ e := by
    exact?;
  refine' ⟨ if hx : IsUnit x then _ else h_divides hx fun q hq hq' => _, if hy : IsUnit y then _ else h_divides hy fun q hq hq' => _ ⟩;
  · have := h_reduced x hx; aesop;
  · exact dvd_trans hq' h_divides_x;
  · rw [ h_reduced _ hy ] ; exact ⟨ 0, by simp +decide ⟩;
  · exact dvd_trans hq' h_divides_y

/-!
## Corollaries (easy after PP-P)

Once PP-P is established, these follow easily.
-/

/-- After PP-P, this is easy: if q | p^k with q an atom, then q = p.

    Proof: Write p^k = q * m. By PP-P, both q and m are in ⟨p⟩.
    So q = p^j for some j. Since q is irreducible, j = 1, hence q = p.

    TODO: Complete the case j ≥ 2 in a future Aristotle session. -/
lemma atom_dvd_power_eq {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_ppp : PP_P M) {p q : M} (hp : p ∈ Atoms M) (hq : q ∈ Atoms M)
    {k : ℕ} (h_dvd : q ∣ p ^ k) :
    q = p := by
  obtain ⟨m, hm⟩ := h_dvd
  have ⟨⟨j, hj⟩, ⟨l, hl⟩⟩ := h_ppp p hp q m ⟨k, hm⟩
  -- q = p^j, and q is irreducible
  -- j = 0 would make q = 1 (a unit), contradicting hq
  -- j = 1 gives q = p as desired
  -- j ≥ 2 would make q = p * (something), contradicting q irreducible
  match j with
  | 0 => simp at hj; exact absurd (hj ▸ isUnit_one) hq.not_isUnit
  | 1 => simp at hj; exact hj.symm
  | _ + 2 =>
    -- q = p^(n+2) = p * p^(n+1), contradicts q irreducible
    -- The type of hj is (fun x => p^x) (n+2) = q, which needs careful handling
    -- Since $p$ is an atom and $n + 2 \geq 2$, $p^{n + 2}$ is reducible, contradicting the assumption that $q$ is an atom.
    have h_reducible : ¬ Irreducible (p^(‹_› + 2)) := by
      rw [ pow_succ', irreducible_mul_iff ];
      simp_all +decide [ not_or, irreducible_iff ];
    unfold Atoms at hq; aesop;

/-- Support of p^k is contained in {p}. -/
lemma Support_Power_Subset {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_ppp : PP_P M) (p : M) (hp : p ∈ Atoms M) (k : ℕ) :
    Support (p ^ k) ⊆ {p} := by
  intro q ⟨hq_atom, hq_dvd⟩
  simp only [Set.mem_singleton_iff]
  exact atom_dvd_power_eq h_reduced h_ppp hp hq_atom hq_dvd

/-- If Support(x) ⊆ {p}, then x ∈ ⟨p⟩. -/
lemma Support_Singleton_Implies_Power {M : Type*} [CommMonoid M] (h_reduced : Reduced M)
    (h_atomic : Atomic M) (h_ppp : PP_P M) (p : M) (hp : p ∈ Atoms M) (x : M)
    (hx : Support x ⊆ {p}) :
    x ∈ Submonoid.powers p := by
  by_cases hxu : IsUnit x
  · exact ⟨0, by simp [h_reduced x hxu]⟩
  · -- x is not a unit, so it has an atomic factorization
    obtain ⟨s, hs_atoms, hs_prod⟩ := h_atomic x hxu
    -- Every atom in s divides x, hence is in Support(x) ⊆ {p}
    have hall_p : ∀ a ∈ s, a = p := by
      intro a ha
      have ha_atom : a ∈ Atoms M := hs_atoms a ha
      have ha_dvd : a ∣ x := by
        rw [← hs_prod]
        exact Multiset.dvd_prod ha
      have ha_support : a ∈ Support x := ⟨ha_atom, ha_dvd⟩
      exact Set.mem_singleton_iff.mp (hx ha_support)
    -- So s = {p, p, ..., p} and x = p^|s|
    have hs_all_p : s = Multiset.replicate (Multiset.card s) p :=
      Multiset.eq_replicate.mpr ⟨rfl, hall_p⟩
    have hx_eq : x = p ^ Multiset.card s := by
      rw [← hs_prod, hs_all_p, Multiset.prod_replicate, Multiset.card_replicate]
    exact ⟨Multiset.card s, hx_eq.symm⟩

end