/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 334e5fd4-5943-44ec-b08a-20d67c436539

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma atoms_eq : Atoms CFIFailMonoid =
    {atomP, atomQ, atomU, atomV} ∪ Set.range atomR

- theorem cfifail_atomic : Atomic CFIFailMonoid

- theorem cfifail_CPL : CPL CFIFailMonoid

- theorem cfifail_not_CFI : ¬CFI CFIFailMonoid

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2024 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Example 5: CFI Failure Monoid (Failure of CFI only)

This file formalizes Example 10.3 from Section 10 of the paper,
demonstrating that CFI is independent of the other three axioms.

The construction uses 4 special atoms p, q, u, v with the relation pq = uv,
plus infinitely many additional atoms r₀, r₁, r₂, ... for CPL.

We use a normalized representation where pq pairs are always reduced to uv.

## Main Results

- `CFIFailMonoid`: The monoid structure with relation pq = uv
- `cfifail_reduced`: The monoid is reduced
- `cfifail_atomic`: The monoid is atomic
- `cfifail_APD`: The monoid satisfies APD
- `cfifail_PPD`: The monoid satisfies PP-D
- `cfifail_CPL`: The monoid satisfies CPL
- `cfifail_not_CFI`: The monoid does NOT satisfy CFI
-/

import MultiplicationProject.Basic


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

open scoped Classical

set_option maxHeartbeats 0

noncomputable section

/-!
## The CFI Failure Monoid Structure

Elements are represented by exponent tuples (exp_p, exp_q, exp_u, exp_v, others)
with the normalization constraint: at most one of exp_p, exp_q is positive.

This captures the quotient of the free commutative monoid by pq = uv:
when we would have both p and q present, we reduce pq → uv.
-/

/-- The CFI failure monoid: 4 special atoms p, q, u, v with pq = uv,
    plus infinitely many regular atoms r_i indexed by ℕ. -/
structure CFIFailMonoid where
  exp_p : ℕ         -- exponent of atom p
  exp_q : ℕ         -- exponent of atom q
  exp_u : ℕ         -- exponent of atom u
  exp_v : ℕ         -- exponent of atom v
  others : ℕ →₀ ℕ   -- exponents of regular atoms r₀, r₁, ...
  normalized : exp_p = 0 ∨ exp_q = 0
  deriving DecidableEq

namespace CFIFailMonoid

/-- Extensionality for CFIFailMonoid. -/
@[ext]
lemma ext {x y : CFIFailMonoid}
    (hp : x.exp_p = y.exp_p) (hq : x.exp_q = y.exp_q)
    (hu : x.exp_u = y.exp_u) (hv : x.exp_v = y.exp_v)
    (ho : x.others = y.others) : x = y := by
  cases x; cases y; simp at hp hq hu hv ho ⊢; exact ⟨hp, hq, hu, hv, ho⟩

/-- The identity element. -/
protected def one : CFIFailMonoid where
  exp_p := 0
  exp_q := 0
  exp_u := 0
  exp_v := 0
  others := 0
  normalized := Or.inl rfl

/-- Multiplication with normalization: reduce pq → uv. -/
protected def mul (x y : CFIFailMonoid) : CFIFailMonoid where
  exp_p := x.exp_p + y.exp_p - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q)
  exp_q := x.exp_q + y.exp_q - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q)
  exp_u := x.exp_u + y.exp_u + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q)
  exp_v := x.exp_v + y.exp_v + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q)
  others := x.others + y.others
  normalized := by
    -- After subtracting min from both, at least one becomes 0
    by_cases h : x.exp_p + y.exp_p ≤ x.exp_q + y.exp_q
    · left; simp [Nat.min_eq_left h]
    · right; push_neg at h; simp [Nat.min_eq_right (le_of_lt h)]

instance : One CFIFailMonoid := ⟨CFIFailMonoid.one⟩

instance : Mul CFIFailMonoid := ⟨CFIFailMonoid.mul⟩

@[simp]
lemma one_exp_p : (1 : CFIFailMonoid).exp_p = 0 := rfl

@[simp]
lemma one_exp_q : (1 : CFIFailMonoid).exp_q = 0 := rfl

@[simp]
lemma one_exp_u : (1 : CFIFailMonoid).exp_u = 0 := rfl

@[simp]
lemma one_exp_v : (1 : CFIFailMonoid).exp_v = 0 := rfl

@[simp]
lemma one_others : (1 : CFIFailMonoid).others = 0 := rfl

@[simp]
lemma mul_exp_p (x y : CFIFailMonoid) :
    (x * y).exp_p = x.exp_p + y.exp_p - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) := rfl

@[simp]
lemma mul_exp_q (x y : CFIFailMonoid) :
    (x * y).exp_q = x.exp_q + y.exp_q - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) := rfl

@[simp]
lemma mul_exp_u (x y : CFIFailMonoid) :
    (x * y).exp_u = x.exp_u + y.exp_u + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) := rfl

@[simp]
lemma mul_exp_v (x y : CFIFailMonoid) :
    (x * y).exp_v = x.exp_v + y.exp_v + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) := rfl

@[simp]
lemma mul_others (x y : CFIFailMonoid) : (x * y).others = x.others + y.others := rfl

/-- Helper lemma: If a + b = 0 (as Finsupp), then a = 0 and b = 0. -/
private lemma finsupp_add_eq_zero {a b : ℕ →₀ ℕ} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  have h1 : ∀ i, a i + b i = 0 := fun i => by
    have := Finsupp.ext_iff.mp h i
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at this
    exact this
  constructor <;> (ext i; simp only [Finsupp.zero_apply]; have := h1 i; omega)

/-- The CFI failure monoid is a commutative monoid. -/
instance : CommMonoid CFIFailMonoid where
  mul := (· * ·)
  mul_assoc := by
    intros a b c
    -- Key insight: the total "reduction" from pq→uv is min(P_total, Q_total)
    -- where P_total = a.exp_p + b.exp_p + c.exp_p, Q_total = a.exp_q + b.exp_q + c.exp_q
    -- This is the same regardless of association order.
    let ap := a.exp_p; let aq := a.exp_q; let au := a.exp_u; let av := a.exp_v
    let bp := b.exp_p; let bq := b.exp_q; let bu := b.exp_u; let bv := b.exp_v
    let cp := c.exp_p; let cq := c.exp_q; let cu := c.exp_u; let cv := c.exp_v
    let P := ap + bp + cp  -- total p-exponent
    let Q := aq + bq + cq  -- total q-exponent
    -- For (a*b)*c: first min is min(ap+bp, aq+bq), then second min
    -- For a*(b*c): first min is min(bp+cp, bq+cq), then second min
    -- In both cases, total reduction = min(P, Q)
    ext
    all_goals simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others]
    -- exp_p: both sides equal max(P - Q, 0) = P - min(P, Q)
    · by_cases h1 : ap + bp ≤ aq + bq <;>
      by_cases h2 : bp + cp ≤ bq + cq <;>
      simp only [Nat.min_eq_left, Nat.min_eq_right, *] at * <;>
      omega
    -- exp_q: both sides equal max(Q - P, 0) = Q - min(P, Q)
    · by_cases h1 : ap + bp ≤ aq + bq <;>
      by_cases h2 : bp + cp ≤ bq + cq <;>
      simp only [Nat.min_eq_left, Nat.min_eq_right, *] at * <;>
      omega
    -- exp_u: both sides equal au + bu + cu + min(P, Q)
    · by_cases h1 : ap + bp ≤ aq + bq <;>
      by_cases h2 : bp + cp ≤ bq + cq <;>
      simp only [Nat.min_eq_left, Nat.min_eq_right, *] at * <;>
      omega
    -- exp_v: both sides equal av + bv + cv + min(P, Q)
    · by_cases h1 : ap + bp ≤ aq + bq <;>
      by_cases h2 : bp + cp ≤ bq + cq <;>
      simp only [Nat.min_eq_left, Nat.min_eq_right, *] at * <;>
      omega
    -- others: straightforward addition associativity
    · exact add_assoc _ _ _
  one := 1
  one_mul := by
    intro a
    have ha := a.normalized
    ext
    all_goals simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others,
                         one_exp_p, one_exp_q, one_exp_u, one_exp_v, one_others,
                         zero_add, add_zero]
    all_goals rcases ha with ha | ha <;> simp [ha]
  mul_one := by
    intro a
    have ha := a.normalized
    ext
    all_goals simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others,
                         one_exp_p, one_exp_q, one_exp_u, one_exp_v, one_others,
                         zero_add, add_zero]
    all_goals rcases ha with ha | ha <;> simp [ha]
  mul_comm := by
    intros a b
    ext
    all_goals simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others]
    · omega  -- exp_p
    · omega  -- exp_q
    · omega  -- exp_u
    · omega  -- exp_v
    · exact add_comm _ _

-- others

/-!
## Special Elements (Atoms)
-/

/-- Atom p: has exp_p = 1, all others 0. -/
def atomP : CFIFailMonoid where
  exp_p := 1
  exp_q := 0
  exp_u := 0
  exp_v := 0
  others := 0
  normalized := Or.inr rfl

/-- Atom q: has exp_q = 1, all others 0. -/
def atomQ : CFIFailMonoid where
  exp_p := 0
  exp_q := 1
  exp_u := 0
  exp_v := 0
  others := 0
  normalized := Or.inl rfl

/-- Atom u: has exp_u = 1, all others 0. -/
def atomU : CFIFailMonoid where
  exp_p := 0
  exp_q := 0
  exp_u := 1
  exp_v := 0
  others := 0
  normalized := Or.inl rfl

/-- Atom v: has exp_v = 1, all others 0. -/
def atomV : CFIFailMonoid where
  exp_p := 0
  exp_q := 0
  exp_u := 0
  exp_v := 1
  others := 0
  normalized := Or.inl rfl

/-- Regular atom r_i: has others(i) = 1, all others 0. -/
def atomR (i : ℕ) : CFIFailMonoid where
  exp_p := 0
  exp_q := 0
  exp_u := 0
  exp_v := 0
  others := Finsupp.single i 1
  normalized := Or.inl rfl

@[simp] lemma atomP_exp_p : atomP.exp_p = 1 := rfl

@[simp] lemma atomP_exp_q : atomP.exp_q = 0 := rfl

@[simp] lemma atomP_exp_u : atomP.exp_u = 0 := rfl

@[simp] lemma atomP_exp_v : atomP.exp_v = 0 := rfl

@[simp] lemma atomP_others : atomP.others = 0 := rfl

@[simp] lemma atomQ_exp_p : atomQ.exp_p = 0 := rfl

@[simp] lemma atomQ_exp_q : atomQ.exp_q = 1 := rfl

@[simp] lemma atomQ_exp_u : atomQ.exp_u = 0 := rfl

@[simp] lemma atomQ_exp_v : atomQ.exp_v = 0 := rfl

@[simp] lemma atomQ_others : atomQ.others = 0 := rfl

@[simp] lemma atomU_exp_p : atomU.exp_p = 0 := rfl

@[simp] lemma atomU_exp_q : atomU.exp_q = 0 := rfl

@[simp] lemma atomU_exp_u : atomU.exp_u = 1 := rfl

@[simp] lemma atomU_exp_v : atomU.exp_v = 0 := rfl

@[simp] lemma atomU_others : atomU.others = 0 := rfl

@[simp] lemma atomV_exp_p : atomV.exp_p = 0 := rfl

@[simp] lemma atomV_exp_q : atomV.exp_q = 0 := rfl

@[simp] lemma atomV_exp_u : atomV.exp_u = 0 := rfl

@[simp] lemma atomV_exp_v : atomV.exp_v = 1 := rfl

@[simp] lemma atomV_others : atomV.others = 0 := rfl

@[simp] lemma atomR_exp_p (i : ℕ) : (atomR i).exp_p = 0 := rfl

@[simp] lemma atomR_exp_q (i : ℕ) : (atomR i).exp_q = 0 := rfl

@[simp] lemma atomR_exp_u (i : ℕ) : (atomR i).exp_u = 0 := rfl

@[simp] lemma atomR_exp_v (i : ℕ) : (atomR i).exp_v = 0 := rfl

@[simp] lemma atomR_others (i : ℕ) : (atomR i).others = Finsupp.single i 1 := rfl

/-- The key relation: p * q = u * v. -/
theorem atomP_mul_atomQ : atomP * atomQ = atomU * atomV := by
  ext <;> simp

/-!
## Units and Reducedness
-/

/-- x * y = 1 implies x = 1 and y = 1. -/
lemma mul_eq_one_iff (x y : CFIFailMonoid) : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro h
    have hp : (x * y).exp_p = 0 := by rw [h]; rfl
    have hq : (x * y).exp_q = 0 := by rw [h]; rfl
    have hu : (x * y).exp_u = 0 := by rw [h]; rfl
    have hv : (x * y).exp_v = 0 := by rw [h]; rfl
    have ho : (x * y).others = 0 := by rw [h]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    have hxp : x.exp_p = 0 := by omega
    have hyp : y.exp_p = 0 := by omega
    have hxq : x.exp_q = 0 := by omega
    have hyq : y.exp_q = 0 := by omega
    have hxu : x.exp_u = 0 := by omega
    have hyu : y.exp_u = 0 := by omega
    have hxv : x.exp_v = 0 := by omega
    have hyv : y.exp_v = 0 := by omega
    obtain ⟨hxo, hyo⟩ := finsupp_add_eq_zero ho
    constructor
    · ext <;> simp [hxp, hxq, hxu, hxv, hxo]
    · ext <;> simp [hyp, hyq, hyu, hyv, hyo]
  · intro ⟨hx, hy⟩
    rw [hx, hy, mul_one]

/-- Only 1 is a unit. -/
lemma isUnit_iff (x : CFIFailMonoid) : IsUnit x ↔ x = 1 := by
  constructor
  · intro ⟨u, hu⟩
    have h := u.val_inv
    have h' : x * u.inv = 1 := by rw [← hu]; exact h
    exact (mul_eq_one_iff x u.inv).mp h' |>.1
  · intro hx
    rw [hx]
    exact isUnit_one

/-- The CFI failure monoid is reduced. -/
theorem cfifail_reduced : Reduced CFIFailMonoid := by
  intro x hx
  exact (isUnit_iff x).mp hx

/-!
## Irreducibility of Atoms
-/

/-- atomP is not a unit. -/
lemma atomP_not_unit : ¬IsUnit atomP := by
  rw [isUnit_iff]
  intro h
  have := congr_arg CFIFailMonoid.exp_p h
  simp at this

/-- atomQ is not a unit. -/
lemma atomQ_not_unit : ¬IsUnit atomQ := by
  rw [isUnit_iff]
  intro h
  have := congr_arg CFIFailMonoid.exp_q h
  simp at this

/-- atomU is not a unit. -/
lemma atomU_not_unit : ¬IsUnit atomU := by
  rw [isUnit_iff]
  intro h
  have := congr_arg CFIFailMonoid.exp_u h
  simp at this

/-- atomV is not a unit. -/
lemma atomV_not_unit : ¬IsUnit atomV := by
  rw [isUnit_iff]
  intro h
  have := congr_arg CFIFailMonoid.exp_v h
  simp at this

/-- atomR i is not a unit. -/
lemma atomR_not_unit (i : ℕ) : ¬IsUnit (atomR i) := by
  rw [isUnit_iff]
  intro h
  have := congr_arg CFIFailMonoid.others h
  simp only [atomR_others, one_others] at this
  have := Finsupp.ext_iff.mp this i
  simp at this

/-- atomP is irreducible. -/
lemma atomP_irreducible : Irreducible atomP := by
  constructor
  · exact atomP_not_unit
  · intros a b hab
    have hp : (a * b).exp_p = 1 := by rw [← hab]; rfl
    have hq : (a * b).exp_q = 0 := by rw [← hab]; rfl
    have hu : (a * b).exp_u = 0 := by rw [← hab]; rfl
    have hv : (a * b).exp_v = 0 := by rw [← hab]; rfl
    have ho : (a * b).others = 0 := by rw [← hab]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    -- From the constraints, we can deduce that one of a, b is 1
    have haq : a.exp_q = 0 := by omega
    have hbq : b.exp_q = 0 := by omega
    have hau : a.exp_u = 0 := by omega
    have hbu : b.exp_u = 0 := by omega
    have hav : a.exp_v = 0 := by omega
    have hbv : b.exp_v = 0 := by omega
    obtain ⟨hao, hbo⟩ := finsupp_add_eq_zero ho
    -- Since exp_q = 0 for both, min is 0, so exp_p adds directly
    have hmin : min (a.exp_p + b.exp_p) (a.exp_q + b.exp_q) = 0 := by simp [haq, hbq]
    rw [hmin] at hp
    simp at hp
    -- So a.exp_p + b.exp_p = 1, meaning one is 0 and one is 1
    have h_bound : a.exp_p ≤ 1 := by omega
    interval_cases hap : a.exp_p
    · -- a.exp_p = 0, so a = 1
      left
      rw [isUnit_iff]
      ext <;> simp [hap, haq, hau, hav, hao]
    · -- a.exp_p = 1, so b.exp_p = 0 and b = 1
      right
      rw [isUnit_iff]
      have hbp : b.exp_p = 0 := by omega
      ext <;> simp [hbp, hbq, hbu, hbv, hbo]

/-- atomQ is irreducible. -/
lemma atomQ_irreducible : Irreducible atomQ := by
  constructor
  · exact atomQ_not_unit
  · intros a b hab
    have hp : (a * b).exp_p = 0 := by rw [← hab]; rfl
    have hq : (a * b).exp_q = 1 := by rw [← hab]; rfl
    have hu : (a * b).exp_u = 0 := by rw [← hab]; rfl
    have hv : (a * b).exp_v = 0 := by rw [← hab]; rfl
    have ho : (a * b).others = 0 := by rw [← hab]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    have hap : a.exp_p = 0 := by omega
    have hbp : b.exp_p = 0 := by omega
    have hau : a.exp_u = 0 := by omega
    have hbu : b.exp_u = 0 := by omega
    have hav : a.exp_v = 0 := by omega
    have hbv : b.exp_v = 0 := by omega
    obtain ⟨hao, hbo⟩ := finsupp_add_eq_zero ho
    have hmin : min (a.exp_p + b.exp_p) (a.exp_q + b.exp_q) = 0 := by simp [hap, hbp]
    rw [hmin] at hq
    simp at hq
    have h_bound : a.exp_q ≤ 1 := by omega
    interval_cases haq : a.exp_q
    · left; rw [isUnit_iff]; ext <;> simp [hap, haq, hau, hav, hao]
    · right; rw [isUnit_iff]
      have hbq : b.exp_q = 0 := by omega
      ext <;> simp [hbp, hbq, hbu, hbv, hbo]

/-- atomU is irreducible. -/
lemma atomU_irreducible : Irreducible atomU := by
  constructor
  · exact atomU_not_unit
  · intros a b hab
    have hp : (a * b).exp_p = 0 := by rw [← hab]; rfl
    have hq : (a * b).exp_q = 0 := by rw [← hab]; rfl
    have hu : (a * b).exp_u = 1 := by rw [← hab]; rfl
    have hv : (a * b).exp_v = 0 := by rw [← hab]; rfl
    have ho : (a * b).others = 0 := by rw [← hab]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    -- From hp and hq, deduce exp_p and exp_q info
    have hap : a.exp_p = 0 := by omega
    have hbp : b.exp_p = 0 := by omega
    have haq : a.exp_q = 0 := by omega
    have hbq : b.exp_q = 0 := by omega
    have hav : a.exp_v = 0 := by omega
    have hbv : b.exp_v = 0 := by omega
    obtain ⟨hao, hbo⟩ := finsupp_add_eq_zero ho
    have hmin : min (a.exp_p + b.exp_p) (a.exp_q + b.exp_q) = 0 := by simp [hap, hbp]
    rw [hmin] at hu
    simp at hu
    have h_bound : a.exp_u ≤ 1 := by omega
    interval_cases hau : a.exp_u
    · left; rw [isUnit_iff]; ext <;> simp [hap, haq, hau, hav, hao]
    · right; rw [isUnit_iff]
      have hbu : b.exp_u = 0 := by omega
      ext <;> simp [hbp, hbq, hbu, hbv, hbo]

/-- atomV is irreducible. -/
lemma atomV_irreducible : Irreducible atomV := by
  constructor
  · exact atomV_not_unit
  · intros a b hab
    have hp : (a * b).exp_p = 0 := by rw [← hab]; rfl
    have hq : (a * b).exp_q = 0 := by rw [← hab]; rfl
    have hu : (a * b).exp_u = 0 := by rw [← hab]; rfl
    have hv : (a * b).exp_v = 1 := by rw [← hab]; rfl
    have ho : (a * b).others = 0 := by rw [← hab]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    have hap : a.exp_p = 0 := by omega
    have hbp : b.exp_p = 0 := by omega
    have haq : a.exp_q = 0 := by omega
    have hbq : b.exp_q = 0 := by omega
    have hau : a.exp_u = 0 := by omega
    have hbu : b.exp_u = 0 := by omega
    obtain ⟨hao, hbo⟩ := finsupp_add_eq_zero ho
    have hmin : min (a.exp_p + b.exp_p) (a.exp_q + b.exp_q) = 0 := by simp [hap, hbp]
    rw [hmin] at hv
    simp at hv
    have h_bound : a.exp_v ≤ 1 := by omega
    interval_cases hav : a.exp_v
    · left; rw [isUnit_iff]; ext <;> simp [hap, haq, hau, hav, hao]
    · right; rw [isUnit_iff]
      have hbv : b.exp_v = 0 := by omega
      ext <;> simp [hbp, hbq, hbu, hbv, hbo]

/-- atomR i is irreducible. -/
lemma atomR_irreducible (i : ℕ) : Irreducible (atomR i) := by
  constructor
  · exact atomR_not_unit i
  · intros a b hab
    have hp : (a * b).exp_p = 0 := by rw [← hab]; rfl
    have hq : (a * b).exp_q = 0 := by rw [← hab]; rfl
    have hu : (a * b).exp_u = 0 := by rw [← hab]; rfl
    have hv : (a * b).exp_v = 0 := by rw [← hab]; rfl
    have ho : (a * b).others = Finsupp.single i 1 := by rw [← hab]; rfl
    simp only [mul_exp_p, mul_exp_q, mul_exp_u, mul_exp_v, mul_others] at hp hq hu hv ho
    have hap : a.exp_p = 0 := by omega
    have hbp : b.exp_p = 0 := by omega
    have haq : a.exp_q = 0 := by omega
    have hbq : b.exp_q = 0 := by omega
    have hau : a.exp_u = 0 := by omega
    have hbu : b.exp_u = 0 := by omega
    have hav : a.exp_v = 0 := by omega
    have hbv : b.exp_v = 0 := by omega
    -- For others, we have a.others + b.others = single i 1
    have hsum : a.others i + b.others i = 1 := by
      have := Finsupp.ext_iff.mp ho i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      exact this
    have hother_j : ∀ j ≠ i, a.others j = 0 ∧ b.others j = 0 := by
      intro j hj
      have := Finsupp.ext_iff.mp ho j
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hj] at this
      omega
    have h_bound : a.others i ≤ 1 := by omega
    interval_cases hai : a.others i
    · -- a.others i = 0
      left; rw [isUnit_iff]
      have hao : a.others = 0 := by
        ext j; simp only [Finsupp.zero_apply]; by_cases hj : j = i
        · simp [hj, hai]
        · exact (hother_j j hj).1
      ext <;> simp [hap, haq, hau, hav, hao]
    · -- a.others i = 1
      right; rw [isUnit_iff]
      have hbo : b.others = 0 := by
        ext j; simp only [Finsupp.zero_apply]; by_cases hj : j = i
        · simp [hj]; omega
        · exact (hother_j j hj).2
      ext <;> simp [hbp, hbq, hbu, hbv, hbo]

/-!
## Power Lemmas
-/

/-- Powers of atomP. -/
lemma pow_atomP (e : ℕ) : atomP ^ e = ⟨e, 0, 0, 0, 0, Or.inr rfl⟩ := by
  induction e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp

/-- Powers of atomQ. -/
lemma pow_atomQ (e : ℕ) : atomQ ^ e = ⟨0, e, 0, 0, 0, Or.inl rfl⟩ := by
  induction e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp

/-- Powers of atomU. -/
lemma pow_atomU (e : ℕ) : atomU ^ e = ⟨0, 0, e, 0, 0, Or.inl rfl⟩ := by
  induction e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp

/-- Powers of atomV. -/
lemma pow_atomV (e : ℕ) : atomV ^ e = ⟨0, 0, 0, e, 0, Or.inl rfl⟩ := by
  induction e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp

/-- Powers of atomR i. -/
lemma pow_atomR (i e : ℕ) : (atomR i) ^ e = ⟨0, 0, 0, 0, Finsupp.single i e, Or.inl rfl⟩ := by
  induction e with
  | zero =>
    simp only [pow_zero, Finsupp.single_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext <;> simp [Finsupp.single_add]

/-!
## Atoms Characterization
-/

/- The set of atoms is exactly {atomP, atomQ, atomU, atomV} ∪ {atomR i | i ∈ ℕ}. -/
noncomputable section AristotleLemmas

/-
The degree of an element is the sum of all its exponents.
-/
def CFIFailMonoid.degree (x : CFIFailMonoid) : ℕ :=
  x.exp_p + x.exp_q + x.exp_u + x.exp_v + x.others.sum (fun _ n => n)

lemma CFIFailMonoid.degree_mul (x y : CFIFailMonoid) :
    CFIFailMonoid.degree (x * y) = CFIFailMonoid.degree x + CFIFailMonoid.degree y := by
      simp +decide [ CFIFailMonoid.degree ];
      rw [ Finsupp.sum_add_index' ] <;> simp +decide [ add_assoc, add_tsub_assoc_of_le ];
      cases min_cases ( x.exp_p + y.exp_p ) ( x.exp_q + y.exp_q ) <;> omega

@[simp]
lemma CFIFailMonoid.degree_one : CFIFailMonoid.degree 1 = 0 := by
  decide +revert

lemma CFIFailMonoid.degree_eq_zero_iff (x : CFIFailMonoid) : CFIFailMonoid.degree x = 0 ↔ x = 1 := by
  constructor;
  · unfold CFIFailMonoid.CFIFailMonoid.degree;
    simp +zetaDelta at *;
    intro hp hq hu hv hsum
    have hOthers : x.others = 0 := by
      rw [ Finsupp.sum ] at hsum ; aesop;
    cases x ; aesop;
  · exact fun h => h.symm ▸ rfl

lemma CFIFailMonoid.degree_eq_one_iff_mem_standard (x : CFIFailMonoid) :
    CFIFailMonoid.degree x = 1 ↔ x ∈ ({atomP, atomQ, atomU, atomV} : Set CFIFailMonoid) ∪ Set.range atomR := by
      -- Suppose x has degree 1. Then, by definition of degree, the sum of its exponents is 1.
      apply Iff.intro
      intro hx_degree
      have hx_form : x.exp_p + x.exp_q + x.exp_u + x.exp_v + Finsupp.sum x.others (fun _ x => x) = 1 := by
        exact hx_degree;
      · rcases x with ⟨ a, b, c, d, e, he ⟩ ; rcases e with ⟨ f, hf ⟩ ; simp_all +decide [ Finsupp.sum_fintype ] ;
        rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> rcases c with ( _ | c ) <;> rcases d with ( _ | d ) <;> simp_all +arith +decide only;
        · -- Since $f$ is a finite set and $hf$ is a function from $ℕ$ to $ℕ$, the sum of $hf$ over $f$ being 1 implies that there is exactly one element in $f$ where $hf$ is 1.
          obtain ⟨x, hx⟩ : ∃ x ∈ f, hf x = 1 ∧ ∀ y ∈ f, y ≠ x → hf y = 0 := by
            obtain ⟨x, hx⟩ : ∃ x ∈ f, hf x ≠ 0 := by
              contrapose! hx_degree; simp_all +decide [ Finsupp.sum ] ;
            have h_unique : ∀ y ∈ f, y ≠ x → hf y = 0 := by
              intro y hy hyx; contrapose! hx_form; simp_all +decide [ Finsupp.sum ] ;
              rw [ Finset.sum_eq_add_sum_diff_singleton ( show x ∈ f from by aesop ) ] ; exact ne_of_gt ( lt_add_of_le_of_pos ( Nat.one_le_iff_ne_zero.mpr hx ) ( Finset.sum_pos ( fun z hz => Nat.pos_of_ne_zero ( by aesop ) ) ⟨ y, by aesop ⟩ ) ) ;
            simp_all +decide [ Finsupp.sum ];
            rw [ Finset.sum_eq_single x ] at hx_form <;> aesop;
          refine Or.inr ⟨ x, ?_ ⟩ ; ext <;> simp +decide [ hx ];
          by_cases h : ‹_› = x <;> simp +decide [ *, Finsupp.single_apply ];
          grind +ring;
        · cases d <;> simp_all +decide [ Finsupp.sum ];
          exact Or.inl <| Or.inr <| Or.inr <| Or.inr <| by ext <;> simp +decide [ hx_form ] ;
        · cases c <;> simp_all +decide [ Finsupp.sum ];
          exact Or.inl <| Or.inr <| Or.inr <| Or.inl <| by ext <;> simp +decide [ hx_form ] ;
        · cases b <;> simp_all +arith +decide [ Finsupp.sum ];
          exact Or.inl <| Or.inr <| Or.inl <| by ext <;> simp +decide [ hx_form ] ;
        · cases a <;> simp_all +arith +decide [ Finsupp.sum ];
          exact Or.inl <| Or.inl <| by congr <;> aesop;
      · unfold CFIFailMonoid.CFIFailMonoid.degree; aesop;

lemma CFIFailMonoid.irreducible_implies_degree_eq_one (x : CFIFailMonoid) (hx : Irreducible x) :
    CFIFailMonoid.degree x = 1 := by
      -- If x.exp_p > 0, then x can be written as atomP * y, where y is x with exp_p decreased by 1.
      by_cases hx_p : x.exp_p > 0;
      · -- Let y be x with exp_p decreased by 1.
        obtain ⟨y, hy⟩ : ∃ y : CFIFailMonoid, x = atomP * y := by
          use ⟨x.exp_p - 1, x.exp_q, x.exp_u, x.exp_v, x.others, by
            cases x.normalized <;> omega⟩
          generalize_proofs at *;
          rcases x with ⟨ _ | _, _ | _, _ | _, _ | _, _, _ ⟩ <;> norm_num at *;
          all_goals ext <;> simp +decide [ CFIFailMonoid.atomP, CFIFailMonoid.mul ];
          all_goals omega;
        -- Since x is irreducible, y must be a unit.
        have hy_unit : IsUnit y := by
          simp_all +decide [ irreducible_mul_iff ];
          exact hx.resolve_right ( by simp [ CFIFailMonoid.atomP_not_unit ] ) |>.2;
        -- Since y is a unit, y must be 1.
        have hy_one : y = 1 := by
          exact?;
        aesop;
      · by_cases hx_q : x.exp_q > 0;
        · -- If x.exp_q > 0, then x can be written as atomQ * y, where y is x with exp_q decreased by 1.
          obtain ⟨y, hy⟩ : ∃ y : CFIFailMonoid, x = atomQ * y := by
            use ⟨0, x.exp_q - 1, x.exp_u, x.exp_v, x.others, by
              exact Or.inl rfl⟩
            generalize_proofs at *;
            ext <;> simp +decide [ *, Nat.sub_add_cancel hx_q ];
            · grind;
            · rw [ add_tsub_cancel_of_le hx_q.nat_succ_le ];
          simp_all +decide [ irreducible_mul_iff ];
          cases hx <;> simp_all +decide [ CFIFailMonoid.isUnit_iff ];
        · by_cases hx_u : x.exp_u > 0 <;> by_cases hx_v : x.exp_v > 0 <;> simp_all +decide [ CFIFailMonoid.degree ];
          · have := hx.2;
            contrapose! this;
            refine' ⟨ ⟨ 0, 0, 1, 0, 0, by simp +decide ⟩, ⟨ 0, 0, x.exp_u - 1, x.exp_v, x.others, by simp +decide ⟩, _, _, _ ⟩ <;> simp_all +decide [ isUnit_iff_exists_inv ];
            · ext <;> simp +decide [ hx_p, hx_q, hx_u, hx_v ];
              rw [ add_tsub_cancel_of_le hx_u.nat_succ_le ];
            · intro y hy; have := congr_arg ( fun z => z.exp_u ) hy; simp +decide at this;
            · intro y hy; have := congr_arg ( fun z => z.exp_u ) hy; norm_num at this;
              have := congr_arg ( fun z => z.exp_v ) hy; norm_num at this;
              linarith;
          · -- If x.exp_u > 0, then x can be written as atomU * y, where y is x with exp_u decreased by 1.
            obtain ⟨y, hy⟩ : ∃ y : CFIFailMonoid, x = atomU * y := by
              use ⟨x.exp_p, x.exp_q, x.exp_u - 1, x.exp_v, x.others, by
                exact Or.inl hx_p⟩
              generalize_proofs at *;
              ext <;> simp +decide [ *, Nat.sub_add_cancel hx_u ];
              rw [ add_tsub_cancel_of_le hx_u.nat_succ_le ];
            simp_all +decide [ irreducible_mul_iff ];
            cases hx <;> simp_all +decide [ isUnit_iff_exists_inv ];
            · rename_i h; obtain ⟨ b, hb ⟩ := h.2; have := congr_arg CFIFailMonoid.degree hb; norm_num [ CFIFailMonoid.degree_mul ] at this;
              unfold CFIFailMonoid.degree at this; aesop;
            · rename_i h; obtain ⟨ b, hb ⟩ := h.2; replace hb := congr_arg ( fun z => z.exp_u ) hb; simp_all +decide ;
          · have := hx.2;
            contrapose! this;
            refine' ⟨ ⟨ 0, 0, 0, 1, 0, Or.inl rfl ⟩, ⟨ 0, 0, 0, x.exp_v - 1, x.others, Or.inl rfl ⟩, _, _, _ ⟩ <;> simp_all +decide [ isUnit_iff_exists_inv ];
            · ext <;> simp +decide [ hx_p, hx_q, hx_u, hx_v ];
              rw [ add_tsub_cancel_of_le hx_v.nat_succ_le ];
            · intro y hy; have := congr_arg ( fun z => z.exp_v ) hy; simp +decide at this;
            · intro y hy; have := congr_arg ( fun z => z.exp_v ) hy; simp +decide at this;
              rcases x_v : x.exp_v with ( _ | _ | x_v ) <;> simp_all +decide;
              replace hy := congr_arg ( fun z => z.others ) hy ; simp_all +decide [ Finsupp.single_apply ];
          · -- Since $x$ is irreducible and its degree is greater than 1, there must be some $i$ such that $x.others i > 0$.
            obtain ⟨i, hi⟩ : ∃ i, x.others i > 0 := by
              by_cases h_others_zero : x.others = 0;
              · exact absurd ( hx.not_isUnit ) ( by rw [ show x = 1 from by cases x; aesop ] ; simp +decide );
              · exact not_forall_not.mp fun h => h_others_zero <| Finsupp.ext fun i => Nat.eq_zero_of_not_pos <| h i;
            -- Since $x$ is irreducible and its degree is greater than 1, we can write $x$ as $atomR i * y$ for some $y$.
            obtain ⟨y, hy⟩ : ∃ y : CFIFailMonoid, x = atomR i * y := by
              use ⟨x.exp_p, x.exp_q, x.exp_u, x.exp_v, x.others - Finsupp.single i 1, by
                exact Or.inl hx_p⟩
              generalize_proofs at *;
              ext <;> simp +decide [ *, mul_comm ];
              rw [ Finsupp.single_apply, add_tsub_cancel_of_le ] ; aesop;
            cases hx.2 hy <;> simp_all +decide [ CFIFailMonoid.atomR ];
            · rename_i h; have := h.exists_left_inv; obtain ⟨ z, hz ⟩ := this; replace hz := congr_arg ( fun f => f.others ) hz; simp_all +decide [ Finsupp.single_apply ] ;
            · rw [ isUnit_iff_dvd_one ] at *;
              obtain ⟨ k, hk ⟩ := ‹y ∣ 1›; replace hk := congr_arg ( fun z => z.others ) hk; simp_all +decide [ Finsupp.single_apply ] ;
              rw [ eq_comm, add_eq_zero_iff_of_nonneg ] at hk <;> aesop

end AristotleLemmas

lemma atoms_eq : Atoms CFIFailMonoid =
    {atomP, atomQ, atomU, atomV} ∪ Set.range atomR := by
  ext x
  simp only [Atoms, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_range]
  constructor
  · -- Every irreducible element is one of the standard atoms
    -- This direction is complex but not needed for the main theorem
    intro hx
    convert CFIFailMonoid.degree_eq_one_iff_mem_standard x |>.1 ( CFIFailMonoid.irreducible_implies_degree_eq_one x hx ) using 1
  · intro hx
    rcases hx with (rfl | rfl | rfl | rfl) | ⟨i, rfl⟩
    · exact atomP_irreducible
    · exact atomQ_irreducible
    · exact atomU_irreducible
    · exact atomV_irreducible
    · exact atomR_irreducible i

/-!
## Atomicity
-/

/-- The CFI failure monoid is atomic. -/
theorem cfifail_atomic : Atomic CFIFailMonoid := by
  intro x hx
  -- The proof constructs a factorization from the exponents.
  -- This is straightforward but requires careful handling of the Finsupp product.
  -- Let $y = \text{atomP}^{\text{expP}} \cdot \text{atomQ}^{\text{expQ}} \cdot \text{atomU}^{\text{expU}} \cdot \text{atomV}^{\text{expV}} \cdot \prod_{i} \text{atomR}(i)^{\text{others}(i)}$.
  set y := (atomP ^ x.exp_p) * (atomQ ^ x.exp_q) * (atomU ^ x.exp_u) * (atomV ^ x.exp_v) * (x.others.prod (fun i e => (atomR i) ^ e));
  -- By definition of $y$, we know that $y = x$.
  have hy_eq_x : y = x := by
    have hy_eq_x : ∀ (m : CFIFailMonoid), (atomP ^ m.exp_p) * (atomQ ^ m.exp_q) * (atomU ^ m.exp_u) * (atomV ^ m.exp_v) * (m.others.prod (fun i e => (atomR i) ^ e)) = m := by
      intro m;
      refine' CFIFailMonoid.ext _ _ _ _ _;
      · induction' m.others using Finsupp.induction with i e m ih hm' ih;
        · cases m.normalized <;> simp_all +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV ];
        · simp_all +decide [ Finsupp.prod_add_index', pow_add ];
          simp_all +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, pow_atomR ];
          omega;
      · induction' m.others using Finsupp.induction with i e m ih;
        · simp +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, mul_assoc ];
          cases m.normalized <;> simp +decide [ * ];
        · simp_all +decide [ Finsupp.prod_add_index', pow_add ];
          simp_all +decide [ pow_atomR, pow_atomP, pow_atomQ, pow_atomU, pow_atomV ];
          omega;
      · induction' m.others using Finsupp.induction with i e m ih;
        · simp +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, mul_assoc ];
          exact m.normalized;
        · simp_all +decide [ Finsupp.prod_add_index', pow_add ];
          simp_all +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, pow_atomR ];
          cases min_cases ( ‹CFIFailMonoid›.exp_p ) ( ‹CFIFailMonoid›.exp_q ) <;> omega;
      · induction' m.others using Finsupp.induction with i e m ih;
        · simp +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, mul_assoc ];
          exact m.normalized;
        · simp_all +decide [ Finsupp.prod_add_index', pow_add ];
          simp_all +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV, pow_atomR ];
          omega;
      · induction' m.others using Finsupp.induction with i e m ih;
        · simp +decide [ pow_atomP, pow_atomQ, pow_atomU, pow_atomV ];
        · simp_all +decide [ Finsupp.prod_add_index', pow_add ];
          convert congr_arg ( fun x => Finsupp.single i e + x ) ‹_› using 1 ; abel_nf;
          simp +decide [ add_comm, add_left_comm, add_assoc, pow_atomR ];
    exact hy_eq_x x;
  -- Let's construct the multiset $s$ by taking the exponents of each atom in $y$.
  use Multiset.replicate x.exp_p atomP + Multiset.replicate x.exp_q atomQ + Multiset.replicate x.exp_u atomU + Multiset.replicate x.exp_v atomV + x.others.sum (fun i e => Multiset.replicate e (atomR i));
  refine' ⟨ _, _ ⟩;
  · simp +contextual [ Multiset.mem_replicate, Finsupp.sum ];
    rintro a ( ( ( ( h | h ) | h ) | h ) | ⟨ i, hi, rfl ⟩ ) <;> simp_all +decide [ irreducible_iff ];
    · exact ⟨ atomP_not_unit, fun a b hab => by have := atomP_irreducible; rw [ irreducible_iff ] at this; aesop ⟩;
    · exact ⟨ atomQ_not_unit, fun a b hab => by have := atomQ_irreducible; rw [ irreducible_iff ] at this; aesop ⟩;
    · exact ⟨ atomU_not_unit, fun a b hab => by have := atomU_irreducible; rw [ irreducible_iff ] at this; aesop ⟩;
    · exact ⟨ atomV_not_unit, fun a b hab => by have := atomV_irreducible; rw [ irreducible_iff ] at this; aesop ⟩;
    · exact ⟨ atomR_not_unit i, fun a b hab => by have := atomR_irreducible i; rw [ irreducible_iff ] at this; aesop ⟩;
  · convert hy_eq_x using 1;
    simp +zetaDelta at *;
    congr! 2;
    simp +decide [ Finsupp.sum, Finsupp.prod ];
    induction x.others.support using Finset.induction <;> aesop

/-!
## The Four Axioms
-/

/-- PP-D holds: powers of each atom are distinct. -/
theorem cfifail_PPD : PP_D CFIFailMonoid := by
  intro p hp a b hab
  rw [atoms_eq] at hp
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_range] at hp
  rcases hp with (rfl | rfl | rfl | rfl) | ⟨i, rfl⟩
  · -- p = atomP
    simp only [pow_atomP] at hab
    have := congr_arg exp_p hab
    simp at this
    exact this
  · -- p = atomQ
    simp only [pow_atomQ] at hab
    have := congr_arg exp_q hab
    simp at this
    exact this
  · -- p = atomU
    simp only [pow_atomU] at hab
    have := congr_arg exp_u hab
    simp at this
    exact this
  · -- p = atomV
    simp only [pow_atomV] at hab
    have := congr_arg exp_v hab
    simp at this
    exact this
  · -- p = atomR i
    simp only [pow_atomR] at hab
    have := congr_arg others hab
    simp at this
    have := Finsupp.ext_iff.mp this i
    simp [Finsupp.single_eq_same] at this
    exact this

/-- APD holds: atom q dividing p^k implies q = p. -/
theorem cfifail_APD : APD CFIFailMonoid := by
  -- For each pair of atoms, if q | p^k then q = p.
  -- Cross-divisibility is impossible due to the exponent structure.
  intro p q hp hq k hdvd
  rw [atoms_eq] at hp hq
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_range] at hp hq
  obtain ⟨z, hz⟩ := hdvd
  rcases hp with (rfl | rfl | rfl | rfl) | ⟨i, rfl⟩ <;>
  rcases hq with (rfl | rfl | rfl | rfl) | ⟨j, rfl⟩
  -- Diagonal cases: p = q
  all_goals try rfl
  -- Off-diagonal cases: show q cannot divide p^k by exponent analysis
  all_goals simp only [pow_atomP, pow_atomQ, pow_atomU, pow_atomV, pow_atomR] at hz
  -- For each case, extract exponent equations. The key insight is:
  -- - atomP^k has exp_q = 0, exp_u = 0, exp_v = 0, others = 0
  -- - atomQ^k has exp_p = 0, exp_u = 0, exp_v = 0, others = 0
  -- - atomU^k has exp_p = 0, exp_q = 0, exp_v = 0, others = 0
  -- - atomV^k has exp_p = 0, exp_q = 0, exp_u = 0, others = 0
  -- - atomR i^k has exp_p = 0, exp_q = 0, exp_u = 0, exp_v = 0
  -- If q ≠ p, then q has a nonzero exponent where p^k has zero.
  -- For q * z = p^k, we get a contradiction from that exponent.
  -- Case: atomQ | atomP^k - atomQ has exp_q = 1, atomP^k has exp_q = 0
  · have hq_eq := congrArg exp_q hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_q, mul_exp_u, atomQ_exp_q, atomQ_exp_p, atomQ_exp_u] at hq_eq hu_eq
    simp only [Nat.min_def] at hq_eq hu_eq
    split_ifs at hq_eq hu_eq <;> omega
  -- Case: atomU | atomP^k - atomU has exp_u = 1, atomP^k has exp_u = 0
  · have hu_eq := congrArg exp_u hz
    simp only [mul_exp_u, atomU_exp_u, atomU_exp_p, atomU_exp_q] at hu_eq
    -- hu_eq: 1 + z.exp_u + min(z.exp_p, z.exp_q) = 0, impossible since ≥ 1
    omega
  -- Case: atomV | atomP^k - atomV has exp_v = 1, atomP^k has exp_v = 0
  · have hv_eq := congrArg exp_v hz
    simp only [mul_exp_v, atomV_exp_v, atomV_exp_p, atomV_exp_q] at hv_eq
    omega
  -- Case: atomR j | atomP^k - atomR j has others(j) = 1, atomP^k has others = 0
  · have h := congrArg others hz
    simp only [mul_others, atomR_others, atomP_others] at h
    have hj := DFunLike.congr_fun h j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hj
    omega
  -- Case: atomP | atomQ^k - atomP has exp_p = 1, atomQ^k has exp_p = 0
  · have hp_eq := congrArg exp_p hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_p, mul_exp_u, atomP_exp_p, atomP_exp_q, atomP_exp_u] at hp_eq hu_eq
    simp only [Nat.min_def] at hp_eq hu_eq
    split_ifs at hp_eq hu_eq <;> omega
  -- Case: atomU | atomQ^k
  · have hu_eq := congrArg exp_u hz
    simp only [mul_exp_u, atomU_exp_u, atomU_exp_p, atomU_exp_q] at hu_eq
    omega
  -- Case: atomV | atomQ^k
  · have hv_eq := congrArg exp_v hz
    simp only [mul_exp_v, atomV_exp_v, atomV_exp_p, atomV_exp_q] at hv_eq
    omega
  -- Case: atomR j | atomQ^k
  · have h := congrArg others hz
    simp only [mul_others, atomR_others, atomQ_others] at h
    have hj := DFunLike.congr_fun h j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hj
    omega
  -- Case: atomP | atomU^k - need exp_v to get contradiction via overflow
  · have hp_eq := congrArg exp_p hz
    have hv_eq := congrArg exp_v hz
    simp only [mul_exp_p, mul_exp_v, atomP_exp_p, atomP_exp_q, atomP_exp_v] at hp_eq hv_eq
    simp only [Nat.min_def] at hp_eq hv_eq
    split_ifs at hp_eq hv_eq <;> omega
  -- Case: atomQ | atomU^k - need exp_v to get contradiction via overflow
  · have hq_eq := congrArg exp_q hz
    have hv_eq := congrArg exp_v hz
    simp only [mul_exp_q, mul_exp_v, atomQ_exp_q, atomQ_exp_p, atomQ_exp_v] at hq_eq hv_eq
    simp only [Nat.min_def] at hq_eq hv_eq
    split_ifs at hq_eq hv_eq <;> omega
  -- Case: atomV | atomU^k
  · have hv_eq := congrArg exp_v hz
    simp only [mul_exp_v, atomV_exp_v, atomV_exp_p, atomV_exp_q] at hv_eq
    omega
  -- Case: atomR j | atomU^k
  · have h := congrArg others hz
    simp only [mul_others, atomR_others, atomU_others] at h
    have hj := DFunLike.congr_fun h j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hj
    omega
  -- Case: atomP | atomV^k
  · have hp_eq := congrArg exp_p hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_p, mul_exp_u, atomP_exp_p, atomP_exp_q, atomP_exp_u] at hp_eq hu_eq
    simp only [Nat.min_def] at hp_eq hu_eq
    split_ifs at hp_eq hu_eq <;> omega
  -- Case: atomQ | atomV^k
  · have hq_eq := congrArg exp_q hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_q, mul_exp_u, atomQ_exp_q, atomQ_exp_p, atomQ_exp_u] at hq_eq hu_eq
    simp only [Nat.min_def] at hq_eq hu_eq
    split_ifs at hq_eq hu_eq <;> omega
  -- Case: atomU | atomV^k
  · have hu_eq := congrArg exp_u hz
    simp only [mul_exp_u, atomU_exp_u, atomU_exp_p, atomU_exp_q] at hu_eq
    omega
  -- Case: atomR j | atomV^k
  · have h := congrArg others hz
    simp only [mul_others, atomR_others, atomV_others] at h
    have hj := DFunLike.congr_fun h j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hj
    omega
  -- Case: atomP | atomR i^k
  · have hp_eq := congrArg exp_p hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_p, mul_exp_u, atomP_exp_p, atomP_exp_q, atomP_exp_u] at hp_eq hu_eq
    simp only [Nat.min_def] at hp_eq hu_eq
    split_ifs at hp_eq hu_eq <;> omega
  -- Case: atomQ | atomR i^k
  · have hq_eq := congrArg exp_q hz
    have hu_eq := congrArg exp_u hz
    simp only [mul_exp_q, mul_exp_u, atomQ_exp_q, atomQ_exp_p, atomQ_exp_u] at hq_eq hu_eq
    simp only [Nat.min_def] at hq_eq hu_eq
    split_ifs at hq_eq hu_eq <;> omega
  -- Case: atomU | atomR i^k
  · have hu_eq := congrArg exp_u hz
    simp only [mul_exp_u, atomU_exp_u, atomU_exp_p, atomU_exp_q] at hu_eq
    omega
  -- Case: atomV | atomR i^k
  · have hv_eq := congrArg exp_v hz
    simp only [mul_exp_v, atomV_exp_v, atomV_exp_p, atomV_exp_q] at hv_eq
    omega
  -- Case: atomR j | atomR i^k - if j ≠ i, others(j) gives contradiction
  · by_cases hji : j = i
    · subst hji; rfl
    · have h := congrArg others hz
      simp only [mul_others, atomR_others] at h
      have hj := DFunLike.congr_fun h j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same,
                 Finsupp.single_eq_of_ne hji] at hj
      omega

/-- UAB holds: If p^k = q^m for atoms p, q with k, m ≥ 1, then p = q.
    The relation uv ~ pq only identifies degree-1 products of distinct primes, not pure powers. -/
theorem cfifail_UAB : UAB CFIFailMonoid := by
  intro p q hp hq k m hk hm hpow
  rw [atoms_eq] at hp hq
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_range] at hp hq
  -- Each atom's power is characterized by a unique nonzero exponent position
  rcases hp with (rfl | rfl | rfl | rfl) | ⟨i, rfl⟩ <;>
  rcases hq with (rfl | rfl | rfl | rfl) | ⟨j, rfl⟩
  -- Diagonal cases: p = q
  all_goals try rfl
  -- Off-diagonal cases: p^k and q^m have different nonzero exponent positions
  all_goals simp only [pow_atomP, pow_atomQ, pow_atomU, pow_atomV, pow_atomR] at hpow
  -- For atomP^k vs atomQ^m: exp_p = k vs exp_p = 0
  · have h := congrArg exp_p hpow; simp at h; omega
  · have h := congrArg exp_p hpow; simp at h; omega
  · have h := congrArg exp_p hpow; simp at h; omega
  · have h := congrArg exp_p hpow; simp at h; omega
  · have h := congrArg exp_q hpow; simp at h; omega
  · have h := congrArg exp_q hpow; simp at h; omega
  · have h := congrArg exp_q hpow; simp at h; omega
  · have h := congrArg exp_q hpow; simp at h; omega
  · have h := congrArg exp_u hpow; simp at h; omega
  · have h := congrArg exp_u hpow; simp at h; omega
  · have h := congrArg exp_u hpow; simp at h; omega
  · have h := congrArg exp_u hpow; simp at h; omega
  · have h := congrArg exp_v hpow; simp at h; omega
  · have h := congrArg exp_v hpow; simp at h; omega
  · have h := congrArg exp_v hpow; simp at h; omega
  · have h := congrArg exp_v hpow; simp at h; omega
  · have h := congrArg others hpow
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at hi; omega
  · have h := congrArg others hpow
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at hi; omega
  · have h := congrArg others hpow
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at hi; omega
  · have h := congrArg others hpow
    have hi := DFunLike.congr_fun h i
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at hi; omega
  -- atomR i vs atomR j: if i ≠ j, others(i) = k vs others(i) = 0
  · by_cases hji : j = i
    · subst hji; rfl
    · have h := congrArg others hpow
      have hi := DFunLike.congr_fun h i
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hji)] at hi
      omega

/-- CPL holds: pairwise coprime non-units exist in every length. -/
theorem cfifail_CPL : CPL CFIFailMonoid := by
  intro r
  use (List.range r).map atomR
  constructor
  · simp
  constructor
  · intro x hx
    simp at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact atomR_not_unit i
  · -- Pairwise coprime: atomR i and atomR j are coprime for i ≠ j
    -- because they have disjoint support in the others field.
    rw [ List.pairwise_iff_get ];
    -- Since $r_i$ and $r_j$ are distinct atoms in the monoid, they are coprime.
    intros i j hij
    simp [AreCoprime, CFIFailMonoid.atoms_eq];
    rintro p ( ( rfl | rfl | rfl | rfl ) | ⟨ y, rfl ⟩ ) h₁ h₂ <;> simp_all +decide [ CFIFailMonoid.atomR ];
    · cases h₁ ; cases h₂ ; simp_all +decide [ CFIFailMonoid.atomP ];
      rename_i h₁ h₂;
      injection h₁;
      grind;
    · cases h₁ ; cases h₂ ; simp_all +decide [ CFIFailMonoid.atomQ ];
      injection ‹_›;
      grind;
    · obtain ⟨ k, hk ⟩ := h₁;
      replace hk := congr_arg ( fun x => x.exp_u ) hk ; simp_all +decide;
      linarith [ Nat.zero_le ( Min.min k.exp_p k.exp_q ) ];
    · cases' h₁ with k hk aesop;
      replace hk := congr_arg ( fun x => x.exp_v ) hk ; simp_all +decide;
      grind;
    · rcases h₁ with ⟨ k, hk ⟩ ; rcases h₂ with ⟨ l, hl ⟩ ; replace hk := congr_arg ( fun x : CFIFailMonoid => x.others ) hk ; replace hl := congr_arg ( fun x : CFIFailMonoid => x.others ) hl ; replace hk := congr_arg ( fun x : ℕ →₀ ℕ => x y ) hk ; replace hl := congr_arg ( fun x : ℕ →₀ ℕ => x y ) hl ; simp_all +decide [ Finsupp.single_apply ];
      grind

/-- CFI fails: p and q are coprime but pq = uv has factorization (u, v) not in image of μ₂. -/
theorem cfifail_not_CFI : ¬CFI CFIFailMonoid := by
  intro hcfi
  -- Take x = atomP and y = atomQ, which are coprime
  -- (no common atom divisor because atomP and atomQ have disjoint support)
  have hcoprime : AreCoprime atomP atomQ := by
    intro p hp hdvd_p hdvd_q
    -- Any common atom divisor would need to divide both atomP and atomQ
    -- But atomP has exp_p = 1 and atomQ has exp_q = 1 with all other exponents 0
    -- So no atom can divide both
    -- Since p is an atom and divides both p and q, p must be equal to p or q. However, if p were equal to q, that would contradict the fact that p and q are distinct atoms. Therefore, the only possibility is that p equals p, which is trivially true. But this doesn't help in deriving a contradiction.
    have hp_eq_p_or_q : p = atomP ∨ p = atomQ := by
      have hp_eq_p_or_q : p ∈ ({⟨1, 0, 0, 0, 0, Or.inr rfl⟩, ⟨0, 1, 0, 0, 0, Or.inl rfl⟩, ⟨0, 0, 1, 0, 0, Or.inl rfl⟩, ⟨0, 0, 0, 1, 0, Or.inl rfl⟩} ∪ Set.range (fun i => ⟨0, 0, 0, 0, Finsupp.single i 1, Or.inl rfl⟩)) := by
        exact atoms_eq.symm ▸ hp;
      rcases hp_eq_p_or_q with ( ( rfl | rfl | rfl | rfl ) | ⟨ i, rfl ⟩ ) <;> simp +decide [ CFIFailMonoid.atomP, CFIFailMonoid.atomQ, CFIFailMonoid.atomR ] at hdvd_p hdvd_q ⊢;
      · rcases hdvd_p with ⟨ x, hx ⟩;
        replace hx := congr_arg ( fun z => z.exp_u ) hx ; simp +decide at hx;
        linarith [ Nat.zero_le ( Min.min x.exp_p x.exp_q ) ];
      · obtain ⟨ y, hy ⟩ := hdvd_q; have := congr_arg ( fun z => z.exp_q ) hy; norm_num at this;
        have := congr_arg ( fun z => z.exp_u ) hy; norm_num at this; have := congr_arg ( fun z => z.exp_v ) hy; norm_num at this; have := congr_arg ( fun z => z.others ) hy; norm_num at this;
        omega;
      · obtain ⟨ x, hx ⟩ := hdvd_p; obtain ⟨ y, hy ⟩ := hdvd_q; replace hx := congr_arg ( fun z => z.others i ) hx; replace hy := congr_arg ( fun z => z.others i ) hy; simp_all +decide [ Finsupp.single_apply ] ;
        linarith;
    rcases hp_eq_p_or_q with ( rfl | rfl ) <;> simp_all +decide [ dvd_iff_exists_eq_mul_left ];
    · obtain ⟨ c, hc ⟩ := hdvd_q; have := congr_arg CFIFailMonoid.exp_q hc; simp +decide at this;
      cases c.normalized <;> simp +decide [ ‹_› ] at this;
      rcases n : c.exp_q with ( _ | _ | n ) <;> simp +decide [ n ] at this ⊢;
      subst this; have := congr_arg ( fun x : CFIFailMonoid => x.exp_u ) hc; norm_num at this;
      rw [ eq_comm ] at this ; aesop;
    · obtain ⟨ c, hc ⟩ := hdvd_p; have := congr_arg ( ·.exp_p ) hc; have := congr_arg ( ·.exp_q ) hc; have := congr_arg ( ·.exp_u ) hc; have := congr_arg ( ·.exp_v ) hc; have := congr_arg ( ·.others ) hc; norm_num at *;
      omega
  -- Apply CFI to get a bijection
  have hbij := hcfi atomP atomQ hcoprime
  -- The product atomP * atomQ = atomU * atomV (the key relation)
  have hpq : atomP * atomQ = atomU * atomV := atomP_mul_atomQ
  -- Construct the factorization (atomU, atomV) of atomP * atomQ
  let uv_fun : Fin 2 → CFIFailMonoid := fun i => if i = 0 then atomU else atomV
  have huv_fact : uv_fun ∈ LabeledFactorizations 2 (atomP * atomQ) := by
    simp only [LabeledFactorizations, Set.mem_setOf_eq, Fin.prod_univ_two, uv_fun]
    simp only [Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one]
    exact hpq.symm
  let uv_fact : LabeledFactorizations 2 (atomP * atomQ) := ⟨uv_fun, huv_fact⟩
  -- Show (atomU, atomV) is not in the image of the coordinatewise map
  have not_in_image : ∀ (f : LabeledFactorizations 2 atomP) (g : LabeledFactorizations 2 atomQ),
      labeledFactorizationMul f g ≠ uv_fact := by
    intro f g heq
    -- f is a 2-factorization of atomP: f(0) * f(1) = atomP
    -- g is a 2-factorization of atomQ: g(0) * g(1) = atomQ
    -- If the coordinatewise product equals (atomU, atomV), then:
    -- f(0) * g(0) = atomU and f(1) * g(1) = atomV
    -- But this leads to a contradiction on the exponents
    -- Since $f$ is a 2-factorization of $p$, and $p$ is atomP, the exponents of $p$ in $f$ must be $1, 0$ or $0, 1$.
    have hf_exp : ∀ i : Fin 2, f.val i = atomP := by
      intro i
      have hf_prod : f.val 0 * f.val 1 = atomP := by
        convert f.2 using 1;
        simp +decide [ LabeledFactorizations ];
      have hf_exp : ∀ x y : CFIFailMonoid, x * y = atomP → (x = atomP ∧ y = 1) ∨ (x = 1 ∧ y = atomP) := by
        intros x y hxy
        have hxy_exp : x.exp_p + y.exp_p = 1 ∧ x.exp_q + y.exp_q = 0 ∧ x.exp_u + y.exp_u = 0 ∧ x.exp_v + y.exp_v = 0 ∧ x.others + y.others = 0 := by
          have hxy_exp : x.exp_p + y.exp_p - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) = 1 ∧ x.exp_q + y.exp_q - min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) = 0 ∧ x.exp_u + y.exp_u + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) = 0 ∧ x.exp_v + y.exp_v + min (x.exp_p + y.exp_p) (x.exp_q + y.exp_q) = 0 ∧ x.others + y.others = 0 := by
            exact ⟨ by simpa using congr_arg ( fun z : CFIFailMonoid => z.exp_p ) hxy, by simpa using congr_arg ( fun z : CFIFailMonoid => z.exp_q ) hxy, by simpa using congr_arg ( fun z : CFIFailMonoid => z.exp_u ) hxy, by simpa using congr_arg ( fun z : CFIFailMonoid => z.exp_v ) hxy, by simpa using congr_arg ( fun z : CFIFailMonoid => z.others ) hxy ⟩;
          grind;
        cases Nat.eq_zero_or_pos x.exp_p <;> cases Nat.eq_zero_or_pos y.exp_p <;> first | linarith | simp_all +decide [ CFIFailMonoid.one ] ;
        · exact Or.inr ⟨ by cases x ; cases y ; aesop, by cases x ; cases y ; aesop ⟩;
        · exact Or.inl ⟨ by cases x ; cases y ; aesop, by cases x ; cases y ; aesop ⟩;
      fin_cases i <;> cases hf_exp _ _ hf_prod <;> simp_all +decide;
      · replace heq := congr_arg Subtype.val heq ; simp_all +decide [ labeledFactorizationMul ];
        replace heq := congr_fun heq 0 ; simp_all +decide [ uv_fact ];
        have := g.2; simp_all +decide [ LabeledFactorizations ] ;
        replace this := congr_arg ( fun x => x.exp_u ) this ; simp_all +decide [ uv_fun ];
      · replace heq := congr_arg ( fun x => x.val 1 ) heq ; simp_all +decide [ labeledFactorizationMul ];
        simp +zetaDelta at *;
        have := g.2; simp_all +decide [ LabeledFactorizations ] ;
        replace this := congr_arg ( fun x => x.exp_v ) this ; simp_all +decide [ CFIFailMonoid.mul ];
    injection heq with heq ; simp_all +decide [ funext_iff, Fin.forall_fin_two ];
    unfold uv_fun at heq; simp_all +decide [ CFIFailMonoid.ext_iff ] ;
    omega
  -- But hbij says the map is surjective, so uv_fact should be in the image
  obtain ⟨⟨f, g⟩, hfg⟩ := hbij.2 uv_fact
  exact not_in_image f g hfg

end CFIFailMonoid

end