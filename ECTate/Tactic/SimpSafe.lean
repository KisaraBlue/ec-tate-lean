/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Lean
import Std.Tactic.OpenPrivate

namespace ECTate
namespace Tactic

open Lean Parser.Tactic Elab.Tactic PrettyPrinter

/-!
# SimpSafe

## Main definitions

* `simp_safe`

-/


-- syntax (name := simpSafe) "simp_safe" (config)? (discharger)? (&" only")?
--   (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? (location)? : tactic

/--

`simp_safe` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `λ x, ...`.
Usage:

- `simp_safe [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
  lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
- `simp_safe [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
- `simp_safe [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_safe` must be expressions that are valid arguments to `simp`.
For example, neither `simp` nor `rw` can solve the following, but `simp_safe` can:

```lean
example {a : ℕ}
  (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
  (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
  (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 :=
by simp_safe [h1, h2]
```
-/
-- elab "simp_safe " con:config dis:discharger rws:((" [" withoutPosition((simpErase <|> simpLemma),*) "]") ?) loc:location ? : tactic => do -- todo only and config
--   let fvarIds ← match expandOptLocation loc.get! with
--   | Location.targets hyps simplifyTarget =>
--     withMainContext (getFVarIds hyps)
--   | Location.wildcard =>
--     withMainContext ((← getMainGoal).getNondepPropHyps)
--   let stx ← fvarIds.mapM fun h : FVarId => do
--     let hh ← delab h.name
--     `(tactic| (simp $con $dis at $hh))

--   `(tactic| ($[$stx]*))


-- syntax (name := simpSafe) "simp_all" (config)? (discharger)? (&" only")?
--   (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? : tactic
syntax (name := simpSafe) "simp_safe" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? (location)? : tactic


syntax (name := simpSafeAll) "simp_safe_all" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? : tactic

open Lean.Elab.Tactic
open Meta
open TSyntax.Compat
open Simp (UsedSimps)


deriving instance Repr for PersistentHashMap.Entry
partial
def reprfun [Repr α] [Repr β] : (PersistentHashMap.Node α β) → Nat → Format :=
let _ : Repr (PersistentHashMap.Node α β) := ⟨reprfun⟩
fun a b =>
match a with
  | .entries t => reprPrec t b
  | .collision t s _ => reprPrec (t, s) b

instance [Repr α] [BEq α] [Hashable α] [Repr β] : Repr (PersistentHashMap α β) :=
{ reprPrec := fun a => (reprPrec (PersistentHashMap.toList a)) }

-- deriving instance Repr for PersistentHashMap.Node
-- deriving ins>retance Repr for PersistentHashMap
deriving instance Repr for DiscrTree.Key
deriving instance Repr for DiscrTree.Trie
deriving instance Repr for DiscrTree
deriving instance Repr for SimpTheorem
instance : Repr SimpTheoremTree := instReprDiscrTree
deriving instance Repr for PersistentHashSet
deriving instance Repr for SimpTheorems
-- deriving instance BEq for PersistentHashMap
-- deriving instance BEq for DiscrTree
-- deriving instance BEq for SimpTheorems

deriving instance Repr for Simp.Context

def simpSafeGoal (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM (Option (Array FVarId × MVarId) × UsedSimps) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut usedSimps := usedSimps
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      logInfo (repr ctx.simpTheorems)
      let ctx' := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }

      logInfo (repr ctx.simpTheorems)
      logInfo (repr <| ctx.simpTheorems.size == ctx'.simpTheorems.size)
      let (r, usedSimps') ← simp type ctx' discharge? usedSimps
      usedSimps := usedSimps'
      match r.proof? with
      | some _ => match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return (none, usedSimps)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.consumeMData.isConstOf ``False then
          mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
          return (none, usedSimps)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarId ctx discharge?) with
      | (none, usedSimps') => return (none, usedSimps')
      | (some mvarIdNew, usedSimps') => mvarId := mvarIdNew; usedSimps := usedSimps'
    let (fvarIdsNew, mvarIdNew) ← mvarId.assertHypotheses toAssert
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    let mvarIdNew ← mvarIdNew.tryClearMany toClear
    return (some (fvarIdsNew, mvarIdNew), usedSimps)
/--
`simpLocation ctx discharge? varIdToLemmaId loc`
runs the simplifier at locations specified by `loc`,
using the simp theorems collected in `ctx`
optionally running a discharger specified in `discharge?` on generated subgoals.

Its primary use is as the implementation of the
`simp [...] at ...` and `simp only [...] at ...` syntaxes,
but can also be used by other tactics when a `Syntax` is not available.

For many tactics other than the simplifier,
one should use the `withLocation` tactic combinator
when working with a `location`.
-/
def simpSafeLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (loc : Location) : TacticM UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ← simpSafeGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return usedSimps


open private addDeclToUnfoldOrTheorem addSimpTheorem in Lean.Elab.Tactic.elabSimpArgs

open Lean.Elab
/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the form `"[" simpTheorem,* "]"`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
  this option only makes sense for `simp_all` or `*` is used.
-/
def elabSimpSafeArgs (stx : Syntax) (ctx : Simp.Context) (eraseLocal : Bool) (kind : SimpKind) : TacticM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term

    syntax simpErase := "-" ident
    -/
    withMainContext do
      let mut thmsArray := ctx.simpTheorems
      let mut thms      := thmsArray[0]!
      let mut starArg   := false
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          let fvar ← if eraseLocal || starArg then Lean.Elab.Term.isLocalIdent? arg[1] else pure none
          if let some fvar := fvar then
            -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
            thms := thms.eraseCore (.fvar fvar.fvarId!)
          else
            let declName ← resolveGlobalConstNoOverloadWithInfo arg[1]
            if ctx.config.autoUnfold then
              thms := thms.eraseCore (.decl declName)
            else
              thms ← thms.erase (.decl declName)
        else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]

          match (← resolveSimpIdTheorem? term) with
          | .expr e  =>
            let fvar ← Term.isLocalIdent? term
            if let some fvar := fvar then
              thms ← addDeclToUnfoldOrTheorem thms (.fvar fvar.fvarId!) e post inv kind
            else
              let name ← mkFreshId
              thms ← addDeclToUnfoldOrTheorem thms (.stx name arg) e post inv kind
          | .ext ext =>
            thmsArray := thmsArray.push (← ext.getTheorems)
          | .none    =>
            let name ← mkFreshId
            thms ← addSimpTheorem thms (.stx name arg) term post inv
        else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
          starArg := true
        else
          throwUnsupportedSyntax
      return { ctx := { ctx with simpTheorems := thmsArray.set! 0 thms }, starArg }
where
  resolveSimpIdTheorem? (simpArgTerm : Term) : TacticM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TacticM ResolveSimpIdResult := do
      if let some ext ← getSimpExtension? n then
        return .ext ext
      else
        return .none
    match simpArgTerm with
    | `($id:ident) =>
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          return .expr e
        else
          resolveExt id.getId.eraseMacroScopes
      catch _ =>
        resolveExt id.getId.eraseMacroScopes
    | _ =>
      if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
        return .expr e
      else
        return .none


open private mkDischargeWrapper in Lean.Elab.Tactic.mkSimpContext
/--
   Create the `Simp.Context` for the `simp`, `dsimp`, and `simp_all` tactics.
   If `kind != SimpKind.simp`, the `discharge` option must be `none`

   TODO: generate error message if non `rfl` theorems are provided as arguments to `dsimp`.
-/
def mkSimpSafeContext (stx : Syntax) (eraseLocal : Bool) (kind := SimpKind.simp) (ignoreStarArg : Bool := false) : TacticM MkSimpContextResult := do
  if !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let congrTheorems ← getSimpCongrTheorems
  let r ← elabSimpSafeArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) {
    config      := (← elabSimpConfig stx[1] (kind := kind))
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !r.starArg || ignoreStarArg then
    return { r with dischargeWrapper }
  else
    let ctx := r.ctx
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    return { ctx, dischargeWrapper }


/-
  "simp " (config)? (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[tactic ECTate.Tactic.simpSafe] def evalSimpSafe : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpSafeContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx discharge? (expandOptLocation stx[5])
  -- logInfo (repr usedSimps.toList)
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps

-- @[tactic ECTate.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => do
--   let { ctx, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
--   let (result?, usedSimps) ← simpAll (← getMainGoal) ctx
--   match result? with
--   | none => replaceMainGoal []
--   | some mvarId => replaceMainGoal [mvarId]
--   if tactic.simp.trace.get (← getOptions) then
--     traceSimpCall stx usedSimps
-- example : False := by
--   simpd

@[tactic ECTate.Tactic.simpSafeAll] def evalSimpSafeAll : Tactic := fun stx => do
  let { ctx, .. } ← mkSimpSafeContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (result?, usedSimps) ← simpAll (← getMainGoal) { ctx with config := { ctx.config with maxSteps := 10 } }
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps
