/-
Copyright (c) 2023 Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao Tadipatri
-/
import Lean.Elab.Term
import Lean.Elab.Tactic
import Lean.SubExpr

/-!

This file defines a `locs` syntax for tactic signatures to
refer to locations in the goal state.

This can be combined with patterns to define
tactics that target specific locations in the goal state.

This file is modelled on `Lean/Elab/Tactic/Location.lean`.

-/

open Lean Meta Elab Tactic

namespace Pattern.Location

/-- A hypothesis location with occurrences optionally specified.
    The location can either refer to the type of a local hypothesis or
    the body of a `let` declaration. -/
syntax hypLoc := ident <|> ("‹" ident ppSpace (Parser.Tactic.Conv.occs)? (ppSpace "in body")? "›")

/-- The `|-` or `⊢` pattern representing the goal. -/
syntax goalPattern := patternIgnore( atomic("|" noWs "-") <|> "⊢")

/-- The goal or target location with occurrences optionally specified. -/
syntax goalLoc := goalPattern <|> ("⟨" goalPattern ppSpace Parser.Tactic.Conv.occs "⟩")

/-- The wildcard location which refers to all valid locations. -/
syntax wildcardLoc := "*"

/-- A list of locations in the goal state with occurrences optionally specified. -/
syntax locs := ppSpace withPosition("at" ppSpace (wildcardLoc <|> (hypLoc* (goalLoc)?)))

/-- Occurrences at a goal location. This is similar to `SubExpr.GoalLocation`. -/
inductive GoalOccurrences
  /-- Occurrences in the type of a hypothesis. -/
  | hypType (fvarId : FVarId) (occs : Occurrences)
  /-- Occurrences in the value of a `let` hypothesis. -/
  | hypValue (fvarId : FVarId) (occs : Occurrences)
  /-- Occurrences in the target. -/
  | target (occs : Occurrences)
deriving Inhabited

open Parser Tactic Conv in
/-- Interpret `occs` syntax as `Occurrences`. -/
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map TSyntax.getNat |>.toList
      | _ => panic! s!"Invalid syntax {occs} for occurrences."

/-- Interpret `locs` syntax as an array of `GoalOccurrences`. -/
def expandLocs : TSyntax ``locs → TacticM (Array GoalOccurrences)
  | `(locs| at $_:wildcardLoc) => withMainContext do
    -- TODO: Maybe reverse the list of declarations, following `Lean/Elab/Tactic/Location.lean`
    (← getLCtx).decls.foldlM (init := #[.target .all]) fun goalOccs decl? => do
      match decl? with
      | some decl =>
        if decl.isImplementationDetail then
          return goalOccs
        else
          let goalOccs :=
            if decl.isLet then
              goalOccs.push <| .hypValue decl.fvarId .all
            else goalOccs
          return goalOccs.push <| .hypType decl.fvarId .all
      | none => return goalOccs
  | `(locs| at $hyps* $[$goal?]?) => withMainContext do
    let hypOccs ← hyps.mapM expandHypLoc
    match goal? with
    | some goal => return hypOccs.push (expandGoalLoc goal)
    | none => return hypOccs
  | _ => throwUnsupportedSyntax
where
  /-- Interpret `hypLoc` syntax as `GoalOccurrences`. -/
  expandHypLoc : TSyntax ``hypLoc → TacticM GoalOccurrences
  | `(hypLoc| $hyp:ident) => withMainContext do
    return .hypType (← getFVarId hyp) .all
  | `(hypLoc| ‹$hyp:ident $[$occs]?›) => withMainContext do
    return .hypType (← getFVarId hyp) (expandOccs occs)
  | `(hypLoc| ‹$hyp $[$occs]? in body›) => withMainContext do
    return .hypValue (← getFVarId hyp) (expandOccs occs)
  |     _ => throwUnsupportedSyntax

  /-- Interpret `goalLoc` syntax as `GoalOccurrences`. -/
  expandGoalLoc : TSyntax ``goalLoc → GoalOccurrences
  | `(goalLoc| $_:goalPattern) => .target .all
  | `(goalLoc| ⟨$_:goalPattern $occs⟩) => .target (expandOccs occs)
  | stx => panic! s!"Invalid syntax {stx} for goal location."

end Pattern.Location


open Pattern.Location

private inductive PatternProgress where
| noMatch : PatternProgress
| someMatch : (pattern : Expr) → PatternProgress
| finished : (pattern inner : Expr) → List LocalDecl → PatternProgress


private abbrev M := ReaderT (List FVarId) StateRefT PatternProgress StateRefT Nat MetaM

/-- the result of `patternAbstract`. -/
structure PatternAbstractResult where
  /-- the inner expression -/
  inner : Expr
  /-- the outer expression -/
  outer : Expr := .bvar 0
  /-- the pattern abstracted from the inner expression -/
  pattern : Expr
  /-- the fvar declarations of the variables introduced by the outer expression -/
  fvarDecls : List LocalDecl := []

/-- `Lean.Expr.instantiat1` bumps up the bvar indices of loose bvars in `subst`.
`instantiate1'` leaves `subst` untouched. -/
private def instantiate1' (e subst : Expr) (depth := 0) : Expr :=
  match e with
    | .mdata m e => .mdata m (instantiate1' e subst depth)
    | .proj s i e => .proj s i (instantiate1' e subst depth)
    | .app f a => .app (instantiate1' f subst depth) (instantiate1' a subst depth)
    | .lam _ t b _ => e.updateLambdaE! (instantiate1' t subst depth) (instantiate1' b subst (depth+1))
    | .forallE _ t b _ => e.updateForallE! (instantiate1' t subst depth) (instantiate1' b subst (depth+1))
    | .letE _ t v b _ => e.updateLet! (instantiate1' t subst depth) (instantiate1' v subst depth) (instantiate1' b subst (depth+1))
    | .bvar idx => if idx == depth then subst else e
    | _ => e

/--
Find all occurence of a pattern, abstracting the locations of this pattern,
also allowing for bound variables. The bound variables are replaced by free variables
which are recorded in the field `.fvarDecls`.
These are exactly the variables introduced in the returned outer expression.
-/
partial def PatternAbstract (e : Expr) (p : AbstractMVarsResult) (occs : Occurrences := .all) : MetaM (Option PatternAbstractResult) := do
  let e ← instantiateMVars e
  withNewMCtxDepth do
  let (mvars, _, p) ← openAbstractMVarsResult p
  let mvarIds := mvars.map Expr.mvarId!
  if p.isFVar && occs == Occurrences.all then
    return some {
      inner := e.abstract #[p]
      pattern := p }
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) : M Expr := do

      let introFVar (n : Name) (d b : Expr) : M Expr :=
        withLocalDeclD n d fun fvar =>
        withReader (fvar.fvarId! :: ·) do
          if let PatternProgress.noMatch ← get then
            let lctx ← getLCtx
            let mctx ← getMCtx
            let refreshLCtx decls mvarId := decls.insert mvarId { decls.find! mvarId with lctx }
            let decls := mvarIds.foldl (init := mctx.decls) refreshLCtx
            setMCtx { mctx with decls }

            let e ← visit (b.instantiate1 fvar)

            match ← get with
            | .noMatch =>
              return b
            | .someMatch pattern =>
              if pattern.containsFVar fvar.fvarId! then
                let fvarDecls ← liftMetaM $ (← read).mapM FVarId.getDecl
                set (PatternProgress.finished pattern (e.abstract #[fvar]) fvarDecls)
                return .bvar ((← read).length)
              else
                return e.abstract #[fvar]
            | .finished .. =>
              return e.abstract #[fvar]

          else
            let e ← visit (b.instantiate1 fvar)
            return e.abstract #[fvar]

      let visitChildren : Unit → M Expr := fun _ => do
        match e with
        | .app f a         => return e.updateApp! (← visit f) (← visit a)
        | .mdata _ b       => return e.updateMData! (← visit b)
        | .proj _ _ b      => return e.updateProj! (← visit b)
        | .letE n t v b _  => return e.updateLet! (← visit t) (← visit v) (← introFVar n t b)
        | .lam n d b _     => return e.updateLambdaE! (← visit d) (← introFVar n d b)
        | .forallE n d b _ => return e.updateForallE! (← visit d) (← introFVar n d b)
        | e                => return e
      let processMatch : Unit → M Expr := fun _ => do
        let i ← getThe Nat
        set (i+1)
        if occs.contains i then
          return .bvar (← read).length
        else
          visitChildren ()

      if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
        visitChildren ()
      else

        match ← get with
          | .noMatch =>
            let mctx ← getMCtx
            if ← isDefEq e p then
              set (PatternProgress.someMatch (← instantiateMVars p))
              processMatch ()
            else
              setMCtx mctx
              visitChildren ()
          | .someMatch pattern =>
            let mctx ← getMCtx
            if ← isDefEq e pattern then
              processMatch ()
            else
              setMCtx mctx
              visitChildren ()
          | .finished .. => return e

    let (e, result) ← visit e |>.run [] |>.run .noMatch |>.run' 0
    match result with
    | .finished pattern inner fvarDecls =>
      return some { inner, outer := e, pattern, fvarDecls }
    | .someMatch pattern =>
      return some { inner := e, pattern }
    | .noMatch => return none

/-- instantiate the `PatternAbstractResult` with `e`. -/
def PatternAbstractResult.instantiate (p : PatternAbstractResult) (e : Expr) : Expr :=
  let fvars := p.fvarDecls.toArray.map (.fvar ·.fvarId)
  let inner := p.inner.instantiate fvars |>.instantiate1 e
  instantiate1' p.outer (inner.abstract fvars.reverse)


/-- Substitute occurrences of a pattern in an expression with the result of `replacement`. -/
def substitute (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences)
    (replace : Expr → MetaM Expr) : MetaM Expr := do
  let some r ← PatternAbstract e pattern occs |
    throwError m!"Failed to find instance of pattern {indentExpr (← openAbstractMVarsResult pattern).2.2} in {indentExpr e}."
  let replacement ← withExistingLocalDecls r.fvarDecls (replace r.pattern)
  return r.instantiate replacement

/-- Replace the value of a local `let` hypothesis with `valNew`,
    which is assumed to be definitionally equal.

    This function is modified from `_root_.Lean.MVarId.replaceLocalDeclDefEq` in
    `Lean/Meta/Tactic/Replace.lean`. -/
def _root_.Lean.MVarId.replaceLocalLetDefEq (mvarId : MVarId) (fvarId : FVarId)
    (valNew : Expr) : MetaM MVarId := do
  mvarId.withContext do
    if valNew == (← fvarId.getValue?) then
      return mvarId
    else
      let mvarDecl ← mvarId.getDecl
      let lctxNew := (← getLCtx).modifyLocalDecl fvarId (·.setValue valNew)
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances)
                      mvarDecl.type mvarDecl.kind mvarDecl.userName
      mvarId.assign mvarNew
      return mvarNew.mvarId!

/-- Replace a pattern at the specified locations with the value of `replacement`,
    which is assumed to be definitionally equal to the original pattern. -/
def replaceOccurrencesDefEq (locs : Array GoalOccurrences) (pattern : AbstractMVarsResult)
    (replacement : Expr → MetaM Expr) : TacticM Unit := withMainContext do
  let mut mvarId ← getMainGoal
  for loc in locs do
    match loc with
    | .hypType fvarId occs =>
      let hypType ← fvarId.getType
      mvarId ← mvarId.replaceLocalDeclDefEq fvarId <| ← substitute hypType pattern occs replacement
    | .hypValue fvarId occs =>
      let .some hypValue ← fvarId.getValue? |
        throwError m!"Hypothesis {fvarId.name} is not a `let`-declaration."
      mvarId ← mvarId.replaceLocalLetDefEq fvarId <| ← substitute hypValue pattern occs replacement
    | .target occs => do
      let targetType ← mvarId.getType
      mvarId ← mvarId.replaceTargetDefEq <| ← substitute targetType pattern occs replacement
  replaceMainGoal [mvarId]

/--
  Convert the given goal `Ctx |- target` into a goal containing `let userName : type := val`
    after the local declaration with if `fvarId`.
  It assumes `val` has type `type`, and that `type` is well-formed after `fvarId`.

  This is modelled on `Lean.MVarId.assertAfter`. -/
def Lean.MVarId.defineAfter (mvarId : MVarId) (fvarId : FVarId) (userName : Name)
    (type : Expr) (val : Expr) : MetaM AssertAfterResult := do
  mvarId.checkNotAssigned `defineAfter
  let (fvarIds, mvarId) ← mvarId.revertAfter fvarId
  let mvarId ← mvarId.define userName type val
  let (fvarIdNew, mvarId) ← mvarId.intro1P
  let (fvarIdsNew, mvarId) ← mvarId.introNP fvarIds.size
  let mut subst := {}
  for f in fvarIds, fNew in fvarIdsNew do
    subst := subst.insert f (mkFVar fNew)
  return { fvarId := fvarIdNew, mvarId, subst }

/-- Replace the value of the local `let` declaration `fvarId` with a new value `valNew`.

    This follows the code of `Lean.MVarId.replaceLocalDecl`. -/
def Lean.MVarId.replaceLocalLetDecl (mvarId : MVarId) (fvarId : FVarId) (valNew : Expr)
    : MetaM AssertAfterResult := mvarId.withContext do
  let localDecl ← fvarId.getDecl
  let (_, localDecl') ← findMaxFVar valNew |>.run localDecl
  let result ← mvarId.defineAfter localDecl'.fvarId localDecl.userName (← fvarId.getType) valNew
  (do let mvarIdNew ← result.mvarId.clear fvarId
      pure { result with mvarId := mvarIdNew })
    <|> pure result
where
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e => do
      if e.isFVar then
        let localDecl' ← e.fvarId!.getDecl
        modify fun localDecl => if localDecl'.index > localDecl.index then localDecl' else localDecl
        return false
      else
        return e.hasFVar

/-- Rewrite the equality term `heq` at the specified locations. -/
def replaceOccurrencesEq (locs : Array GoalOccurrences)
    (heq : Expr) (symm : Bool := false) : TacticM Unit := withMainContext do
  let mut mvarId ← getMainGoal
  let mut newGoals : List MVarId := []
  for loc in locs do
    match loc with
    | .hypType fvarId occs =>
      let hypType ← fvarId.getType
      let rwResult ← Term.withSynthesize <|
        mvarId.rewrite hypType heq symm (config := { occs := occs })
      mvarId := (← mvarId.replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof).mvarId
      newGoals := newGoals ++ rwResult.mvarIds
    | .hypValue fvarId occs =>
      let .some hypValue ← fvarId.getValue? |
        throwError m!"Hypothesis {fvarId.name} is not a `let`-declaration."
      let rwResult ← Term.withSynthesize <|
        mvarId.rewrite hypValue heq symm (config := { occs := occs })
      mvarId := (← mvarId.replaceLocalLetDecl fvarId rwResult.eNew).mvarId
      newGoals := newGoals ++ rwResult.mvarIds
    | .target occs => do
      let targetType ← mvarId.getType
      let rwResult ← mvarId.rewrite targetType heq symm (config := { occs := occs })
      mvarId ← mvarId.replaceTargetEq rwResult.eNew rwResult.eqProof
      newGoals := newGoals ++ rwResult.mvarIds
  replaceMainGoal (mvarId :: newGoals)
