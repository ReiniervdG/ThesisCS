import Lean.Util.CollectFVars
import Lean.Parser.Term
import Lean.Meta.RecursorInfo
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.ElimInfo
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeVars
import Lean.Elab.App
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Generalize

import Struct.CustomTactics

namespace InductionHelper

open 
  Lean 
  Lean.Expr
  Lean.Meta 
  Lean.Elab
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser.Tactic

-- # Necessary duplicate (private) helper functions from Lean.Elab.Tactic.induction from nightly-2022-08-09
-- # Removed most comments, removed namespaces
private def getFirstAltLhs (alt : Syntax) : Syntax :=
  alt[0][0]
private def getAltName (alt : Syntax) : Name :=
  let lhs := getFirstAltLhs alt
  if !lhs[1].isOfKind ``Parser.Term.hole then lhs[1][1].getId.eraseMacroScopes else `_
private def altHasExplicitModifier (alt : Syntax) : Bool :=
  let lhs := getFirstAltLhs alt
  !lhs[1].isOfKind ``Parser.Term.hole && !lhs[1][0].isNone
private def getAltVars (alt : Syntax) : Array Syntax :=
  let lhs := getFirstAltLhs alt
  lhs[2].getArgs
private def getAltVarNames (alt : Syntax) : Array Name :=
  getAltVars  alt |>.map getNameOfIdent'
private def getAltRHS (alt : Syntax) : Syntax :=
  alt[2]
private def getAltDArrow (alt : Syntax) : Syntax :=
  alt[1]

def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind ``Parser.Term.syntheticHole || rhs.isOfKind ``Parser.Term.hole

def evalAlt (mvarId : MVarId) (alt : Syntax) (remainingGoals : Array MVarId) : TacticM (Array MVarId) :=
  let rhs := getAltRHS alt
  withCaseRef (getAltDArrow alt) rhs do
    if isHoleRHS rhs then
      let gs' ← mvarId.withContext <| withRef rhs do
        let mvarDecl ← mvarId.getDecl
        let val ← elabTermEnsuringType rhs mvarDecl.type
        mvarId.assign val
        let gs' ← getMVarsNoDelayed val
        tagUntaggedGoals mvarDecl.userName `induction gs'.toList
        pure gs'
      return remainingGoals ++ gs'
    else
      setGoals [mvarId]
      closeUsingOrAdmit (withTacticInfoContext alt (evalTactic rhs))
      return remainingGoals

structure Context where
  elimInfo : ElimInfo
  targets  : Array Expr -- targets provided by the user

structure State where
  argPos    : Nat := 0 -- current argument position
  targetPos : Nat := 0 -- current target at targetsStx
  f         : Expr
  fType     : Expr
  alts      : Array (Name × MVarId) := #[]
  insts     : Array MVarId := #[]

abbrev M := ReaderT Context $ StateRefT State TermElabM

private def addNewArg (arg : Expr) : M Unit :=
  modify fun s => { s with argPos := s.argPos+1, f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }

private def getBindingName : M Name := return (← get).fType.bindingName!
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

private def getFType : M Expr := do
  let fType ← whnfForall (← get).fType
  modify fun s => { s with fType := fType }
  pure fType

structure Result where
  elimApp : Expr
  alts    : Array (Name × MVarId) := #[]
  others  : Array MVarId := #[]

partial def mkElimApp (elimInfo : ElimInfo) (targets : Array Expr) (tag : Name) : TermElabM Result := do
  let rec loop : M Unit := do
    match (← getFType) with
    | .forallE binderName _ _ c =>
      let ctx ← read
      let argPos := (← get).argPos
      if ctx.elimInfo.motivePos == argPos then
        let motive ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.syntheticOpaque
        addNewArg motive
      else if ctx.elimInfo.targetsPos.contains argPos then
        let s ← get
        let ctx ← read
        unless s.targetPos < ctx.targets.size do
          throwError "insufficient number of targets for '{elimInfo.name}'"
        let target := ctx.targets[s.targetPos]!
        let expectedType ← getArgExpectedType
        let target ← withAssignableSyntheticOpaque <| Term.ensureHasType expectedType target
        modify fun s => { s with targetPos := s.targetPos + 1 }
        addNewArg target
      else match c with
        | .implicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | .strictImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType)
          addNewArg arg
        | .instImplicit =>
          let arg ← mkFreshExprMVar (← getArgExpectedType) (kind := MetavarKind.synthetic) (userName := appendTag tag binderName)
          modify fun s => { s with insts := s.insts.push arg.mvarId! }
          addNewArg arg
        | _ =>
          let arg ← mkFreshExprSyntheticOpaqueMVar (← getArgExpectedType) (tag := appendTag tag binderName)
          let x   ← getBindingName
          modify fun s => { s with alts := s.alts.push (x, arg.mvarId!) }
          addNewArg arg
      loop
    | _ =>
      pure ()
  let f ← Term.mkConst elimInfo.name
  let fType ← inferType f
  let (_, s) ← (loop).run { elimInfo := elimInfo, targets := targets } |>.run { f := f, fType := fType }
  let mut others := #[]
  for mvarId in s.insts do
    try
      unless (← Term.synthesizeInstMVarCore mvarId) do
        mvarId.setKind .syntheticOpaque
        others := others.push mvarId
    catch _ =>
      mvarId.setKind .syntheticOpaque
      others := others.push mvarId
  let alts ← s.alts.filterM fun alt => return !(← alt.2.isAssigned)
  return { elimApp := (← instantiateMVars s.f), alts, others := others }

def setMotiveArg (mvarId : MVarId) (motiveArg : MVarId) (targets : Array FVarId) : MetaM Unit := do
  let type ← inferType (mkMVar mvarId)
  let motive ← mkLambdaFVars (targets.map mkFVar) type
  let motiverInferredType ← inferType motive
  let motiveType ← inferType (mkMVar motiveArg)
  unless (← isDefEqGuarded motiverInferredType motiveType) do
    throwError "type mismatch when assigning motive{indentExpr motive}\n{← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
  motiveArg.assign motive

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "unknown alternative name '{altName}'"

private def checkAltNames (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax) : TacticM Unit :=
  for i in [:altsSyntax.size] do
    let altStx := altsSyntax[i]!
    if getAltName altStx == `_ && i != altsSyntax.size - 1 then
      withRef altStx <| throwError "invalid occurrence of wildcard alternative, it must be the last alternative"
    let altName := getAltName altStx
    if altName != `_ then
      unless alts.any fun (n, _) => n == altName do
        throwErrorAt altStx "invalid alternative name '{altName}'"

private def getNumExplicitFields (altMVarId : MVarId) (numFields : Nat) : MetaM Nat := altMVarId.withContext do
  let target ← altMVarId.getType
  withoutModifyingState do
    let (_, bis, _) ← forallMetaBoundedTelescope target numFields
    return bis.foldl (init := 0) fun r bi => if bi.isExplicit then r + 1 else r

private def saveAltVarsInfo (altMVarId : MVarId) (altStx : Syntax) (fvarIds : Array FVarId) : TacticM Unit :=
  withSaveInfoContext <| altMVarId.withContext do
    let useNamesForExplicitOnly := !altHasExplicitModifier altStx
    let mut i := 0
    let altVars := getAltVars altStx
    for fvarId in fvarIds do
      if !useNamesForExplicitOnly || (← fvarId.getDecl).binderInfo.isExplicit then
        if i < altVars.size then
          Term.addLocalVarInfo altVars[i]! (mkFVar fvarId)
          i := i + 1

def reorderAlts (alts : Array (Name × MVarId)) (altsSyntax : Array Syntax) : Array (Name × MVarId) := Id.run do
  if altsSyntax.isEmpty then
    return alts
  else
    let mut alts := alts
    let mut result := #[]
    for altStx in altsSyntax do
      let altName := getAltName altStx
      let some i := alts.findIdx? (·.1 == altName) | return result ++ alts
      result := result.push alts[i]!
      alts := alts.eraseIdx i
    return result ++ alts

private def getUserGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
  withRef stx do
    let generalizingStx := stx[3]
    if generalizingStx.isNone then
      pure #[]
    else
      trace[Elab.induction] "{generalizingStx}"
      let vars := generalizingStx[1].getArgs
      getFVarIds vars

private def generalizeVars (mvarId : MVarId) (stx : Syntax) (targets : Array Expr) : TacticM (Nat × MVarId) :=
  mvarId.withContext do
    let userFVarIds ← getUserGeneralizingFVarIds stx
    let forbidden ← mkGeneralizationForbiddenSet targets
    let mut s ← getFVarSetToGeneralize targets forbidden
    for userFVarId in userFVarIds do
      if forbidden.contains userFVarId then
        throwError "variable cannot be generalized because target depends on it{indentExpr (mkFVar userFVarId)}"
      if s.contains userFVarId then
        throwError "unnecessary 'generalizing' argument, variable '{mkFVar userFVarId}' is generalized automatically"
      s := s.insert userFVarId
    let fvarIds ← sortFVarIds s.toArray
    let (fvarIds, mvarId') ← mvarId.revert fvarIds
    return (fvarIds.size, mvarId')

private def getAltsOfInductionAlts (inductionAlts : Syntax) : Array Syntax :=
  inductionAlts[2].getArgs

private def getAltsOfOptInductionAlts (optInductionAlts : Syntax) : Array Syntax :=
  if optInductionAlts.isNone then #[] else getAltsOfInductionAlts optInductionAlts[0]

private def getOptPreTacOfOptInductionAlts (optInductionAlts : Syntax) : Syntax :=
  if optInductionAlts.isNone then mkNullNode else optInductionAlts[0][1]

private def isMultiAlt (alt : Syntax) : Bool :=
  alt[0].getNumArgs > 1

/-- Return `some #[alt_1, ..., alt_n]` if `alt` has multiple LHSs. -/
private def expandMultiAlt? (alt : Syntax) : Option (Array Syntax) := Id.run do
  if isMultiAlt alt then
    some <| alt[0].getArgs.map fun lhs => alt.setArg 0 (mkNullNode #[lhs])
  else
    none

private def expandInductionAlts? (inductionAlts : Syntax) : Option Syntax := Id.run do
  let alts := getAltsOfInductionAlts inductionAlts
  if alts.any isMultiAlt then
    let mut altsNew := #[]
    for alt in alts do
      if let some alt' := expandMultiAlt? alt then
        altsNew := altsNew ++ alt'
      else
        altsNew := altsNew.push alt
    some <| inductionAlts.setArg 2 (mkNullNode altsNew)
  else
    none

private def expandInduction? (induction : Syntax) : Option Syntax := do
  let optInductionAlts := induction[4]
  guard <| !optInductionAlts.isNone
  let inductionAlts' ← expandInductionAlts? optInductionAlts[0]
  return induction.setArg 4 (mkNullNode #[inductionAlts'])

private def expandCases? (induction : Syntax) : Option Syntax := do
  let optInductionAlts := induction[3]
  guard <| !optInductionAlts.isNone
  let inductionAlts' ← expandInductionAlts? optInductionAlts[0]
  return induction.setArg 3 (mkNullNode #[inductionAlts'])

private def checkAltsOfOptInductionAlts (optInductionAlts : Syntax) : TacticM Unit :=
  unless optInductionAlts.isNone do
    let mut found := false
    for alt in getAltsOfInductionAlts optInductionAlts[0] do
      let n := getAltName alt
      if n == `_ then
        unless (getAltVarNames alt).isEmpty do
          throwErrorAt alt "wildcard alternative must not specify variable names"
        if found then
          throwErrorAt alt "more than one wildcard alternative '| _ => ...' used"
        found := true

def getInductiveValFromMajor (major : Expr) : TacticM InductiveVal :=
  liftMetaMAtMain fun mvarId => do
    let majorType ← inferType major
    let majorType ← whnf majorType
    matchConstInduct majorType.getAppFn
      (fun _ => Meta.throwTacticEx `induction mvarId m!"major premise type is not an inductive type {indentExpr majorType}")
      (fun val _ => pure val)

private def getElimNameInfo (optElimId : Syntax) (targets : Array Expr) (induction : Bool): TacticM ElimInfo := do
  if optElimId.isNone then
    if let some elimInfo ← getCustomEliminator? targets then
      return elimInfo
    unless targets.size == 1 do
      throwError "eliminator must be provided when multiple targets are used (use 'using <eliminator-name>'), and no default eliminator has been registered using attribute `[eliminator]`"
    let indVal ← getInductiveValFromMajor targets[0]!
    if induction && indVal.all.length != 1 then
      throwError "'induction' tactic does not support mutually inductive types, the eliminator '{mkRecName indVal.name}' has multiple motives"
    if induction && indVal.isNested then
      throwError "'induction' tactic does not support nested inductive types, the eliminator '{mkRecName indVal.name}' has multiple motives"
    let elimName := if induction then mkRecName indVal.name else mkCasesOnName indVal.name
    getElimInfo elimName
  else
    let elimId := optElimId[1]
    let elimName ← withRef elimId do resolveGlobalConstNoOverloadWithInfo elimId
    withRef elimId <| getElimInfo elimName

private def shouldGeneralizeTarget (e : Expr) : MetaM Bool := do
  if let .fvar fvarId .. := e then
    return (←  fvarId.getDecl).hasValue -- must generalize let-decls
  else
    return true

private def generalizeTargets (exprs : Array Expr) : TacticM (Array Expr) := do
  if (← withMainContext <| exprs.anyM (shouldGeneralizeTarget ·)) then
    liftMetaTacticAux fun mvarId => do
      let (fvarIds, mvarId) ← mvarId.generalize (exprs.map fun expr => { expr })
      return (fvarIds.map mkFVar, [mvarId])
  else
    return exprs

def elabCasesTargets (targets : Array Syntax) : TacticM (Array Expr) :=
  withMainContext do
    let args ← targets.mapM fun target => do
      let hName? := if target[0].isNone then none else some target[0][0].getId
      let expr ← elabTerm target[1] none
      return { expr, hName? : GeneralizeArg }
    if (← withMainContext <| args.anyM fun arg => shouldGeneralizeTarget arg.expr <||> pure arg.hName?.isSome) then
      liftMetaTacticAux fun mvarId => do
        let argsToGeneralize ← args.filterM fun arg => shouldGeneralizeTarget arg.expr <||> pure arg.hName?.isSome
        let (fvarIdsNew, mvarId) ← mvarId.generalize argsToGeneralize
        let mut result := #[]
        let mut j := 0
        for arg in args do
          if (← shouldGeneralizeTarget arg.expr) || arg.hName?.isSome then
            result := result.push (mkFVar fvarIdsNew[j]!)
            j := j+1
          else
            result := result.push arg.expr
        return (result, [mvarId])
    else
      return args.map (·.expr)

-- # End of duplicate code

def appendMVars (old : Array MVarId) (new : Array MVarId) : TacticM (Array MVarId) := 
  return old ++ new

-- Resembles `evalAlts` in Core Lean
def getMVarsFromAlts (elimInfo : ElimInfo) (alts : Array (Name × MVarId)) (optPreTac : Syntax) (altsSyntax : Array Syntax)
    (initialInfo : Info)
    (numEqs : Nat := 0) (numGeneralized : Nat := 0) (toClear : Array FVarId := #[]) : TacticM (Array MVarId) := do
  checkAltNames alts altsSyntax
  let hasAlts := altsSyntax.size > 0
  if hasAlts then
    -- default to initial state outside of alts
    withInfoContext go (pure initialInfo)
  else go
where
  go := do
    let alts := reorderAlts alts altsSyntax
    let hasAlts := altsSyntax.size > 0
    let mut usedWildcard := false
    let mut subgoals := #[] -- when alternatives are not provided, we accumulate subgoals here
    let mut altsSyntax := altsSyntax

    -- TODO foreach, add mvar to list, or alts.mapM
    let mut mvars : List MVarId := []
    
    for (altName, altMVarId) in alts do
      let numFields ← getAltNumFields elimInfo altName
      let mut isWildcard := false
      let altStx? ←
        match altsSyntax.findIdx? (fun alt => getAltName alt == altName) with
        | some idx =>
          let altStx := altsSyntax[idx]!
          altsSyntax := altsSyntax.eraseIdx idx
          pure (some altStx)
        | none => match altsSyntax.findIdx? (fun alt => getAltName alt == `_) with
          | some idx =>
            isWildcard := true
            pure (some altsSyntax[idx]!)
          | none =>
            pure none
      match altStx? with
      | none =>
        -- Change: Ignore this match, 
        -- this is probably a match without any alternative syntax, all intro's are inaccessible anyways
        let mut (_, altMVarId) ← altMVarId.introN numFields
        match (← Cases.unifyEqs? numEqs altMVarId {}) with
        | none   => pure () -- alternative is not reachable
        | some (altMVarId', _) =>
          (_, altMVarId) ← altMVarId'.introNP numGeneralized
          for fvarId in toClear do
            altMVarId ← altMVarId.tryClear fvarId
          let altMVarIds ← applyPreTac altMVarId
          if !hasAlts then
            -- User did not provide alternatives using `|`
            subgoals := subgoals ++ altMVarIds.toArray
          else if altMVarIds.isEmpty then
            pure ()
          else
            logError m!"alternative '{altName}' has not been provided"
            altMVarIds.forM fun mvarId => admitGoal mvarId
      | some altStx =>
        let mut mvarsWithinAlt : List MVarId := []
        (subgoals, usedWildcard, mvarsWithinAlt) ← withRef altStx do
          let unusedAlt :=
            if isWildcard then
              pure (#[], usedWildcard, [])
            else
              throwError "alternative '{altName}' is not needed"
          let altVarNames := getAltVarNames altStx
          let numFieldsToName ← if altHasExplicitModifier altStx then pure numFields else getNumExplicitFields altMVarId numFields
          if altVarNames.size > numFieldsToName then
            logError m!"too many variable names provided at alternative '{altName}', #{altVarNames.size} provided, but #{numFieldsToName} expected"
          let mut (fvarIds, altMVarId) ← altMVarId.introN numFields altVarNames.toList (useNamesForExplicitOnly := !altHasExplicitModifier altStx)

          saveAltVarsInfo altMVarId altStx fvarIds
          match (← Cases.unifyEqs? numEqs altMVarId {}) with
          | none => unusedAlt
          | some (altMVarId', _) =>
            (_, altMVarId) ← altMVarId'.introNP numGeneralized
            for fvarId in toClear do
              altMVarId ← altMVarId.tryClear fvarId
            let altMVarIds ← applyPreTac altMVarId
            if altMVarIds.isEmpty then
              unusedAlt
            else
              let mut subgoals := subgoals
              for altMVarId' in altMVarIds do
                subgoals ← evalAlt altMVarId' altStx subgoals
              pure (subgoals, usedWildcard || isWildcard, altMVarIds)    
        mvars := mvars ++ mvarsWithinAlt

    if usedWildcard then
      altsSyntax := altsSyntax.filter fun alt => getAltName alt != `_
    unless altsSyntax.isEmpty do
      logErrorAt altsSyntax[0]! "unused alternative"
    setGoals subgoals.toList
    -- Change, actually return mvars
    return mvars.toArray
  applyPreTac (mvarId : MVarId) : TacticM (List MVarId) :=
    if optPreTac.isNone then do
      return [mvarId]
    else
      evalTacticAt optPreTac[0] mvarId

-- Resembles `evalCases` in Core Lean
def getMVarsFromCaseMatch (stx : Syntax) : TacticM (Array MVarId) :=
  match expandCases? stx with
  | some stxNew => do
    -- Changed to ignore macro expansion, since evalTactic does not automatically reduce to a correctly nested call to this function
    trace[Elab.induction] m!"Current implementation ignores macro expansion"
    return #[]
  | _ => focus do
    let targets ← elabCasesTargets stx[1].getSepArgs
    let optInductionAlts := stx[3]
    let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
    let alts :=  getAltsOfOptInductionAlts optInductionAlts
    let targetRef := stx[1]
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := false)
    let mvarId ← getMainGoal
    let initInfo ← mkTacticInfo (← getMCtx) (← getUnsolvedGoals) (← getRef)
    let tag ← mvarId.getTag
    mvarId.withContext do
      let targets ← addImplicitTargets elimInfo targets
      let result ← withRef targetRef <| mkElimApp elimInfo targets tag
      let elimArgs := result.elimApp.getAppArgs
      let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]!
      let motiveType ← inferType elimArgs[elimInfo.motivePos]!
      let mvarId ← generalizeTargetsEq mvarId motiveType targets
      let (targetsNew, mvarId) ← mvarId.introN targets.size

      mvarId.withContext do
        setMotiveArg mvarId elimArgs[elimInfo.motivePos]!.mvarId! targetsNew
        mvarId.assign result.elimApp

        -- Changed call to `evalAlts` to modified version that returns `Array MVarId`
        return (←  getMVarsFromAlts elimInfo result.alts optPreTac alts initInfo (numEqs := targets.size) (toClear := targetsNew))

-- Resembles `evalInduction` in Core Lean
-- def 
def getMVarsFromInductionMatch (stx : Syntax) : TacticM (Array MVarId) := 
  match expandInduction? stx with
  | some stxNew => do
    -- Changed to ignore macro expansion, since evalTactic does not automatically reduce to a correctly nested call to this function
      trace[Elab.induction] m!"Current implementation ignores macro expansion"
      return #[]
  | _ => focus do
    let optInductionAlts := stx[4]
    let alts := getAltsOfOptInductionAlts optInductionAlts
    let targets ← withMainContext <| stx[1].getSepArgs.mapM (elabTerm · none)
    let targets ← generalizeTargets targets
    let elimInfo ← withMainContext <| getElimNameInfo stx[2] targets (induction := true)
    let mvarId ← getMainGoal
    -- save initial info before main goal is reassigned
    let initInfo ← mkTacticInfo (← getMCtx) (← getUnsolvedGoals) (← getRef)
    let tag ← mvarId.getTag
    mvarId.withContext do
      let targets ← addImplicitTargets elimInfo targets
      checkTargets targets
      let targetFVarIds := targets.map (·.fvarId!)
      let (n, mvarId) ← generalizeVars mvarId stx targets
      mvarId.withContext do
        let result ← withRef stx[1] do -- use target position as reference
          mkElimApp elimInfo targets tag
        trace[Elab.induction] "elimApp: {result.elimApp}"
        let elimArgs := result.elimApp.getAppArgs
        setMotiveArg mvarId elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
        let optPreTac := getOptPreTacOfOptInductionAlts optInductionAlts
        mvarId.assign result.elimApp

        -- Changed call to `evalAlts` to modified version that returns `Array MVarId`
        return (←  getMVarsFromAlts elimInfo result.alts optPreTac alts initInfo (numGeneralized := n) (toClear := targetFVarIds))
where
  checkTargets (targets : Array Expr) : MetaM Unit := do
    let mut foundFVars : FVarIdSet := {}
    for target in targets do
      unless target.isFVar do
        throwError "index in target's type is not a variable (consider using the `cases` tactic instead){indentExpr target}"
      if foundFVars.contains target.fvarId! then
        throwError "target (or one of its indices) occurs more than once{indentExpr target}"

-- # TMP DUPLICATE CODE
structure StateDiff where
  newlyChangedGoal : Option Term
  newDecls : Array LocalDecl -- TODO: Change LocalDecl to something that can't change
  changedDecls : Array LocalDecl
  removedDecls : Array LocalDecl

def StateDiff.toMessageData (s : StateDiff) : MessageData :=
  m!"isGoalChanged: {if s.newlyChangedGoal == none then "false" else "true"}, 
      newDecls: [{s.newDecls.map fun ldecl => ldecl.type}], 
      changedDecls: [{s.changedDecls.map fun ldecl => ldecl.type}],
      removedDecls: [ {s.removedDecls.map fun ldecl => ldecl.type} ]"

def goalsToStateDiff (oldGoal : MVarId) (newGoal : MVarId) : TacticM StateDiff := do
  let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
  let newGoalType ← instantiateMVars (← newGoal.getDecl).type
  let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData
  let newlyChangedGoal := if isSameGoal then none else some (← delab newGoalType)

  let oldLCtx := (← oldGoal.getDecl).lctx
  let newLCtx := (← newGoal.getDecl).lctx

  let mut newDecls := #[]
  let mut changedDecls := #[]
  let mut removedDecls := #[]

  for newDecl in newLCtx do
    if !newDecl.isAuxDecl then
      let mut foundMatch : Bool := false
      for oldDecl in oldLCtx do
        if !oldDecl.isAuxDecl then
          if newDecl.userName == oldDecl.userName then
            foundMatch := true
            if !(newDecl.type.consumeMData == oldDecl.type.consumeMData) then
              changedDecls := changedDecls.push newDecl
      if !foundMatch then
        newDecls := newDecls.push newDecl

  for oldDecl in oldLCtx do
    if !oldDecl.isAuxDecl then
      let mut foundMatch : Bool := false
      for newDecl in newLCtx do
        if !newDecl.isAuxDecl then
          if oldDecl.userName == newDecl.userName then
            foundMatch := true
      if !foundMatch then
        removedDecls := removedDecls.push oldDecl

  return StateDiff.mk newlyChangedGoal newDecls changedDecls removedDecls
-- # END DUPLICATE CODE

def mapMVarToNote (oldGoal : MVarId) (newGoal : MVarId) : TacticM (TSyntax `tactic) := do
  newGoal.withContext do
    let s ← goalsToStateDiff oldGoal newGoal
    match s.newlyChangedGoal with
    | none =>
      match (s.newDecls ++ s.changedDecls) with
      | #[] => `(tactic|show $(← delab (← instantiateMVars (← newGoal.getDecl).type)))
      | decls => 
        let binders ← decls.mapM (fun decl => declToBinder decl)
        `(tactic|note $[$binders]*)
    | some t => 
      match (s.newDecls ++ s.changedDecls) with
      | #[] => `(tactic|show $t)
      | decls => 
        let binders ← decls.mapM (fun decl => declToBinder decl)
        `(tactic|show $[$binders]* ⊢ $t)

def getMVarsFromMatch (oldGoal : MVarId) (matchTactic : TSyntax `tactic) (isInduction : Bool) : TacticM (Array (TSyntax `tactic)) := do
  oldGoal.withContext do
    withoutModifyingState do 
      match isInduction with
      | true =>   
        let mvars ← getMVarsFromInductionMatch matchTactic.raw
        mvars.mapM (fun mvar => do mapMVarToNote oldGoal mvar)          
      | false =>  
        let mvars ← getMVarsFromCaseMatch matchTactic.raw
        mvars.mapM (fun mvar => do mapMVarToNote oldGoal mvar)

end InductionHelper
