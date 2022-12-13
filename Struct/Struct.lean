import Lean

import Struct.CustomTactics

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

/-
  # Stuct - Core of the `structured` tactic

  

-/

-- ## xx
def mkSuffices (newGoalTerm : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  `(tactic|s_suffices $newGoalTerm:term by $tacSeq)

def mkHave (decl : LocalDecl) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  let declType ← delab (← instantiateMVars decl.type)
  match decl.userName.hasMacroScopes with
  | true => 
    let id := mkIdent decl.userName
    `(tactic|have $id : $declType := by $tacSeq)
  | false =>
    let nameBase := if ← isProp decl.type then "h" else "a"
    let autoName := mkIdent $ (← getLCtx).getUnusedName (.str .anonymous nameBase)
    `(tactic|have $autoName : $declType := by $tacSeq)


def mkSuggestion (decls : Array LocalDecl := #[]) (optGoal : Option Term := none) (optTacSeq : Option (TSyntax ``tacticSeq)) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)  
  match optGoal with
  | some goal => 
    match optTacSeq with
    | some tacSeq => 
      if binders.size == 0 then
        `(tactic|s_suffices $goal:term by $tacSeq)    
      else
        `(tactic|s_suffices $[$binders]* ⊢ $goal by $tacSeq)
    | none => 
      if binders.size == 0 then
        `(tactic|show $goal)
      else
        `(tactic|s_show $[$binders]* ⊢ $goal)
  | none => 
    match optTacSeq with
    | some tacSeq => 
      if binders.size == 0 then
        throwError "No change of state detected, unreachable state, this should be caught by goal comparison match"
      else
        `(tactic|s_have $[$binders]* by $tacSeq)
    | none => 
      if binders.size == 0 then
        throwError "No change of state detected, unreachable state, this should be caught by goal comparison match"
      else
        `(tactic|s_have $[$binders]*)


-- ## Segment description
structure StateDiff where
  newlyChangedGoal : Option Term
  newDecls : Array LocalDecl
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
    if !newDecl.isImplementationDetail then
      let mut foundMatch : Bool := false
      for oldDecl in oldLCtx do
        if !oldDecl.isImplementationDetail then
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

def mkNameFromTerm (type : Term) : TacticM (TSyntax `ident) := do
  let elaboratedTerm ← elabTerm type none
  let nameBase := if (← isProp elaboratedTerm) then "h" else "a"
  let ident := mkIdent $ (← getLCtx).getUnusedName (.str .anonymous nameBase)
  return ident

def mkTypeFromTac (rhs : TSyntax `tactic) : TacticM (TSyntax `term) := 
  withoutModifyingState do
    let oldGoal ← getMainGoal
    evalTactic rhs
    let newGoal ← getMainGoal
    let s ← goalsToStateDiff oldGoal newGoal
    match (s.newDecls, s.changedDecls) with
    | (#[decl], #[]) => 
      return ← delab (← instantiateMVars decl.type)
    | (#[], #[decl]) => 
      return ← delab (← instantiateMVars decl.type)
    | _ => throwError "Not a single hypothesis change detected"

def mapMVarToNote (oldGoal : MVarId) (newGoal : MVarId) : TacticM (TSyntax `tactic) := do
  newGoal.withContext do
    let s ← goalsToStateDiff oldGoal newGoal
    mkSuggestion (s.changedDecls ++ s.newDecls) s.newlyChangedGoal none

def getNotesFromTac (oldGoal : MVarId) (tac : TSyntax `tactic) : TacticM (List (TSyntax `tactic)) := do
  oldGoal.withContext do
    withoutModifyingState do 
      evalTactic tac
      let mvars ← getUnsolvedGoals
      mvars.mapM (fun mvar => do mapMVarToNote oldGoal mvar)

def getNotesFromTacSeq (oldGoal : MVarId) (tac : TSyntax ``tacticSeq) : TacticM (List (TSyntax `tactic)) := do
  oldGoal.withContext do
    withoutModifyingState do 
      evalTactic tac
      let mvars ← getUnsolvedGoals
      mvars.mapM (fun mvar => do mapMVarToNote oldGoal mvar)

def getTacs (ts : TSyntax ``tacticSeq) : TermElabM (Array (TSyntax `tactic)) :=
  match ts with
  | `(tacticSeq| { $[$tacs:tactic]* }) => return tacs
  | `(tacticSeq| $[$tacs:tactic]*) => return tacs
  | _ => throwUnsupportedSyntax

def replaceHoleWithNoteInductionAlt (old : TSyntax ``inductionAlt) (note : TSyntax `tactic) : TermElabM (TSyntax ``inductionAlt) := do
  match old with
  | `(inductionAlt| | $lhs $[$ids]* => ?_) => 
      `(inductionAlt| | $lhs $[$ids]* => 
        $note:tactic)
  | _ => 
    throwUnsupportedSyntax

def replaceHoleWithNoteCaseTactic (old : TSyntax `tactic) (note : TSyntax `tactic) : TermElabM (TSyntax `tactic) := do
  match old with
  | `(tactic|case $tag $[$ids]* => skip) => 
      `(tactic|case $tag $[$ids]* => 
        $note:tactic)
  | _ => 
    throwUnsupportedSyntax

-- Function that turns a specific TSyntax to a more generic TSyntax
def mapBinderIdentToTerm (id : TSyntax ([`ident, `Lean.Parser.Term.hole])): TacticM (TSyntax `term) := do 
  match id with 
  | `(term|$id) => `(term|$id)

-- ## Structured branches
def structuredIntros (target : Expr) (terms : TSyntaxArray `term) : TacticM Unit := do
  forallBoundedTelescope target (some terms.size) fun fvarExprs _ => do 
    let mut lctx ← getLCtx
    let mut types := #[]
    let mut binders := #[]
    let localInsts <- getLocalInstances
    for t in terms, fvarExpr in fvarExprs do
      match fvarExpr with
      | .fvar fvarId =>
        let typeExpr := (← fvarId.getDecl).type
        let type <- withLCtx lctx localInsts $ delab typeExpr
        let baseAutoName := if ← isProp typeExpr then "h" else "a"
        types := types.push type

        match t with
        | `( _ ) =>
          let autoName := lctx.getUnusedName (.str .anonymous baseAutoName)
          lctx := lctx.setUserName fvarId autoName
          binders := binders.push (← `(term| ($(mkIdent autoName) : $type)))
          addTrace `xx m!"From underscore to ({autoName} : {type})"
        | `( $id:ident ) =>
          -- TODO verify id available
          binders := binders.push (← `(term| ($id : $type)))
          addTrace `xx m!"From only ident to ({id} : {type})"
        | `( ( _ : $t:term) ) =>
          let autoName := lctx.getUnusedName (.str .anonymous baseAutoName)
          lctx := lctx.setUserName fvarId autoName
          binders := binders.push (← `(term| ($(mkIdent autoName) : $t)))
          addTrace `xx m!"From only type to ({autoName} : {t})"
        | `( ($id:ident : $t:term) ) =>
          -- TODO: verify id available
          binders := binders.push (← `(term| ($id : $t)))
          addTrace `xx m!"This is a binder with ident, already structured"
        | _ =>
          binders := binders.push (← `(term| ($t : $type)))
          addTrace `xx m!"From dark magic to ({t} : {type})"
      | _ => throwUnsupportedSyntax
    let suggestion ← `(tactic|intro $[$binders]*)
    addTrace `test m!"Try this: {suggestion}"

-- TODO : Refactor out stuff
def structuredCasesOrInduction (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (target : TSyntax `term) (isInduction : Bool) : TacticM Unit :=
  oldGoal.withContext do
    let mut cases : Array (TSyntax ``inductionAlt) := #[]

    let env ← getEnv

    let targetExpr ← elabTerm target none
    let targetType ← inferType targetExpr
    let fnExpr := targetType.getAppFn
    
    match fnExpr with
    | .const fnName _ =>

      let ival ← getInductiveValFromMajor targetExpr

      for ctor in ival.ctors do
        let ctorInfo := env.find? ctor

        match ctor with
        | .str _ s => 
          let ctorIdent := mkIdent s

          match ctorInfo with
          | some (.ctorInfo cval) =>
            let decls ← forallTelescopeReducing cval.type fun args _ => 
              args.mapM (fun arg => arg.fvarId!.getDecl)

            let mut ctorArgs : Array Ident := #[]
            let mut indArgs : Array Ident := #[]

            for decl in decls do
              if decl.userName.hasMacroScopes then
                let baseName := if ← isProp decl.type then "h" else "a"
                let ctorName := (← getLCtx).getUnusedName (.str .anonymous baseName)
                ctorArgs := ctorArgs.push (mkIdent ctorName)

                if isInduction ∧ decl.type.isAppOf fnName then
                  let indName := (← getLCtx).getUnusedName (.str ctorName "ih")
                  indArgs := indArgs.push (mkIdent indName)
              else
                let ctorName := (← getLCtx).getUnusedName decl.userName
                ctorArgs := ctorArgs.push (mkIdent ctorName)

                if isInduction ∧ decl.type.isAppOf fnName then
                  let indName := (← getLCtx).getUnusedName (.str ctorName "ih")
                  indArgs := indArgs.push (mkIdent indName)
            
            let case ← `(inductionAlt| | $ctorIdent $[$ctorArgs]* $[$indArgs]* => ?_)
            cases := cases.push case

          | _ => addTrace `xx m!"Unexpected state 02"
          
        | _ => addTrace `xx m!"Unexpected state 01"
      
      if isInduction then
        let matchWithoutNotes ← `(tactic| induction $target:term with $[$cases]*)
        let notes ← getNotesFromTac oldGoal matchWithoutNotes
        let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
        let matchWithNotes ← `(tactic| induction $target:term with $[$casesWithNotes]*)
        addTrace `test m!"Try this: {matchWithNotes}"
      else
        let matchWithoutNotes ← `(tactic| cases $target:term with $[$cases]*)
        let notes ← getNotesFromTac oldGoal matchWithoutNotes
        let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
        let matchWithNotes ← `(tactic| cases $target:term with $[$casesWithNotes]*)
        addTrace `test m!"Try this: {matchWithNotes}"
    | _ => addTrace `xx m!"Unexpected state 00"

-- structuredCasesDefault: When multiple post-goals, but no match on cases or induction
def structuredCasesDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (newGoals : List MVarId) : TacticM Unit := do
  let mut cases : Array (TSyntax `tactic) := #[]

  -- Construct a case for each new goal
  -- TODO : Move to separate function and use MapM
  for newGoal in newGoals do 
    let s ← goalsToStateDiff oldGoal newGoal

    -- For any inaccessible decl, create a new unused name, and use that
    let mut caseArgs : Array (TSyntax ``binderIdent) := #[]
    for decl in s.newDecls do
      if decl.userName.hasMacroScopes then
        let baseName := if ← isProp decl.type then "h" else "a"
        let caseArgName := (← newGoal.getDecl).lctx.getUnusedName (.str .anonymous baseName) 
        let caseArgIdent := mkIdent caseArgName
        caseArgs := caseArgs.push (← `(binderIdent|$caseArgIdent:ident))

    -- Construct full case
    let caseIdName := mkIdent (← newGoal.getTag)
    let caseBinderId : TSyntax ``binderIdent ← `(binderIdent|$caseIdName:ident)
    let case ← `(tactic|case $caseBinderId $[$caseArgs]* => skip)
    cases := cases.push case  
  
  -- Construct notes with decided names
  let casesWithoutNotes ← `(tacticSeq| $[$cases]*)
  let notes ← getNotesFromTacSeq oldGoal casesWithoutNotes
  let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteCaseTactic case note)

  -- Append all 
  let suggestion ← mkTacticSeqAppendTacs tacSeq casesWithNotes
  addTrace `structured m!"Try this: {suggestion}"

def structuredDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => 
    addTrace `structured m!"Goal finished, no need to add structure!"
  | [newGoal] => 
    let s ← goalsToStateDiff oldGoal newGoal

    match (s.newlyChangedGoal, s.newDecls, s.changedDecls, s.removedDecls) with
    | (none, #[], #[], #[]) => 
      throwError "Unexpected state: no changes before and after tactic evaluation"
    | ((some newGoal), #[], #[], #[]) => 
      let suggestion ← mkSuffices newGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (none, #[newDecl], #[], #[]) =>
      let suggestion ← mkHave newDecl tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (newlyChangedGoal, newDecls, changedDecls, #[]) =>
      let suggestion ← mkSuggestion (newDecls ++ changedDecls) newlyChangedGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | _ => 
      throwError "Unexpected state: Currently only occurs if any local declaration is lost after tactic evaluation.
                  Removed Declarations: {s.removedDecls.map (fun ldecl => ldecl.type)}"

  | newGoals => 
    structuredCasesDefault tacSeq oldGoal newGoals

-- ## Core structured elaboration
def structuredCore (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  match (← getUnsolvedGoals) with
  | [] => 
    logWarning m!"No goals to solve, shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] => 
    let tacs ← getTacs tacSeq
    let goalType := (← goal.getDecl).type
    match tacs with
    | #[] => logWarning "No tactics in tacSeq"
    | #[t] =>
      match t with
      -- Native Lean 4 tactics
      | `(tactic|suffices $_) 
      | `(tactic|show $_) 
      | `(tactic|clear $_)
      | `(tactic|have $id:ident : $t:term := $rhs)
      | `(tactic|let $id:ident : $t:term := $rhs)
      -- Custom tactics
      | `(tactic|s_suffices $[$bs]* ⊢ $_ by $_)
      | `(tactic|s_suffices $_:term by $_)
      | `(tactic|s_have $[$bs]* by $_)
      | `(tactic|s_have $[$bs]*)
      | `(tactic|s_show $[$bs]* ⊢ $_)
        => 
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq

      | `(tactic|have $h:hole : $type:term := $rhs) -- hole-named typed
        =>
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|have $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
      | tac@`(tactic|have $id:ident := $rhs) -- named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let suggestion ← `(tactic|have $id : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
      | tac@`(tactic|have $h:hole := $rhs) -- hole-named untyped
      | tac@`(tactic|have := $rhs) -- unnamed untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm autoType
          let suggestion ← `(tactic|have $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"

      | `(tactic|let $h:hole : $type:term := $rhs)  -- hole-named typed
        => 
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|let $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
      | tac@`(tactic|let $h:hole := $rhs) -- hole-named untyped    
        => 
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm autoType
          let suggestion ← `(tactic|let $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"

      | tac@`(tactic|intro $ts:term*) 
        => 
          evalTactic tac
          withMainContext do
            -- If intro is called anonymously, manually add the hole for easier function
            if ts.size == 0 then do
              let hole ← `( _ )
              structuredIntros goalType #[hole]
            else
              structuredIntros goalType ts

      | tac@`(tactic|intros $ids*)
        => 
          evalTactic tac
          withMainContext do
            if ids.size == 0 then do
              -- The procedure to handle unbounded intros is to execute tactic
              -- And compare goals, the amount of newDecls is the bound for structuredIntros
              -- That amount of underscores are provided as terms to structuredIntros
              let newGoal ← getMainGoal
              let s ← goalsToStateDiff goal newGoal
              match (s.newDecls, s.changedDecls, s.removedDecls) with
              | (newDecls, #[], #[]) => 
                -- TODO there must be an easier way to create an newDecls.size array of _
                let mut termHoles := #[]
                for _ in newDecls do
                  termHoles := termHoles.push (← `( _ ))
                structuredIntros goalType termHoles
              | _ => throwUnsupportedSyntax
            else
              let termIds ← ids.mapM mapBinderIdentToTerm            
              structuredIntros goalType termIds

      | `(tactic|cases $target:term) 
        => structuredCasesOrInduction tacSeq goal target false
      | `(tactic|induction $target:term)
        => structuredCasesOrInduction tacSeq goal target true
      | _ => structuredDefault tacSeq goal
    | _ => structuredDefault tacSeq goal
  | _ =>
    addTrace `structured m!"Multiple goals pre-execution is not supported for this tactic. 
      Executing tacitc, but no suggestions provided"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structuredCore t

-- TMP Testing code below

inductive Even : Nat → Prop
| zero : Even Nat.zero
| add_two : ∀ k : Nat, Even k → Even (k+2)
| combine_two (n : Nat) (hn : Even n) : ∀ m : Nat, Even m → Even (n + m)

example : Even 4 := by
  structured repeat apply Even.add_two _ _


example : Even 4 := by
  structured 
    have _ : Even 0 := Even.zero

  structured 
    have x := Even.zero

  structured
    have := Even.zero
  let _ : Even 0 := Even.zero

example : α₁ → α₂ ∧ α₃ → α₄ ∧ α₅ → α₆ ∧ α₇ → α₁ := by
  structured
    intros
  -- intro (ha1 : α₁) (h : α₂ ∧ α₃) (h_1 : α₄ ∧ α₅) 
  

example (n m : Nat) : Even n ∧ Even m → Even 0 → Even 2 → Even (n + m) := by 
  -- intro
  -- intro _ 
  -- intro hnm
  -- intros _
  -- intro hnm _
  -- intros
  -- intros hm _
  -- structured intro ⟨hn, _⟩ _ _
  structured intro (⟨hn, _⟩ : Even n ∧ Even m)(h : Even 0)(h_1 : Even 2)
