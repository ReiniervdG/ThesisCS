import Lean

-- import Struct.Helpers
import Struct.CustomTactics

open 
  Lean 
  Lean.Expr
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

-- TMP for debugging
set_option pp.rawOnError true

/-
  # Description of this file ..

-/

-- ## State to tactic(Seq) builders
def mkShow (newGoalTerm : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  `(tactic|show $newGoalTerm by $tacSeq)
 
def mkSuffices (newGoalTerm : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  `(tactic|suffices $newGoalTerm by $tacSeq)

def mkHave (decl : LocalDecl) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  let declType ← delab (← instantiateMVars decl.type)
  match decl.userName.hasMacroScopes with
  | true => 
    let id := mkIdent decl.userName
    `(tactic|have $id : $declType := by $tacSeq)
  | false => 
    `(tactic|have : $declType := by $tacSeq)

def mkFix (decls : Array LocalDecl) (goal : Term) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)
  `(tactic|fix $[$binders]* ⊢ $goal)

def mkNote (decls : Array LocalDecl := #[]) (optGoal : Option Term := none) (optTacSeq : Option (TSyntax ``tacticSeq)) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)  
  match optGoal with
  | some goal => 
    match optTacSeq with
    | some tacSeq => `(tactic|note $[$binders]* ⊢ $goal by $tacSeq)
    | none => `(tactic|show $[$binders]* ⊢ $goal)
  | none => 
    match optTacSeq with
    | some tacSeq => `(tactic|note $[$binders]* by $tacSeq)
    | none => 
      if binders.size == 0 then
        throwError "Nothing to note, TODO"
      else
        `(tactic|note $[$binders]*)


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
    if !newDecl.isAuxDecl then -- todo isImplementationDetail
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

def mapMVarToNote (oldGoal : MVarId) (newGoal : MVarId) : TacticM (TSyntax `tactic) := do
  newGoal.withContext do
    let s ← goalsToStateDiff oldGoal newGoal
    mkNote (s.changedDecls ++ s.newDecls) s.newlyChangedGoal none

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
  | _ => throwError "unknown syntax"

def replaceHoleWithNoteInductionAlt (old : TSyntax ``inductionAlt) (note : TSyntax `tactic) : TermElabM (TSyntax ``inductionAlt) := do
  match old with
  | `(inductionAlt| | $lhs $[$ids]* => ?_) => 
      `(inductionAlt| | $lhs $[$ids]* => 
        $note:tactic)
  | _ => 
    throwError "Shouldnt reach"

def replaceHoleWithNoteCaseTactic (old : TSyntax `tactic) (note : TSyntax `tactic) : TermElabM (TSyntax `tactic) := do
  match old with
  | `(tactic|case $tag $[$ids]* => skip) => 
      `(tactic|case $tag $[$ids]* => 
        $note:tactic)
  | _ => 
    throwError "Shouldnt reach"


-- ## Structured branches
def structuredIntros (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  addTrace `xx m!"Testxx"
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => throwError "Finishing with intros should be impossible"
  | [newGoal] => 
    let s ← goalsToStateDiff oldGoal newGoal

    match (s.newlyChangedGoal, s.newDecls, s.changedDecls, s.removedDecls) with
    | ((some newGoalTerm), newDecls, changedDecls, #[]) => 
      let suggestion ← mkFix (newDecls ++ changedDecls) newGoalTerm
      addTrace `structured m!"Try this: {suggestion}"
    | _ => throwError "Unexpected state: {StateDiff.toMessageData s}"
  | _ => throwError "Unexpected state: Multiple goals after executing intro statement"

-- TODO : Refactor out stuff

def structuredCasesOrInduction (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (target : TSyntax `term) (isInduction : Bool) : TacticM Unit :=
  oldGoal.withContext do
    let mut cases : Array (TSyntax ``inductionAlt) := #[]

    let env ← getEnv

    let targetExpr ← elabTerm target none
    let targetType ← inferType targetExpr
    let fnExpr := getAppFn targetType
    
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
                let ctorName := (← getLCtx).getUnusedName (.str .anonymous "a")
                ctorArgs := ctorArgs.push (mkIdent ctorName)

                if isInduction ∧ isAppOf decl.type fnName then
                  let indName := (← getLCtx).getUnusedName (.str ctorName "ih")
                  indArgs := indArgs.push (mkIdent indName)
              else
                let ctorName := (← getLCtx).getUnusedName decl.userName
                ctorArgs := ctorArgs.push (mkIdent ctorName)

                if isInduction ∧ isAppOf decl.type fnName then
                  -- Use previous human-readable userIdent and attempt to make that + "ih"
                  let indName := (← getLCtx).getUnusedName (.str ctorName "ih")
                  indArgs := indArgs.push (mkIdent indName)
            
            -- TODO consider ?_ instead of skip
            let case ← `(inductionAlt| | $ctorIdent $[$ctorArgs]* $[$indArgs]* => ?_)
            cases := cases.push case

          | _ => addTrace `xx m!"Unexpected state 02"
          
        | _ => addTrace `xx m!"Unexpected state 01"
      
      -- Do stuff with cases, find out mvars inside
      -- TODO if then else
      match isInduction with
      | true => 
        let matchWithoutNotes ← `(tactic| induction $target:term with $[$cases]*)
        let notes ← getNotesFromTac oldGoal matchWithoutNotes
        let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
        let matchWithNotes ← `(tactic| induction $target:term with $[$casesWithNotes]*)
        addTrace `test m!"Try this: {matchWithNotes}"
      | false => 
        let matchWithoutNotes ← `(tactic| cases $target:term with $[$cases]*)
        let notes ← getNotesFromTac oldGoal matchWithoutNotes
        let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
        let matchWithNotes ← `(tactic| cases $target:term with $[$casesWithNotes]*)
        addTrace `test m!"Try this: {matchWithNotes}"
    | _ => addTrace `xx m!"Unexpected state 00"

-- structuredCasesDefault: When multiple post-goals, but no match on cases or induction
def structureCasesDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (newGoals : List MVarId) : TacticM Unit := do
  let mut cases : Array (TSyntax `tactic) := #[]

  -- Construct a case for each new goal
  -- TODO : Move to separate function and use MapM
  for newGoal in newGoals do 
    let s ← goalsToStateDiff oldGoal newGoal

    -- For any inaccessible decl, create a new unused name, and use that
    let mut caseArgs : Array (TSyntax ``binderIdent) := #[]
    for decl in s.newDecls do
      if decl.userName.hasMacroScopes then
        let caseArgName := (← newGoal.getDecl).lctx.getUnusedName (.str .anonymous "a") 
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

  addTrace `xx m!"Test: {casesWithoutNotes} {casesWithNotes}"

  -- Append all 
  let suggestion ← mkTacticSeqAppendTacs tacSeq casesWithNotes
  addTrace `structured m!"Try this: {suggestion}"

def structuredDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => 
    let suggestion ← mkShow (← delab (← oldGoal.getDecl).type) tacSeq
    addTrace `structured m!"Try this: {suggestion}"
  | [newGoal] => 
    let s ← goalsToStateDiff oldGoal newGoal

    match (s.newlyChangedGoal, s.newDecls, s.changedDecls, s.removedDecls) with
    | (none, #[], #[], #[]) => 
      throwError "Unexpected state: no changes before and after tactic evaluation"
    | ((some newGoal), #[], #[], #[]) => 
      let suggestion ← mkSuffices newGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (none, #[newDecl], #[], #[]) => -- TODO, can you both match on having nonzero newDecls, and name it so we can use it
      let suggestion ← mkHave newDecl tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (newlyChangedGoal, newDecls, changedDecls, #[]) =>
      let suggestion ← mkNote (newDecls ++ changedDecls) newlyChangedGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | _ => 
      throwError "Unexpected state: Currently only occurs if any local declaration is lost after tactic evaluation.
                  Removed Declarations: {s.removedDecls.map (fun ldecl => ldecl.type)}"

  | newGoals => 
    structureCasesDefault tacSeq oldGoal newGoals
    pure ()

-- ## Core structured elaboration
def structuredCore (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  match (← getUnsolvedGoals) with
  | [] => 
    logWarning m!"No goals to solve, kind of shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] => 
    let tacs ← getTacs tacSeq
    match tacs with
    | #[] => logWarning "No tactics in tacSeq"
    -- TODO: Match on alternatives of existing structured tactics (from/by, etc)
    | #[t] =>
      match t with
      -- Matching `suffices` Syntax
      | `(tactic|suffices $_ by $_) 
      | `(tactic|show $_ by $_) 
      | `(tactic|have $[$id]? : $_ := by $_) 
      | `(tactic|have $[$id]? : $_ := $_) 
      | `(tactic|clear $_)
        => 
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq
      -- TODO: Only match on intro $_, then unpack the content further in structuredIntros
      | `(tactic|intro $[$ids:ident]*)
      -- | `(tactic|intros $ids*)
        => 
        let ids : Array (TSyntax `ident) := ids -- TODO mwe Zulip
        addTrace `xx m!"{ids.map (fun x => repr x.raw)}"
        structuredIntros tacSeq goal
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

example (n : Nat) : n = n := by
  structured 
    cases n
    try apply Even.zero
  repeat sorry

example : α ∧ β → β := by
  structured intro ⟨_, _⟩ 

-- TODO: Wrap defaultCases in a show .. by .. block ?
