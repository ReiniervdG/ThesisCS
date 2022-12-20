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

def mkSuggestion (fvars : Array FVarId := #[]) (optTarget : Option Term := none) (optTacSeq : Option (TSyntax ``tacticSeq)) : TermElabM (TSyntax `tactic) := do
  let decls ← fvars.mapM fun fvar => do fvar.getDecl
  let binders ← decls.mapM fun decl => declToBinder decl

  match (optTarget, binders, optTacSeq) with
  | (none, #[], _) => throwError "Nothing to annotate!"
  | (some target, #[], none) => `(tactic|show $target)
  | (some target, #[], some tacSeq) => `(tactic|s_suffices $target:term by $tacSeq)
  | (some target, bs, none) => `(tactic|s_show $[$bs]* ⊢ $target)
  | (some target, bs, some tacSeq) => `(tactic|s_suffices $[$bs]* ⊢ $target by $tacSeq)
  | (none, #[_], some tacSeq) => 
      let decl := decls[0]!
      let declIdent := mkIdent decl.userName
      let declType ← delab (← instantiateMVars decl.type) 
      `(tactic|have $declIdent:ident : $declType := by $tacSeq)
  | (none, bs, some tacSeq) => `(tactic|s_have $[$bs]* by $tacSeq)
  | (none, bs, none) => `(tactic|s_have $[$bs]*)

-- ## Segment description
structure StateDiff where
  target : Option (TSyntax `term)
  diffFvars : Array FVarId

def goalsToStateDiff (oldGoal : MVarId) (newGoal : MVarId) : TacticM StateDiff := do
  let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
  let newGoalType ← instantiateMVars (← newGoal.getDecl).type
  let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData
  let target := if isSameGoal then none else some (← delab newGoalType)

  let oldLCtx := (← oldGoal.getDecl).lctx
  let newLCtx := (← newGoal.getDecl).lctx

  let mut fvars := #[]

  for newDecl in newLCtx do
    if !newDecl.isImplementationDetail then
      let mut foundMatch : Bool := false
      for oldDecl in oldLCtx do
        if !oldDecl.isImplementationDetail then
          if newDecl.userName == oldDecl.userName then
            foundMatch := true
            if !(newDecl.type.consumeMData == oldDecl.type.consumeMData) then
              fvars := fvars.push newDecl.fvarId
      if !foundMatch then
        fvars := fvars.push newDecl.fvarId

  return StateDiff.mk target fvars 

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
    newGoal.withContext do
      match s.diffFvars with
      | (#[fvar]) => 
        return ← delab (← instantiateMVars (← fvar.getDecl).type)
      | _ => throwError "Not a single hypothesis change detected"

def mapMVarToNote (oldGoal : MVarId) (newGoal : MVarId) : TacticM (TSyntax `tactic) := do
  newGoal.withContext do
    let s ← goalsToStateDiff oldGoal newGoal
    mkSuggestion s.diffFvars s.target none

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

-- Function that turns a specific TSyntax to a more generic TSyntax
def mapBinderIdentToTerm (id : TSyntax ([`ident, `Lean.Parser.Term.hole])): TacticM (TSyntax `term) := do 
  match id with 
  | `(term|$id) => `(term|$id)

-- ## Structured branches
def structuredIntros (target : Expr) (terms : TSyntaxArray `term) : TacticM Unit := do
  forallBoundedTelescope target (some terms.size) fun fvarExprs _ => do 
    let mut lctx ← getLCtx
    let mut binders := #[]
    let localInsts <- getLocalInstances
    for t in terms, fvarExpr in fvarExprs do
      match fvarExpr with
      | .fvar fvarId =>
        let typeExpr := (← fvarId.getDecl).type
        let type <- withLCtx lctx localInsts $ delab typeExpr
        let baseAutoName := if ← isProp typeExpr then "h" else "a"

        match t with
        | `( _ ) =>
          let autoName := lctx.getUnusedName (.str .anonymous baseAutoName)
          lctx := lctx.setUserName fvarId autoName
          binders := binders.push (← `(term| ($(mkIdent autoName) : $type)))
        | `( $id:ident ) =>
          binders := binders.push (← `(term| ($id : $type)))
        | `( ( _ : $t:term) ) =>
          let autoName := lctx.getUnusedName (.str .anonymous baseAutoName)
          lctx := lctx.setUserName fvarId autoName
          binders := binders.push (← `(term| ($(mkIdent autoName) : $t)))
        | `( ($id:ident : $t:term) ) =>
          binders := binders.push (← `(term| ($id : $t)))
        | _ =>
          binders := binders.push (← `(term| ($t : $type)))
      | _ => throwUnsupportedSyntax
    let suggestion ← `(tactic|intro $[$binders]*)
    addTrace `structured m!"Try this: {suggestion}"

-- Sub function for `structuredCasesOrInduction`
def mkInductionAlt (fnName : Name) (ctor : Name) (isInduction : Bool) : TacticM (TSyntax ``inductionAlt) := do
  let env ← getEnv
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
      return case

    | _ => unreachable!
  | _ => unreachable!

-- When matched on `induction` or `cases`
def structuredCasesOrInduction (oldGoal : MVarId) (target : TSyntax `term) (isInduction : Bool) : TacticM Unit := do
  let targetExpr ← elabTerm target none
  let targetType ← inferType targetExpr
  let fnExpr := targetType.getAppFn
  
  match fnExpr with
  | .const fnName _ =>
    let ival ← getInductiveValFromMajor targetExpr

    let cases := (← ival.ctors.mapM fun ctor => mkInductionAlt fnName ctor isInduction).toArray
    
    if isInduction then
      let matchWithoutNotes ← `(tactic| induction $target with $[$cases]*)
      let notes ← getNotesFromTac oldGoal matchWithoutNotes
      let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
      let matchWithNotes ← `(tactic| induction $target:term with $[$casesWithNotes]*)
      addTrace `structured m!"Try this: {matchWithNotes}"
    else
      let matchWithoutNotes ← `(tactic| cases $target:term with $[$cases]*)
      let notes ← getNotesFromTac oldGoal matchWithoutNotes
      let casesWithNotes ← cases.zip notes.toArray |>.mapM (fun (case, note) => do replaceHoleWithNoteInductionAlt case note)
      let matchWithNotes ← `(tactic| cases $target:term with $[$casesWithNotes]*)
      addTrace `structured m!"Try this: {matchWithNotes}"
  | _ => unreachable!

-- Sub function for `structuredCasesDefault`
def mkDefaultCase (oldGoal : MVarId) (newGoal : MVarId) : TacticM (TSyntax `tactic) := do
  withoutModifyingState do
    newGoal.withContext do
      let caseTag ← `(binderIdent|$(mkIdent (← newGoal.getTag)):ident)

      let s ← goalsToStateDiff oldGoal newGoal

      -- Go over newFVars, rename if they are inaccessible, keep track in lctx 
      let mut lctx := (← newGoal.getDecl).lctx
      let mut caseArgs := #[]
      
      for fvar in s.diffFvars do
        let decl ← fvar.getDecl
        if decl.userName.hasMacroScopes then
          let baseName := if ← isProp decl.type then "h" else "a"
          let caseArgName := lctx.getUnusedName (.str .anonymous baseName) 
          let caseArgIdent := mkIdent caseArgName
          caseArgs := caseArgs.push (← `(binderIdent|$caseArgIdent:ident))
          lctx := lctx.setUserName fvar caseArgName

      -- Use updated lctx specifically to make the suggestions, this time from fvars because decls change, fvars dont 
      withLCtx lctx (← getLocalInstances) do
        let noteSuggestion ← mkSuggestion s.diffFvars s.target none
        `(tactic|case $caseTag $[$caseArgs]* => $noteSuggestion:tactic)

-- When multiple post-goals, but no match on cases or induction
def structuredCasesDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (newGoals : List MVarId) : TacticM Unit := do
  let cases ← newGoals.mapM fun newGoal => mkDefaultCase oldGoal newGoal
  let suggestion ← mkTacticSeqAppendTacs tacSeq cases.toArray
  addTrace `structured m!"Try this: {suggestion}"

-- When no syntax is matched with a single post-goal
def structuredDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  withMainContext do
    match (← getUnsolvedGoals) with
    | [] => 
      addTrace `structured m!"Goal finished, no need to add structure!"
    | [newGoal] => 
      let s ← goalsToStateDiff oldGoal newGoal
      let suggestion ← mkSuggestion s.diffFvars s.target tacSeq
      addTrace `structured m!"Try this: {suggestion}"
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
    | #[tac] =>
      match tac with
      -- Native Lean 4 tactics
      | `(tactic|suffices $_) 
      | `(tactic|show $_) 
      | `(tactic|clear $_)
      | `(tactic|have $_:ident : $_:term := $_)
      | `(tactic|let $_:ident : $_:term := $_)
      -- Custom tactics
      | `(tactic|s_suffices $[$bs]* ⊢ $_ by $_)
      | `(tactic|s_suffices $_:term by $_)
      | `(tactic|s_have $[$bs]* by $_)
      | `(tactic|s_have $[$bs]*)
      | `(tactic|s_show $[$bs]* ⊢ $_)
        => 
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq

      | `(tactic|have $_:hole : $type:term := $rhs) -- hole-named typed
        =>
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|have $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have : $type:term := $rhs) -- unnamed typed
        =>
          let autoName := mkIdent (.str .anonymous "this")
          let suggestion ← `(tactic|have $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have $id:ident := $rhs) -- named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let suggestion ← `(tactic|have $id : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have $_:hole := $rhs) -- hole-named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|have $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have := $rhs) -- unnamed untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName := mkIdent (.str .anonymous "this")
          let suggestion ← `(tactic|have $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac

      | `(tactic|let $_:hole : $type:term := $rhs)  -- hole-named typed
        => 
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|let $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|let $_:hole := $rhs) -- hole-named untyped    
        => 
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm autoType
          let suggestion ← `(tactic|let $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac

      | `(tactic|intro $ts:term*) 
        => 
          evalTactic tac
          withMainContext do
            -- If intro is called anonymously, manually add the hole for easier function
            if ts.size == 0 then do
              let hole ← `( _ )
              structuredIntros goalType #[hole]
            else
              structuredIntros goalType ts

      | `(tactic|intros $ids*)
        => 
          evalTactic tac
          withMainContext do
            if ids.size == 0 then do
              -- The procedure to handle unbounded intros is to execute tactic
              -- And compare goals, the amount of newFVars is the bound for structuredIntros
              -- That amount of underscores are provided as terms to structuredIntros
              let newGoal ← getMainGoal
              let s ← goalsToStateDiff goal newGoal
              let termHoles := mkArray s.diffFvars.size (← `( _ ))
              structuredIntros goalType termHoles
            else
              let termIds ← ids.mapM mapBinderIdentToTerm            
              structuredIntros goalType termIds

      | `(tactic|cases $target:term) 
        => 
          structuredCasesOrInduction goal target false
          evalTactic tac
      | `(tactic|induction $target:term)
        => 
          structuredCasesOrInduction goal target true
          evalTactic tac
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
  admit

example : Even 4 := by
  structured 
    have _ : Even 0 := Even.zero
  structured have : Even 0 := Even.zero

  structured 
    have x := Even.zero

  structured
    have := Even.zero
  let _ : Even 0 := Even.zero
  admit

example : α₁ → α₂ ∧ α₃ → α₄ ∧ α₅ → α₆ ∧ α₇ → α₁ := by
  structured
    intros
  -- intro (ha1 : α₁) (h : α₂ ∧ α₃) (h_1 : α₄ ∧ α₅) 
  admit
  

example (n m : Nat) : Even n ∧ Even m → Even 0 → Even 2 → Even (n + m) := by 
  -- intro
  -- intro _ 
  -- intro hnm
  -- intros _
  -- intro hnm _
  -- intros
  -- intros hm _
  -- structured intro ⟨hn, _⟩ _ _
  -- structured intro (⟨hn, _⟩ : Even n ∧ Even m)(h : Even 0)(h_1 : Even 2)
  structured intros
  admit

example : α ↔ α := by
  structured
    apply Iff.intro
    intro _
  repeat admit
  -- apply Iff.intro
  -- intro _
  -- case mp h => 
  --   s_show (h : α) ⊢ α
  -- case mpr => show α → α

example (n : Nat) : n = n := by
  structured cases n
  -- cases n with
  -- | zero => 
  --   show Nat.zero = Nat.zero
  --   admit
  -- | succ n_1 => 
  --   s_show (n_1 : Nat) ⊢ Nat.succ n_1 = Nat.succ n_1 
  --   admit
  admit


example : Even 4 := by
  structured repeat apply Even.add_two _ _
  admit


example (n m : Nat) (h : Even (n + m)) : m = 0 → Even n := by
  intro hm
  structured 
    rw [hm] at h
    simp at *
  admit
