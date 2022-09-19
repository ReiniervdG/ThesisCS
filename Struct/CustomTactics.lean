import Lean

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

/- 
  # Description of the purpose of this file 

  Extends the tactic version of `show` to also allow `show .. by ..` statements like proof term mode supports

  Introduces functionality to assert hypotheses, e.g.
  `by assert_hyp h : α` Checks named hypothesis `h` of type `α`
  `by assert_hyp : α ` Checks any hypothesis of type `α`
  `by assert_goal α` Checks goal is of type `α`

  Defines `TSyntax` objects for the elements of the `fix` and `note` tactic
  Defines mapping of those `TSyntax` objects to relevant tactics
  Defines expansion functions to unpack any `fix` and `note` tactic with optional arguments

  Elaborates the `note` tactic;
  `note (ha : α) (_ : β)` -> `assert_hyp ha : α; assert_hyp : β`
  `note ⊢ α` -> `assert_goal α`
  
  `note (ha : α) (_ : β) ⊢ α` -> `assert_hyp ha : α; assert_hyp : β; assert_goal α`
  `note (ha : α) (_ : β) by intros ha _` -> `intros ha _; assert_hyp ha : α; assert_hyp hb: β`  

  `note (ha : α) (_ : β) ⊢ α by intros ha _` -> `intros ha _; assert_hyp ha : α; assert_hyp hb: β; assert_goal α`

  Simple Elaboration of `fix` to `note` tactic
  `fix (ha : α) (_ : β) ⊢ α` -> `note (ha : α) (_ : β) ⊢ α by intros ha _`

  Finally some examples of `fix` and `note` tactics
-/

-- ##  Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => 
  `(exact show $type by $tacSeq)

-- ## Introduce assertion helpers
def assertGoal (goalType : TSyntax `term) : TacticM Unit := withMainContext do
  let realGoalType ← instantiateMVars (← (← getMainGoal).getDecl).type.consumeMData
  let expectedGoalType := (← elabTerm goalType none).consumeMData
  if !(realGoalType == expectedGoalType) then
    throwError m!"AssertionError: Expected goal {expectedGoalType}, got {realGoalType}"
  else
    return

elab &"assertGoal " t:term : tactic =>
  assertGoal t

def assertHyp (hypName : Option (TSyntax `ident) := none) (hypType : TSyntax `term) : TacticM Unit := withMainContext do
  let hypExpr ← elabTerm hypType none
  let mainGoal ← getMainGoal
  let lCtx := (← mainGoal.getDecl).lctx
  match hypName with
  | none => 
    for ldecl in lCtx do
      if ldecl.type.consumeMData == hypExpr.consumeMData then
        return
    throwError m!"Cannot find unnamed hypothesis of type {hypExpr}"
  | some hypName => 
    let hypNameExpr := hypName.getId
    for ldecl in lCtx do
      if ldecl.userName == hypNameExpr then
        if ldecl.type.consumeMData == hypExpr.consumeMData then
          return
        else
          throwError "Found named hypothesis, but types do not match"
    throwError "Cannot find named hypothesis TODO of type TODO"

elab &"assertHyp " hypName:(ident)? " : " hypType:term : tactic =>
  assertHyp hypName hypType

-- ## Define helpers for building tacticSeqs
def mkTacticSeqAppendTac (tacSeq : TSyntax ``tacticSeq) (tac : TSyntax `tactic) : TermElabM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) =>
    `(tacticSeq| { $[$(tacs.push tac)]* })
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) =>
    `(tacticSeq| $[$(tacs.push tac)]*)
  | _ => throwUnsupportedSyntax

def mkTacticSeqAppendTacs (tacSeq : TSyntax ``tacticSeq) (tail : Array (TSyntax `tactic)) : TermElabM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) =>
    `(tacticSeq| { $[$(tacs)]* $[$(tail)]* })
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) =>
    `(tacticSeq| $[$(tacs)]* $[$(tail)]*)
  | _ => throwUnsupportedSyntax

-- ## Define TSyntax objects for note
-- TODO: Optionally reuse the Lean.Tactics `binderIdent` syntax
syntax strucBinder := " (" ((ident <|> hole)) " : " term ") "
syntax strucGoal := " ⊢ " term
syntax strucBy := " by " tacticSeq

/- ## Map TSyntax to useful TSyntax -/
def strucBinderToAssertTactic : TSyntax ``strucBinder → TermElabM (TSyntax `tactic)
  | `(strucBinder| ($i:ident : $u:term)) => `(tactic|assertHyp $i : $u)
  | `(strucBinder| (_ : $u:term)) => `(tactic|assertHyp : $u)
  | _ => throwUnsupportedSyntax

def strucGoalToAssertGoal : TSyntax ``strucGoal → TermElabM (TSyntax `tactic)
  | `(strucGoal| ⊢ $t:term) => `(tactic|assertGoal $t)
  | _ => throwUnsupportedSyntax

def strucByToTacSeq : TSyntax ``strucBy → TermElabM (TSyntax ``tacticSeq)
  | `(strucBy| by $tacSeq:tacticSeq) => `(tacticSeq|$tacSeq)
  | _ => throwUnsupportedSyntax

def strucBinderToId (b : TSyntax `strucBinder) : TermElabM (TSyntax [`ident, `Lean.Parser.Term.hole]) := do
  match b with
  | `(strucBinder| ($i:ident : $u:term)) => return i
  | `(strucBinder| ($h:hole : $u:term)) => return h
  | _ => throwUnsupportedSyntax

-- ## Map from state to necessary TSyntax objects
def declToBinder (decl : LocalDecl) : TermElabM (TSyntax `strucBinder) := do
  if decl.userName.hasMacroScopes then
    return (← `(strucBinder|(_ : $(← delab decl.type))))
  else 
    return (← `(strucBinder|($(mkIdent decl.userName) : $(← delab decl.type))))

-- ## Expand optional syntax structures to optional tacticSeq
def expandStrucBy (osb : Option (TSyntax `strucBy)) : TermElabM (Option (TSyntax ``tacticSeq)) := do
  match osb with
  | some sb => 
    return (← strucByToTacSeq sb)
  | none => 
    return none

def expandBinders (lhs : Option (TSyntax ``tacticSeq)) (bs : Array (TSyntax `strucBinder)) : TermElabM (Option (TSyntax ``tacticSeq)) := do
  let mut tacs : Array (TSyntax `tactic) := #[]
  for binder in bs do
    tacs := tacs.push (← strucBinderToAssertTactic binder)
  match lhs with
  | some tacSeq => return (← mkTacticSeqAppendTacs tacSeq tacs)
  | none => 
    -- Match to ensure we return none if it's empty
    match tacs with
    | #[] => return none
    | nonzeroTacs => return some (← `(tacticSeq| $[$(nonzeroTacs)]*))

def expandStrucGoal (lhs : Option (TSyntax ``tacticSeq)) (osg : Option (TSyntax `strucGoal)) : TermElabM (Option (TSyntax ``tacticSeq)) := do
  match osg with
  | some sg =>
    match lhs with
    | some tacSeq => return (← mkTacticSeqAppendTac tacSeq (← strucGoalToAssertGoal sg))
    | none => 
      return some (← `(tacticSeq|$(← strucGoalToAssertGoal sg):tactic))
  | none =>
    return lhs 

elab &"note " bs:strucBinder* optStrucGoal:(strucGoal)? optStrucBy:(strucBy)? : tactic => do
  match (← expandStrucGoal (← expandBinders (← expandStrucBy optStrucBy) bs) optStrucGoal) with
  | some tacSeq => 
    addTrace `note m!"{tacSeq}"
    evalTactic tacSeq
  | none => logWarning "No tacSeq to run"

-- TODO optional fix that the squigle line under fix is not the correct length, something about withRef
elab &"fix " bs:strucBinder* strucGoal:strucGoal : tactic => do
  let ids ← bs.mapM (fun b => strucBinderToId b)
  evalTactic (← `(tactic|note $bs:strucBinder* $strucGoal:strucGoal by intros $[$ids]*))


example : α → β → α := by
  intros ha _
  exact ha
example : α → β → α := by
  note (ha : α) (_ : β) ⊢ α by intros ha _
  exact ha
example : α → β → α := by
  fix (ha : α) (_ : β) ⊢ α
  exact ha
