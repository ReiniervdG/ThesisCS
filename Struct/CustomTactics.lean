import Lean

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

-- assertHyp also allows an unnamed assertion with a (_ : type) binder, but is not fully supported in suggestions anymore
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
        if (← instantiateMVars ldecl.type).consumeMData == hypExpr.consumeMData then
          return
        else
          throwError "Found named hypothesis, but types do not match, {ldecl.type} vs {hypExpr}"
    throwError "Cannot find named hypothesis {hypName} of type {hypExpr}"

elab &"assertHyp " hypName:(ident)? " : " hypType:term : tactic =>
  assertHyp hypName hypType

-- ## Define helpers for building tacticSeqs
def mkTacticSeqAppendTac (tacSeq : TSyntax ``tacticSeq) (tac : TSyntax `tactic) : TermElabM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic]* }) =>
    `(tacticSeq| { $[$(tacs.push tac)]* })
  | `(tacticSeq| $[$tacs:tactic]*) =>
    `(tacticSeq| $[$(tacs.push tac)]*)
  | _ => throwUnsupportedSyntax

def mkTacticSeqAppendTacs (tacSeq : TSyntax ``tacticSeq) (tail : Array (TSyntax `tactic)) : TermElabM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic]* }) =>
    `(tacticSeq| { $[$(tacs ++ tail)]*})
  | `(tacticSeq| $[$tacs:tactic]*) =>
    `(tacticSeq| $[$(tacs ++ tail)]*)
  | _ => throwUnsupportedSyntax

-- ## Define TSyntax objects for note
syntax strucBinder := " (" ((ident <|> hole)) " : " term ") "
syntax strucBy := " by " tacticSeq

syntax strucBinders := (strucBinder+ " ⊢ ")

/- ## Map TSyntax to useful TSyntax -/
def strucBinderToAssertTactic : TSyntax ``strucBinder → TermElabM (TSyntax `tactic)
  | `(strucBinder| ($i:ident : $u:term)) => `(tactic|assertHyp $i : $u)
  | `(strucBinder| (_ : $u:term)) => `(tactic|assertHyp : $u)
  | _ => throwUnsupportedSyntax

def strucByToTacSeq : TSyntax ``strucBy → TermElabM (TSyntax ``tacticSeq)
  | `(strucBy| by $tacSeq:tacticSeq) => `(tacticSeq|$tacSeq)
  | _ => throwUnsupportedSyntax

def declToBinder (decl : LocalDecl) : TermElabM (TSyntax `strucBinder) := do
  if decl.userName.hasMacroScopes then
    return (← `(strucBinder|(_ : $(← delab (← instantiateMVars decl.type)))))
  else 
    return (← `(strucBinder|($(mkIdent decl.userName) : $(← delab (← instantiateMVars decl.type)))))

-- # Main custom tactics

elab &"s_suffices " bs:strucBinder* " ⊢ " g:term sb:strucBy : tactic => do
  evalTactic (← strucByToTacSeq sb)
  for b in bs do
    evalTactic (← strucBinderToAssertTactic b)
  evalTactic (← `(tactic|show $g))

elab &"s_have" bs:strucBinder* osb:(strucBy)? : tactic => do
  if let some sb := osb then
    evalTactic (← strucByToTacSeq sb)
  for b in bs do
    evalTactic (← strucBinderToAssertTactic b)

elab &"s_show" obs:(strucBinders)? g:term : tactic => do
  if let some bs := obs then
    match bs with
    | `(strucBinders| $bs:strucBinder* ⊢) =>
      for b in bs do
        evalTactic (← strucBinderToAssertTactic b)
    | _ => throwUnsupportedSyntax
  evalTactic (← `(tactic|show $g))
