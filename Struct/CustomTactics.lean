import Lean

-- Need to import, but circular dependency
-- import Struct.Helpers

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

def assertGoal (goalType : TSyntax `term) : TacticM Unit := do
  let realGoalType ← instantiateMVars (← (← getMainGoal).getDecl).type.consumeMData
  let mut expectedGoalType := (← elabTerm goalType none).consumeMData
  if !(realGoalType == expectedGoalType) then
    throwError m!"AssertionError: Expected goal {expectedGoalType}, got {realGoalType}"
  else
    return

elab &"assert_goal " t:term : tactic =>
  assertGoal t

def assertHyp (hypName : Option (TSyntax `ident) := none) (hypType : TSyntax `term) : TacticM Unit := do
  let hypExpr ← elabTerm hypType none
  let mainGoal ← getMainGoal
  let lCtx := (← mainGoal.getDecl).lctx
  match hypName with
  | none => 
    for ldecl in lCtx do
      if ldecl.type.consumeMData == hypExpr.consumeMData then
        addTrace `structured m!"Found it unnamed!"
        return
    throwError m!"Cannot find unnamed hypothesis of type {hypExpr}"
  | some hypName => 
    let hypNameExpr := hypName.getId
    for ldecl in lCtx do
      if ldecl.userName == hypNameExpr then
        if ldecl.type.consumeMData == hypExpr.consumeMData then
          addTrace `structured m!"Found it named!"
          return
        else
          throwError "Found named hypothesis, but types do not match"
    throwError "Cannot find named hypothesis TODO of type TODO"

elab &"assert_hyp " hypName:(ident)? " : " hypType:term : tactic =>
  assertHyp hypName hypType

-- Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => 
  `(exact show $type by $tacSeq)

/- # BEGIN note tactic block -/
/- ## Define helper functions, appendTacSeq or something -/
-- TODO Duplicates from Helpers, but circular dependency
def getTacs (ts : TSyntax ``tacticSeq) : MacroM (Array (TSyntax `tactic)) :=
  match ts with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) => return tacs
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) => return tacs
  | _ => Macro.throwUnsupported

def mkTacticSeqAppendTac (tacSeq : TSyntax ``tacticSeq) (tac : TSyntax `tactic) : MacroM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) =>
    `(tacticSeq| { $[$(tacs.push tac)]* })
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) =>
    `(tacticSeq| $[$(tacs.push tac)]*)
  | _ => Macro.throwUnsupported

def mkTacticSeqAppendTacs (tacSeq : TSyntax ``tacticSeq) (tacs : Array (TSyntax `tactic)) : MacroM (TSyntax ``tacticSeq) :=
  match tacSeq with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) =>
    `(tacticSeq| { $[$(tacs)]* $[$(tacs)]* })
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) =>
    `(tacticSeq| $[$(tacs)]* $[$(tacs)]*)
  | _ => Macro.throwUnsupported

-- END PARTIAL DUPLICATE BLOCK

/- ## Define syntax -/
syntax strucBinder := "(" ("_" <|> ident) " : " term ")"
syntax strucGoal := "⊢ " term
syntax strucBy := "by " tacticSeq

/- ## Map TSyntax to useful terms -/
def strucBinderToAssertTactic : TSyntax ``strucBinder → MacroM (TSyntax `tactic)
  | `(strucBinder| ($i:ident : $u:term)) => `(tactic|assert_hyp $i : $u)
  | `(strucBinder| (_ : $u:term)) => `(tactic|assert_hyp : $u)
  | _ => Macro.throwUnsupported

def strucGoalToAssertGoal : TSyntax ``strucGoal → MacroM (TSyntax `tactic)
  | `(strucGoal| ⊢ $t:term) => `(tactic|assert_goal $t)
  | _ => Macro.throwUnsupported

def strucByToTacSeq : TSyntax ``strucBy → MacroM (TSyntax ``tacticSeq)
  | `(strucBy| by $tacSeq:tacticSeq) => `(tacticSeq|$tacSeq)
  | _ => Macro.throwUnsupported

/- ## Elaborate note macro -/
-- ### Possibility 1: Continuously expand an Option tacticSeq with new 
def expandStrucBy (osb : Option (TSyntax `strucBy)) : MacroM (Option (TSyntax ``tacticSeq)) := do
  match osb with
  | some sb => 
    return (← strucByToTacSeq sb)
  | none => 
    return none

def expandBinders (lhs : Option (TSyntax ``tacticSeq)) (bs : Array (TSyntax `strucBinder)) : MacroM (Option (TSyntax ``tacticSeq)) := do
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

def expandStrucGoal (lhs : Option (TSyntax ``tacticSeq)) (osg : Option (TSyntax `strucGoal)) : MacroM (Option (TSyntax ``tacticSeq)) := do
  match osg with
  | some sg =>
    match lhs with
    | some tacSeq => return (← mkTacticSeqAppendTac tacSeq (← strucGoalToAssertGoal sg))
    | none => return none
  | none => 
    return lhs   

-- ### Possibility 2: gather all tactics separately, concatenate at the end (harder to )

-- TODO: this note tactic doesn't reduce to a single tactic but a tacSeq, how does that work?
macro &"note " bs:strucBinder* optStrucGoal:(strucGoal)? optStrucBy:(strucBy)? : tactic => do
  let x ← expandStrucGoal (← expandBinders (← expandStrucBy optStrucBy) bs) optStrucGoal
  match x with
  | some y => 
    let z ← getTacs y
    `(tactic|{$[$(z)]*})
  | none => `(tactic|rfl)

-- example : α → β → α := by
--   -- intros ha _
--   note (ha : α) (_ : β) -- TODO: this probably cuts of the tacticSeq after this
--     ⊢ α 
--     by intros ha _
--   exact ha
/- # END note tactic block-/


-- TESTING BELOW

-- syntax strucBinder := "(" ("_" <|> ident) " : " term ")"
-- syntax strucGoal := "⊢ " term
-- syntax strucBy := "by " tacticSeq

def strucBinderToTerm : TSyntax ``strucBinder → MacroM Term
  | `(strucBinder| ($i:ident : $u:term)) => `(($i : $u))
  | `(strucBinder| (_ : $u:term)) => `((_ : $u))
  | _ => Macro.throwUnsupported

-- def strucBinderToAssertTactic : TSyntax ``strucBinder → MacroM (TSyntax `tactic)
--   | `(strucBinder| ($i:ident : $u:term)) => `(tactic|assert_hyp $i : $u)
--   | `(strucBinder| (_ : $u:term)) => `(tactic|assert_hyp : $u)
--   | _ => Macro.throwUnsupported

def strucGoalToTerm : TSyntax ``strucGoal → MacroM Term
  | `(strucGoal| ⊢ $t:term) => return t
  | _ => Macro.throwUnsupported

-- def strucGoalToAssertGoal : TSyntax ``strucGoal → MacroM (TSyntax `tactic)
--   | `(strucGoal| ⊢ $t:term) => `(tactic|assert_goal $t)
--   | _ => Macro.throwUnsupported

-- def strucByToTacSeq : TSyntax ``strucBy → MacroM (TSyntax ``tacticSeq)
--   | `(strucBy| by $tacSeq:tacticSeq) => `(tacticSeq|$tacSeq)
--   | _ => Macro.throwUnsupported
 
macro &"fix " bs:strucBinder* " ⊢ " t:term : tactic => do
  `(intro $(← bs.mapM strucBinderToTerm):term*)

syntax (name := fix') &"fix' " strucBinder " ⊢ " term : tactic

open Lean.Elab.Tactic in
@[tactic fix']
def evalFix' : Tactic := λ stx =>
  withRef stx do
  match stx with
  | `(tactic| fix $bs:strucBinder* ⊢ $t:term) =>
    for b in bs do
      match b with
      | `(strucBinder| ($i:ident : $u:term)) => sorry
      | `(strucBinder| (_ : $u:term)) => sorry
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
--

-- def tmpHelper (tacSeq : Option TSyntax ``tacticSeq) (tac : TSyntax `tactic) : TSyntax ``tacticSeq :=
--   sorry

-- Attempt at note, simplify to `(tacSeq; assert_hyps bs; assert_goal newGoal)
-- macro &"note " bs:strucBinder* optStrucGoal:(strucGoal)? optStrucBy:(strucBy)? : tactic => do
--   match optStrucBy with
--   | some strucBy => 
--     let byTacSeq ← strucByToTacSeq strucBy
--     let mut hypTacs := #[]
--     for b in bs do
--       let hypTac ← strucBinderToAssertTactic b
--       hypTacs := hypTacs.push hypTac

--     match optStrucGoal with
--     | some strucGoal => 
--       let goalTac ← strucGoalToAssertGoal strucGoal
--       -- Return tacSeq with all the things
--       `(tactic|rfl)
--     | none => 
--       -- return tacSeq without goalTac
--       `(tactic|rfl)
--   | none => 
--     -- TODO: duplicate code from other match statement, separate function
--     -- Return tacSeq without strucBy
--     `(tacticSeq|rfl)


--  `(tactic|intros h1 _)
  -- Match on tacSeq
  -- match tacSeq with
  -- | some tacSeq => 
    -- We have some tacSeq, append relevant stuff
    -- NOTE: this is in Helpers, needs to be imported eventually, but is circular
    -- mkTacticSeqAppend tacSeq `(tactic|rfl)
  -- | none => sorry
    -- We don't have tacSeq, just execute assertions

  -- match newGoal with
  -- | some newGoal => sorry
  -- | none => sorry

-- def handleBinders (bs : TSyntaxArray `structBinder): MetaM (TSyntax ``tacticSeq) := do 
  -- `(tacticSeq|rfl)

  -- match id with
  -- | some tmp =>
  --   match tmp with
  --   | `(strucGoal|⊢ $t:term) => `(tactic|rfl) 
  --   | _ => Macro.throwUnsupported
  -- | none => `(tactic|rfl) 


-- example : α → β → α  := by
--   note (ha : α) (_ : β) ⊢ α by intros ha _ 
--   intros ha _
--   assert_goal α
--   assert_hyp (ha : α)
--   assert_hyp (_ : β)



-- OLD BELOW

-- TODO: specify term further, requiring type annotations
-- macro &"fix " ts:term* " ⊢ " newGoal:(term)? : tactic => `(tactic|intro $ts:term*; assert_goal $newGoal)

-- assert_hyp (h1 : a) (h2 : b)

-- macro structNote
-- macro &"structuredNote "  


-- Could this even be a macro? Need some way to extract lists of idents and types, though
-- (hyps : Array (Option Ident × Expr))
-- "fix " [[[hypIdent:ident]? " : " hypType:term "]+ ⊢ " newGoal:term
-- => `(tacticSeq| intros hypIdent1 hypIdent2 ..; assertHyp hypIdent1 : hypType1; assertHyp ...; assertGoal newGoal)

-- def fix (hyps : Array (Option Ident × Expr)) (newGoal : Expr) : TacticM Unit := do
--   let a ← `(tactic|sorry) 

-- elab &"fix " : tactic =>
--   fix

-- Structured Annotation
-- `strucNote ($name : $type)* (⊢ $newGoal)? (by $tacSeq)?`
-- execute tacSeq
-- assert all hyps
-- if newGoal, then check that's new goal, else check oldGoal same

-- (ha : a)
-- note (ha : b) by ..
-- apply ha

-- example (ns : List α) : 0 = 0 := by
--   induction ns with
--   | cons (x : α) (xs : List α) => sorry
--   | _  => sorry