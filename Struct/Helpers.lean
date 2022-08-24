import Lean

import Struct.CustomTactics

open 
  Lean 
  Lean.Parser.Tactic 
  Lean.Elab

-- TODO: Create structure that completely determines changes before and after tacticSeq
-- hasGoalChanged : Bool
-- declsAdded : Array LocalDecl
-- declsChanged : Array LocalDecl (or LocalDecl × LocalDecl if we need old one as well)
-- .. TODO

-- TODO: Create function that takes 2 `MVarId`s and constructs the change structure object

-- TODO: Make Syntax object based on change structure object


-- TODO: Refactor to `compareLCtx`, returning list of lostDecls, addedDecls, changedDecls
-- TODO: Also check with usernames
def diffLCtx (ctx₁ : LocalContext) (ctx₂: LocalContext) : Array LocalDecl := Id.run do
  let mut x := #[]
  -- TODO: change for hashmaps instead of double loops
  for ldecl₁ in ctx₁ do
    let mut foundDecl := false
    for ldecl₂ in ctx₂ do
      if ldecl₁.type.consumeMData == ldecl₂.type.consumeMData then
        foundDecl := true
        break
    if !foundDecl then 
      x := x.push ldecl₁
  return x

def getTacs (ts : TSyntax ``tacticSeq) : TermElabM (Array (TSyntax `tactic)) :=
  match ts with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) => return tacs
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) => return tacs
  | _ => throwError "unknown syntax"

-- Matches existing tacticSeq `ts` and appends tactic `t` at the end
def mkTacticSeqAppend (ts : TSyntax ``tacticSeq) (t : TSyntax `tactic) : TermElabM (TSyntax ``tacticSeq) :=
  match ts with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) =>
    `(tacticSeq| { $[$(tacs.push t)]* })
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) =>
    `(tacticSeq| $[$(tacs.push t)]*)
  | _ => throwError "unknown syntax"

def mkShow (t : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax ``tacticSeq) :=
  `(tacticSeq|
      show $t by
        $tacSeq)

-- def mkSuffices
def mkSuffices (t : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax ``tacticSeq) := do
  let finishTac ← `(tactic|exact this)
  let newTacSeq ← mkTacticSeqAppend tacSeq finishTac
  `(tacticSeq|
      suffices $t by
        $newTacSeq)

-- def mkHave
def mkHave (t : Term) (tacSeq : TSyntax ``tacticSeq) (n : Option Ident := none) : TermElabM (TSyntax ``tacticSeq) :=
  match n with
  | some name => 
    `(tacticSeq|
      have $name : $t := by
        $tacSeq)
  | none => 
    `(tacticSeq|
      have : $t := by
        $tacSeq)

-- def mkFix ... TODO from intro/intros

-- def mkStrucNote ... TODO

-- def mkCases
-- def mkCases (target : TSyntax ``casesTarget) (cases : Array Term) : TermElabM (TSyntax ``tacticSeq) := do
  -- match tacSeq with
  -- | `(tactic|rfl) => sorry
  -- | _ => sorry
  -- let n : Term := _
  -- let a ← `(tactic|
  --   cases $target with
  --   | $n => sorry)
  -- sorry

-- def mkInduction
