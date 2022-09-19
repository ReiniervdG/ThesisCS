import Lean

import Struct.CustomTactics

open 
  Lean 
  Lean.Parser.Tactic 
  Lean.Elab

/- 
  # Helpers : Some functionality to automatically generate new names, largely copied from Jannis Limperg Aesop directory
  https://github.com/JLimperg/aesop/blob/705bc02b138a0f9dd7502f97c827beefaf2b0f5b/Aesop/Util/Basic.lean#L1553
-/

-- TODO copy needed name generation from Jannis

-- TODO Below is mostly deprecated code, to be restructured later

-- TODO: Also check with usernames
-- @[deprecated]
-- def diffLCtx (ctx₁ : LocalContext) (ctx₂: LocalContext) : Array LocalDecl := Id.run do
--   let mut x := #[]
--   -- TODO: change for hashmaps instead of double loops
--   for ldecl₁ in ctx₁ do
--     let mut foundDecl := false
--     for ldecl₂ in ctx₂ do
--       if ldecl₁.type.consumeMData == ldecl₂.type.consumeMData then
--         foundDecl := true
--         break
--     if !foundDecl then 
--       x := x.push ldecl₁
--   return x

-- @[deprecated]
-- def getTacs (ts : TSyntax ``tacticSeq) : TermElabM (Array (TSyntax `tactic)) :=
--   match ts with
--   | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) => return tacs
--   | `(tacticSeq| $[$tacs:tactic $[;]?]*) => return tacs
--   | _ => throwError "unknown syntax"
