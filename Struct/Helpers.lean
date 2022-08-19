import Lean

open Lean

def diff_lctx (ctx₁ : LocalContext) (ctx₂: LocalContext) : Array LocalDecl := Id.run do
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