import Lean

open 
  Lean 
  Lean.Parser.Tactic 
  Lean.Elab

/- 
  # Helpers : Some functionality to automatically generate new names, partly inspired from Jannis Limperg Aesop directory
  https://github.com/JLimperg/aesop/blob/705bc02b138a0f9dd7502f97c827beefaf2b0f5b/Aesop/Util/Basic.lean#L1553
-/

-- TODO Some Name Generation functionality 
namespace String

def dropPrefix (s : String) (pre : String) : Option Substring :=
  let s := s.toSubstring
  if s.take pre.length == pre.toSubstring then
    s.drop pre.length
  else
    none

end String


namespace Substring

def parseIndexSuffix (s : Substring) : Option Nat :=
  if s.isEmpty then
    none
  else if s.front == '_' then
    s.drop 1 |>.toNat?
  else
    none

end Substring

namespace Lean.LocalContext

private inductive MatchUpToIndexSuffix
| exactMatch
| noMatch
| suffixMatch (i : Nat)

private def matchUpToIndexSuffix (n : Name) (query : Name) :
    MatchUpToIndexSuffix :=
  match n, query with
  | Name.str _ s₁, Name.str _ s₂ =>
    match s₁.dropPrefix s₂ with
    | none => MatchUpToIndexSuffix.noMatch
    | some suffix =>
      if suffix.isEmpty then
        MatchUpToIndexSuffix.exactMatch
      else
        match suffix.parseIndexSuffix with
        | none => MatchUpToIndexSuffix.noMatch
        | some i => MatchUpToIndexSuffix.suffixMatch i
  | n, query =>
    if n == query then
      MatchUpToIndexSuffix.exactMatch
    else
      MatchUpToIndexSuffix.noMatch

private def getUnusedUserNameIndex (lctx : LocalContext) (suggestion : Name) :
    Option Nat := Id.run do
  let mut minSuffix := none
  for ldecl in lctx do
    match matchUpToIndexSuffix ldecl.userName.eraseMacroScopes suggestion with
    | MatchUpToIndexSuffix.exactMatch =>
      minSuffix := updateMinSuffix minSuffix 1
    | MatchUpToIndexSuffix.noMatch =>
      continue
    | MatchUpToIndexSuffix.suffixMatch i =>
      minSuffix := updateMinSuffix minSuffix (i + 1)
  minSuffix
  where
    @[inline]
    updateMinSuffix : Option Nat → Nat → Option Nat
      | none, j => some j
      | some i, j => some $ i.max j

private def applyUserNameIndex (i : Option Nat) (suggestion : Name) : Name :=
  match i with
  | none => suggestion
  | some i => suggestion.appendIndexAfter i

def getUnusedName' (lctx : LocalContext) (suggestion : Name) : Name :=
  let suggestion := suggestion.eraseMacroScopes
  applyUserNameIndex (lctx.getUnusedUserNameIndex suggestion) suggestion

partial def getUnusedUserNames (lctx : LocalContext) (n : Nat) (suggestion : Name) :
    Array Name :=
  if n == 0 then
    #[]
  else
    let suggestion := suggestion.eraseMacroScopes
    let acc := Array.mkEmpty n
    match lctx.getUnusedUserNameIndex suggestion with
    | none => loop (acc.push suggestion) (n - 1) 1
    | some i => loop acc n i
  where
    loop (acc : Array Name) (n i : Nat) : Array Name :=
      match n with
      | 0 => acc
      | n + 1 => loop (acc.push $ suggestion.appendIndexAfter i) n (i + 1)

end LocalContext

def getUnusedUserName [Monad m] [MonadLCtx m] (suggestion : Name) : m Name :=
  return (← getLCtx).getUnusedName' suggestion

def getUnusedUserNames [Monad m] [MonadLCtx m] (n : Nat) (suggestion : Name) :
    m (Array Name) :=
  return (← getLCtx).getUnusedUserNames n suggestion

def mkFreshIdWithPrefix [Monad m] [MonadNameGenerator m] («prefix» : Name) :
    m Name := do
  let ngen ← getNGen
  let r := { ngen with namePrefix := «prefix» }.curr
  setNGen ngen.next
  pure r

end Lean
