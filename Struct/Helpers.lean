import Lean

import Struct.CustomTactics

open 
  Lean 
  Lean.Parser.Tactic 
  Lean.Elab

/- 
  # Helpers : Some functionality to automatically generate new names, partly inspired from Jannis Limperg Aesop directory
  https://github.com/JLimperg/aesop/blob/705bc02b138a0f9dd7502f97c827beefaf2b0f5b/Aesop/Util/Basic.lean#L1553
-/

-- TODO Some Name Generation functionality 
