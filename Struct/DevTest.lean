import Struct.Struct

set_option pp.rawOnError true
set_option trace.debug true

-- Case testing
-- example (n : Nat) : n > 0 := by
--   structured simp
--   structured cases n 
--   case zero => sorry