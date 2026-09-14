import Tree.HashCache

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- The binary rebase cache guard for inputs whose supplied lengths describe
their materialized sequences. It reads stored bytes and lengths only; it
asserts no collision law or correctness of a computed hash. -/
def RebaseHashShortcut (origHash baseHash : CacheHash) (origLength baseLength : Nat) : Prop :=
  (¬ ∀ byte ∈ origHash.val, byte = 0#u8) ∧ origHash.val = baseHash.val ∧ origLength = baseLength

end milhouse.tree
