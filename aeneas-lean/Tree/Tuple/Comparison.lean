import Tree.Funs

open Aeneas Aeneas.Std Result

namespace Pair.Insts.CoreCmpPartialEqPair

variable {T U : Type} (first : core.cmp.PartialEq T T)
  (second : core.cmp.PartialEq U U) (left right : T × U)

/-- Tuple inequality stops at the first true element `ne`. Neither element
`eq` nor the second element `ne` needs to return or satisfy any law. -/
theorem ne_of_left_true (hfirst : first.ne left.1 right.1 = ok true) :
    ne first second left right = ok true := by
  simp [ne, hfirst]

/-- A false first `ne` delegates exactly to the second `ne`, including its
failure or divergence. No relationship between `eq` and `ne` is assumed. -/
theorem ne_of_left_false (hfirst : first.ne left.1 right.1 = ok false) :
    ne first second left right = second.ne left.2 right.2 := by
  simp [ne, hfirst]

theorem ne_of_left_fail (error : Error)
    (hfirst : first.ne left.1 right.1 = fail error) :
    ne first second left right = fail error := by
  simp [ne, hfirst]

theorem ne_of_left_div (hfirst : first.ne left.1 right.1 = div) :
    ne first second left right = div := by
  simp [ne, hfirst]

/-- A false tuple inequality result requires exactly two false element `ne`
results. This is a success characterization, with no totality or coherence law. -/
theorem ne_false_iff :
    ne first second left right = ok false ↔
      first.ne left.1 right.1 = ok false ∧ second.ne left.2 right.2 = ok false := by
  cases hfirst : first.ne left.1 right.1 with
  | fail error => simp [ne, hfirst]
  | div => simp [ne, hfirst]
  | ok answer => cases answer <;> simp [ne, hfirst]

/-- A true tuple inequality result comes from the first true comparison or
from a false first comparison followed by a true second comparison. -/
theorem ne_true_iff :
    ne first second left right = ok true ↔
      first.ne left.1 right.1 = ok true ∨
        first.ne left.1 right.1 = ok false ∧ second.ne left.2 right.2 = ok true := by
  cases hfirst : first.ne left.1 right.1 with
  | fail error => simp [ne, hfirst]
  | div => simp [ne, hfirst]
  | ok answer => cases answer <;> simp [ne, hfirst]

end Pair.Insts.CoreCmpPartialEqPair
