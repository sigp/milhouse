import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- A range reported empty excludes every successfully read pending value in
    that range. Bulk content preservation only needs this direction of range
    correctness; positive answers may conservatively visit extra subtrees. -/
def RangeExcludesValues {T U : Type} (mapInst : UpdateMap U T) (updates : U) : Prop :=
  ∀ (lo hi query : Std.Usize) (found : Option T),
    mapInst.has_any_in_range updates lo hi = ok false →
    mapInst.get updates query = ok found →
    lo.val ≤ query.val → query.val < hi.val → found = none

end milhouse.update_map
