import Tree.Rebase.SelectedContents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Successful rebasing preserves the original materialized sequence, and
    equality actions also certify agreement with the base. Length and depth
    metadata describe the dense inputs. Positive element `eq` identifies equal
    unpacked values; packed elements need agreement only when every paired
    `ne` returns false. Corresponding caches agree at equal materialized lengths. -/
theorem Tree.rebase_on_contents_correct {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (core.result.Result.Ok action)) : action.ContentsCorrect orig base := by
  exact Tree.rebase_on_contents_correct_of_inputs ValueInst
    (Tree.rebaseContentInputs_of_dense ValueInst hlayout hdepth horig hbase hequality hhashes) hrebase

end milhouse.tree
