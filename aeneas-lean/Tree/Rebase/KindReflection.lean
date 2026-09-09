import Tree.Rebase.SelectedKindReflection

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- The input-based classifier gives the exact category of every successful
Rust rebase action. Accurate dense metadata connects the stored contents to
the source's length guards. No element or cache soundness, comparison
termination, assumed child execution, or cache-validity premise is needed. -/
theorem Tree.rebase_on_kind_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (.Ok action)) :
    orig.rebaseKind ValueInst.corecmpPartialEqInst base = action.kind := by
  rw [← Tree.rebaseKindFor_eq_of_dense ValueInst hlayout hdepth horig hbase]
  exact Tree.rebase_on_kindFor_spec ValueInst hrebase

end milhouse.tree
