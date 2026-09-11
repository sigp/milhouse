import Tree.ProgressiveList.Iter.Construction

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_list

/-- The actual borrowed `IntoIterator` implementation constructs the same
    valid cursor as `iter` and enumerates the complete merged sequence. -/
theorem ProgressiveList.into_iter_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ∃ cursor,
      SharedAProgressiveList.Insts.CoreIterTraitsCollectIntoIteratorSharedATProgressiveListIter.into_iter
        ValueInst mapInst self = ok cursor ∧
      ProgressiveListIter.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = 0#usize ∧
      IteratorYields (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
        cursor contents := by
  exact ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits

end milhouse.progressive_list
