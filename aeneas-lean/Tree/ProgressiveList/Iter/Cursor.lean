import Tree.ProgressiveList.Iter.Overlay
import Tree.ProgressiveTree.Iter.Construction

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A list cursor keeps the exact backing suffix at its current index and the
    same pending overlay as the represented contents. The recorded logical
    length is exact. No bounds on the current index are needed for exhaustion. -/
structure ProgressiveListIter.Valid {T U : Type} (ValueInst : Value T)
    (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    (backing contents : _root_.List T) (self : ProgressiveListIter T U) : Prop where
  tree : ProgressiveTreeIter.Valid ValueInst factor self.tree_iter (backing.drop self.index.val)
  overlay : ProgressiveListIter.Overlay mapInst self.updates backing contents
  length_eq : self.length.val = contents.length

end milhouse.progressive_list
