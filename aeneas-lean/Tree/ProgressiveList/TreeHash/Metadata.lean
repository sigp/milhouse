import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Progressive lists are classified as lists regardless of their element
type, pending updates, or backing representation. -/
theorem ProgressiveList.tree_hash_type_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.Tree_hashTreeHash.tree_hash_type ValueInst mapInst =
      ok tree_hash.TreeHashType.List := rfl

/-- A progressive list cannot be packed into a parent chunk. The actual
trait method always panics, including for an empty or otherwise valid list. -/
theorem ProgressiveList.tree_hash_packed_encoding_panics {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U) :
    ProgressiveList.Insts.Tree_hashTreeHash.tree_hash_packed_encoding ValueInst mapInst self =
      fail .panic := rfl

theorem ProgressiveList.tree_hash_packing_factor_panics {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.Tree_hashTreeHash.tree_hash_packing_factor ValueInst mapInst =
      fail .panic := rfl

end milhouse.progressive_list
