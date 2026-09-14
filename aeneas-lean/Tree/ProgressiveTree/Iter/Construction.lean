import Tree.ProgressiveTree.Iter.Seek
import Tree.ProgressiveTree.Iter.Next

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Progressive iterator construction succeeds and establishes its exact suffix
    invariant for every machine index, including the end and indices beyond it.
    Density, packing layout, and representable layers supply all other bounds. -/
theorem ProgressiveTreeIter.from_index_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (root : ProgressiveTree T) (index length : Std.Usize)
    (hdense : root.Dense factor 0 length.val) (hfits : root.Fits factor 0) :
    ∃ self, ProgressiveTreeIter.from_index ValueInst root index length = ok self ∧
      ProgressiveTreeIter.Valid ValueInst factor self (root.elements.drop index.val) ∧
      self.length = length ∧ self.yielded = index := by
  let initial : ProgressiveTreeIter T :=
    { current_prog_node := some root, current_iter := none, prog_depth := 0#u32,
      length, yielded := index }
  obtain ⟨self, hseek, hvalid, hlength, hyielded⟩ :=
    ProgressiveTreeIter.seek_to_subtree_spec ValueInst hlayout initial root index rfl
      (by simpa [initial, progressiveCapacity] using hdense)
      (by simpa [initial] using hfits)
      (by simp [initial, progressiveCapacity]) rfl
  refine ⟨self, hseek, ?_, hlength, hyielded⟩
  simpa [initial, progressiveCapacity] using hvalid

/-- The constructed progressive iterator enumerates exactly the requested
    suffix through exhaustion, with its cursor and termination proved from
    the input representation rather than assumed from iterator output. -/
theorem ProgressiveTreeIter.from_index_yields {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (root : ProgressiveTree T) (index length : Std.Usize)
    (hdense : root.Dense factor 0 length.val) (hfits : root.Fits factor 0) :
    ∃ self, ProgressiveTreeIter.from_index ValueInst root index length = ok self ∧
      IteratorYields (ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
        self (root.elements.drop index.val) := by
  obtain ⟨self, hfrom, hvalid, _⟩ := ProgressiveTreeIter.from_index_spec ValueInst hlayout root index length hdense hfits
  exact ⟨self, hfrom, ProgressiveTreeIter.yields ValueInst hlayout self _ hvalid⟩

/-- The public progressive-tree iterator method enumerates the requested
    sequence suffix for every machine starting index. -/
theorem ProgressiveTree.iter_from_yields {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (root : ProgressiveTree T) (index length : Std.Usize)
    (hdense : root.Dense factor 0 length.val) (hfits : root.Fits factor 0) :
    ∃ self, ProgressiveTree.iter_from ValueInst root index length = ok self ∧
      IteratorYields (ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
        self (root.elements.drop index.val) :=
  ProgressiveTreeIter.from_index_yields ValueInst hlayout root index length hdense hfits

end milhouse.progressive_tree
