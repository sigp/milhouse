import Tree.Iter.Path
import Tree.Iter.Stack

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- The saved frames follow the search path for the current index, and the
    cached geometry agrees with the root and its element packing layout.
    A live cursor always has at least one frame. -/
structure Iter.Valid {T : Type} (root : tree.Tree T) (depth : Std.Usize)
    (factor : Option Std.Usize) (packingDepth : Std.Usize) (length : utils.Length)
    (self : Iter T) : Prop where
  full_depth : self.full_depth = depth
  packing_factor : self.packing_factor = factor.getD 0#usize
  packing_depth : self.packing_depth = packingDepth
  length_eq : self.length = length
  path : Path packingDepth.val root depth.val self.index.val self.stack.val
  live : self.index.val < length.val → self.stack.val ≠ []

/-- Binary traversal construction succeeds and records exactly the supplied
    starting index, root, geometry, and length. It establishes its path invariant
    directly and needs no density or starting-index bound. -/
theorem Iter.from_index_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (index : Std.Usize) (root : tree.Tree T) (depth : Std.Usize) (length : utils.Length) :
    ∃ self, Iter.from_index ValueInst index root depth length = ok self ∧
      self.index = index ∧ self.stack.val = [root] ∧
      Iter.Valid root depth factor packingDepth length self := by
  let empty := alloc.vec.Vec.with_capacity (tree.Tree T) depth
  have hempty : empty.val = [] := rfl
  have hroom : empty.val.length < Usize.max := by
    rw [hempty]
    have := System.Platform.numBits_pos
    simp only [_root_.List.length_nil]
    scalar_tac
  obtain ⟨stack, hstack, hvalues⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec empty root hroom)
  have hsingleton : stack.val = [root] := by simpa [hempty] using hvalues
  let self : Iter T := ⟨stack, index, depth, factor.getD 0#usize, packingDepth, length⟩
  refine ⟨self, ?_, rfl, hsingleton, ?_⟩
  · unfold Iter.from_index
    dsimp only
    rw [hstack]
    simp only [bind_tc_ok, hlayout.opt_packing_factor_eq, hlayout.opt_packing_depth_eq,
      lift, hlayout.unwrap_opt_packing_depth_eq]
    cases factor <;> rfl
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change Path packingDepth.val root depth.val index.val stack.val
      rw [hsingleton]
      exact .stop _ _ _
    · intro _
      change stack.val ≠ []
      simp [hsingleton]

/-- An exhausted binary iterator returns `none` without changing its state,
    including when the index is beyond its recorded length. -/
theorem Iter.next_exhausted {T : Type} (ValueInst : Value T) (self : Iter T)
    (hexhausted : self.length ≤ self.index) :
    Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self = ok (none, self) := by
  rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
  simp only [utils.Length.as_usize, bind_tc_ok, if_pos hexhausted]

end milhouse.iter
