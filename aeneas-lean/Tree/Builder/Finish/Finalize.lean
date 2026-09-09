import Tree.Builder.Finish.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.tree

/-- The common finalization suffix succeeds on every nonempty normalized
builder and returns its one completed dense root, with unchanged metadata. -/
theorem finishTreeAndFinalize_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (cursor : Std.Usize)
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevelValid : self.level.val = 0 ∨ self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val = subtreeCapacity self.packing_factor self.depth.val)
    (hroot : self.depth.val + self.packing_depth.val < System.Platform.numBits)
    {base logical physical : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base self.stack.val
      self.depth.val logical physical)
    (hbase : base = if self.level.val = 0 then 0 else self.level.val - self.packing_depth.val)
    (hpositive : 0 < logical)
    (hcursor : physical = cursor.val * 2 ^ self.level.val) :
    ∃ tree, finishTreeAndFinalize ValueInst self cursor =
      ok (core.result.Result.Ok (tree, self.depth, self.length)) ∧
      DenseTree self.packing_factor tree self.depth.val logical := by
  obtain ⟨forest, hloop, hnormalizedFull⟩ := Builder.finish_tree_loop_success self cursor
    hlayout hlevelValid hcapacity hroot hnormalized hbase hpositive hcursor
  obtain ⟨entry, hentries, hdense⟩ := hnormalizedFull.full_physical_singleton hlayout hpositive hcapacity
  obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) forest [] entry hentries
  have hempty : alloc.vec.Vec.is_empty Global rest = ok true := by
    simp only [alloc.vec.Vec.is_empty, hrest, _root_.List.isEmpty_nil]
  refine ⟨maybeArcedTree entry, ?_, hdense⟩
  simp! only [finishTreeAndFinalize, Builder.finish_tree, hloop, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch, hpop, core.option.Option.ok_or,
    maybeArced_arced, hempty, ↓reduceIte]

end milhouse.tree
