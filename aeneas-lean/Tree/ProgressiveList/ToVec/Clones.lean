import Tree.ProgressiveList.ToVec.Loop
import Tree.ProgressiveList.Iter.Length

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Complete collection has exactly the ordered element-cloning behavior of
`List.mapM`, including failure and divergence. Iterator construction, its
length observer, and every vector push are justified by the input invariants.
No element clone is assumed to terminate or preserve its value. -/
theorem ProgressiveList.to_vec_mapM {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    (do let output ← ProgressiveList.to_vec ValueInst mapInst self
        ok output.val) = _root_.List.mapM ValueInst.corecloneCloneInst.clone contents := by
  obtain ⟨cursor, hiter, hvalid, _, hyields⟩ :=
    ProgressiveList.into_iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  have hlength := @ProgressiveListIter.Valid.length_eq T U ValueInst mapInst factor
    self.tree.elements contents cursor hvalid
  obtain ⟨remaining, hremaining, _⟩ := ProgressiveListIter.exact_len_spec
    ValueInst mapInst cursor contents hlength
  let accumulator := alloc.vec.Vec.with_capacity T remaining
  have hempty : accumulator.val = [] := rfl
  have hbound : accumulator.val.length + contents.length ≤ Std.Usize.max := by
    rw [hempty]
    simp only [_root_.List.length_nil, Nat.zero_add]
    rw [← hlength]
    scalar_tac
  have hloop := ProgressiveList.to_vec_loop_mapM
    ValueInst mapInst cursor contents accumulator hyields hbound
  simp only [hempty, _root_.List.nil_append] at hloop
  simp only [ProgressiveList.to_vec, hiter, bind_tc_ok, hremaining]
  refine hloop.trans ?_
  cases _root_.List.mapM ValueInst.corecloneCloneInst.clone contents <;> rfl

/-- A particular vector is returned exactly when ordered element cloning
returns its values. This characterizes arbitrary successful clone results,
without an identity or separate clone-termination premise. -/
theorem ProgressiveList.to_vec_clones_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (output : alloc.vec.Vec T) :
    ProgressiveList.to_vec ValueInst mapInst self = ok output ↔
      _root_.List.mapM ValueInst.corecloneCloneInst.clone contents = ok output.val := by
  have hprojection := ProgressiveList.to_vec_mapM ValueInst mapInst hlayout self contents hrep hdense hfits
  constructor
  · intro hresult
    simpa only [hresult, bind_tc_ok] using hprojection.symm
  · intro hclones
    have hvalues := hprojection.trans hclones
    cases hresult : ProgressiveList.to_vec ValueInst mapInst self with
    | fail e => simp [hresult] at hvalues
    | div => simp [hresult] at hvalues
    | ok copied =>
      have heq : copied.val = output.val := by simpa only [hresult, bind_tc_ok, ok.injEq] using hvalues
      exact congrArg ok (Subtype.ext heq)

/-- Collection propagates exactly the failure of ordered cloning; later
clones impose no laws. Iterator and capacity failures have already been ruled
out by the input invariants. -/
theorem ProgressiveList.to_vec_fail_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (error : Aeneas.Std.Error) :
    ProgressiveList.to_vec ValueInst mapInst self = fail error ↔
      _root_.List.mapM ValueInst.corecloneCloneInst.clone contents = fail error := by
  rw [← ProgressiveList.to_vec_mapM ValueInst mapInst hlayout self contents hrep hdense hfits]
  cases ProgressiveList.to_vec ValueInst mapInst self <;> simp

/-- Collection diverges exactly when ordered cloning diverges, with no
termination premise on any clone. -/
theorem ProgressiveList.to_vec_div_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ProgressiveList.to_vec ValueInst mapInst self = div ↔
      _root_.List.mapM ValueInst.corecloneCloneInst.clone contents = div := by
  rw [← ProgressiveList.to_vec_mapM ValueInst mapInst hlayout self contents hrep hdense hfits]
  cases ProgressiveList.to_vec ValueInst mapInst self <;> simp

end milhouse.progressive_list
