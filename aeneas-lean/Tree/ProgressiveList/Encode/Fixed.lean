import Tree.ProgressiveList.Iter.Construction

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_list

/-- Direct encoding appends exactly the element encodings in iterator order,
    preserving the existing output prefix. The aggregate byte bound supplies
    every per-element append bound. -/
theorem ProgressiveList.ssz_append_fixed_loop_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (encode : T → _root_.List Std.U8) (buf : alloc.vec.Vec Std.U8)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) cursor values)
    (happend : ∀ value ∈ values, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbound : buf.val.length + (values.flatMap encode).length ≤ Std.Usize.max) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0
      ValueInst mapInst buf cursor = ok output ∧ output.val = buf.val ++ values.flatMap encode := by
  induction hyields generalizing buf with
  | nil hnext =>
    refine ⟨buf, ?_, by simp⟩
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0.body, hnext, bind_tc_ok]
  | @cons cursor rest value values hnext hyields ih =>
    have hroom : buf.val.length + (encode value).length ≤ Std.Usize.max := by
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hbound
      omega
    obtain ⟨appended, hitem, happended⟩ := happend value (by simp) buf hroom
    have htailBound : appended.val.length + (values.flatMap encode).length ≤ Std.Usize.max := by
      rw [happended]
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hbound ⊢
      omega
    obtain ⟨output, hloop, houtput⟩ := ih appended
      (fun item hmem => happend item (by simp [hmem])) htailBound
    refine ⟨output, ?_, ?_⟩
    · rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0, loop]
      simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0.body,
        hnext, bind_tc_ok, hitem]
      exact hloop
    · simpa [happended, _root_.List.append_assoc] using houtput

private theorem fixed_payload_length {T : Type} (encode : T → _root_.List Std.U8)
    (values : _root_.List T) (width : Nat)
    (hwidth : ∀ value ∈ values, (encode value).length = width) :
    (values.flatMap encode).length = width * values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp only [_root_.List.flatMap_cons, _root_.List.length_append, _root_.List.length_cons]
    rw [hwidth value (by simp), ih (fun item hmem => hwidth item (by simp [hmem]))]
    simp [Nat.mul_add, Nat.add_comm]

/-- Fixed-element SSZ appends the exact represented merged sequence's bytes.
    The ordinary element codec law gives each encoding its declared width;
    one final output-size bound covers reservation and all appends. -/
theorem ProgressiveList.ssz_append_fixed_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (encode : T → _root_.List Std.U8) (buf : alloc.vec.Vec Std.U8)
    (hwidths : ∀ value ∈ contents, (encode value).length = width.val)
    (happend : ∀ value ∈ contents, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbound : buf.val.length + width.val * contents.length ≤ Std.Usize.max) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.ssz_append ValueInst mapInst self buf = ok output ∧
      output.val = buf.val ++ contents.flatMap encode := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  obtain ⟨count, hcount, hcountValue⟩ := hrep.1
  obtain ⟨bytes, hmul, hbytes⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := width) (y := count) (by rw [hcountValue]; omega))
  have hreserve : alloc.vec.Vec.reserve Global buf bytes = ok buf := by
    simp only [alloc.vec.Vec.reserve]
    split
    · rfl
    · rename_i hbad
      exfalso
      apply hbad
      rw [hbytes, hcountValue]
      exact hbound
  obtain ⟨output, hloop, houtput⟩ := ProgressiveList.ssz_append_fixed_loop_spec
    ValueInst mapInst cursor contents encode buf hyields happend
    (by rw [fixed_payload_length encode contents width.val hwidths]; exact hbound)
  exact ⟨output, by simp [ProgressiveList.Insts.SszEncodeEncode.ssz_append,
    hfixed, hwidth, hcount, hmul, hreserve, hiter, hloop], houtput⟩

end milhouse.progressive_list
