import Tree.ProgressiveList.Iter.Construction
import Tree.ProgressiveList.Encode.FixedLength

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_list

/-- Complete payload-size accumulation over the proved merged iterator. The
    final size bound supplies every intermediate addition bound; only element
    sizes actually consumed by the loop need a semantic law. -/
theorem ProgressiveList.ssz_bytes_len_loop_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (size : T → Nat) (accumulator : Std.Usize)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) cursor values)
    (hsize : ∀ value ∈ values, ∃ length,
      ValueInst.sszencodeEncodeInst.ssz_bytes_len value = ok length ∧ length.val = size value)
    (hbound : accumulator.val + (values.map size).sum ≤ Std.Usize.max) :
    ∃ length, ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop
      ValueInst mapInst cursor accumulator = ok length ∧
      length.val = accumulator.val + (values.map size).sum := by
  induction hyields generalizing accumulator with
  | nil hnext =>
    refine ⟨accumulator, ?_, by simp⟩
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop.body, hnext, bind_tc_ok]
  | @cons cursor rest value values hnext hyields ih =>
    obtain ⟨itemLength, hitem, hitemSize⟩ := hsize value (by simp)
    have haddBound : accumulator.val + itemLength.val ≤ Std.Usize.max := by
      simp only [_root_.List.map_cons, _root_.List.sum_cons] at hbound
      omega
    obtain ⟨nextLength, hadd, hnextLength⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := accumulator) (y := itemLength) haddBound)
    have htailBound : nextLength.val + (values.map size).sum ≤ Std.Usize.max := by
      simp only [_root_.List.map_cons, _root_.List.sum_cons] at hbound
      omega
    obtain ⟨length, hloop, hlength⟩ := ih nextLength
      (fun item hmem => hsize item (by simp [hmem])) htailBound
    refine ⟨length, ?_, ?_⟩
    · rw [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop, loop]
      simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop.body,
        hnext, bind_tc_ok, hitem, hadd]
      exact hloop
    · simp only [_root_.List.map_cons, _root_.List.sum_cons]
      omega

/-- Variable-element encoding size is the sum of represented element sizes
    plus one four-byte offset per element, including pending updates. The
    iterator proof supplies traversal; the final byte bound supplies all
    arithmetic bounds without additional termination or clone premises. -/
theorem ProgressiveList.ssz_bytes_len_variable_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (size : T → Nat)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (hsize : ∀ value ∈ contents, ∃ length,
      ValueInst.sszencodeEncodeInst.ssz_bytes_len value = ok length ∧ length.val = size value)
    (hbound : (contents.map size).sum + 4 * contents.length ≤ Std.Usize.max) :
    ∃ length, ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = ok length ∧
      length.val = (contents.map size).sum + 4 * contents.length := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  obtain ⟨payload, hpayload, hpayloadSize⟩ := ProgressiveList.ssz_bytes_len_loop_spec
    ValueInst mapInst cursor contents size 0#usize hyields hsize (by simp; omega)
  simp at hpayloadSize
  obtain ⟨count, hcount, hcountValue⟩ := hrep.1
  obtain ⟨offsets, hoffsets, hoffsetsSize⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := 4#usize) (y := count) (by simp [hcountValue]; omega))
  obtain ⟨length, hadd, hlength⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := payload) (y := offsets) (by scalar_tac))
  refine ⟨length, ?_, ?_⟩
  · simp only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len, hvariable,
      bind_tc_ok, Bool.false_eq_true, ↓reduceIte, hiter, hpayload, hcount,
      ssz.BYTES_PER_LENGTH_OFFSET, hoffsets, hadd]
  · scalar_tac

end milhouse.progressive_list
