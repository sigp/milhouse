import Tree.ProgressiveList.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The fixed-width branch multiplies the actual logical length by the
returned width, preserving length failure/divergence and multiplication
overflow. It does not read elements or traverse the backing tree. -/
theorem ProgressiveList.ssz_bytes_len_fixed_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    (self : ProgressiveList T U) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = (do
      let count ← ProgressiveList.len ValueInst mapInst self
      width * count) := by
  simp only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len,
    hfixed, hwidth, bind_tc_ok, ↓reduceIte]

/-- Fixed-width encoding size needs only length agreement, rather than the
indexed-read component of sequence representation. No packing, density,
cloning, or per-element size law is required. -/
theorem ProgressiveList.ssz_bytes_len_fixed_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    (self : ProgressiveList T U) (count : Std.Usize)
    (hcount : ProgressiveList.len ValueInst mapInst self = ok count)
    (hbound : width.val * count.val ≤ Std.Usize.max) :
    ∃ length, ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = ok length ∧
      length.val = width.val * count.val := by
  obtain ⟨length, hmul, hlength⟩ := WP.spec_imp_exists (Usize.mul_spec (x := width) (y := count) hbound)
  exact ⟨length, by rw [ProgressiveList.ssz_bytes_len_fixed_eq ValueInst mapInst hfixed width hwidth,
    hcount, bind_tc_ok, hmul], hlength⟩

/-- Total fixed-width size calculation directly from the returned map maximum
and arithmetic bounds. The actual length call is proved internally; no sequence
representation or successful milhouse subcall is assumed. The successor check
is still needed when the width is zero, because length is computed first. -/
theorem ProgressiveList.ssz_bytes_len_fixed_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hindex : ∀ index, largest = some index → index.val < Std.Usize.max)
    (hbound : width.val * largest.elim self.length.val
      (fun index => max (index.val + 1) self.length.val) ≤ Std.Usize.max) :
    ∃ length, ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = ok length ∧
      length.val = width.val * largest.elim self.length.val
        (fun index => max (index.val + 1) self.length.val) := by
  obtain ⟨count, hcount, hvalue⟩ := ProgressiveList.len_total_spec ValueInst mapInst self largest hmax hindex
  obtain ⟨length, hlength, hbytes⟩ := ProgressiveList.ssz_bytes_len_fixed_spec
    ValueInst mapInst hfixed width hwidth self count hcount (by simpa only [hvalue] using hbound)
  exact ⟨length, hlength, by simpa only [hvalue] using hbytes⟩

/-- Given returned width and maximum metadata, the successor and final byte
bounds are necessary as well as sufficient. This covers malformed metadata
and zero-width elements without representation or traversal assumptions. -/
theorem ProgressiveList.ssz_bytes_len_fixed_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest) :
    (∃ length, ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = ok length) ↔
      (∀ index, largest = some index → index.val < Std.Usize.max) ∧
      width.val * largest.elim self.length.val
        (fun index => max (index.val + 1) self.length.val) ≤ Std.Usize.max := by
  constructor
  · rintro ⟨length, hlength⟩
    rw [ProgressiveList.ssz_bytes_len_fixed_eq ValueInst mapInst hfixed width hwidth] at hlength
    cases hcount : ProgressiveList.len ValueInst mapInst self with
    | fail error | div => simp [hcount] at hlength
    | ok count =>
      have hmul : width * count = ok length := by simpa only [hcount, bind_tc_ok] using hlength
      change UScalar.mul width count = ok length at hmul
      have hproduct := UScalar.mul_equiv width count
      rw [hmul] at hproduct
      simp at hproduct
      have hindex := (ProgressiveList.len_success_iff ValueInst mapInst self largest hmax).mp ⟨count, hcount⟩
      obtain ⟨computed, hcomputed, hvalue⟩ := ProgressiveList.len_total_spec ValueInst mapInst self largest hmax hindex
      have heq : computed = count := ok.inj (hcomputed.symm.trans hcount)
      rw [heq] at hvalue
      refine ⟨hindex, ?_⟩
      rw [← hvalue]
      scalar_tac
  · rintro ⟨hindex, hbound⟩
    obtain ⟨length, hlength, _⟩ := ProgressiveList.ssz_bytes_len_fixed_total_spec
      ValueInst mapInst hfixed width hwidth self largest hmax hindex hbound
    exact ⟨length, hlength⟩

end milhouse.progressive_list
