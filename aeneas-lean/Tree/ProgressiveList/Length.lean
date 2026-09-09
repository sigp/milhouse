import Tree.ProgressiveList.Observers
import Tree.UpdateMap.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

theorem ProgressiveList.len_eq_updated_length {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) :
    ProgressiveList.len ValueInst mapInst self =
      utils.updated_length mapInst self.length self.updates := by
  unfold ProgressiveList.len
  cases utils.updated_length mapInst self.length self.updates <;> rfl

/-- The logical length includes all of the backing sequence. -/
theorem ProgressiveList.len_ge_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (length : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length) :
    self.length.val ≤ length.val := by
  rw [ProgressiveList.len_eq_updated_length] at hlen
  exact utils.updated_length_ge_backing mapInst self.length self.updates length hlen

/-- The exact length when pending updates have a largest index. Successful
    evaluation discharges checked addition, rather than requiring an extra
    non-overflow premise from the caller. -/
theorem ProgressiveList.len_of_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize)
    (hmax : mapInst.max_index self.updates = ok (some index))
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length) :
    length.val = max (index.val + 1) self.length.val := by
  rw [ProgressiveList.len_eq_updated_length] at hlen
  exact utils.updated_length_max_spec mapInst self.length self.updates index length hmax hlen

/-- The public length observer terminates and returns the exact merged
metadata length. It needs only the actual map maximum and its successor bound,
without indexed-read, density, packing, or representation assumptions. -/
theorem ProgressiveList.len_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hbound : ∀ index, largest = some index → index.val < Std.Usize.max) :
    ∃ length, ProgressiveList.len ValueInst mapInst self = ok length ∧
      length.val = largest.elim self.length.val (fun index => max (index.val + 1) self.length.val) := by
  simpa only [ProgressiveList.len_eq_updated_length] using
    utils.updated_length_total_spec mapInst self.length self.updates largest hmax hbound

/-- Once the generic maximum lookup returns, the successor check is the exact
success condition for the public observer, including malformed metadata. -/
theorem ProgressiveList.len_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest) :
    (∃ length, ProgressiveList.len ValueInst mapInst self = ok length) ↔
      ∀ index, largest = some index → index.val < Std.Usize.max := by
  simpa only [ProgressiveList.len_eq_updated_length] using
    utils.updated_length_success_iff mapInst self.length self.updates largest hmax

end milhouse.progressive_list
