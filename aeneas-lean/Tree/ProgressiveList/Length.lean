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

end milhouse.progressive_list
