import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

theorem ProgressiveList.ssz_is_fixed_len_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.SszEncodeEncode.is_ssz_fixed_len ValueInst mapInst = ok false := rfl

theorem ProgressiveList.ssz_fixed_len_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_fixed_len ValueInst mapInst = ok 4#usize := rfl

/-- Owning serialization is exactly the proved append operation starting
    from an empty byte vector, without cloning or a separate size pass. -/
theorem ProgressiveList.as_ssz_bytes_eq_append {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U) :
    ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self =
      ProgressiveList.Insts.SszEncodeEncode.ssz_append ValueInst mapInst self (alloc.vec.Vec.new Std.U8) := rfl

end milhouse.progressive_list
