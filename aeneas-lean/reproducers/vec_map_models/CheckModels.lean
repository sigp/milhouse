import VecMapSource.Funs

open Aeneas Aeneas.Std Result

namespace VecMapSource

/-- Logical effect of returning an optional mutable reference. An absent
loan cannot insert a value, and a missing replacement preserves a present one. -/
def returnSlot {T : Type} (original replacement : Option T) : Option T :=
  original.map (fun value => replacement.getD value)

theorem option_as_ref_eq {T : Type} (value : Option T) :
    core.option.Option.as_ref value = ok value := by
  cases value <;> rfl

theorem option_as_mut_eq {T : Type} (value : Option T) :
    core.option.Option.as_mut value = ok (value, returnSlot value) := by
  cases value with
  | none => rfl
  | some value =>
    simp only [core.option.Option.as_mut]
    congr 2
    funext replacement
    cases replacement <;> rfl

theorem vec_map_new_eq (T : Type) :
    vec_map.VecMap.new T = ok ⟨0#usize, alloc.vec.Vec.new (Option T)⟩ := rfl

theorem vec_map_len_eq {T : Type} (map : vec_map.VecMap T) :
    vec_map.VecMap.len map = ok map.n := rfl

theorem vec_map_is_empty_eq {T : Type} (map : vec_map.VecMap T) :
    vec_map.VecMap.is_empty map = ok (decide (map.n = 0#usize)) := rfl

/-- Indexed lookup uses the slot vector independently of occupancy metadata.
Both holes and keys beyond the backing slots return `none`. -/
theorem vec_map_get_eq {T : Type} (map : vec_map.VecMap T) (key : Std.Usize) :
    vec_map.VecMap.get map key = ok (map.v.val[key.val]?.join) := by
  unfold vec_map.VecMap.get
  by_cases hbound : key.val < map.v.val.length
  · simp [alloc.vec.Vec.index_usize, hbound, option_as_ref_eq]
  · simp [hbound]

/-- The entire mutable lookup result, including its actual continuation,
agrees with slot lookup and updating only an originally present slot. -/
theorem vec_map_get_mut_eq {T : Type} (map : vec_map.VecMap T) (key : Std.Usize) :
    vec_map.VecMap.get_mut map key = ok
      (map.v.val[key.val]?.join, fun replacement =>
        match map.v.val[key.val]?.join with
        | none => map
        | some original => { map with v := map.v.set key (some (replacement.getD original)) }) := by
  unfold vec_map.VecMap.get_mut
  by_cases hbound : key.val < map.v.val.length
  · have hindex : key < alloc.vec.Vec.len map.v := by scalar_tac
    have hslot : map.v.val[key.val]? = some map.v.val[key.val] :=
      _root_.List.getElem?_eq_getElem hbound
    obtain ⟨⟨value, back⟩, hcall, hvalue, hback⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_mut_usize_spec map.v key hbound)
    subst value back
    simp only [if_pos hindex, alloc.vec.Vec.index_mut_slice_index, hcall, bind_tc_ok]
    simp only [option_as_mut_eq, bind_tc_ok, hslot]
    cases hvalue : map.v.val[key.val] with
    | none =>
      have hrestore : map.v.set key none = map.v := by
        have hrestore := alloc.vec.Vec.set_getElem_eq (Option T) map.v key hbound
        change map.v.set key map.v.val[key.val] = map.v at hrestore
        simpa only [hvalue] using hrestore
      simp [returnSlot, hrestore]
    | some original => simp [returnSlot]
  · simp [hbound]

end VecMapSource

#print axioms VecMapSource.option_as_ref_eq
#print axioms VecMapSource.option_as_mut_eq
#print axioms VecMapSource.vec_map_new_eq
#print axioms VecMapSource.vec_map_len_eq
#print axioms VecMapSource.vec_map_is_empty_eq
#print axioms VecMapSource.vec_map_get_eq
#print axioms VecMapSource.vec_map_get_mut_eq
