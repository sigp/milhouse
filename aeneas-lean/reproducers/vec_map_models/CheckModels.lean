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

/-- Presence follows the actual indexed slot, without a count invariant or
an input bound. Extreme missing keys remain ordinary absent lookups. -/
theorem vec_map_contains_key_eq {T : Type} (map : vec_map.VecMap T) (key : Std.Usize) :
    vec_map.VecMap.contains_key map key = ok (map.v.val[key.val]?.join.isSome) := by
  rw [vec_map.VecMap.contains_key, vec_map_get_eq]
  cases map.v.val[key.val]?.join <;> rfl

def entryMap {T : Type} : vec_map.Entry T → vec_map.VecMap T
  | .Vacant entry => entry.map
  | .Occupied entry => entry.map

def entryKey {T : Type} : vec_map.Entry T → Std.Usize
  | .Vacant entry => entry.index
  | .Occupied entry => entry.index

def entryOccupied {T : Type} : vec_map.Entry T → Bool
  | .Vacant _ => false
  | .Occupied _ => true

/-- The source entry continuation accepts the returned map from its
original entry variant. A different variant restores the original map. -/
def entryBack {T : Type} (map : vec_map.VecMap T) (occupied : Bool)
    (replacement : vec_map.Entry T) : vec_map.VecMap T :=
  match occupied, replacement with
  | false, .Vacant entry => entry.map
  | true, .Occupied entry => entry.map
  | _, _ => map

/-- Exact source acquisition, including its entire backward continuation.
The actual entry contains the map and key, rather than an assumed abstract
vacant-slot footprint. Acquisition neither grows storage nor changes count. -/
theorem vec_map_entry_eq {T : Type} (map : vec_map.VecMap T) (key : Std.Usize) :
    vec_map.VecMap.entry map key = ok
      (if map.v.val[key.val]?.join.isSome then
         .Occupied ⟨map, key⟩ else .Vacant ⟨map, key⟩,
       entryBack map map.v.val[key.val]?.join.isSome) := by
  rw [vec_map.VecMap.entry, vec_map_contains_key_eq]
  cases map.v.val[key.val]?.join.isSome <;> apply congrArg ok <;> apply Prod.ext
  all_goals
    first
    | rfl
    | funext replacement
      cases replacement <;> rfl

/-- Entry acquisition is total, classifies occupancy from the requested
slot, retains the exact map and key, and releases unchanged to the whole
original map. No count, clone, allocation, or key-bound premise is needed. -/
theorem vec_map_entry_spec {T : Type} (map : vec_map.VecMap T) (key : Std.Usize) :
    ∃ found back, vec_map.VecMap.entry map key = ok (found, back) ∧
      entryMap found = map ∧ entryKey found = key ∧
      entryOccupied found = map.v.val[key.val]?.join.isSome ∧ back found = map := by
  rw [vec_map_entry_eq]
  cases map.v.val[key.val]?.join.isSome <;> exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

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

/-- The cached entry count agrees with occupied slots. Lookup does not need
this invariant; semantic cardinality and emptiness do. -/
def CountMatches {T : Type} (map : vec_map.VecMap T) : Prop :=
  map.n.val = map.v.val.countP Option.isSome

theorem vec_map_new_count_matches (T : Type) :
    ∃ map, vec_map.VecMap.new T = ok map ∧ CountMatches map := by
  refine ⟨_, vec_map_new_eq T, ?_⟩
  simp [CountMatches]

theorem vec_map_len_spec {T : Type} (map : vec_map.VecMap T) (hcount : CountMatches map) :
    ∃ count, vec_map.VecMap.len map = ok count ∧ count.val = map.v.val.countP Option.isSome :=
  ⟨map.n, vec_map_len_eq map, hcount⟩

theorem vec_map_is_empty_iff_slots_none {T : Type} (map : vec_map.VecMap T)
    (hcount : CountMatches map) :
    vec_map.VecMap.is_empty map = ok true ↔ ∀ slot ∈ map.v.val, slot = none := by
  rw [vec_map_is_empty_eq]
  have hzero : map.n = 0#usize ↔ map.v.val.countP Option.isSome = 0 := by
    constructor
    · intro hn
      simpa [CountMatches, hn] using hcount.symm
    · intro hslots
      apply UScalar.eq_of_val_eq
      simpa [CountMatches, hslots] using hcount
  simpa using hzero

/-- Missing lookup returns no mutable loan, and every continuation input
restores the whole map, including holes inside the backing vector. -/
theorem vec_map_get_mut_missing_eq {T : Type} (map : vec_map.VecMap T) (key : Std.Usize)
    (hget : vec_map.VecMap.get map key = ok none) :
    vec_map.VecMap.get_mut map key = ok (none, fun _ => map) := by
  have hslot : map.v.val[key.val]?.join = none := by simpa only [vec_map_get_eq, Result.ok.injEq] using hget
  rw [vec_map_get_mut_eq, hslot]

/-- A present mutable loan changes exactly its backing slot and preserves
cached cardinality. No invariant, cloning, or caller-supplied bound is needed. -/
theorem vec_map_get_mut_present_spec {T : Type} (map : vec_map.VecMap T)
    (key : Std.Usize) (original : T)
    (hget : vec_map.VecMap.get map key = ok (some original)) :
    ∃ back, vec_map.VecMap.get_mut map key = ok (some original, back) ∧
      ∀ replacement,
        (back (some replacement)).n = map.n ∧
        (back (some replacement)).v.val = map.v.val.set key.val (some replacement) := by
  have hslot : map.v.val[key.val]?.join = some original := by
    simpa only [vec_map_get_eq, Result.ok.injEq] using hget
  refine ⟨fun replacement => { map with v := map.v.set key (some (replacement.getD original)) }, ?_, ?_⟩
  · rw [vec_map_get_mut_eq, hslot]
  · intro replacement
    exact ⟨rfl, alloc.vec.Vec.set_val_eq map.v key (some replacement)⟩

/-- Every continuation from actual mutable lookup preserves agreement of
the cached count with slot occupancy, including absent loans and releases. -/
theorem vec_map_get_mut_preserves_count {T : Type} (map : vec_map.VecMap T)
    (key : Std.Usize) (hcount : CountMatches map)
    {found : Option T} {back : Option T → vec_map.VecMap T}
    (hmut : vec_map.VecMap.get_mut map key = ok (found, back)) :
    ∀ replacement, CountMatches (back replacement) := by
  rw [vec_map_get_mut_eq] at hmut
  cases hslot : map.v.val[key.val]?.join with
  | none =>
    simp only [hslot, Result.ok.injEq, Prod.mk.injEq] at hmut
    obtain ⟨rfl, rfl⟩ := hmut
    exact fun _ => hcount
  | some original =>
    simp only [hslot, Result.ok.injEq, Prod.mk.injEq] at hmut
    obtain ⟨rfl, rfl⟩ := hmut
    have hbound : key.val < map.v.val.length := by
      by_contra hbound
      simp [hbound] at hslot
    have hvalue : map.v.val[key.val] = some original := by simpa [hbound] using hslot
    have hpositive : 0 < map.v.val.countP Option.isSome := by
      apply _root_.List.countP_pos_iff.mpr
      exact ⟨some original, hvalue ▸ _root_.List.getElem_mem hbound, rfl⟩
    intro replacement
    change map.n.val = (map.v.set key (some (replacement.getD original))).val.countP Option.isSome
    rw [alloc.vec.Vec.set_val_eq, _root_.List.countP_set hbound]
    simp only [hvalue, Option.isSome_some, ↓reduceIte]
    unfold CountMatches at hcount
    omega

end VecMapSource

#print axioms VecMapSource.option_as_ref_eq
#print axioms VecMapSource.option_as_mut_eq
#print axioms VecMapSource.vec_map_new_eq
#print axioms VecMapSource.vec_map_len_eq
#print axioms VecMapSource.vec_map_is_empty_eq
#print axioms VecMapSource.vec_map_get_eq
#print axioms VecMapSource.vec_map_get_mut_eq
#print axioms VecMapSource.vec_map_new_count_matches
#print axioms VecMapSource.vec_map_len_spec
#print axioms VecMapSource.vec_map_is_empty_iff_slots_none
#print axioms VecMapSource.vec_map_get_mut_missing_eq
#print axioms VecMapSource.vec_map_get_mut_present_spec
#print axioms VecMapSource.vec_map_get_mut_preserves_count
#print axioms VecMapSource.vec_map_contains_key_eq
#print axioms VecMapSource.vec_map_entry_eq
#print axioms VecMapSource.vec_map_entry_spec
