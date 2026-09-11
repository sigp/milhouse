import Tree.ProgressiveList.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Raw lookup behavior for append at one query: the appended key stores the
new value, and other keys agree after the original backing fallback. This
does not assume a public read or constrain unrelated map operations. -/
def ProgressiveList.AppendReadAgrees {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) (index : Std.Usize) (value : T)
    (query : Std.Usize) : Prop :=
  if query = index then mapInst.get updates query = ok (some value)
  else update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
    (mapInst.get updates query) (mapInst.get self.updates query)

/-- The usual exact insertion/lookup law implies the weaker append law. -/
theorem ProgressiveList.AppendReadAgrees.of_get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) (index : Std.Usize) (value : T)
    (query : Std.Usize)
    (hget : mapInst.get updates query =
      if query = index then ok (some value) else mapInst.get self.updates query) :
    self.AppendReadAgrees ValueInst mapInst updates index value query := by
  by_cases heq : query = index
  · simpa only [AppendReadAgrees, if_pos heq] using hget
  · simp only [AppendReadAgrees, if_neg heq]
    exact update_map.LookupResultsAgree.of_eq _ (by simpa only [if_neg heq] using hget)

/-- Exact public append-read criterion. Only a query of the inserted key
needs the backing bound; other queries require no length or structural law. -/
theorem ProgressiveList.get_with_updates_append_eq_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) (index : Std.Usize) (value : T)
    (query : Std.Usize) (hbound : query = index → self.length.val ≤ query.val) :
    ProgressiveList.get ValueInst mapInst { self with updates } query =
      (if query = index then ok (some value) else ProgressiveList.get ValueInst mapInst self query) ↔
      self.AppendReadAgrees ValueInst mapInst updates index value query := by
  by_cases heq : query = index
  · simp only [AppendReadAgrees, if_pos heq]
    rw [ProgressiveList.get_eq_map_get_of_backing_bound ValueInst mapInst
      { self with updates } query (hbound heq)]
  · simp only [AppendReadAgrees, if_neg heq]
    exact ProgressiveList.get_with_updates_eq_iff ValueInst mapInst self updates query

end milhouse.progressive_list
