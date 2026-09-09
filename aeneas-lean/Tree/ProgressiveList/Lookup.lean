import Tree.ProgressiveList.Observers
import Tree.UpdateMap.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The pending-map answers agree after resolving absent entries against the
actual original backing lookup. Raw map answers may differ; no backing lookup
success or public list-read postcondition is assumed. All machine indices are
included because pending entries take precedence over backing bounds. -/
def ProgressiveList.UpdateReadsAgree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) : Prop :=
  ∀ query, update_map.LookupResultsAgree
    (ProgressiveList.backing_get ValueInst mapInst self query)
    (mapInst.get updates query) (mapInst.get self.updates query)

/-- The old exact map-read law supplies the weaker agreement contract. -/
theorem ProgressiveList.UpdateReadsAgree.of_get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U)
    (hget : ∀ query, mapInst.get updates query = mapInst.get self.updates query) :
    self.UpdateReadsAgree ValueInst mapInst updates := by
  intro query
  exact update_map.LookupResultsAgree.of_eq _ (hget query)

private theorem get_eq_lookup_with_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (query : Std.Usize) :
    ProgressiveList.get ValueInst mapInst self query =
      (do let value ← mapInst.get self.updates query
          value.elim (ProgressiveList.backing_get ValueInst mapInst self query)
            (fun item => ok (some item))) := by
  unfold ProgressiveList.get
  congr 1
  funext value
  cases value <;> rfl

/-- Replacing the pending map preserves this complete public read exactly
when its raw lookup outcomes agree at the actual backing fallback. -/
theorem ProgressiveList.get_with_updates_eq_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) (query : Std.Usize) :
    ProgressiveList.get ValueInst mapInst { self with updates } query =
        ProgressiveList.get ValueInst mapInst self query ↔
      update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
        (mapInst.get updates query) (mapInst.get self.updates query) := by
  rw [get_eq_lookup_with_fallback, get_eq_lookup_with_fallback]
  simpa only [ProgressiveList.backing_get, ProgressiveList.backing_len] using
    update_map.lookup_with_fallback_eq_iff
      (ProgressiveList.backing_get ValueInst mapInst self query)
      (mapInst.get updates query) (mapInst.get self.updates query)

/-- The map agreement contract is necessary and sufficient for all public
lookup results to agree, without representation or structural assumptions. -/
theorem ProgressiveList.reads_with_updates_eq_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) :
    (∀ query, ProgressiveList.get ValueInst mapInst { self with updates } query =
      ProgressiveList.get ValueInst mapInst self query) ↔
      self.UpdateReadsAgree ValueInst mapInst updates := by
  exact forall_congr' (fun query => ProgressiveList.get_with_updates_eq_iff ValueInst mapInst self updates query)

end milhouse.progressive_list
