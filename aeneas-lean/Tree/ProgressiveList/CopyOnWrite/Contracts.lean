import Tree.ProgressiveList.Spine
import Tree.ProgressiveList.WriteBack
import Tree.UpdateMap.CopyOnWrite
import Tree.UpdateMap.CowWriteBack

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The optional value selected before calling the map's CoW primitive.
A pending hit supplies `none`; a pending miss supplies the successful backing
read. This describes input lookups, independently of CoW acquisition success. -/
def ProgressiveList.CowFallbackSelected {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (fallback : Option T) : Prop :=
  (∃ pending, mapInst.get self.updates index = ok (some pending) ∧ fallback = none) ∨
  (mapInst.get self.updates index = ok none ∧
    ProgressiveList.backing_get ValueInst mapInst self index = ok fallback)

/-- Read behavior is required only for the fallback selected by these input
lookups, including both present and missing handles. -/
abbrev ProgressiveList.GetCowReads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValueReadsFor mapInst ValueInst.corecloneCloneInst self.updates index fallback

/-- Release behavior is required only at the selected fallback. -/
abbrev ProgressiveList.GetCowPreserves {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValuePreservesFor mapInst ValueInst.corecloneCloneInst self.updates index fallback

/-- Entry-location behavior is required only at the selected fallback. -/
abbrev ProgressiveList.GetCowEntryAt {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValueEntryAtFor mapInst ValueInst.corecloneCloneInst self.updates index fallback

/-- Already-pending values need no clone, at the selected fallback only. -/
abbrev ProgressiveList.GetCowExistingMutable {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValueExistingMutableFor mapInst ValueInst.corecloneCloneInst self.updates index fallback

/-- Filled-entry lookup agreement is required only at the selected fallback. -/
abbrev ProgressiveList.GetCowWriteReads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValueWriteReadsFor mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self) fallback

/-- Filled-entry maximum-result agreement is required only at the selected
fallback and the list's actual backing length. -/
abbrev ProgressiveList.GetCowMaxIndexAgrees {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    update_map.GetCowWithValueMaxIndexAgreesFor mapInst ValueInst.corecloneCloneInst self.updates index
      self.length fallback

end milhouse.progressive_list
