import Tree.ProgressiveList.Arbitrary.Traits
import Tree.ProgressiveList.Construction.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Every successfully generated list has cleared caches, regardless of
element-generator, packing, input-consumption, or default-map behavior. -/
theorem ProgressiveList.arbitrary_caches_cleared {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) : self.tree.CachesCleared := by
  obtain ⟨values, _, hnew⟩ :=
    (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
  exact ProgressiveList.new_caches_cleared ValueInst mapInst values hnew

theorem ProgressiveList.arbitrary_take_rest_caches_cleared {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self)) : self.tree.CachesCleared := by
  obtain ⟨after, hresult⟩ :=
    (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mp hresult
  exact ProgressiveList.arbitrary_caches_cleared inst ValueInst mapInst input after self hresult

end milhouse.progressive_list
