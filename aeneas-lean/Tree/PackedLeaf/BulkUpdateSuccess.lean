import Tree.PackedLeaf.Insert
import Tree.PackedLeaf.BulkUpdate
import Tree.BulkUpdate.Window
import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.packed_leaf

private theorem clone_values_success {T : Type} (cloneInst : core.clone.Clone T)
    (self : alloc.vec.Vec T)
    (hclone : ∀ value ∈ self.val, ∃ cloned, cloneInst.clone value = ok cloned) :
    ∃ values, alloc.vec.CloneVec.clone cloneInst self = ok values ∧
      values.val.length = self.val.length := by
  have hmap : ∀ input : _root_.List T,
      (∀ value ∈ input, ∃ cloned, cloneInst.clone value = ok cloned) →
      ∃ values, _root_.List.mapM cloneInst.clone input = ok values := by
    intro input
    induction input with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons value rest ih =>
      intro hclone
      obtain ⟨cloned, hcloned⟩ := hclone value (by simp)
      obtain ⟨values, hvalues⟩ := ih (fun value hv => hclone value (by simp [hv]))
      refine ⟨cloned :: values, ?_⟩
      simp only [_root_.List.mapM_cons, hcloned, hvalues, bind_tc_ok]
      rfl
  obtain ⟨values, hvalues⟩ := hmap self.val hclone
  have hlength := List.mapM_Result_length hvalues
  let result : alloc.vec.Vec T := ⟨values, by rw [hlength]; exact self.property⟩
  refine ⟨result, ?_, hlength⟩
  unfold alloc.vec.CloneVec.clone Slice.clone Aeneas.Std.List.clone
  split <;> simp_all [result]
  rfl

/-- A dense packed-window scan terminates and reaches its target length.
Only queried map entries and actually copied pending values need successful
external calls; cloning need not preserve values for this length theorem. -/
theorem PackedLeaf.update_loop_success {T U : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor stop : Std.Usize) (window oldLength newLength : Nat)
    (hend : stop.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      window factor.val oldLength newLength)
    (hcapacity : newLength ≤ factor.val)
    (hget : ∀ query : Std.Usize, window ≤ query.val → query.val < stop.val →
      ∃ found, mapInst.get updates query = ok found)
    (hclone : ∀ (query : Std.Usize) value, window ≤ query.val → query.val < stop.val →
      mapInst.get updates query = ok (some value) →
      ∃ cloned, cloneInst.clone value = ok cloned) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      updated.values.val.length = max oldLength (min newLength (index.val - window)) →
      ∃ result, PackedLeaf.update_loop hashInst cloneInst mapInst updates
        updated factor stop index = ok (core.result.Result.Ok result) ∧
        result.values.val.length = newLength := by
  have hmono := hwindow.length_mono
  intro fuel
  induction fuel with
  | zero =>
    intro updated index hfuel hlo hhi hlength
    have hstop : ¬ index < stop := by scalar_tac
    refine ⟨updated, ?_, by omega⟩
    rw [PackedLeaf.update_loop_step]
    simp only [PackedLeaf.update_loop.body, hstop, ↓reduceIte]
  | succ fuel ih =>
    intro updated index hfuel hlo hhi hlength
    by_cases hlt : index < stop
    · have hltVal : index.val < stop.val := hlt
      have hfactor : 0 < factor.val := by omega
      have hslot : index.val - window < factor.val := by omega
      have hindex : window + (index.val - window) = index.val := by omega
      obtain ⟨next, hnext, hnextVal⟩ := usize_add_succeeds (x := index) (y := 1#usize)
        (by have := stop.hBounds; scalar_tac)
      have hnextVal' : next.val = index.val + 1 := by simpa using hnextVal
      obtain ⟨found, hfound⟩ := hget index hlo hltVal
      cases found with
      | none =>
        have hmissing : ¬ (oldLength ≤ index.val - window ∧
            index.val - window < newLength) := by
          rintro ⟨hold, hnew⟩
          have hhas := hwindow.extension_complete (index.val - window) hold hnew
          rw [hindex] at hhas
          obtain ⟨value, hvalue⟩ := update_map.get_some_of_hasValueAt mapInst updates hhas
          rw [hfound] at hvalue
          cases hvalue
        obtain ⟨result, hresult, hlen⟩ := ih updated next (by omega) (by omega)
          (by omega) (by omega)
        refine ⟨result, ?_, hlen⟩
        rw [PackedLeaf.update_loop_step]
        simp only [PackedLeaf.update_loop.body, hlt, ↓reduceIte, hfound,
          bind_tc_ok, hnext]
        exact hresult
      | some value =>
        have hnew : index.val - window < newLength := by
          apply hwindow.updates_bounded (index.val - window) hslot
          rw [hindex]
          exact ⟨index, value, rfl, hfound⟩
        obtain ⟨sub, hrem, hsub⟩ := usize_rem_succeeds index hfactor
        have hsubVal : sub.val = index.val - window := by
          calc
            sub.val = (window + (index.val - window)) % factor.val := by
              rw [hindex, hsub]
            _ = index.val - window := by
              simp only [Nat.add_mod, halign, Nat.zero_add,
                Nat.mod_eq_of_lt hslot]
        obtain ⟨cloned, hcloned⟩ := hclone index value hlo hltVal hfound
        obtain ⟨inserted, hinsert, hvalues⟩ := PackedLeaf.insert_mut_success hashInst cloneInst
          updated sub cloned (by omega) (by have := factor.hBounds; scalar_tac)
        have hinserted : inserted.values.val.length =
            max oldLength (min newLength (next.val - window)) := by
          rw [hvalues]
          split <;> simp only [_root_.List.length_append, _root_.List.length_singleton,
            _root_.List.length_set] <;> omega
        obtain ⟨result, hresult, hlen⟩ := ih inserted next (by omega) (by omega)
          (by omega) hinserted
        refine ⟨result, ?_, hlen⟩
        rw [PackedLeaf.update_loop_step]
        simp! only [PackedLeaf.update_loop.body, hlt, ↓reduceIte, hfound,
          bind_tc_ok, hrem, hcloned, hinsert, core.result.Result.Insts.CoreOpsTry.branch,
          hnext]
        exact hresult
    · have hstop : stop.val ≤ index.val := by scalar_tac
      refine ⟨updated, ?_, by omega⟩
      rw [PackedLeaf.update_loop_step]
      simp only [PackedLeaf.update_loop.body, hlt, ↓reduceIte]

/-- The complete packed update succeeds for a dense update window with a
representable end. The clone laws require termination only for stored values
and pending values in this window, not identity or behavior elsewhere. -/
theorem PackedLeaf.update_success {T U : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (self : PackedLeaf T)
    (start factor : Std.Usize)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) (updates : U)
    (newLength : Nat) (hfactor : hashInst.tree_hash_packing_factor = ok factor)
    (halign : start.val % factor.val = 0)
    (hend : start.val + factor.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      start.val factor.val self.values.val.length newLength)
    (hcapacity : newLength ≤ factor.val)
    (hget : ∀ query : Std.Usize, start.val ≤ query.val → query.val < start.val + factor.val →
      ∃ found, mapInst.get updates query = ok found)
    (hcloneStored : ∀ value ∈ self.values.val, ∃ cloned, cloneInst.clone value = ok cloned)
    (hclonePending : ∀ (query : Std.Usize) value,
      start.val ≤ query.val → query.val < start.val + factor.val →
      mapInst.get updates query = ok (some value) →
      ∃ cloned, cloneInst.clone value = ok cloned) :
    ∃ result, PackedLeaf.update hashInst cloneInst mapInst self start hash updates =
      ok (core.result.Result.Ok result) ∧ result.values.val.length = newLength := by
  obtain ⟨values, hvalues, hlength⟩ := clone_values_success cloneInst self.values hcloneStored
  obtain ⟨stop, hstop, hstopVal⟩ := WP.spec_imp_exists (UScalar.add_spec (x := start) (y := factor)
    (by simpa only [UScalar.max_USize_eq] using hend))
  obtain ⟨result, hresult, hlen⟩ := PackedLeaf.update_loop_success hashInst cloneInst mapInst
    updates factor stop start.val self.values.val.length newLength hstopVal halign hwindow hcapacity
    (fun query hlo hhi => hget query hlo (by omega))
    (fun query value hlo hhi hget => hclonePending query value hlo (by omega) hget)
    (stop.val - start.val) { hash, values } start (Nat.le_refl _) (Nat.le_refl _)
    (by omega) (by simp only [hlength, Nat.sub_self, Nat.min_zero, Nat.max_zero])
  refine ⟨result, ?_, hlen⟩
  simp only [PackedLeaf.update, lock_api.rwlock.RwLock.new, hvalues, hfactor, hstop,
    bind_tc_ok, hresult]

/-- Total packed bulk update preserves the merged value at every position
and has exactly the dense target length. Copied storage needs terminating
clones; identity is required only for retained slots and pending values in
the window. No range-query or maximum-index laws are required. -/
theorem PackedLeaf.update_total_spec {T U : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (self : PackedLeaf T)
    (start factor : Std.Usize)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) (updates : U)
    (newLength : Nat) (hfactor : hashInst.tree_hash_packing_factor = ok factor)
    (halign : start.val % factor.val = 0)
    (hend : start.val + factor.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      start.val factor.val self.values.val.length newLength)
    (hcapacity : newLength ≤ factor.val)
    (hget : ∀ query : Std.Usize, start.val ≤ query.val → query.val < start.val + factor.val →
      ∃ found, mapInst.get updates query = ok found)
    (hcloneStored : ∀ value ∈ self.values.val, ∃ cloned, cloneInst.clone value = ok cloned)
    (hcloneRetained : ∀ (query : Std.Usize) value,
      start.val ≤ query.val → query.val < start.val + factor.val →
      mapInst.get updates query = ok none →
      self.values.val[query.val - start.val]? = some value →
      cloneInst.clone value = ok value)
    (hclonePending : ∀ (query : Std.Usize) value,
      start.val ≤ query.val → query.val < start.val + factor.val →
      mapInst.get updates query = ok (some value) → cloneInst.clone value = ok value) :
    ∃ result, PackedLeaf.update hashInst cloneInst mapInst self start hash updates =
      ok (core.result.Result.Ok result) ∧ result.values.val.length = newLength ∧
      ∀ query : Std.Usize, start.val ≤ query.val → query.val < start.val + factor.val →
        ∃ pending, mapInst.get updates query = ok pending ∧
          result.values.val[query.val - start.val]? =
            pending.or self.values.val[query.val - start.val]? := by
  obtain ⟨result, hupdate, hlength⟩ := PackedLeaf.update_success hashInst cloneInst mapInst
    self start factor hash updates newLength hfactor halign hend hwindow hcapacity hget
    hcloneStored
    (fun query value hlo hhi hget => ⟨value, hclonePending query value hlo hhi hget⟩)
  refine ⟨result, hupdate, hlength, ?_⟩
  intro query hlo hhi
  obtain ⟨pending, hpending⟩ := hget query hlo hhi
  exact ⟨pending, hpending, PackedLeaf.get_after_update_of_clone_on_window
    hcloneRetained hclonePending hfactor halign hlo hhi hpending hupdate⟩

end milhouse.packed_leaf
