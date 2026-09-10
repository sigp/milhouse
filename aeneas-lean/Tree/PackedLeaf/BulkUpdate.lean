import Tree.PackedLeaf.Contents
import Tree.Vec.Clone

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private theorem add_one_val {index next : Std.Usize} (h : index + 1#usize = ok next) :
    next.val = index.val + 1 := by
  have hs := UScalar.add_equiv index 1#usize
  rw [h] at hs
  simp at hs
  omega

/-- One step of the extracted loop, retaining all failure behavior. -/
theorem PackedLeaf.update_loop_step {T U : Type}
    (thi : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (updates : U)
    (updated : PackedLeaf T) (factor stop index : Std.Usize) :
    PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
      match PackedLeaf.update_loop.body thi cloneInst mapInst updates factor stop updated index with
      | ok (.cont (u, i)) => PackedLeaf.update_loop thi cloneInst mapInst updates u factor stop i
      | ok (.done b) => ok b
      | fail e => fail e
      | div => div := by
  conv_lhs => unfold PackedLeaf.update_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hb : PackedLeaf.update_loop.body thi cloneInst mapInst updates factor stop updated index with
  | fail e => simp [hb]
  | div => simp [hb]
  | ok cf =>
    cases cf with
    | cont x => obtain ⟨u, i⟩ := x; simp [hb]; rfl
    | done b => simp [hb]

/-- A packed scan returns the actual clone of a pending value at the queried
slot, or retains the input slot if it has already passed it or no update exists.
No clone identity or termination law is assumed. -/
theorem PackedLeaf.update_loop_get_cloned {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor stop query : Std.Usize} {window : Nat} {pending : Option T}
    (hend : stop.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hquery_lo : window ≤ query.val) (hquery_hi : query.val < stop.val)
    (hquery : mapInst.get updates query = ok pending) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize) (result : PackedLeaf T),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
        ok (core.result.Result.Ok result) →
      (if index.val ≤ query.val then
        do let copied ← core.option.OptionShared0T.cloned cloneInst pending
           ok (copied.or updated.values.val[query.val - window]?)
       else ok updated.values.val[query.val - window]?) =
        ok result.values.val[query.val - window]? := by
  have hfactor : 0 < factor.val := by omega
  intro fuel
  induction fuel with
  | zero =>
    intro updated index result hfuel hlo hhi hloop
    have hstop : ¬ index < stop := by scalar_tac
    rw [PackedLeaf.update_loop_step] at hloop
    unfold PackedLeaf.update_loop.body at hloop
    rw [if_neg hstop] at hloop
    simp at hloop
    subst hloop
    rw [if_neg (by omega)]
  | succ fuel ih =>
    intro updated index result hfuel hlo hhi hloop
    rw [PackedLeaf.update_loop_step] at hloop
    by_cases hlt : index < stop
    case neg =>
      unfold PackedLeaf.update_loop.body at hloop
      rw [if_neg hlt] at hloop
      simp at hloop
      subst hloop
      rw [if_neg (by scalar_tac)]
    case pos =>
    cases hb : PackedLeaf.update_loop.body thi cloneInst mapInst updates factor stop updated index with
    | fail e => rw [hb] at hloop; simp at hloop
    | div => rw [hb] at hloop; simp at hloop
    | ok cf =>
    rw [hb] at hloop
    unfold PackedLeaf.update_loop.body at hb
    rw [if_pos hlt, bind_eq_ok_iff] at hb
    obtain ⟨found, hfound, hb⟩ := hb
    cases found with
    | none =>
      rw [bind_eq_ok_iff] at hb
      obtain ⟨next, hplus, hb⟩ := hb
      have hnext := add_one_val hplus
      simp at hb
      subst hb
      simp at hloop
      have hread := ih updated next result (by scalar_tac) (by omega) (by scalar_tac) hloop
      by_cases heq : query = index
      · subst query
        rw [hfound] at hquery
        cases hquery
        simpa [core.option.OptionShared0T.cloned, if_neg (show ¬ next.val ≤ index.val by omega)] using hread
      · have hne : query.val ≠ index.val := by intro h; apply heq; scalar_tac
        have hguard : (next.val ≤ query.val) ↔ (index.val ≤ query.val) := by omega
        simpa only [hguard] using hread
    | some value =>
      rw [bind_eq_ok_iff] at hb
      obtain ⟨sub, hrem, hb⟩ := hb
      have hsub : sub.val = index.val - window := by
        have hs := Std.Usize.rem_bv_spec index (Nat.ne_of_gt hfactor)
        rw [hrem] at hs
        have hklt : index.val - window < factor.val := by scalar_tac
        have hidx : index.val = window + (index.val - window) := by omega
        have hm : index.val % factor.val = index.val - window := by
          rw [hidx, Nat.add_mod, halign]
          simp [Nat.mod_eq_of_lt hklt]
        exact hs.1.trans hm
      rw [bind_eq_ok_iff] at hb
      obtain ⟨cloned, hcloned, hb⟩ := hb
      rw [bind_eq_ok_iff] at hb
      obtain ⟨⟨r, updated1⟩, hins, hb⟩ := hb
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hb
        subst hb
        simp at hloop
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hb
        rw [bind_eq_ok_iff] at hb
        obtain ⟨next, hplus, hb⟩ := hb
        have hnext := add_one_val hplus
        simp at hb
        subst hb
        simp at hloop
        have hread := ih updated1 next result (by scalar_tac) (by omega) (by scalar_tac) hloop
        rw [PackedLeaf.get_after_insert_mut hins, hsub] at hread
        by_cases heq : query = index
        · subst query
          rw [hfound] at hquery
          cases hquery
          simpa [core.option.OptionShared0T.cloned, hcloned,
            if_neg (show ¬ next.val ≤ index.val by omega)] using hread
        · have hne : query.val ≠ index.val := by intro h; apply heq; scalar_tac
          have hsub_ne : query.val - window ≠ index.val - window := by omega
          have hguard : (next.val ≤ query.val) ↔ (index.val ≤ query.val) := by omega
          simpa only [if_neg hsub_ne, hguard] using hread

/-- Identity is required only for the queried pending value, and only if the
scan has not yet passed it. All other clone results may differ. -/
theorem PackedLeaf.update_loop_get_of_clone_at_query {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor stop query : Std.Usize} {window : Nat} {pending : Option T}
    (hend : stop.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hquery_lo : window ≤ query.val) (hquery_hi : query.val < stop.val)
    (hquery : mapInst.get updates query = ok pending) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize) (result : PackedLeaf T),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      (index.val ≤ query.val → ∀ value, pending = some value → cloneInst.clone value = ok value) →
      PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
        ok (core.result.Result.Ok result) →
      result.values.val[query.val - window]? =
        if index.val ≤ query.val then pending.or updated.values.val[query.val - window]?
        else updated.values.val[query.val - window]? := by
  intro fuel updated index result hfuel hlo hhi hclone hloop
  have hread := PackedLeaf.update_loop_get_cloned hend halign hquery_lo hquery_hi hquery
    fuel updated index result hfuel hlo hhi hloop
  by_cases hbefore : index.val ≤ query.val
  · cases pending with
    | none =>
      simpa only [if_pos hbefore, core.option.OptionShared0T.cloned,
        bind_tc_ok, Option.none_or, Result.ok.injEq] using hread.symm
    | some value =>
      simpa only [if_pos hbefore, core.option.OptionShared0T.cloned,
        hclone hbefore value rfl, bind_tc_ok, Option.some_or, Result.ok.injEq] using hread.symm
  · simpa only [if_neg hbefore, Result.ok.injEq] using hread.symm

/-- A pending-clone law on the whole window specializes the query-local
    theorem. No identity law for copied storage is needed by the scan itself. -/
theorem PackedLeaf.update_loop_get_of_clone_on_window {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor stop query : Std.Usize} {window : Nat} {pending : Option T}
    (hend : stop.val = window + factor.val)
    (hclone : ∀ (index : Std.Usize) value, window ≤ index.val → index.val < stop.val →
      mapInst.get updates index = ok (some value) → cloneInst.clone value = ok value)
    (halign : window % factor.val = 0)
    (hquery_lo : window ≤ query.val) (hquery_hi : query.val < stop.val)
    (hquery : mapInst.get updates query = ok pending) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize) (result : PackedLeaf T),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
        ok (core.result.Result.Ok result) →
      result.values.val[query.val - window]? =
        if index.val ≤ query.val then pending.or updated.values.val[query.val - window]?
        else updated.values.val[query.val - window]? := by
  intro fuel updated index result hfuel hlo hhi hloop
  exact PackedLeaf.update_loop_get_of_clone_at_query hend halign hquery_lo hquery_hi hquery
    fuel updated index result hfuel hlo hhi
    (fun _ value hpending => hclone query value hquery_lo hquery_hi (by rw [hquery, hpending])) hloop

/-- Compatibility form using a clone law for every value. The stronger
window-scoped theorem requires that law only for actual pending reads. -/
theorem PackedLeaf.update_loop_get {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    (hclone : ∀ value, cloneInst.clone value = ok value)
    {factor stop query : Std.Usize} {window : Nat} {pending : Option T}
    (hend : stop.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hquery_lo : window ≤ query.val) (hquery_hi : query.val < stop.val)
    (hquery : mapInst.get updates query = ok pending) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize) (result : PackedLeaf T),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
        ok (core.result.Result.Ok result) →
      result.values.val[query.val - window]? =
        if index.val ≤ query.val then pending.or updated.values.val[query.val - window]?
        else updated.values.val[query.val - window]? := by
  exact PackedLeaf.update_loop_get_of_clone_on_window hend
    (fun _ value _ _ _ => hclone value) halign hquery_lo hquery_hi hquery

/-- A complete packed update stores the actual clone of the pending value,
or of the retained source value when no pending replacement exists. No clone
identity, clone termination, or input density law is assumed. -/
theorem PackedLeaf.get_after_update_cloned {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {prefix1 factor query : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize} {pending : Option T}
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hquery_lo : prefix1.val ≤ query.val)
    (hquery_hi : query.val < prefix1.val + factor.val)
    (hquery : mapInst.get updates query = ok pending)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates =
      ok (core.result.Result.Ok result)) :
    core.option.OptionShared0T.cloned cloneInst
      (pending.or self.values.val[query.val - prefix1.val]?) =
      ok result.values.val[query.val - prefix1.val]? := by
  unfold PackedLeaf.update at hupdate
  simp only [lock_api.rwlock.RwLock.new, bind_tc_ok] at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨copied, hcopied, hupdate⟩ := hupdate
  simp only [hfactor, bind_tc_ok] at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨stop, hstop, hupdate⟩ := hupdate
  have hstop_val : stop.val = prefix1.val + factor.val := by
    have hs := UScalar.add_equiv prefix1 factor
    rw [hstop] at hs
    simp at hs
    omega
  have hread := PackedLeaf.update_loop_get_cloned hstop_val halign
    hquery_lo (by omega) hquery (stop.val - prefix1.val)
    { hash, values := copied } prefix1 result (Nat.le_refl _) (Nat.le_refl _)
    (by omega) hupdate
  cases pending with
  | none =>
    have hstored := milhouse_models.vec_clone_get_cloned cloneInst
      (query.val - prefix1.val) hcopied
    have hread : ok copied.val[query.val - prefix1.val]? =
        ok result.values.val[query.val - prefix1.val]? := by
      simpa only [if_pos hquery_lo, core.option.OptionShared0T.cloned, bind_tc_ok, Option.none_or] using hread
    simpa only [Option.none_or] using hstored.trans hread
  | some value =>
    cases hcloned : cloneInst.clone value with
    | fail e => simp [if_pos hquery_lo, core.option.OptionShared0T.cloned, hcloned] at hread
    | div => simp [if_pos hquery_lo, core.option.OptionShared0T.cloned, hcloned] at hread
    | ok cloned =>
      simpa [if_pos hquery_lo, core.option.OptionShared0T.cloned, hcloned] using hread

/-- Correctness at a queried packed slot is equivalent to identity of the
clone that survives there. Overwritten stored copies and unrelated clones need
no identity law; absent slots impose no clone requirement. -/
theorem PackedLeaf.get_after_update_iff_clone_visible {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {prefix1 factor query : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize} {pending : Option T}
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hquery_lo : prefix1.val ≤ query.val)
    (hquery_hi : query.val < prefix1.val + factor.val)
    (hquery : mapInst.get updates query = ok pending)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates =
      ok (core.result.Result.Ok result)) :
    result.values.val[query.val - prefix1.val]? =
      pending.or self.values.val[query.val - prefix1.val]? ↔
      ∀ value, pending.or self.values.val[query.val - prefix1.val]? = some value →
        cloneInst.clone value = ok value := by
  have hread := PackedLeaf.get_after_update_cloned hfactor halign hquery_lo hquery_hi hquery hupdate
  constructor
  · intro heq
    rw [heq] at hread
    exact (milhouse_models.option_clone_identity_iff cloneInst
      (pending.or self.values.val[query.val - prefix1.val]?)).mp hread
  · intro hidentity
    have hidentity := (milhouse_models.option_clone_identity_iff cloneInst
      (pending.or self.values.val[query.val - prefix1.val]?)).mpr hidentity
    exact Result.ok.inj (hread.symm.trans hidentity)

/-- The original pointwise content contract follows from identity of the
pending clone or, if absent, the retained stored clone. -/
theorem PackedLeaf.get_after_update_of_clone_at_query {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {prefix1 factor query : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize} {pending : Option T}
    (hcloneStored : pending = none → ∀ value,
      self.values.val[query.val - prefix1.val]? = some value → cloneInst.clone value = ok value)
    (hclonePending : ∀ value, pending = some value → cloneInst.clone value = ok value)
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hquery_lo : prefix1.val ≤ query.val)
    (hquery_hi : query.val < prefix1.val + factor.val)
    (hquery : mapInst.get updates query = ok pending)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates =
      ok (core.result.Result.Ok result)) :
    result.values.val[query.val - prefix1.val]? =
      pending.or self.values.val[query.val - prefix1.val]? := by
  apply (PackedLeaf.get_after_update_iff_clone_visible hfactor halign
    hquery_lo hquery_hi hquery hupdate).mpr
  intro value hvisible
  cases pending with
  | none => exact hcloneStored rfl value (by simpa only [Option.none_or] using hvisible)
  | some pendingValue =>
    have heq : pendingValue = value := by simpa only [Option.some_or, Option.some.injEq] using hvisible
    cases heq
    exact hclonePending value rfl

/-- A successful packed-leaf bulk update reads the pending value at each slot
    in its aligned packing window, or the previous value if no update exists.
    Only retained stored values and pending values in that window need clone
    identity. Initial cloning and the complete update loop are included. -/
theorem PackedLeaf.get_after_update_of_clone_on_window {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {prefix1 factor query : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize} {pending : Option T}
    (hcloneStored : ∀ (index : Std.Usize) value,
      prefix1.val ≤ index.val → index.val < prefix1.val + factor.val →
      mapInst.get updates index = ok none →
      self.values.val[index.val - prefix1.val]? = some value →
      cloneInst.clone value = ok value)
    (hclonePending : ∀ (index : Std.Usize) value,
      prefix1.val ≤ index.val → index.val < prefix1.val + factor.val →
      mapInst.get updates index = ok (some value) → cloneInst.clone value = ok value)
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hquery_lo : prefix1.val ≤ query.val)
    (hquery_hi : query.val < prefix1.val + factor.val)
    (hquery : mapInst.get updates query = ok pending)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates =
      ok (core.result.Result.Ok result)) :
    result.values.val[query.val - prefix1.val]? =
      pending.or self.values.val[query.val - prefix1.val]? := by
  exact PackedLeaf.get_after_update_of_clone_at_query
    (fun hnone value hv => hcloneStored query value hquery_lo hquery_hi
      (by rw [hquery, hnone]) hv)
    (fun value hpending => hclonePending query value hquery_lo hquery_hi
      (by rw [hquery, hpending]))
    hfactor halign hquery_lo hquery_hi hquery hupdate

/-- Global clone identity specializes the content theorem whose actual clone
requirements are confined to the stored values and the updated window. -/
theorem PackedLeaf.get_after_update {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    (hclone : ∀ value, cloneInst.clone value = ok value)
    {self result : PackedLeaf T} {prefix1 factor query : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize} {pending : Option T}
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hquery_lo : prefix1.val ≤ query.val)
    (hquery_hi : query.val < prefix1.val + factor.val)
    (hquery : mapInst.get updates query = ok pending)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates =
      ok (core.result.Result.Ok result)) :
    result.values.val[query.val - prefix1.val]? =
      pending.or self.values.val[query.val - prefix1.val]? := by
  exact PackedLeaf.get_after_update_of_clone_on_window
    (fun _ value _ _ _ _ => hclone value) (fun _ value _ _ _ => hclone value)
    hfactor halign hquery_lo hquery_hi hquery hupdate

end milhouse.packed_leaf
