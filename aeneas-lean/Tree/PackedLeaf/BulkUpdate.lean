import Tree.PackedLeaf.Contents

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

/-- During a packed-window scan, each query already passed is preserved, and
    each query still to be visited is replaced exactly when the map contains
    a value there. No map range/maximum laws or density assumptions are needed
    for this content theorem; it is conditional on successful loop execution. -/
theorem PackedLeaf.update_loop_get {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    (hclone : ∀ value, cloneInst.clone value = ok value)
    {factor stop query : Std.Usize} {window : Nat} {pending : Option T}
    (hend : stop.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hfactor : 0 < factor.val)
    (hquery_lo : window ≤ query.val) (hquery_hi : query.val < stop.val)
    (hquery : mapInst.get updates query = ok pending) :
    ∀ (fuel : Nat) (updated : PackedLeaf T) (index : Std.Usize) (result : PackedLeaf T),
      stop.val - index.val ≤ fuel → window ≤ index.val → index.val ≤ stop.val →
      PackedLeaf.update_loop thi cloneInst mapInst updates updated factor stop index =
        ok (core.result.Result.Ok result) →
      result.values.val[query.val - window]? =
        if index.val ≤ query.val then pending.or updated.values.val[query.val - window]?
        else updated.values.val[query.val - window]? := by
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
      rw [ih updated next result (by scalar_tac) (by omega) (by scalar_tac) hloop]
      by_cases heq : query = index
      · subst query
        rw [hfound] at hquery
        cases hquery
        simp
      · have hne : query.val ≠ index.val := by intro h; apply heq; scalar_tac
        have hguard : (next.val ≤ query.val) ↔ (index.val ≤ query.val) := by omega
        simp only [hguard]
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
      simp only [hclone, bind_tc_ok] at hb
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
        rw [ih updated1 next result (by scalar_tac) (by omega) (by scalar_tac) hloop]
        rw [PackedLeaf.get_after_insert_mut hins, hsub]
        by_cases heq : query = index
        · subst query
          rw [hfound] at hquery
          cases hquery
          simp
        · have hne : query.val ≠ index.val := by intro h; apply heq; scalar_tac
          have hsub_ne : query.val - window ≠ index.val - window := by omega
          have hguard : (next.val ≤ query.val) ↔ (index.val ≤ query.val) := by omega
          simp only [if_neg hsub_ne, hguard]

end milhouse.packed_leaf
