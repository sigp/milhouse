import Tree.BulkUpdate.Guards
import Tree.BulkUpdate.Node

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private def zeroBit {T : Type} : Tree T → Nat
  | .Zero _ => 1
  | _ => 0

private theorem zeroBit_le_one {T : Type} (self : Tree T) : zeroBit self ≤ 1 := by
  cases self <;> simp [zeroBit]

private theorem guards_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) :
    ∀ (n : Nat) (depth : Std.Usize) (treeDepth : Nat) (before after : Tree T)
      (prefix1 offset : Std.Usize),
      2 * depth.val + zeroBit before ≤ n → depth.val = treeDepth →
      before.Shape factor treeDepth → prefix1.val % subtreeCapacity factor treeDepth = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes = ok (.Ok after) →
      BulkGuardsPass mapInst updates factor treeDepth (prefix1.val + offset.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro depth treeDepth before after prefix1 offset hmeasure hdepth hshape halign hupdate
    cases hshape with
    | leaf value =>
      intro _
      obtain ⟨_, index, pending, result, hindex, hget, _, _⟩ :=
        Tree.with_updated_leaves_leaf_cloned ValueInst mapInst hupdate
      exact ⟨index, pending, usize_add_val hindex, hget⟩
    | packed factor value =>
      intro hnone
      cases hnone
    | @node factor left right child oldHash hleft hright =>
      obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
        hnd, hrightPrefix, hlo, hmiddle, hstop, _, leftStep, rightStep, hselected⟩ :=
        Tree.with_updated_leaves_node_step_selected ValueInst mapInst hlayout
          (by simpa only [hdepth] using halign) hupdate
      have hndDepth : nd.val = child := by omega
      have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hrightPrefix' : rightPrefix.val = prefix1.val + subtreeCapacity factor child := by
        simpa only [hndDepth] using hrightPrefix
      have hstop' : stop.val = prefix1.val + offset.val + subtreeCapacity factor (child + 1) := by
        simpa only [hdepth] using hstop
      have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
        apply mod_half_eq_zero
        rwa [← hcapacity]
      have halignRight : rightPrefix.val % subtreeCapacity factor child = 0 := by
        rw [hrightPrefix', Nat.add_mod_right]
        exact halignLeft
      have hsmall (old : Tree T) : 2 * nd.val + zeroBit old < n := by
        have := zeroBit_le_one old
        simp only [zeroBit] at hmeasure
        omega
      intro queryLo queryMiddle queryStop hqueryLo hqueryMiddle hqueryStop
      have heqLo : queryLo = lo := by scalar_tac
      have heqMiddle : queryMiddle = middle := by scalar_tac
      have heqStop : queryStop = stop := by scalar_tac
      subst queryLo
      subst queryMiddle
      subst queryStop
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hfalseLeft, hfalseRight⟩
        rcases hselected with htrue | htrue
        · rw [hfalseLeft] at htrue
          cases htrue
        · rw [hfalseRight] at htrue
          cases htrue
      · intro htrue
        rcases leftStep with ⟨hempty, _⟩ | ⟨_, hleftUpdate⟩
        · rw [htrue] at hempty
          cases hempty
        · exact ih _ (hsmall left) nd child left newLeft prefix1 offset (Nat.le_refl _)
            hndDepth hleft halignLeft hleftUpdate
      · intro htrue
        rcases rightStep with ⟨hempty, _⟩ | ⟨_, hrightUpdate⟩
        · rw [htrue] at hempty
          cases hempty
        · simpa only [hrightPrefix', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih _ (hsmall right) nd child right newRight rightPrefix offset (Nat.le_refl _)
              hndDepth hright halignRight hrightUpdate
    | zero factor zeroDepth =>
      have heq : zeroDepth = depth := by scalar_tac
      subst zeroDepth
      unfold Tree.with_updated_leaves at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨opt, _, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨hash, _, hupdate⟩ := hupdate
      change (if depth = depth then _ else _) = _ at hupdate
      rw [if_pos rfl] at hupdate
      by_cases hz : depth = 0#usize
      · subst depth
        intro hnone
        subst factor
        simp only [hlayout.opt_packing_factor_eq, bind_tc_ok, core.option.Option.is_some,
          Option.isSome, Bool.false_eq_true, ↓reduceIte] at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨index, hindex, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨found, hfound, hupdate⟩ := hupdate
        cases found with
        | none =>
          simp [core.option.OptionShared0T.cloned, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | some value => exact ⟨index, value, usize_add_val hindex, hfound⟩
      · rw [if_neg hz, bind_eq_ok_iff] at hupdate
        obtain ⟨nd, hnd, hupdate⟩ := hupdate
        have hndVal := usize_sub_one_val hnd
        simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        have hsmall : 2 * depth.val + zeroBit (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) < n := by
          simp only [zeroBit] at hmeasure ⊢
          omega
        have hexpanded : Tree.Shape factor (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) depth.val := by
          rw [hndVal]
          exact .node hash (.zero factor nd) (.zero factor nd)
        exact ih _ hsmall depth depth.val (Tree.Node hash (.Zero nd) (.Zero nd)) after
          prefix1 offset (Nat.le_refl _) rfl hexpanded halign hupdate

/-- Actual success certifies every selected missing-update guard. Layout,
input shape, and prefix alignment suffice; no range correctness, clone,
termination, density, capacity, or offset-alignment law is assumed. -/
theorem Tree.with_updated_leaves_guards_pass {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after)) :
    BulkGuardsPass mapInst updates factor depth.val (prefix1.val + offset.val) :=
  guards_aux ValueInst mapInst updates hlayout hashes (2 * depth.val + zeroBit before)
    depth depth.val before after prefix1 offset (Nat.le_refl _) rfl hshape halign hupdate

end milhouse.tree
