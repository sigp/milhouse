import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Separate laws for copied packed storage and pending values, restricted to
children selected by the binary traversal's range queries. The storage law
can depend on the leaf's global start, so retained and overwritten slots can
have different requirements. No update call or result is part of this law. -/
def Tree.BulkCloneScope {T U : Type}
    (stored : packed_leaf.PackedLeaf T → Nat → Prop) (pending : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) : (depth start : Nat) → Prop
  | 0, start =>
    (match self with
      | .PackedLeaf leaf => stored leaf start
      | _ => True) ∧
    ∀ (query : Std.Usize) value, start ≤ query.val → query.val < start + leafCapacity factor →
      mapInst.get updates query = ok (some value) → pending value
  | depth + 1, start =>
    let (left, right) := match self with
      | .Node _ left right => (left, right)
      | _ => (.Zero 0#usize, .Zero 0#usize)
    (∀ (lo hi : Std.Usize), lo.val = start → hi.val = start + subtreeCapacity factor depth →
      mapInst.has_any_in_range updates lo hi = ok true →
      left.BulkCloneScope stored pending mapInst updates factor depth start) ∧
    (∀ (lo hi : Std.Usize), lo.val = start + subtreeCapacity factor depth →
      hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth →
      mapInst.has_any_in_range updates lo hi = ok true →
      right.BulkCloneScope stored pending mapInst updates factor depth (start + subtreeCapacity factor depth))

/-- Pointwise implications for storage and pending values preserve the same
selection of binary children. -/
theorem Tree.BulkCloneScope.mono {T U : Type}
    {S R : packed_leaf.PackedLeaf T → Nat → Prop} {P Q : T → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (hSR : ∀ leaf start, S leaf start → R leaf start)
    (hPQ : ∀ value, P value → Q value) (self : Tree T) (depth start : Nat)
    (hself : self.BulkCloneScope S P mapInst updates factor depth start) :
    self.BulkCloneScope R Q mapInst updates factor depth start := by
  induction depth generalizing self start with
  | zero =>
    constructor
    · cases self with
      | PackedLeaf leaf => exact hSR leaf start hself.1
      | Leaf _ => trivial
      | Node _ _ _ => trivial
      | Zero _ => trivial
    · intro query value hlo hhi hget
      exact hPQ value (hself.2 query value hlo hhi hget)
  | succ depth ih =>
    cases self <;> simp only [Tree.BulkCloneScope] at hself ⊢
    all_goals
      constructor
      · intro lo hi hlo hhi hselected
        exact ih _ _ (hself.1 lo hi hlo hhi hselected)
      · intro lo hi hlo hhi hselected
        exact ih _ _ (hself.2 lo hi hlo hhi hselected)

/-- Zero nodes have no copied storage, independently of their Rust depth tag. -/
theorem Tree.BulkCloneScope.zero_congr {T U : Type}
    (S : packed_leaf.PackedLeaf T → Nat → Prop) (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (first second : Std.Usize) (depth start : Nat) :
    (Tree.Zero first : Tree T).BulkCloneScope S P mapInst updates factor depth start ↔
      (Tree.Zero second : Tree T).BulkCloneScope S P mapInst updates factor depth start := by
  cases depth <;> rfl

/-- Expanding a zero node introduces no stored values or clone requirements. -/
theorem Tree.BulkCloneScope.zero_expand {T U : Type}
    (S : packed_leaf.PackedLeaf T → Nat → Prop) (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (zeroDepth childDepth : Std.Usize) (depth start : Nat)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)) :
    (Tree.Zero zeroDepth : Tree T).BulkCloneScope S P mapInst updates factor (depth + 1) start ↔
      (Tree.Node hash (.Zero childDepth) (.Zero childDepth) : Tree T).BulkCloneScope
        S P mapInst updates factor (depth + 1) start := by
  simp only [Tree.BulkCloneScope,
    Tree.BulkCloneScope.zero_congr S P mapInst updates factor 0#usize childDepth]

/-- A single value law on all selected clone inputs. Termination uses this
scope because even stored values subsequently overwritten are first cloned. -/
abbrev Tree.BulkCloneOn {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start : Nat) : Prop :=
  self.BulkCloneScope (fun leaf _ => ∀ value ∈ leaf.values.val, P value)
    P mapInst updates factor depth start

/-- A value law only for stored slots retained because the pending map has
no replacement. Slots outside the packing window are not observed. -/
def PackedRetainedCloneOn {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (capacity : Nat)
    (leaf : packed_leaf.PackedLeaf T) (start : Nat) : Prop :=
  ∀ (query : Std.Usize) value, start ≤ query.val → query.val < start + capacity →
    mapInst.get updates query = ok none → leaf.values.val[query.val - start]? = some value → P value

/-- Content preservation needs identity only for retained stored slots and
pending values in selected leaf windows. -/
abbrev Tree.BulkRetainedCloneOn {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start : Nat) : Prop :=
  self.BulkCloneScope (PackedRetainedCloneOn P mapInst updates (leafCapacity factor))
    P mapInst updates factor depth start

/-- Exactly the clone laws used by total content correctness: every copied
stored value terminates, retained slots preserve their values, and pending
values preserve theirs. Identity of discarded stored copies is unnecessary. -/
def Tree.BulkCloneLaws {T U : Type} (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start : Nat) : Prop :=
  self.BulkCloneScope
    (fun leaf start =>
      (∀ value ∈ leaf.values.val, ∃ cloned, cloneInst.clone value = ok cloned) ∧
      PackedRetainedCloneOn (fun value => cloneInst.clone value = ok value)
        mapInst updates (leafCapacity factor) leaf start)
    (fun value => cloneInst.clone value = ok value) mapInst updates factor depth start

theorem Tree.BulkCloneLaws.terminates {T U : Type} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth start : Nat}
    (hself : self.BulkCloneLaws cloneInst mapInst updates factor depth start) :
    self.BulkCloneOn (fun value => ∃ cloned, cloneInst.clone value = ok cloned)
      mapInst updates factor depth start :=
  Tree.BulkCloneScope.mono mapInst updates factor (fun _ _ h => h.1)
    (fun value h => ⟨value, h⟩) self depth start hself

theorem Tree.BulkCloneLaws.preserves {T U : Type} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth start : Nat}
    (hself : self.BulkCloneLaws cloneInst mapInst updates factor depth start) :
    self.BulkRetainedCloneOn (fun value => cloneInst.clone value = ok value)
      mapInst updates factor depth start :=
  Tree.BulkCloneScope.mono mapInst updates factor (fun _ _ h => h.2)
    (fun _ h => h) self depth start hself

/-- A global value law specializes to selected clone inputs. -/
theorem Tree.BulkCloneOn.of_all {T U : Type} {P : T → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (hP : ∀ value, P value) (self : Tree T) (depth start : Nat) :
    self.BulkCloneOn P mapInst updates factor depth start := by
  induction depth generalizing self start with
  | zero =>
    constructor
    · cases self <;> simp_all
    · intro query value _ _ _
      exact hP value
  | succ depth ih =>
    cases self <;> simp only [Tree.BulkCloneOn, Tree.BulkCloneScope] <;>
      constructor <;> intro lo hi _ _ _ <;> apply ih

/-- Implications between value laws lift through the same selected inputs. -/
theorem Tree.BulkCloneOn.mono {T U : Type} {P Q : T → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (hPQ : ∀ value, P value → Q value) (self : Tree T) (depth start : Nat)
    (hself : self.BulkCloneOn P mapInst updates factor depth start) :
    self.BulkCloneOn Q mapInst updates factor depth start :=
  Tree.BulkCloneScope.mono mapInst updates factor
    (fun _ _ h value hv => hPQ value (h value hv)) hPQ self depth start hself

/-- Restrict a law on copied storage to the slots that survive the update. -/
theorem Tree.BulkCloneOn.retained {T U : Type} {P : T → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth start : Nat}
    (hself : self.BulkCloneOn P mapInst updates factor depth start) :
    self.BulkRetainedCloneOn P mapInst updates factor depth start :=
  Tree.BulkCloneScope.mono mapInst updates factor
    (fun _ _ h _ value _ _ _ hv => h value (_root_.List.mem_of_getElem? hv))
    (fun _ h => h) self depth start hself

/-- Identity on every copied value supplies the narrower total clone laws. -/
theorem Tree.BulkCloneOn.to_laws {T U : Type} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth start : Nat}
    (hself : self.BulkCloneOn (fun value => cloneInst.clone value = ok value)
      mapInst updates factor depth start) :
    self.BulkCloneLaws cloneInst mapInst updates factor depth start :=
  Tree.BulkCloneScope.mono mapInst updates factor
    (fun _ _ h => ⟨fun value hv => ⟨value, h value hv⟩,
      fun _ value _ _ _ hv => h value (_root_.List.mem_of_getElem? hv)⟩)
    (fun _ h => h) self depth start hself

theorem Tree.BulkCloneOn.zero_congr {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (first second : Std.Usize) (depth start : Nat) :
    (Tree.Zero first : Tree T).BulkCloneOn P mapInst updates factor depth start ↔
      (Tree.Zero second : Tree T).BulkCloneOn P mapInst updates factor depth start :=
  Tree.BulkCloneScope.zero_congr _ P mapInst updates factor first second depth start

theorem Tree.BulkCloneOn.zero_expand {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (zeroDepth childDepth : Std.Usize) (depth start : Nat)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)) :
    (Tree.Zero zeroDepth : Tree T).BulkCloneOn P mapInst updates factor (depth + 1) start ↔
      (Tree.Node hash (.Zero childDepth) (.Zero childDepth) : Tree T).BulkCloneOn
        P mapInst updates factor (depth + 1) start :=
  Tree.BulkCloneScope.zero_expand _ P mapInst updates factor zeroDepth childDepth depth start hash

end milhouse.tree
