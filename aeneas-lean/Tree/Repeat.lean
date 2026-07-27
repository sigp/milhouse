-- Preservation for the specialized repeated-list constructor.
import Tree.Invariants

open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Repeated layers -/

/-- The at-most-two-entry representation maintained by `repeat_list`.

    A singleton is either one final partial tree or copies of a full tree. A
    split layer consists of copies of a full tree followed by one non-empty
    partial tree. `total` is the logical length represented by the layer. -/
inductive RepeatLayer {T : Type} (packing_factor : Option Std.Usize) :
    Nat → Nat → List (Tree T × Std.Usize) → Prop where
  | single (tree : Tree T) (count : Std.Usize) (depth len total : Nat)
      (dense : DenseTree packing_factor tree depth len)
      (len_pos : 0 < len) (count_pos : 0 < count.val)
      (total_eq : total = len * count.val)
      (one_or_full : count.val = 1 ∨
        len = subtreeCapacity packing_factor depth) :
      RepeatLayer packing_factor depth total [(tree, count)]
  | split (repeated lonely : Tree T) (count : Std.Usize)
      (depth lonely_len total : Nat)
      (repeated_dense : DenseTree packing_factor repeated depth
        (subtreeCapacity packing_factor depth))
      (lonely_dense : DenseTree packing_factor lonely depth lonely_len)
      (count_pos : 0 < count.val) (lonely_pos : 0 < lonely_len)
      (lonely_partial : lonely_len < subtreeCapacity packing_factor depth)
      (total_eq : total =
        subtreeCapacity packing_factor depth * count.val + lonely_len) :
      RepeatLayer packing_factor depth total
        [(repeated, count), (lonely, 1#usize)]

/-- A finalized singleton layer contains a dense tree for its entire logical
    length. -/
theorem RepeatLayer.singleton_dense {T : Type}
    {packing_factor : Option Std.Usize} {depth total : Nat} {tree : Tree T}
    (hlayer : RepeatLayer packing_factor depth total [(tree, 1#usize)]) :
    DenseTree packing_factor tree depth total := by
  cases hlayer with
  | single tree count depth len total hdense _ _ htotal _ =>
    simp at htotal
    simpa [htotal] using hdense

private theorem subtreeCapacity_succ
    (packing_factor : Option Std.Usize) (depth : Nat) :
    subtreeCapacity packing_factor (depth + 1) =
      2 * subtreeCapacity packing_factor depth := by
  simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Padding a non-empty dense tree on the right preserves its logical length. -/
private theorem DenseTree.pad_right {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T}
    (depth : Std.Usize) {len : Nat}
    (hdense : DenseTree packing_factor tree depth.val len)
    (hlen : 0 < len)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash tree (Tree.Zero depth))
      (depth.val + 1) len := by
  simpa using DenseTree.node packing_factor hash tree (Tree.Zero depth)
    depth.val len 0 hdense (DenseTree.zero packing_factor depth) hlen (by omega)

/-- Pairing two copies of a full dense tree produces a full parent. -/
private theorem DenseTree.pair_full {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T}
    (depth : Std.Usize)
    (hdense : DenseTree packing_factor tree depth.val
      (subtreeCapacity packing_factor depth.val))
    (hcapacity : 0 < subtreeCapacity packing_factor depth.val)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash tree tree) (depth.val + 1)
      (subtreeCapacity packing_factor (depth.val + 1)) := by
  have hnode := DenseTree.node packing_factor hash tree tree depth.val
    (subtreeCapacity packing_factor depth.val)
    (subtreeCapacity packing_factor depth.val) hdense hdense hcapacity
    (by intros; rfl)
  simpa [subtreeCapacity_succ, two_mul] using hnode

/-- Appending a non-empty partial dense tree to a full left sibling produces
    the corresponding dense parent. -/
private theorem DenseTree.pair_partial {T : Type}
    {packing_factor : Option Std.Usize} {left right : Tree T}
    (depth : Std.Usize) {right_len : Nat}
    (hleft : DenseTree packing_factor left depth.val
      (subtreeCapacity packing_factor depth.val))
    (hright : DenseTree packing_factor right depth.val right_len)
    (hcapacity : 0 < subtreeCapacity packing_factor depth.val)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash left right) (depth.val + 1)
      (subtreeCapacity packing_factor depth.val + right_len) := by
  exact DenseTree.node packing_factor hash left right depth.val
    (subtreeCapacity packing_factor depth.val) right_len hleft hright
    hcapacity (by intros; rfl)

/-! ## Loop preservation -/

private theorem range_usize_next_some
    (iter : core.ops.range.Range Std.Usize)
    (hlt : iter.start.val < iter.end.val) :
    ∃ iter1,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some iter.start, iter1) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end := by
  have hspec :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        ⦃ option iter1 => option = some iter.start ∧
          iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ⦄ :=
    core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty := .Usize) (by intros; rfl) (by intros; rfl) iter hlt
  cases hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter with
  | fail error => rw [hnext] at hspec; simp at hspec
  | div => rw [hnext] at hspec; simp at hspec
  | ok result =>
    rw [hnext] at hspec
    simp at hspec
    obtain ⟨option, iter1⟩ := result
    change option = some iter.start ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end at hspec
    obtain ⟨rfl, hstart, hend⟩ := hspec
    exact ⟨iter1, by simp, hstart, hend⟩

private theorem usize_zero_add_one :
    (0#usize + 1#usize) = ok 1#usize := by
  have hspec := UScalar.add_equiv (0#usize) (1#usize)
  cases hadd : 0#usize + 1#usize with
  | fail error =>
    rw [hadd] at hspec
    simp at hspec
    have hbits : 0 < System.Platform.numBits := by native_decide
    omega
  | div => rw [hadd] at hspec; simp at hspec
  | ok result =>
    rw [hadd] at hspec
    have hresult : result = 1#usize :=
      UScalar.eq_of_val_eq (by simpa using hspec.2.1)
    simpa [hresult] using hadd

private theorem usize_one_add_one :
    (1#usize + 1#usize) = ok 2#usize := by
  have hspec := UScalar.add_equiv (1#usize) (1#usize)
  cases hadd : 1#usize + 1#usize with
  | fail error =>
    rw [hadd] at hspec
    simp at hspec
    have hbits : 2 < 2 ^ System.Platform.numBits := by native_decide
    omega
  | div => rw [hadd] at hspec; simp at hspec
  | ok result =>
    rw [hadd] at hspec
    have hresult : result = 2#usize :=
      UScalar.eq_of_val_eq (by simpa using hspec.2.1)
    simpa [hresult] using hadd

private theorem repeat_list_body_next {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (iter : core.ops.range.Range Std.Usize) {total : Nat}
    {layer : List (Tree T × Std.Usize)}
    (hlt : iter.start.val < iter.end.val)
    (hlayer : RepeatLayer packing_factor iter.start.val total layer) :
    ∃ iter1 layer1,
      repeat.repeat_list_loop.body ValueInst iter layer =
        ok (.cont (iter1, layer1)) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
      RepeatLayer packing_factor iter1.start.val total layer1 := by
  obtain ⟨iter1, hnext, hstart, hend⟩ := range_usize_next_some iter hlt
  let hash : alloy_primitives.bits.fixed.FixedBytes 32#usize :=
    Array.repeat 32#usize 0#u8
  have hcapacity : 0 < subtreeCapacity packing_factor iter.start.val :=
    hlayout.subtreeCapacity_pos iter.start.val
  have hzero_add_one := usize_zero_add_one
  have hone_add_one := usize_one_add_one
  cases hlayer with
  | single tree count depth len total hdense hlen hcount htotal hone_full =>
    by_cases hone : count.val = 1
    · have hcount_eq : count = 1#usize := UScalar.eq_of_val_eq (by simpa using hone)
      subst count
      let padded := Tree.Node hash tree (Tree.Zero iter.start)
      refine ⟨iter1, [(padded, 1#usize)], ?_, hstart, hend, ?_⟩
      · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one, padded, hash,
          smallvec.SmallVec.pop, smallvec.SmallVec.new,
          smallvec.SmallVec.inline_size, Array.Insts.SmallvecArray.size,
          smallvec.SmallVec.push,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.zero, Tree.node,
          alloy_primitives.bits.fixed.FixedBytes.ZERO,
          lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
      · rw [hstart]
        apply RepeatLayer.single padded 1#usize (iter.start.val + 1) len total
        · exact hdense.pad_right iter.start hlen hash
        · exact hlen
        · simp
        · simpa using htotal
        · exact Or.inl (by simp)
    · have hfull : len = subtreeCapacity packing_factor iter.start.val :=
        hone_full.resolve_left hone
      obtain ⟨half, hhalf, hhalf_val⟩ :=
        UScalar.div_spec count (y := 2#usize) (by simp)
      have hhalf_nat : half.val = count.val / 2 := by simpa using hhalf_val
      by_cases heven : count.val % 2 = 0
      · have hcount_even : count.val = 2 * half.val := by
          rw [hhalf_nat]
          omega
        let paired := Tree.Node hash tree tree
        refine ⟨iter1, [(paired, half)], ?_, hstart, hend, ?_⟩
        · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one,
            core.num.Usize.is_multiple_of, UScalar.is_multiple_of, heven,
            hhalf, paired, hash, smallvec.SmallVec.pop,
            smallvec.SmallVec.new, smallvec.SmallVec.inline_size,
            Array.Insts.SmallvecArray.size, smallvec.SmallVec.push,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.node,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
        · rw [hstart]
          have hdense_full : DenseTree packing_factor tree iter.start.val
              (subtreeCapacity packing_factor iter.start.val) := by
            simpa [hfull] using hdense
          apply RepeatLayer.single paired half (iter.start.val + 1)
            (subtreeCapacity packing_factor (iter.start.val + 1)) total
          · exact hdense_full.pair_full iter.start hcapacity hash
          · rw [subtreeCapacity_succ]; omega
          · omega
          · rw [htotal, hfull, hcount_even, subtreeCapacity_succ]
            ring
          · exact Or.inr rfl
      · have hcount_odd : count.val = 2 * half.val + 1 := by
          rw [hhalf_nat]
          omega
        let paired := Tree.Node hash tree tree
        let padded := Tree.Node hash tree (Tree.Zero iter.start)
        refine ⟨iter1, [(paired, half), (padded, 1#usize)], ?_, hstart,
          hend, ?_⟩
        · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one,
            hone_add_one,
            core.num.Usize.is_multiple_of, UScalar.is_multiple_of, heven,
            hhalf, paired, padded, hash, smallvec.SmallVec.pop,
            smallvec.SmallVec.new, smallvec.SmallVec.inline_size,
            Array.Insts.SmallvecArray.size, smallvec.SmallVec.push,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.zero, Tree.node,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
        · rw [hstart]
          have hdense_full : DenseTree packing_factor tree iter.start.val
              (subtreeCapacity packing_factor iter.start.val) := by
            simpa [hfull] using hdense
          apply RepeatLayer.split paired padded half (iter.start.val + 1)
            (subtreeCapacity packing_factor iter.start.val) total
          · exact hdense_full.pair_full iter.start hcapacity hash
          · exact hdense_full.pad_right iter.start hcapacity hash
          · omega
          · exact hcapacity
          · rw [subtreeCapacity_succ]; omega
          · rw [htotal, hfull, hcount_odd, subtreeCapacity_succ]
            ring
  | split repeated lonely count depth lonely_len total hrepeated hlonely
      hcount hlonely_pos hlonely_partial htotal =>
    by_cases hone : count.val = 1
    · have hcount_eq : count = 1#usize := UScalar.eq_of_val_eq (by simpa using hone)
      subst count
      let joined := Tree.Node hash repeated lonely
      refine ⟨iter1, [(joined, 1#usize)], ?_, hstart, hend, ?_⟩
      · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one, joined, hash,
          smallvec.SmallVec.pop, smallvec.SmallVec.new,
          smallvec.SmallVec.inline_size, Array.Insts.SmallvecArray.size,
          smallvec.SmallVec.push,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.node,
          alloy_primitives.bits.fixed.FixedBytes.ZERO,
          lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
      · rw [hstart]
        apply RepeatLayer.single joined 1#usize (iter.start.val + 1)
          (subtreeCapacity packing_factor iter.start.val + lonely_len) total
        · exact hrepeated.pair_partial iter.start hlonely hcapacity hash
        · omega
        · simp
        · simpa using htotal
        · exact Or.inl (by simp)
    · obtain ⟨half, hhalf, hhalf_val⟩ :=
        UScalar.div_spec count (y := 2#usize) (by simp)
      have hhalf_nat : half.val = count.val / 2 := by simpa using hhalf_val
      by_cases heven : count.val % 2 = 0
      · have hcount_even : count.val = 2 * half.val := by
          rw [hhalf_nat]
          omega
        let paired := Tree.Node hash repeated repeated
        let padded := Tree.Node hash lonely (Tree.Zero iter.start)
        refine ⟨iter1, [(paired, half), (padded, 1#usize)], ?_, hstart,
          hend, ?_⟩
        · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one,
            hone_add_one,
            core.num.Usize.is_multiple_of, UScalar.is_multiple_of, heven,
            hhalf, paired, padded, hash, smallvec.SmallVec.pop,
            smallvec.SmallVec.new, smallvec.SmallVec.inline_size,
            Array.Insts.SmallvecArray.size, smallvec.SmallVec.push,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.zero, Tree.node,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
        · rw [hstart]
          apply RepeatLayer.split paired padded half (iter.start.val + 1)
            lonely_len total
          · exact hrepeated.pair_full iter.start hcapacity hash
          · exact hlonely.pad_right iter.start hlonely_pos hash
          · omega
          · exact hlonely_pos
          · rw [subtreeCapacity_succ]; omega
          · rw [htotal, hcount_even, subtreeCapacity_succ]
            ring
      · have hcount_odd : count.val = 2 * half.val + 1 := by
          rw [hhalf_nat]
          omega
        let paired := Tree.Node hash repeated repeated
        let joined := Tree.Node hash repeated lonely
        refine ⟨iter1, [(paired, half), (joined, 1#usize)], ?_, hstart,
          hend, ?_⟩
        · simp [repeat.repeat_list_loop.body, hnext, hzero_add_one,
            hone_add_one,
            core.num.Usize.is_multiple_of, UScalar.is_multiple_of, heven,
            hhalf, paired, joined, hash, smallvec.SmallVec.pop,
            smallvec.SmallVec.new, smallvec.SmallVec.inline_size,
            Array.Insts.SmallvecArray.size, smallvec.SmallVec.push,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.node,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
        · rw [hstart]
          apply RepeatLayer.split paired joined half (iter.start.val + 1)
            (subtreeCapacity packing_factor iter.start.val + lonely_len) total
          · exact hrepeated.pair_full iter.start hcapacity hash
          · exact hrepeated.pair_partial iter.start hlonely hcapacity hash
          · omega
          · omega
          · rw [subtreeCapacity_succ]; omega
          · rw [htotal, hcount_odd, subtreeCapacity_succ]
            ring

private theorem range_usize_next_none
    (iter : core.ops.range.Range Std.Usize)
    (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (none, iter) := by
  have hspec :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        ⦃ option iter1 => option = none ∧ iter1 = iter ⦄ :=
    core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty := .Usize) (by intros; rfl) iter hge
  cases hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter with
  | fail error => rw [hnext] at hspec; simp at hspec
  | div => rw [hnext] at hspec; simp at hspec
  | ok result =>
    rw [hnext] at hspec
    simp at hspec
    obtain ⟨option, iter1⟩ := result
    change option = none ∧ iter1 = iter at hspec
    obtain ⟨rfl, rfl⟩ := hspec
    rfl

private theorem repeat_list_loop_step {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.Usize)
    (layer : List (Tree T × Std.Usize)) :
    repeat.repeat_list_loop ValueInst iter layer =
      match repeat.repeat_list_loop.body ValueInst iter layer with
      | ok (.cont (iter1, layer1)) =>
        repeat.repeat_list_loop ValueInst iter1 layer1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold repeat.repeat_list_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : repeat.repeat_list_loop.body ValueInst iter layer with
  | fail error => simp [hbody]
  | div => simp [hbody]
  | ok flow =>
    cases flow with
    | cont state =>
      obtain ⟨iter1, layer1⟩ := state
      simp [hbody]
      rfl
    | done result => simp [hbody]

/-- Every successful execution of the repeat loop preserves the represented
    logical length and advances the layer depth to the range end. -/
private theorem repeat_list_loop_preserves_layer {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth) :
    ∀ (fuel : Nat) (iter : core.ops.range.Range Std.Usize)
      (layer result : List (Tree T × Std.Usize)) (total : Nat),
      iter.end.val - iter.start.val ≤ fuel →
      iter.start.val ≤ iter.end.val →
      RepeatLayer packing_factor iter.start.val total layer →
      repeat.repeat_list_loop ValueInst iter layer = ok result →
      RepeatLayer packing_factor iter.end.val total result := by
  intro fuel
  induction fuel with
  | zero =>
    intro iter layer result total hfuel hbounds hlayer hloop
    have heq : iter.start.val = iter.end.val := by omega
    have hnext := range_usize_next_none iter (by omega)
    rw [repeat_list_loop_step] at hloop
    unfold repeat.repeat_list_loop.body at hloop
    simp [hnext] at hloop
    subst result
    simpa [heq] using hlayer
  | succ fuel ih =>
    intro iter layer result total hfuel hbounds hlayer hloop
    by_cases hlt : iter.start.val < iter.end.val
    · obtain ⟨iter1, layer1, hbody, hstart, hend, hlayer1⟩ :=
        repeat_list_body_next hlayout iter hlt hlayer
      rw [repeat_list_loop_step, hbody] at hloop
      simp at hloop
      rw [← hend]
      apply ih iter1 layer1 result total
      · rw [hend, hstart]
        omega
      · rw [hend, hstart]
        omega
      · exact hlayer1
      · exact hloop
    · have heq : iter.start.val = iter.end.val := by omega
      have hnext := range_usize_next_none iter (by omega)
      rw [repeat_list_loop_step] at hloop
      unfold repeat.repeat_list_loop.body at hloop
      simp [hnext] at hloop
      subst result
      simpa [heq] using hlayer

end milhouse.tree
