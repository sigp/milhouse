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

/-! ## Container boundary -/

/-- `List::from_parts` records its tree, depth, and length unchanged, and
    caches exactly the packing depth supplied by the valid layout. -/
private theorem list_from_parts_fields {T N U : Type}
    {ValueInst : Value T}
    (UnsignedInst : typenum.marker_traits.Unsigned N)
    (UpdateMapInst : update_map.UpdateMap U T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (tree : Tree T) (depth length : Std.Usize) {result : list.List T N U}
    (hparts : list.List.from_parts ValueInst UnsignedInst UpdateMapInst
      tree depth length = ok result) :
    result.interface.backing.tree = tree ∧
      result.interface.backing.depth = depth ∧
      result.interface.backing.length = length ∧
      result.interface.backing.packing_depth = packing_depth := by
  unfold list.List.from_parts at hparts
  cases hlayout with
  | unpacked factor_eq depth_eq =>
    rw [depth_eq] at hparts
    simp [core.option.Option.unwrap_or] at hparts
    unfold interface.Interface.new at hparts
    cases hdefault : UpdateMapInst.coredefaultDefaultInst.default with
    | fail error => simp [hdefault, lift] at hparts
    | div => simp [hdefault, lift] at hparts
    | ok updates =>
      simp [hdefault, lift] at hparts
      subst result
      simp
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    rw [depth_eq] at hparts
    simp [core.option.Option.unwrap_or] at hparts
    unfold interface.Interface.new at hparts
    cases hdefault : UpdateMapInst.coredefaultDefaultInst.default with
    | fail error => simp [hdefault, lift] at hparts
    | div => simp [hdefault, lift] at hparts
    | ok updates =>
      simp [hdefault, lift] at hparts
      subst result
      simp

private def repeatListFinalize {T N U : Type}
    (ValueInst : Value T)
    (UnsignedInst : typenum.marker_traits.Unsigned N)
    (UpdateMapInst : update_map.UpdateMap U T)
    (tree_depth n : Std.Usize) (layer : List (Tree T × Std.Usize)) :
    Result (core.result.Result (list.List T N U) error.Error) := do
  let layer1 ← repeat.repeat_list_loop ValueInst
    { start := 0#usize, «end» := tree_depth } layer
  let (entry, rest) ←
    smallvec.SmallVec.pop (Array.Insts.SmallvecArray
      ((triomphe.arc.Arc (Tree T)) × Std.Usize) 2#usize) layer1
  let root_count ← core.option.Option.ok_or entry
    error.Error.BuilderStackEmptyFinalize
  let branch ← core.result.Result.Insts.CoreOpsTry.branch root_count
  match branch with
  | .Continue val =>
    let (root, count) := val
    do
    let empty ← smallvec.SmallVec.is_empty (Array.Insts.SmallvecArray
      ((triomphe.arc.Arc (Tree T)) × Std.Usize) 2#usize) rest
    if empty then
      if count != 1#usize then
        ok (core.result.Result.Err error.Error.BuilderStackLeftover)
      else
        let result ← list.List.from_parts ValueInst UnsignedInst
          UpdateMapInst root tree_depth n
        ok (core.result.Result.Ok result)
    else
      ok (core.result.Result.Err error.Error.BuilderStackLeftover)
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (list.List T N U) (core.convert.FromSame error.Error) residual

/-- Finalizing a valid repeated layer returns a list whose cached fields and
    dense backing tree all describe the represented logical length. -/
private theorem repeatListFinalize_returns_dense {T N U : Type}
    {ValueInst : Value T}
    (UnsignedInst : typenum.marker_traits.Unsigned N)
    (UpdateMapInst : update_map.UpdateMap U T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (tree_depth n : Std.Usize) (layer : List (Tree T × Std.Usize))
    (hlayer : RepeatLayer packing_factor 0 n.val layer)
    {result : list.List T N U}
    (hfinalize : repeatListFinalize ValueInst UnsignedInst UpdateMapInst
      tree_depth n layer = ok (core.result.Result.Ok result)) :
    result.interface.backing.length = n ∧
      result.interface.backing.packing_depth = packing_depth ∧
      DenseTree packing_factor result.interface.backing.tree
        result.interface.backing.depth.val n.val := by
  unfold repeatListFinalize at hfinalize
  cases hloop : repeat.repeat_list_loop ValueInst
      { start := 0#usize, «end» := tree_depth } layer with
  | fail error => simp [hloop] at hfinalize
  | div => simp [hloop] at hfinalize
  | ok final_layer =>
    have hfinal_layer := repeat_list_loop_preserves_layer hlayout
      tree_depth.val { start := 0#usize, «end» := tree_depth }
      layer final_layer n.val (by simp) (by simp) hlayer hloop
    cases hfinal_layer with
    | single tree count depth len total hdense hlen hcount htotal hone_full =>
      by_cases hcount_one : count = 1#usize
      · subst count
        cases hparts : list.List.from_parts ValueInst UnsignedInst
            UpdateMapInst tree tree_depth n with
        | fail error =>
          simp [hloop, smallvec.SmallVec.pop,
            core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            smallvec.SmallVec.is_empty, hparts] at hfinalize
        | div =>
          simp [hloop, smallvec.SmallVec.pop,
            core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            smallvec.SmallVec.is_empty, hparts] at hfinalize
        | ok built =>
          simp [hloop, smallvec.SmallVec.pop,
            core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            smallvec.SmallVec.is_empty, hparts] at hfinalize
          subst built
          obtain ⟨htree, hdepth, hlength, hpacking⟩ :=
            list_from_parts_fields UnsignedInst UpdateMapInst hlayout tree
              tree_depth n hparts
          refine ⟨hlength, hpacking, ?_⟩
          rw [htree, hdepth]
          simp at htotal
          simpa [htotal] using hdense
      · have hcount_val_ne : count.val ≠ 1 := by
          intro hval
          exact hcount_one (UScalar.eq_of_val_eq (by simpa using hval))
        simp [hloop, smallvec.SmallVec.pop,
          core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          smallvec.SmallVec.is_empty, hcount_val_ne] at hfinalize
    | split repeated lonely count depth lonely_len total hrepeated hlonely
        hcount hlonely_pos hlonely_partial htotal =>
      simp [hloop, smallvec.SmallVec.pop,
        core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        smallvec.SmallVec.is_empty] at hfinalize

private def repeatInitialLayer {T : Type} (ValueInst : Value T) (elem : T)
    (n : Std.Usize) (packing_factor : Option Std.Usize) :
    Result (List (Tree T × Std.Usize)) :=
  match packing_factor with
  | none => do
    let leaf ← leaf.Leaf.new elem
    let tree ← triomphe.arc.Arc.new (Tree.Leaf leaf)
    ok [(tree, n)]
  | some factor => do
    let repeated_count ← n / factor
    let lonely_count ← n % factor
    let cloned ← ValueInst.corecloneCloneInst.clone elem
    let repeated_leaf ← packed_leaf.PackedLeaf.repeat
      ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst cloned factor
    let repeated ← triomphe.arc.Arc.new (Tree.PackedLeaf repeated_leaf)
    let lonely_leaf ← packed_leaf.PackedLeaf.repeat
      ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst elem
        lonely_count
    let lonely ← triomphe.arc.Arc.new (Tree.PackedLeaf lonely_leaf)
    match repeated_count.val with
    | 0 => match lonely_count.val with
           | 0 => fail Error.panic
           | _ => ok ()
    | _ => ok ()
    match lonely_count.val with
    | 0 => ok [(repeated, repeated_count)]
    | _ =>
      match repeated_count.val with
      | 0 => ok [(lonely, 1#usize)]
      | _ => ok [(repeated, repeated_count), (lonely, 1#usize)]

/-- The leaf layer created by `repeat_list` is a valid repeated layer. The
    only non-layout premise is the branch condition `n != 0`. -/
private theorem repeatInitialLayer_preserves {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (elem : T) (n : Std.Usize) (hn : n ≠ 0#usize)
    {layer : List (Tree T × Std.Usize)}
    (hinitial : repeatInitialLayer ValueInst elem n packing_factor = ok layer) :
    RepeatLayer packing_factor 0 n.val layer := by
  have hn_pos : 0 < n.val := by
    have hn_val : n.val ≠ 0 := by
      intro hzero
      apply hn
      exact UScalar.eq_of_val_eq (by simpa using hzero)
    omega
  cases hlayout with
  | unpacked factor_eq depth_eq =>
    unfold repeatInitialLayer at hinitial
    simp [leaf.Leaf.new, leaf.Leaf.with_hash,
      alloy_primitives.bits.fixed.FixedBytes.ZERO,
      lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hinitial
    subst layer
    apply RepeatLayer.single _ n 0 1 n.val
    · exact DenseTree.leaf _
    · omega
    · exact hn_pos
    · simp
    · right
      simp [subtreeCapacity, leafCapacity]
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    have hfactor_pos : 0 < factor.val := by
      simpa [leafCapacity, factor_is_power] using
        (PackingLayout.packed factor packing_depth factor_eq depth_eq
          factor_is_power).leafCapacity_pos
    unfold repeatInitialLayer at hinitial
    cases hdiv : n / factor with
    | fail error => simp [hdiv] at hinitial
    | div => simp [hdiv] at hinitial
    | ok repeated_count =>
      obtain ⟨expected, hexpected, hexpected_val⟩ :=
        UScalar.div_spec n (y := factor) (by omega)
      rw [hdiv] at hexpected
      simp at hexpected
      subst expected
      have hrepeated_val : repeated_count.val = n.val / factor.val := by
        simpa using hexpected_val
      cases hrem : n % factor with
      | fail error => simp [hdiv, hrem] at hinitial
      | div => simp [hdiv, hrem] at hinitial
      | ok lonely_count =>
        have hrem_spec := UScalar.rem_spec n (y := factor) (by omega)
        rw [hrem] at hrem_spec
        simp at hrem_spec
        have hlonely_val : lonely_count.val = n.val % factor.val := by
          simpa using hrem_spec
        cases hclone : ValueInst.corecloneCloneInst.clone elem with
        | fail error => simp [hdiv, hrem, hclone] at hinitial
        | div => simp [hdiv, hrem, hclone] at hinitial
        | ok cloned =>
          cases hrepeated_leaf : packed_leaf.PackedLeaf.repeat
              ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst
              cloned factor with
          | fail error =>
            simp [hdiv, hrem, hclone, hrepeated_leaf] at hinitial
          | div =>
            simp [hdiv, hrem, hclone, hrepeated_leaf] at hinitial
          | ok repeated_leaf =>
            have hrepeated_dense := packedLeaf_repeat_preserves_dense
              ValueInst
              (PackingLayout.packed factor packing_depth factor_eq depth_eq
                factor_is_power) cloned hfactor_pos hrepeated_leaf
            cases hlonely_leaf : packed_leaf.PackedLeaf.repeat
                ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst
                elem lonely_count with
            | fail error =>
              simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                triomphe.arc.Arc.new] at hinitial
            | div =>
              simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                triomphe.arc.Arc.new] at hinitial
            | ok lonely_leaf =>
              by_cases hrepeated_zero : repeated_count.val = 0
              · by_cases hlonely_zero : lonely_count.val = 0
                · simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                    hrepeated_zero, hlonely_zero, triomphe.arc.Arc.new] at hinitial
                · have hlonely_pos : 0 < lonely_count.val := by omega
                  have hlonely_dense := packedLeaf_repeat_preserves_dense
                    ValueInst
                    (PackingLayout.packed factor packing_depth factor_eq
                      depth_eq factor_is_power) elem hlonely_pos hlonely_leaf
                  simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                    hrepeated_zero, hlonely_zero, triomphe.arc.Arc.new] at hinitial
                  subst layer
                  apply RepeatLayer.single _ 1#usize 0 lonely_count.val n.val
                  · exact hlonely_dense
                  · exact hlonely_pos
                  · simp
                  · have hone_val : (1#usize).val = 1 := by rfl
                    rw [hone_val, Nat.mul_one]
                    rw [hrepeated_val] at hrepeated_zero
                    rw [hlonely_val]
                    have hdecomp := Nat.mod_add_div n.val factor.val
                    rw [hrepeated_zero, Nat.mul_zero, Nat.add_zero] at hdecomp
                    exact hdecomp.symm
                  · exact Or.inl (by simp)
              · have hrepeated_pos : 0 < repeated_count.val := by omega
                by_cases hlonely_zero : lonely_count.val = 0
                · simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                    hrepeated_zero, hlonely_zero, triomphe.arc.Arc.new] at hinitial
                  subst layer
                  apply RepeatLayer.single _ repeated_count 0 factor.val n.val
                  · exact hrepeated_dense
                  · exact hfactor_pos
                  · exact hrepeated_pos
                  · rw [hlonely_val] at hlonely_zero
                    rw [hrepeated_val]
                    have hdecomp := Nat.mod_add_div n.val factor.val
                    rw [hlonely_zero, Nat.zero_add] at hdecomp
                    exact hdecomp.symm
                  · exact Or.inr (by simp [subtreeCapacity, leafCapacity])
                · have hlonely_pos : 0 < lonely_count.val := by omega
                  have hlonely_dense := packedLeaf_repeat_preserves_dense
                    ValueInst
                    (PackingLayout.packed factor packing_depth factor_eq
                      depth_eq factor_is_power) elem hlonely_pos hlonely_leaf
                  simp [hdiv, hrem, hclone, hrepeated_leaf, hlonely_leaf,
                    hrepeated_zero, hlonely_zero, triomphe.arc.Arc.new] at hinitial
                  subst layer
                  apply RepeatLayer.split _ _ repeated_count 0
                    lonely_count.val n.val
                  · simpa [subtreeCapacity, leafCapacity] using
                      hrepeated_dense
                  · exact hlonely_dense
                  · exact hrepeated_pos
                  · exact hlonely_pos
                  · simp [subtreeCapacity, leafCapacity]
                    rw [hlonely_val]
                    exact Nat.mod_lt _ hfactor_pos
                  · simp [subtreeCapacity, leafCapacity]
                    rw [hrepeated_val, hlonely_val]
                    have hdecomp := Nat.mod_add_div n.val factor.val
                    simpa [Nat.add_comm] using hdecomp.symm

/-- After exposing the two proof-side helpers, the non-empty translated
    function is exactly initial-layer construction followed by finalization. -/
private theorem repeat_list_nonempty_eq {T N U : Type}
    (ValueInst : Value T)
    (UnsignedInst : typenum.marker_traits.Unsigned N)
    (UpdateMapInst : update_map.UpdateMap U T)
    (elem : T) (n : Std.Usize) (hn : n ≠ 0#usize) :
    repeat.repeat_list ValueInst UnsignedInst UpdateMapInst elem n = (do
      let packing_factor ←
        utils.opt_packing_factor ValueInst.tree_hashTreeHashInst
      let tree_depth ← list.List.depth ValueInst UnsignedInst UpdateMapInst
      let layer ← repeatInitialLayer ValueInst elem n packing_factor
      repeatListFinalize ValueInst UnsignedInst UpdateMapInst tree_depth n
        layer) := by
  unfold repeat.repeat_list repeatInitialLayer repeatListFinalize
  simp [hn, usize_zero_add_one, usize_one_add_one,
    smallvec.SmallVec.new, smallvec.SmallVec.inline_size,
    Array.Insts.SmallvecArray.size, smallvec.SmallVec.push,
    smallvec.SmallVec.from_vec, triomphe.arc.Arc.new]
  intros
  rfl

/-- A successful `repeat_list` call returns a list whose cached logical length
    and packing depth agree with its dense backing tree.

    `PackingLayout` is the sole semantic premise. In particular, no separate
    `n ≤ capacity` premise is needed: oversized requests can only satisfy the
    theorem when the translated function itself successfully finalizes them. -/
theorem repeat_list_returns_dense {T N U : Type}
    {ValueInst : Value T}
    (UnsignedInst : typenum.marker_traits.Unsigned N)
    (UpdateMapInst : update_map.UpdateMap U T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (elem : T) (n : Std.Usize) {result : list.List T N U}
    (hrepeat : repeat.repeat_list ValueInst UnsignedInst UpdateMapInst elem n =
      ok (core.result.Result.Ok result)) :
    result.interface.backing.length = n ∧
      result.interface.backing.packing_depth = packing_depth ∧
      DenseTree packing_factor result.interface.backing.tree
        result.interface.backing.depth.val n.val := by
  by_cases hn : n = 0#usize
  · subst n
    unfold repeat.repeat_list at hrepeat
    simp only [if_pos rfl] at hrepeat
    cases hempty : list.List.empty ValueInst UnsignedInst UpdateMapInst with
    | fail error => simp [hempty] at hrepeat
    | div => simp [hempty] at hrepeat
    | ok empty =>
      simp [hempty] at hrepeat
      subst empty
      unfold list.List.empty at hempty
      cases hdepth : list.List.depth ValueInst UnsignedInst UpdateMapInst with
      | fail error => simp [hdepth] at hempty
      | div => simp [hdepth] at hempty
      | ok depth =>
        cases hparts : list.List.from_parts ValueInst UnsignedInst
            UpdateMapInst (Tree.Zero depth) depth 0#usize with
        | fail error =>
          simp [hdepth, Tree.empty, Tree.zero, triomphe.arc.Arc.new,
            hparts] at hempty
        | div =>
          simp [hdepth, Tree.empty, Tree.zero, triomphe.arc.Arc.new,
            hparts] at hempty
        | ok built =>
          simp [hdepth, Tree.empty, Tree.zero, triomphe.arc.Arc.new,
            hparts] at hempty
          subst built
          obtain ⟨htree, hcached_depth, hlength, hpacking⟩ :=
            list_from_parts_fields UnsignedInst UpdateMapInst hlayout
              (Tree.Zero depth) depth 0#usize hparts
          refine ⟨hlength, hpacking, ?_⟩
          rw [htree, hcached_depth]
          exact DenseTree.zero packing_factor depth
  · rw [repeat_list_nonempty_eq ValueInst UnsignedInst UpdateMapInst
      elem n hn, hlayout.opt_packing_factor_eq] at hrepeat
    cases hdepth : list.List.depth ValueInst UnsignedInst UpdateMapInst with
    | fail error => simp [hdepth] at hrepeat
    | div => simp [hdepth] at hrepeat
    | ok tree_depth =>
      cases hinitial : repeatInitialLayer ValueInst elem n packing_factor with
      | fail error => simp [hdepth, hinitial] at hrepeat
      | div => simp [hdepth, hinitial] at hrepeat
      | ok layer =>
        simp [hdepth, hinitial] at hrepeat
        have hlayer := repeatInitialLayer_preserves hlayout elem n hn hinitial
        exact repeatListFinalize_returns_dense UnsignedInst UpdateMapInst
          hlayout tree_depth n layer hlayer hrepeat

end milhouse.tree
