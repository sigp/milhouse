import Tree.FunsExternal
import VecSource.Funs

open Aeneas Aeneas.Std Result

/-! The compared vector bodies are freshly extracted from pinned Rust. Only
the two comparison declaration names are changed to bypass builtin replacement;
the audit checks that the entire remaining LLBC is unchanged. Vector length,
vector indexing, and slice comparison retain the Aeneas foundation models. -/

theorem vec_is_empty_agrees {T : Type} (A : Type) (value : alloc.vec.Vec T) :
    VecSource.alloc.vec.Vec.is_empty A value = alloc.vec.Vec.is_empty A value := by
  simp only [VecSource.alloc.vec.Vec.is_empty, alloc.vec.Vec.is_empty]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.isEmpty_iff_length_eq_zero]
  constructor
  · intro h
    simpa using congrArg UScalar.val h
  · intro h
    apply UScalar.eq_of_val_eq
    simpa using h

private theorem allM_not_eq_not_anyM {T : Type} (p : T → Result Bool) (values : List T) :
    List.allM (fun value => do let b ← p value; ok (!b)) values =
      (do let b ← List.anyM p values; ok (!b)) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.allM, List.anyM]
    cases p value with
    | fail error => rfl
    | div => rfl
    | ok answer => cases answer <;> simp [pure, ih]

theorem vec_eq_agrees {T U : Type} (A1 A2 : Type)
    (inst : core.cmp.PartialEq T U) (left : alloc.vec.Vec T) (right : alloc.vec.Vec U) :
    VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq A1 A2 inst left right =
      milhouse_models.vec_eq inst left right := by
  simp only [VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq, alloc.vec.Vec.index,
    VecSource.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
    bind_tc_ok]
  simp only [core.slice.cmp.PartialEqSlice.eq, milhouse_models.vec_eq,
    alloc.vec.partial_eq.PartialEqVec.ne]
  split <;> simp_all [allM_not_eq_not_anyM]

theorem vec_ne_agrees {T U : Type} (A1 A2 : Type)
    (inst : core.cmp.PartialEq T U) (left : alloc.vec.Vec T) (right : alloc.vec.Vec U) :
    VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.ne A1 A2 inst left right =
      alloc.vec.partial_eq.PartialEqVec.ne inst left right := by
  have hne : VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.ne A1 A2 inst left right =
      (do let b ← VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq A1 A2 inst left right
          ok (!b)) := by
    simp only [VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.ne,
      VecSource.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq, alloc.vec.Vec.index,
      VecSource.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
      bind_tc_ok]
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  rw [hne, vec_eq_agrees]
  unfold milhouse_models.vec_eq
  cases alloc.vec.partial_eq.PartialEqVec.ne inst left right with
  | fail error => rfl
  | div => rfl
  | ok answer => cases answer <;> rfl

#print axioms vec_is_empty_agrees
#print axioms vec_eq_agrees
#print axioms vec_ne_agrees
