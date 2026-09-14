import Tree.Rebase.ContentsAction

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- Packed equality needs element soundness only if every paired `ne` call
returns false. Any true, failed, or diverging call removes the obligation on
all pairs, including earlier false answers: the vector cannot compare equal. -/
def NeSoundIfAllFalse {T : Type} (inst : core.cmp.PartialEq T T)
    (pairs : _root_.List (T × T)) : Prop :=
  (∀ pair ∈ pairs, inst.ne pair.1 pair.2 = ok false) →
    ∀ pair ∈ pairs, pair.1 = pair.2

/-- The earlier reached-pair law implies the weaker positive-result law. -/
theorem NeSoundIfAllFalse.of_neOn {T : Type} {inst : core.cmp.PartialEq T T}
    {pairs : _root_.List (T × T)} (hsound : NeOn inst (NeSoundAt inst) pairs) :
    NeSoundIfAllFalse inst pairs := by
  induction pairs with
  | nil => simp [NeSoundIfAllFalse]
  | cons pair rest ih =>
    intro hall item hitem
    have hhead := hall pair (by simp)
    rcases _root_.List.mem_cons.mp hitem with rfl | hrest
    · exact hsound.1 hhead
    · exact ih (hsound.2 hhead) (fun other hother => hall other (by simp [hother])) item hrest

/-- A single non-false result is enough to dispense with all soundness laws.
The call need not terminate successfully or itself be reached by the loop. -/
theorem NeSoundIfAllFalse.of_not_false {T : Type} {inst : core.cmp.PartialEq T T}
    {pairs : _root_.List (T × T)} {pair : T × T} (hmem : pair ∈ pairs)
    (hcall : inst.ne pair.1 pair.2 ≠ ok false) : NeSoundIfAllFalse inst pairs := by
  intro hall
  exact (hcall (hall pair hmem)).elim

/-- The short-circuit loop returns false exactly when every element call does.
This equivalence retains failures and divergence and assumes no termination. -/
theorem anyM_ne_false_iff {T U : Type} (inst : core.cmp.PartialEq T U)
    (pairs : _root_.List (T × U)) :
    _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) pairs = ok false ↔
      ∀ pair ∈ pairs, inst.ne pair.1 pair.2 = ok false := by
  induction pairs with
  | nil => simp [pure]
  | cons pair rest ih =>
    cases hcall : inst.ne pair.1 pair.2 with
    | fail error => simp [hcall]
    | div => simp [hcall]
    | ok different => cases different <;> simp [hcall, pure, ih]

/-- Positive vector equality is exactly length agreement and false `ne` on
every paired input. No comparison coherence or termination law is required. -/
theorem vec_eq_true_iff_ne_false {T : Type} (inst : core.cmp.PartialEq T T)
    (left right : alloc.vec.Vec T) :
    vec_eq inst left right = ok true ↔
      left.val.length = right.val.length ∧
        ∀ pair ∈ left.val.zip right.val, inst.ne pair.1 pair.2 = ok false := by
  rw [← anyM_ne_false_iff]
  unfold vec_eq alloc.vec.partial_eq.PartialEqVec.ne
  split
  · rename_i hlength
    cases _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) (left.val.zip right.val) with
    | fail error => simp [hlength]
    | div => simp [hlength]
    | ok different => cases different <;> simp [hlength]
  · rename_i hlength
    simp [hlength]

/-- The guarded element law is necessary and sufficient for soundness of
positive equality on these vectors. It imposes no obligation when their
lengths differ or a paired `ne` result prevents equality. -/
theorem vec_eq_sound_iff {T : Type} (inst : core.cmp.PartialEq T T)
    (left right : alloc.vec.Vec T) :
    (left.val.length = right.val.length → NeSoundIfAllFalse inst (left.val.zip right.val)) ↔
      (vec_eq inst left right = ok true → left.val = right.val) := by
  constructor
  · intro hsound heq
    obtain ⟨hlength, hall⟩ := (vec_eq_true_iff_ne_false inst left right).mp heq
    exact milhouse.tree.vec_eq_contents inst
      (fun _ => NeOn.of_pairs inst (NeSoundAt inst) _
        (fun pair hpair _ => hsound hlength hall pair hpair)) heq
  · intro hsound hlength hall
    have heq := hsound ((vec_eq_true_iff_ne_false inst left right).mpr ⟨hlength, hall⟩)
    rw [heq]
    intro pair hpair
    generalize right.val = values at hpair
    induction values with
    | nil => simp at hpair
    | cons value rest ih =>
      simp only [_root_.List.zip_cons_cons, _root_.List.mem_cons] at hpair
      rcases hpair with rfl | hrest
      · rfl
      · exact ih hrest

end milhouse_models
