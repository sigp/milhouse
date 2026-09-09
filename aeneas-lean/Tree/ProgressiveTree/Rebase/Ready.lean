import Tree.ProgressiveTree.Rebase.SelectedSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Complete input conditions for successful progressive rebasing. Missing
or shared inputs skip packing queries altogether. Otherwise the actual query
results select the reached arithmetic, geometry, and element-call conditions.
There is no packing-coherence law or rebase/traversal-success premise. -/
def ProgressiveTree.RebaseReady {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength depth : Nat) : Prop :=
  (orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨
    triomphe.arc.Arc.ptr_eq orig base = ok true) ∨
  ∃ factor packingDepth, RebasePackingQueries ValueInst.tree_hashTreeHashInst factor packingDepth ∧
    orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength baseLength depth

/-- Entering a node pair and returning successfully exposes the actual
packing queries. The successful depth query also supplies the factor result;
no layout law, metadata-success hypothesis, or query totality is assumed. -/
theorem ProgressiveTree.rebase_on_recursive_entered_packing {T : Type} (ValueInst : Value T)
    {origHash baseHash : CacheHash} {origLeft baseLeft : tree.Tree T}
    {origRight baseRight after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hpointer : triomphe.arc.Arc.ptr_eq (.ProgressiveNode origHash origLeft origRight : ProgressiveTree T)
      (.ProgressiveNode baseHash baseLeft baseRight) = ok false)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst (.ProgressiveNode origHash origLeft origRight)
      (.ProgressiveNode baseHash baseLeft baseRight) origLength baseLength depth = ok (.Ok after)) :
    ∃ factor packingDepth, RebasePackingQueries ValueInst.tree_hashTreeHashInst factor packingDepth := by
  rw [ProgressiveTree.rebase_on_recursive, hpointer] at hrebase
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨start, _, hrebase⟩ := hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨next, _, hrebase⟩ := hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨capacity, _, hrebase⟩ := hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨binary, _, hrebase⟩ := hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨optionalDepth, hdepth, _⟩ := hrebase
  obtain ⟨factor, hqueries⟩ := rebasePackingQueries_of_depth ValueInst.tree_hashTreeHashInst hdepth
  exact ⟨factor, _, hqueries⟩

/-- Successful execution reflects all input requirements, with no separate
packing, shape, capacity, density, comparison, or cache assumption. -/
theorem ProgressiveTree.rebase_on_recursive_ready {T : Type} (ValueInst : Value T)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after)) :
    orig.RebaseReady ValueInst base origLength.val baseLength.val depth.val := by
  by_cases hstop : orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨ triomphe.arc.Arc.ptr_eq orig base = ok true
  · exact Or.inl hstop
  · apply Or.inr
    cases orig with
    | ProgressiveZero => exact (hstop (Or.inl rfl)).elim
    | ProgressiveNode origHash origLeft origRight =>
      cases base with
      | ProgressiveZero => exact (hstop (Or.inr (Or.inl rfl))).elim
      | ProgressiveNode baseHash baseLeft baseRight =>
        obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec
          (.ProgressiveNode origHash origLeft origRight : ProgressiveTree T) (.ProgressiveNode baseHash baseLeft baseRight)
        cases same with
        | true => exact (hstop (Or.inr (Or.inr hpointer))).elim
        | false =>
          obtain ⟨factor, packingDepth, hqueries⟩ := ProgressiveTree.rebase_on_recursive_entered_packing ValueInst hpointer hrebase
          exact ⟨factor, packingDepth, hqueries,
            ProgressiveTree.rebase_on_recursive_requirements ValueInst hqueries hrebase⟩

/-- The complete input requirements imply actual recursive success. Immediate
stops impose no packing-query law, even if such queries fail or diverge. -/
theorem ProgressiveTree.rebase_on_recursive_success_of_ready {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (hready : orig.RebaseReady ValueInst base origLength.val baseLength.val depth.val) :
    ∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after) := by
  rcases hready with hstop | ⟨factor, packingDepth, hqueries, hinputs⟩
  · rcases hstop with rfl | rfl | hpointer
    · rw [ProgressiveTree.rebase_on_recursive]
      obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec (.ProgressiveZero : ProgressiveTree T) base
      cases same <;> simp [hpointer,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
    · rw [ProgressiveTree.rebase_on_recursive]
      obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec orig (.ProgressiveZero : ProgressiveTree T)
      cases same <;> cases orig <;> simp [hpointer,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
    · refine ⟨base, ?_⟩
      rw [ProgressiveTree.rebase_on_recursive, hpointer]
      rfl
  · exact ProgressiveTree.rebase_on_recursive_success_of_requirements ValueInst hqueries
      orig base origLength baseLength depth hinputs

/-- The complete selected-input criterion for recursive rebase success.
Packing queries are conditions only when reached, not global assumptions. -/
theorem ProgressiveTree.rebase_on_recursive_success_iff_ready {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32) :
    (∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after)) ↔
      orig.RebaseReady ValueInst base origLength.val baseLength.val depth.val := by
  constructor
  · rintro ⟨after, hrebase⟩
    exact ProgressiveTree.rebase_on_recursive_ready ValueInst hrebase
  · exact ProgressiveTree.rebase_on_recursive_success_of_ready ValueInst orig base origLength baseLength depth

/-- The public progressive call has the same exact criterion at depth zero,
with no packing-layout or global packing-query premise. -/
theorem ProgressiveTree.rebase_on_success_iff_ready {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) :
    (∃ after, ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) ↔
      orig.RebaseReady ValueInst base origLength.val baseLength.val 0 :=
  ProgressiveTree.rebase_on_recursive_success_iff_ready ValueInst orig base origLength baseLength 0#u32

end milhouse.progressive_tree
