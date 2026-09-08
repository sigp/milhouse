import Tree.Builder.Carry

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- The actual trailing-zero carry count succeeds when a value has prepared
a nonempty base subtree after an aligned canonical prefix. The index and
logical counter equations also supply the vector and counter bounds. -/
theorem Builder.push_loop0_append_success {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (stack : alloc.vec.Vec (utils.MaybeArced (tree.Tree T)))
    (length nextIndex : Std.Usize) (zeros : Std.U32) (top : tree.Tree T)
    {root total topLen : Nat}
    (hstack : BuilderStack factor 0 stack.val root total)
    (htop : DenseTree factor top 0 topLen) (hpositive : 0 < topLen)
    (haligned : total % subtreeCapacity factor 0 = 0)
    (hfits : total + topLen ≤ subtreeCapacity factor root)
    (hcursor : length.val + 1 = total + topLen)
    (hnext : nextIndex.val = length.val + 1)
    (hzeros : core.num.Usize.trailing_zeros nextIndex = ok zeros) :
    ∃ resultStack resultLength,
      Builder.push_loop0 ValueInst
        { start := 0#u32, «end» := core.num.U32.saturating_sub zeros (UScalar.cast .U32 packingDepth) }
        stack length top =
        ok (core.result.Result.Ok (), resultStack, resultLength) := by
  have hlength : length.val < Std.Usize.max := by
    have hn : nextIndex.val ≤ Std.Usize.max := by scalar_tac
    omega
  have hroom : stack.val.length < Std.Usize.max := by
    have hentries := hstack.entries_le_length
    omega
  by_cases hfull : topLen = subtreeCapacity factor 0
  · obtain ⟨count, finalStack, finalTop, finalDepth, finalLen, hplan, hcarry, _⟩ :=
      hstack.append_subtree hlayout htop hpositive haligned hfits
    have hcount := push_full_base_merge_count_eq hlayout hcarry
      (show nextIndex.val = total + subtreeCapacity factor 0 by omega) hzeros
    obtain ⟨resultStack, resultLength, hloop, _⟩ := Builder.push_loop0_success hplan
      { start := 0#u32, «end» := core.num.U32.saturating_sub zeros (UScalar.cast .U32 packingDepth) }
      stack length
      (by simpa using hcount) rfl hroom hlength
    exact ⟨resultStack, resultLength, hloop⟩
  · have hpartial : topLen < subtreeCapacity factor 0 := by
      have hbound := htop.length_le_capacity
      omega
    cases factor with
    | none =>
      simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hpartial
      omega
    | some factor =>
      have hmod : nextIndex.val % factor.val ≠ 0 := by
        simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at haligned hpartial
        rw [hnext, hcursor, Nat.add_mod, haligned, Nat.zero_add,
          Nat.mod_eq_of_lt hpartial, Nat.mod_eq_of_lt hpartial]
        omega
      have hcount := push_partial_base_merge_count_zero hlayout
        (show 0 < nextIndex.val by omega) hmod hzeros
      have hplan := BuilderMergePlan.done (ValueInst := ValueInst) stack.val top 0 topLen htop hpositive
      obtain ⟨resultStack, resultLength, hloop, _⟩ := Builder.push_loop0_success hplan
        { start := 0#u32, «end» := core.num.U32.saturating_sub zeros (UScalar.cast .U32 packingDepth) }
        stack length
        (by simpa using hcount) rfl hroom hlength
      exact ⟨resultStack, resultLength, hloop⟩

end milhouse.builder
