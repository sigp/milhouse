import Tree.ProgressiveList.ToVec.Clones
import Tree.Vec.Clone

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Collection succeeds exactly when the clones of its represented values
terminate. It needs no identity law and no conditions on unrelated values;
all traversal and vector-capacity obligations follow from the input invariants. -/
theorem ProgressiveList.to_vec_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    (∃ output, ProgressiveList.to_vec ValueInst mapInst self = ok output) ↔
      ∀ value ∈ contents, ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied := by
  rw [← milhouse_models.list_clone_success_iff ValueInst.corecloneCloneInst contents]
  constructor
  · rintro ⟨output, hresult⟩
    exact ⟨output.val, (ProgressiveList.to_vec_clones_iff
      ValueInst mapInst hlayout self contents hrep hdense hfits output).mp hresult⟩
  · rintro ⟨copied, hclones⟩
    have hprojection := ProgressiveList.to_vec_mapM
      ValueInst mapInst hlayout self contents hrep hdense hfits
    rw [hclones] at hprojection
    cases hresult : ProgressiveList.to_vec ValueInst mapInst self with
    | fail e => simp [hresult] at hprojection
    | div => simp [hresult] at hprojection
    | ok output => exact ⟨output, rfl⟩

/-- Terminating clones suffice for complete collection, returning their
actual results in order and preserving the sequence length. Clone identity is
only needed when specializing this result to unchanged element values. -/
theorem ProgressiveList.to_vec_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (hclone : ∀ value ∈ contents, ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied) :
    ∃ output, ProgressiveList.to_vec ValueInst mapInst self = ok output ∧
      _root_.List.mapM ValueInst.corecloneCloneInst.clone contents = ok output.val ∧
      output.val.length = contents.length := by
  obtain ⟨output, hresult⟩ := (ProgressiveList.to_vec_success_iff
    ValueInst mapInst hlayout self contents hrep hdense hfits).mpr hclone
  have hclones := (ProgressiveList.to_vec_clones_iff
    ValueInst mapInst hlayout self contents hrep hdense hfits output).mp hresult
  exact ⟨output, hresult, hclones, List.mapM_Result_length hclones⟩

end milhouse.progressive_list
