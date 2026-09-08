import Tree.ProgressiveTree.Equality.Correctness
import Tree.ProgressiveTree.Equality.Soundness
import Tree.ProgressiveList.Equality.Structure

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Actual derived list equality terminates and characterizes its compared
    fields. The map law concerns only these two maps, and is needed only when
    the preceding tree and length comparisons succeed. No backing invariant,
    packing, cloning, hash law, or literal map equality is assumed. -/
theorem ProgressiveList.partial_eq_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U)
    (hne : milhouse_models.NeSpec ValueInst.corecmpPartialEqInst)
    (updatesEqual : U → U → Prop) (self other : ProgressiveList T U)
    (hmap : self.tree.StructuralEq other.tree → self.length = other.length →
      ∃ different, mapEqInst.ne self.updates other.updates = ok different ∧
        (different = false ↔ updatesEqual self.updates other.updates)) :
    ∃ equal, ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq
      ValueInst mapInst ValueInst mapInst mapEqInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq updatesEqual other) := by
  obtain ⟨treeEqual, htree, htreeSame⟩ :=
    progressive_tree.ProgressiveTree.arc_eq_spec ValueInst hne self.tree other.tree
  cases treeEqual with
  | false =>
    refine ⟨false, ?_, ?_⟩
    · simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree]
    · simp [ProgressiveList.StructuralEq, ← htreeSame]
  | true =>
    by_cases hlength : self.length = other.length
    · obtain ⟨different, hcompare, hsame⟩ := hmap (htreeSame.mp rfl) hlength
      refine ⟨!different, ?_, ?_⟩
      · cases different <;>
          simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength, hcompare]
      · cases different <;>
          simpa [ProgressiveList.StructuralEq, ← htreeSame, hlength] using hsame
    · refine ⟨false, ?_, ?_⟩
      · simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
          core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength]
      · simp [ProgressiveList.StructuralEq, hlength]

/-- The extracted trait's default inequality returns exactly the negation of
    structural equality, with the same short-circuit-sensitive generic laws. -/
theorem ProgressiveList.partial_ne_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U)
    (hne : milhouse_models.NeSpec ValueInst.corecmpPartialEqInst)
    (updatesEqual : U → U → Prop) (self other : ProgressiveList T U)
    (hmap : self.tree.StructuralEq other.tree → self.length = other.length →
      ∃ different, mapEqInst.ne self.updates other.updates = ok different ∧
        (different = false ↔ updatesEqual self.updates other.updates)) :
    ∃ different, (ProgressiveList.Insts.CoreCmpPartialEqProgressiveList
      ValueInst mapInst ValueInst mapInst mapEqInst).ne self other = ok different ∧
      (different = false ↔ self.StructuralEq updatesEqual other) := by
  obtain ⟨equal, hcompare, hsame⟩ :=
    ProgressiveList.partial_eq_spec ValueInst mapInst mapEqInst hne updatesEqual self other hmap
  refine ⟨!equal, ?_, ?_⟩
  · simp [core.cmp.PartialEq.ne.default, hcompare]
  · cases equal <;> simpa using hsame

/-- A positive result records exactly the three successful comparisons, with
    no semantic laws or termination assumptions. -/
theorem ProgressiveList.partial_eq_true_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U) (self other : ProgressiveList T U) :
    ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq
      ValueInst mapInst ValueInst mapInst mapEqInst self other = ok true ↔
      progressive_tree.ProgressiveTree.arc_eq ValueInst self.tree other.tree = ok true ∧
        self.length = other.length ∧ mapEqInst.ne self.updates other.updates = ok false := by
  cases htree : progressive_tree.ProgressiveTree.arc_eq ValueInst self.tree other.tree with
  | fail e => simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree]
  | div => simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree]
  | ok equal =>
    cases equal with
    | false => simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree]
    | true =>
      by_cases hlength : self.length = other.length
      · cases hmap : mapEqInst.ne self.updates other.updates <;>
          simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength, hmap]
      · simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
          core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength]

/-- Positive list equality needs only soundness of the successful element and
    pending-map comparisons; comparisons on other inputs may fail or diverge. -/
theorem ProgressiveList.partial_eq_true_imp_structural {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    (updatesEqual : U → U → Prop) {self other : ProgressiveList T U}
    (hmap : mapEqInst.ne self.updates other.updates = ok false →
      updatesEqual self.updates other.updates)
    (hequal : ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq
      ValueInst mapInst ValueInst mapInst mapEqInst self other = ok true) :
    self.StructuralEq updatesEqual other := by
  obtain ⟨htree, hlength, hupdates⟩ :=
    (ProgressiveList.partial_eq_true_iff ValueInst mapInst mapEqInst self other).mp hequal
  exact ⟨progressive_tree.ProgressiveTree.arc_eq_true_imp_structural ValueInst hsound htree,
    hlength, hmap hupdates⟩

/-- A positive comparison identifies the same represented merged sequence and
    transfers backing validity. Map equality need only preserve observable
    reads and maximum; the other representation and backing are conclusions. -/
theorem ProgressiveList.partial_eq_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self other : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hmapGet : mapEqInst.ne self.updates other.updates = ok false →
      ∀ query, mapInst.get other.updates query = mapInst.get self.updates query)
    (hmapMax : mapEqInst.ne self.updates other.updates = ok false →
      mapInst.max_index other.updates = mapInst.max_index self.updates)
    (hequal : ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq
      ValueInst mapInst ValueInst mapInst mapEqInst self other = ok true) :
    other.Represents ValueInst mapInst contents ∧ other.BackingValid factor := by
  let updatesEqual := fun left right => mapEqInst.ne left right = ok false
  have heq := ProgressiveList.partial_eq_true_imp_structural ValueInst mapInst mapEqInst
    hsound updatesEqual (fun h => h) hequal
  exact ⟨heq.represents ValueInst mapInst hlayout contents hrep hbacking hmapGet hmapMax,
    heq.backing hbacking⟩

end milhouse.progressive_list
