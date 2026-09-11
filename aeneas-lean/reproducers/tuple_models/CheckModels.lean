import Tree.FunsExternal
import TupleSource.Funs

open Aeneas Aeneas.Std Result

/-! Compare the complete extracted tuple bodies for arbitrary callback
dictionaries. No consistency, success, or termination law is imposed on
element comparisons, and callbacks after a short circuit remain arbitrary. -/

theorem tuple_eq_agrees {T U : Type}
    (first : core.cmp.PartialEq T T) (second : core.cmp.PartialEq U U)
    (left right : T × U) :
    TupleSource.Pair.Insts.CoreCmpPartialEqPair.eq first second left right =
      Pair.Insts.CoreCmpPartialEqPair.eq first second left right := by
  cases left; cases right; rfl

theorem tuple_ne_agrees {T U : Type}
    (first : core.cmp.PartialEq T T) (second : core.cmp.PartialEq U U)
    (left right : T × U) :
    TupleSource.Pair.Insts.CoreCmpPartialEqPair.ne first second left right =
      Pair.Insts.CoreCmpPartialEqPair.ne first second left right := by
  cases left; cases right; rfl

theorem tuple_partial_cmp_agrees {T U : Type}
    (first : core.cmp.PartialOrd T T) (second : core.cmp.PartialOrd U U)
    (left right : T × U) :
    TupleSource.Pair.Insts.CoreCmpPartialOrdPair.partial_cmp first second left right =
      Pair.Insts.CoreCmpPartialOrdPair.partial_cmp first second left right := by
  cases left with
  | mk a b =>
    cases right with
    | mk c d =>
      change (first.partial_cmp a c >>= _) = (first.partial_cmp a c >>= _)
      cases first.partial_cmp a c with
      | fail error => rfl
      | div => rfl
      | ok answer =>
        cases answer with
        | none => rfl
        | some order => cases order <;> rfl

theorem tuple_cmp_agrees {T U : Type}
    (first : core.cmp.Ord T) (second : core.cmp.Ord U)
    (left right : T × U) :
    TupleSource.Pair.Insts.CoreCmpOrd.cmp first second left right =
      Pair.Insts.CoreCmpOrd.cmp first second left right := by
  cases left with
  | mk a b =>
    cases right with
    | mk c d =>
      change (first.cmp a c >>= _) = (first.cmp a c >>= _)
      cases first.cmp a c with
      | fail error => rfl
      | div => rfl
      | ok order => cases order <;> rfl

#print axioms tuple_eq_agrees
#print axioms tuple_ne_agrees
#print axioms tuple_partial_cmp_agrees
#print axioms tuple_cmp_agrees
