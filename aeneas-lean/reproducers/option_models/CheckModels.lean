import Tree.FunsExternal
import OptionSource.Funs

open Aeneas Aeneas.Std Result

/-! Compare local models with independently extracted pinned standard-library
bodies. Callback dictionaries are arbitrary, including failure/divergence.
The final theorem checks `cloned` composition, not its failed direct extraction. -/

theorem option_is_some_and_agrees {T F : Type}
    (inst : core.ops.function.FnOnce F T Bool) (value : Option T) (f : F) :
    OptionSource.core.option.Option.is_some_and inst value f =
      core.option.Option.is_some_and inst value f := by
  cases value with
  | none => rfl
  | some value =>
    simp only [OptionSource.core.option.Option.is_some_and, core.option.Option.is_some_and]

theorem option_is_none_or_agrees {T F : Type}
    (inst : core.ops.function.FnOnce F T Bool) (value : Option T) (f : F) :
    OptionSource.core.option.Option.is_none_or inst value f =
      core.option.Option.is_none_or inst value f := by
  cases value with
  | none => rfl
  | some value =>
    simp only [OptionSource.core.option.Option.is_none_or, core.option.Option.is_none_or]

theorem option_map_agrees {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (value : Option T) (f : F) :
    OptionSource.core.option.Option.map inst value f = core.option.Option.map inst value f := by
  cases value with
  | none => rfl
  | some value =>
    simp only [OptionSource.core.option.Option.map, core.option.Option.map]

theorem option_map_or_agrees {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (value : Option T) (fallback : U) (f : F) :
    OptionSource.core.option.Option.map_or inst value fallback f =
      core.option.Option.map_or inst value fallback f := by
  cases value with
  | none => rfl
  | some value =>
    simp only [OptionSource.core.option.Option.map_or, core.option.Option.map_or]

theorem option_unwrap_or_default_agrees {T : Type}
    (inst : core.default.Default T) (value : Option T) :
    OptionSource.core.option.Option.unwrap_or_default inst value =
      core.option.Option.unwrap_or_default inst value := by
  cases value <;> rfl

theorem option_ok_or_agrees {T E : Type} (value : Option T) (error : E) :
    OptionSource.core.option.Option.ok_or_source value error = core.option.Option.ok_or value error := by
  cases value <;> rfl

theorem option_or_agrees {T : Type} (value fallback : Option T) :
    OptionSource.core.option.Option.or value fallback = core.option.Option.or value fallback := by
  cases value <;> rfl

theorem option_unzip_agrees {T U : Type} (value : Option (T × U)) :
    OptionSource.core.option.OptionPair.unzip value = core.option.OptionPair.unzip value := by
  cases value with
  | none => rfl
  | some pair => cases pair; rfl

theorem option_copied_agrees {T : Type} (inst : core.marker.Copy T) (value : Option T) :
    OptionSource.core.option.OptionShared0T.copied inst value =
      core.option.OptionShared0T.copied inst value := by
  cases value <;> rfl

theorem option_branch_agrees {T : Type} (value : Option T) :
    OptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch value =
      core.option.Option.Insts.CoreOpsTry_traitTry.branch value := by
  cases value <;> rfl

theorem option_from_residual_agrees (T : Type) (value : Option core.convert.Infallible) :
    OptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T value =
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T value := by
  cases value with
  | none =>
    simp only [OptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      read_discriminant, optionInfallibleDiscriminant, core.intrinsics.assume,
      decide_true, ite_true, bind_tc_ok]
  | some impossible => cases impossible

/-- Rust spells `cloned` as `self.map(T::clone)`. Its function-item adapter
fails direct extraction. This theorem checks the composition using the fully
extracted `map` body and the actual generic clone callback, without any clone
termination or identity assumption. It is not a direct `cloned` body check. -/
theorem option_cloned_composition_agrees {T : Type} (inst : core.clone.Clone T) (value : Option T) :
    OptionSource.core.option.Option.map
      ({ call_once := fun (_ : Unit) item => inst.clone item } : core.ops.function.FnOnce Unit T T)
      value () = core.option.OptionShared0T.cloned inst value := by
  rw [option_map_agrees]
  cases value <;> rfl

#print axioms option_is_some_and_agrees
#print axioms option_is_none_or_agrees
#print axioms option_map_agrees
#print axioms option_map_or_agrees
#print axioms option_unwrap_or_default_agrees
#print axioms option_ok_or_agrees
#print axioms option_or_agrees
#print axioms option_unzip_agrees
#print axioms option_copied_agrees
#print axioms option_branch_agrees
#print axioms option_from_residual_agrees
#print axioms option_cloned_composition_agrees
