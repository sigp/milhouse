import ControlsOnly.Funs

open Aeneas Aeneas.Std Result milhouse_cow_regions_probe

theorem read_plain_value {T : Type} (value : T) :
    read_plain value = ok value := by rfl

theorem read_nested_value {T : Type} (value : T) :
    read_nested value = ok value := by rfl

theorem read_shared_field_value {T : Type} (handle : SharedField T) :
    read_shared_field handle = ok handle.value := by rfl

theorem read_unique_field_value {T : Type} (handle : UniqueField T) :
    read_unique_field handle = ok handle.value := by rfl

#print axioms read_plain_value
#print axioms read_nested_value
#print axioms read_shared_field_value
#print axioms read_unique_field_value
