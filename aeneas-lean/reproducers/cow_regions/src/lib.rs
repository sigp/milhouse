//! Isolate lifetime grouping from the map/entry and trait boundaries of CoW reads.

pub struct SharedField<'a, T> {
    pub value: &'a T,
}

pub struct UniqueField<'a, T> {
    pub value: &'a mut T,
}

pub fn read_plain<T>(value: &T) -> &T {
    value
}

pub fn read_nested<'s, 'a, T>(value: &'s &'a T) -> &'s T {
    value
}

pub fn read_shared_field<'s, 'a, T>(handle: &'s SharedField<'a, T>) -> &'s T {
    handle.value
}

pub fn read_unique_field<'s, 'a, T>(handle: &'s UniqueField<'a, T>) -> &'s T {
    handle.value
}

pub enum OneRegion<'a, T> {
    Shared(&'a T),
    Unique(&'a mut T),
}

pub enum SplitRegions<'value, 'entry, T> {
    Shared(&'value T),
    Unique(&'entry mut T),
}

pub enum OneRegionEntry<'a, T> {
    Immutable {
        value: &'a T,
        entry: Option<&'a mut T>,
    },
    Mutable {
        value: &'a mut T,
    },
}

pub enum SplitRegionsEntry<'value, 'entry, T> {
    Immutable {
        value: &'value T,
        entry: Option<&'entry mut T>,
    },
    Mutable {
        value: &'entry mut T,
    },
}

pub fn read_one<'s, 'a, T>(handle: &'s OneRegion<'a, T>) -> &'s T {
    match handle {
        OneRegion::Shared(value) => value,
        OneRegion::Unique(value) => value,
    }
}

pub fn read_split<'s, 'value, 'entry, T>(handle: &'s SplitRegions<'value, 'entry, T>) -> &'s T {
    match handle {
        SplitRegions::Shared(value) => value,
        SplitRegions::Unique(value) => value,
    }
}

pub fn read_one_entry<'s, 'a, T>(handle: &'s OneRegionEntry<'a, T>) -> &'s T {
    match handle {
        OneRegionEntry::Immutable { value, .. } => value,
        OneRegionEntry::Mutable { value } => value,
    }
}

pub fn read_one_via_helper<'s, 'a, T>(handle: &'s OneRegion<'a, T>) -> &'s T {
    match handle {
        OneRegion::Shared(value) => read_nested(value),
        OneRegion::Unique(value) => value,
    }
}

pub fn read_one_by_copy<'s, 'a, T>(handle: &'s OneRegion<'a, T>) -> &'s T {
    match *handle {
        OneRegion::Shared(value) => value,
        OneRegion::Unique(ref value) => value,
    }
}

pub fn read_one_entry_by_copy<'s, 'a, T>(handle: &'s OneRegionEntry<'a, T>) -> &'s T {
    match *handle {
        OneRegionEntry::Immutable { value, .. } => value,
        OneRegionEntry::Mutable { ref value } => value,
    }
}

pub fn read_one_entry_via_helper<'s, 'a, T>(handle: &'s OneRegionEntry<'a, T>) -> &'s T {
    match handle {
        OneRegionEntry::Immutable { value, .. } => read_nested(value),
        OneRegionEntry::Mutable { value } => value,
    }
}

pub fn read_split_entry<'s, 'value, 'entry, T>(
    handle: &'s SplitRegionsEntry<'value, 'entry, T>,
) -> &'s T {
    match handle {
        SplitRegionsEntry::Immutable { value, .. } => value,
        SplitRegionsEntry::Mutable { value } => value,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_reference_layouts_read_the_selected_value() {
        let backing = 7;
        let mut pending = 9;
        assert_eq!(*read_plain(&backing), 7);
        assert_eq!(*read_nested(&&backing), 7);
        assert_eq!(*read_shared_field(&SharedField { value: &backing }), 7);
        assert_eq!(
            *read_unique_field(&UniqueField {
                value: &mut pending,
            }),
            9
        );
        assert_eq!(*read_one(&OneRegion::Shared(&backing)), 7);
        assert_eq!(*read_one(&OneRegion::Unique(&mut pending)), 9);
        assert_eq!(*read_one_via_helper(&OneRegion::Shared(&backing)), 7);
        assert_eq!(*read_one_via_helper(&OneRegion::Unique(&mut pending)), 9);
        assert_eq!(*read_one_by_copy(&OneRegion::Shared(&backing)), 7);
        assert_eq!(*read_one_by_copy(&OneRegion::Unique(&mut pending)), 9);
        assert_eq!(*read_split(&SplitRegions::Shared(&backing)), 7);
        assert_eq!(*read_split(&SplitRegions::Unique(&mut pending)), 9);
        assert_eq!(
            *read_one_entry(&OneRegionEntry::Immutable {
                value: &backing,
                entry: Some(&mut pending),
            }),
            7
        );
        assert_eq!(
            *read_one_entry(&OneRegionEntry::Mutable {
                value: &mut pending,
            }),
            9
        );
        assert_eq!(
            *read_one_entry_via_helper(&OneRegionEntry::Immutable {
                value: &backing,
                entry: Some(&mut pending),
            }),
            7
        );
        assert_eq!(
            *read_one_entry_via_helper(&OneRegionEntry::Mutable {
                value: &mut pending,
            }),
            9
        );
        assert_eq!(
            *read_one_entry_by_copy(&OneRegionEntry::Immutable {
                value: &backing,
                entry: Some(&mut pending),
            }),
            7
        );
        assert_eq!(
            *read_one_entry_by_copy(&OneRegionEntry::Mutable {
                value: &mut pending,
            }),
            9
        );
        assert_eq!(
            *read_split_entry(&SplitRegionsEntry::Immutable {
                value: &backing,
                entry: Some(&mut pending),
            }),
            7
        );
        assert_eq!(
            *read_split_entry(&SplitRegionsEntry::Mutable {
                value: &mut pending,
            }),
            9
        );
        assert_eq!(backing, 7);
        assert_eq!(pending, 9);
    }
}
