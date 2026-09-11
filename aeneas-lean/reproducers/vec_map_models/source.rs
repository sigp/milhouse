use vec_map::VecMap;

pub fn new<T>() -> VecMap<T> {
    VecMap::new()
}
pub fn len<T>(map: &VecMap<T>) -> usize {
    map.len()
}
pub fn is_empty<T>(map: &VecMap<T>) -> bool {
    map.is_empty()
}
pub fn get<T>(map: &VecMap<T>, key: usize) -> Option<&T> {
    map.get(key)
}
pub fn get_mut<T>(map: &mut VecMap<T>, key: usize) -> Option<&mut T> {
    map.get_mut(key)
}

// Kept for native checks and the separate, incomplete insertion extraction.
pub fn insert<T>(map: &mut VecMap<T>, key: usize, value: T) -> Option<T> {
    map.insert(key, value)
}

#[cfg(test)]
mod tests {
    use super::{get, get_mut, insert, is_empty, len, new};

    #[test]
    fn empty_observers_and_missing_mutation_cover_extreme_keys() {
        let mut map = new::<u64>();
        for key in [0, 1, 31, 255, usize::MAX] {
            assert_eq!(get(&map, key), None);
            assert_eq!(get_mut(&mut map, key), None);
            assert_eq!(len(&map), 0);
            assert!(is_empty(&map));
        }
    }

    #[test]
    fn sparse_lookup_counts_entries_instead_of_backing_slots() {
        let mut map = new();
        for (key, value) in [(0, 10), (7, 70), (255, 2550)] {
            assert_eq!(insert(&mut map, key, value), None);
        }
        for key in 0..300 {
            let expected = match key {
                0 => Some(&10),
                7 => Some(&70),
                255 => Some(&2550),
                _ => None,
            };
            assert_eq!(get(&map, key), expected);
        }
        assert_eq!(get(&map, usize::MAX), None);
        assert_eq!(len(&map), 3);
        assert!(!is_empty(&map));
    }

    #[test]
    fn mutable_lookup_preserves_other_values_and_occupancy() {
        let mut map = new();
        for (key, value) in [(0, 10), (7, 70), (255, 2550)] {
            insert(&mut map, key, value);
        }
        for key in [1, 6, 8, 254, 256, usize::MAX] {
            assert_eq!(get_mut(&mut map, key), None);
            assert_eq!(len(&map), 3);
        }
        *get_mut(&mut map, 7).unwrap() = 71;
        assert_eq!(get(&map, 0), Some(&10));
        assert_eq!(get(&map, 7), Some(&71));
        assert_eq!(get(&map, 255), Some(&2550));
        assert_eq!(len(&map), 3);
        assert!(!is_empty(&map));
    }

    #[test]
    fn lookups_do_not_require_cloning_and_keep_empty_reserved_maps_empty() {
        struct NonClone(u64);
        let mut map = vec_map::VecMap::with_capacity(64);
        assert!(is_empty(&map));
        assert_eq!(len(&map), 0);
        assert!(get_mut(&mut map, 12).is_none());
        insert(&mut map, 12, NonClone(12));
        get_mut(&mut map, 12).unwrap().0 = 13;
        assert_eq!(get(&map, 12).unwrap().0, 13);
        assert_eq!(len(&map), 1);
        map.remove(12);
        assert!(is_empty(&map));
        assert!(get_mut(&mut map, 12).is_none());
        assert!(map.capacity() >= 64);
    }
}
