use parking_lot::RwLock;

pub fn read_write_read(lock: &RwLock<u64>, value: u64) -> (u64, u64) {
    let before = *lock.read();
    *lock.write() = value;
    let after = *lock.read();
    (before, after)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_write_is_visible_to_the_next_read() {
        let lock = RwLock::new(7);
        assert_eq!(read_write_read(&lock, 9), (7, 9));
        assert_eq!(*lock.read(), 9);
        assert_eq!(read_write_read(&lock, 11), (9, 11));

        let same_initial_value = RwLock::new(7);
        assert_eq!(read_write_read(&same_initial_value, 11), (7, 11));
    }
}
