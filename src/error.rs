/// An error type to communicate that an attempt to construct a circular index failed as a result of
/// the provided value not being strictly lesser than `N` in `CircularIndex<N>`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueError {
    /// The value of the `N` const-generic of the particular
    /// [`CircularIndex`](crate::circular_index::CircularIndex) type that was attempted to be
    /// constructed.
    pub(crate) n: usize,

    /// The erroneous value provided to the
    /// [`CircularIndex::new`](crate::circular_index::CircularIndex::new) constructor.
    pub(crate) value: usize,
}

impl std::fmt::Display for ValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "cannot create a circular index with N equal to {n} from a value of {value}",
            n = self.n,
            value = self.value,
        )
    }
}

impl std::error::Error for ValueError {}

#[cfg(test)]
mod tests {
    use super::ValueError;

    #[test]
    fn the_display_trait_implementation_works_as_intended() {
        let e = ValueError { n: 4, value: 6 };

        let s = e.to_string();

        assert_eq!(
            s,
            "cannot create a circular index with N equal to 4 from a value of 6"
        );
    }

    #[test]
    fn is_send() {
        fn assert_is_send<T: Send>() {}

        assert_is_send::<ValueError>();
    }

    #[test]
    fn is_sync() {
        fn assert_is_sync<T: Sync>() {}

        assert_is_sync::<ValueError>();
    }
}
