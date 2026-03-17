use cirkulaer::{CircularIndex, ValueError};
use core::error::Error;
use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::mem::size_of;

#[cfg(test)]
mod duplication {
    use super::*;

    #[test]
    const fn implements_the_clone_trait() {
        const fn assert_implements_clone<T: Clone>() {}

        assert_implements_clone::<ValueError>();
    }

    #[test]
    const fn implements_the_copy_trait() {
        const fn assert_implements_copy<T: Copy>() {}

        assert_implements_copy::<ValueError>();
    }
}

#[cfg(test)]
mod comparison {
    use super::*;

    #[test]
    const fn implements_the_partial_eq_trait() {
        const fn assert_implements_partial_eq<T: PartialEq>() {}

        assert_implements_partial_eq::<ValueError>();
    }

    #[test]
    const fn implements_the_eq_trait() {
        const fn assert_implements_eq<T: Eq>() {}

        assert_implements_eq::<ValueError>();
    }
}

#[cfg(test)]
mod hashing {
    use super::*;

    #[test]
    const fn implements_the_hash_trait() {
        const fn assert_implements_hash<T: Hash>() {}

        assert_implements_hash::<ValueError>();
    }
}

#[cfg(test)]
mod interoperability {
    use super::*;

    #[test]
    const fn implements_the_error_trait() {
        const fn assert_implements_error<T: Error>() {}

        assert_implements_error::<ValueError>();
    }
}

#[cfg(test)]
mod multithreading {
    use super::*;

    #[test]
    const fn implements_the_send_trait() {
        const fn assert_implements_send<T: Send>() {}

        assert_implements_send::<ValueError>();
    }

    #[test]
    const fn implements_the_sync_trait() {
        const fn assert_implements_sync<T: Sync>() {}

        assert_implements_sync::<ValueError>();
    }
}

#[cfg(test)]
mod string_representation {
    use super::*;

    #[test]
    const fn implements_the_debug_trait() {
        const fn assert_implements_debug<T: Debug>() {}

        assert_implements_debug::<ValueError>();
    }

    #[test]
    const fn implements_the_display_trait() {
        const fn assert_implements_display<T: Display>() {}

        assert_implements_display::<ValueError>();
    }

    #[test]
    fn the_debug_string_is_developer_friendly() {
        let error = CircularIndex::<6>::new(7).expect_err("7 should be rejected");
        let expected = "ValueError { N: 6, value: 7 }";

        let actual = format!("{:?}", error);

        assert_eq!(actual, expected);
    }

    #[test]
    fn the_pretty_debug_string_is_developer_friendly() {
        let error = CircularIndex::<3>::new(5).expect_err("5 should be rejected");
        let expected = "ValueError {\n    N: 3,\n    value: 5\n}";

        let actual = format!("{:#?}", error);

        assert_eq!(actual, expected);
    }

    #[test]
    fn the_display_string_is_user_friendly() {
        let error = CircularIndex::<13>::new(15).expect_err("15 should be rejected");
        let expected = "a `CircularIndex<13>` cannot be created from a value of 15";

        let actual = format!("{}", error);

        assert_eq!(actual, expected);
    }
}

#[cfg(test)]
mod size {
    use super::*;

    #[test]
    fn is_twice_the_size_of_usize() {
        let size_of_usize = size_of::<usize>();

        let size = size_of::<ValueError>();

        assert_eq!(size, 2 * size_of_usize);
    }
}
