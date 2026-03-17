use cirkulaer::{CircularIndex, ValueError};
use core::fmt::Debug;
use core::hash::{Hash, Hasher};
use core::mem::size_of;
use std::hash::DefaultHasher;

type Res = Result<(), ValueError>;

#[cfg(test)]
mod associated_constants {
    use super::*;

    #[test]
    fn the_associated_constant_n_equals_the_const_generic_n() {
        assert_eq!(CircularIndex::<11>::N, 11);
    }
}

#[cfg(test)]
mod creation {
    use super::*;

    #[test]
    fn new_accepts_values_strictly_lesser_than_n_minus_one() {
        let res = CircularIndex::<3>::new(1);

        assert!(res.is_ok());
    }

    #[test]
    fn new_accepts_values_equal_to_n_minus_one() {
        let res = CircularIndex::<7>::new(6);

        assert!(res.is_ok());
    }

    #[test]
    fn new_rejects_values_equal_to_n() {
        let res = CircularIndex::<12>::new(12);

        assert!(res.is_err());
    }

    #[test]
    fn new_rejects_values_strictly_greater_than_n() {
        let res = CircularIndex::<17>::new(39);

        assert!(res.is_err());
    }

    #[test]
    fn new_unchecked_accepts_values_strictly_lesser_than_n_minus_one() {
        let i = CircularIndex::<7>::new_unchecked(2);

        assert_eq!(i.get(), 2);
    }

    #[test]
    fn new_unchecked_accepts_values_equal_to_n_minus_one() {
        let i = CircularIndex::<14>::new_unchecked(13);

        assert_eq!(i.get(), 13);
    }

    #[cfg(debug_assertions)]
    #[should_panic(
        expected = "a `CircularIndex<N>` must only be created from a value strictly lesser than `N`"
    )]
    #[test]
    fn new_unchecked_panics_if_given_values_equal_to_n_and_if_debug_assertions_are_enabled() {
        let _ = CircularIndex::<3>::new_unchecked(3);
    }

    #[cfg(debug_assertions)]
    #[should_panic(
        expected = "a `CircularIndex<N>` must only be created from a value strictly lesser than `N`"
    )]
    #[test]
    fn new_unchecked_panics_if_given_values_strictly_greater_than_n_and_if_debug_assertions_are_enabled()
     {
        let _ = CircularIndex::<9>::new_unchecked(15);
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn new_unchecked_does_not_panic_if_debug_assertions_are_disabled() {
        let _ = CircularIndex::<15>::new_unchecked(18);
    }

    #[test]
    fn zero_initializes_the_contained_index_to_zero() {
        let i = CircularIndex::<4>::zero();

        assert_eq!(i.get(), 0);
    }

    #[test]
    fn calling_default_is_identical_to_calling_zero() {
        let i = CircularIndex::<7>::zero();

        let j = CircularIndex::<7>::default();

        assert_eq!(i, j);
    }

    #[test]
    fn is_try_from_constructible_from_usizes_strictly_lesser_than_n_minus_one() -> Res {
        let i = CircularIndex::<16>::try_from(6)?;

        assert_eq!(i.get(), 6);

        Ok(())
    }

    #[test]
    fn is_try_from_constructible_from_usizes_equal_to_n_minus_one() -> Res {
        let i = CircularIndex::<10>::try_from(9)?;

        assert_eq!(i.get(), 9);

        Ok(())
    }

    #[test]
    fn is_not_try_from_constructible_from_usizes_equal_to_n() {
        let i = CircularIndex::<2>::try_from(2);

        assert!(i.is_err());
    }

    #[test]
    fn is_not_try_from_constructible_from_usizes_strictly_greater_than_n() {
        let i = CircularIndex::<18>::try_from(27);

        assert!(i.is_err());
    }

    #[test]
    fn is_try_into_constructible_from_usizes_strictly_lesser_than_n_minus_one() -> Res {
        let i: CircularIndex<6> = 3.try_into()?;

        assert_eq!(i.get(), 3);

        Ok(())
    }

    #[test]
    fn is_try_into_constructible_from_usizes_equal_to_n_minus_one() -> Res {
        let i: CircularIndex<13> = 12.try_into()?;

        assert_eq!(i.get(), 12);

        Ok(())
    }

    #[test]
    fn is_not_try_into_constructible_from_usizes_equal_to_n() {
        let i: Result<CircularIndex<7>, ValueError> = 7.try_into();

        assert!(i.is_err());
    }

    #[test]
    fn is_not_try_into_constructible_from_usizes_strictly_greater_than_n() {
        let i: Result<CircularIndex<13>, ValueError> = 16.try_into();

        assert!(i.is_err());
    }
}

#[cfg(test)]
mod getter {
    use super::*;

    #[test]
    fn get_returns_the_contained_index() -> Res {
        let i = CircularIndex::<8>::new(5)?;

        let gotten = i.get();

        assert_eq!(gotten, 5);

        Ok(())
    }

    #[test]
    fn get_reflects_the_current_value_of_the_contained_index() -> Res {
        let mut i = CircularIndex::<4>::new(1)?;
        i += 1;

        let gotten = i.get();

        assert_eq!(gotten, 2);

        Ok(())
    }
}

#[cfg(test)]
mod duplication {
    use super::*;

    #[test]
    const fn implements_the_copy_trait() {
        const fn assert_implements_copy<T: Copy>() {}

        assert_implements_copy::<CircularIndex<7>>();
    }

    #[test]
    const fn implements_the_clone_trait() {
        const fn assert_implements_clone<T: Clone>() {}

        assert_implements_clone::<CircularIndex<4>>();
    }

    #[test]
    fn copies_compare_equal_to_their_source() -> Res {
        let source = CircularIndex::<11>::new(3)?;

        let copy = source;

        assert_eq!(copy, source);

        Ok(())
    }

    #[test]
    fn clones_compare_equal_to_their_source() -> Res {
        let source = CircularIndex::<6>::new(5)?;

        let clone = source.clone();

        assert_eq!(clone, source);

        Ok(())
    }

    #[test]
    fn modifying_copies_does_not_modify_their_source() -> Res {
        let source = CircularIndex::<4>::new(3)?;

        let mut copy = source;
        copy -= 1;

        assert_ne!(copy, source);

        Ok(())
    }

    #[test]
    fn modifying_clones_does_not_modify_their_source() -> Res {
        let source = CircularIndex::<13>::new(2)?;

        let mut clone = source.clone();
        clone += 1;

        assert_ne!(clone, source);

        Ok(())
    }
}

#[cfg(test)]
mod comparison {
    use super::*;

    #[test]
    const fn implements_the_partial_eq_trait() {
        const fn assert_implements_partial_eq<T: PartialEq>() {}

        assert_implements_partial_eq::<CircularIndex<3>>();
    }

    #[test]
    const fn implements_the_eq_trait() {
        const fn assert_implements_eq<T: Eq>() {}

        assert_implements_eq::<CircularIndex<7>>();
    }

    #[test]
    const fn implements_the_partial_ord_trait() {
        const fn assert_implements_partial_ord<T: PartialOrd>() {}

        assert_implements_partial_ord::<CircularIndex<12>>();
    }

    #[test]
    const fn implements_the_ord_trait() {
        const fn assert_implements_ord<T: Ord>() {}

        assert_implements_ord::<CircularIndex<7>>();
    }

    #[test]
    fn indexes_with_the_same_contained_index_compare_equal() -> Res {
        let i = CircularIndex::<9>::new(7)?;
        let j = CircularIndex::<9>::new(7)?;

        assert_eq!(i, j);

        Ok(())
    }

    #[test]
    fn indexes_with_different_contained_indexes_do_not_compare_equal() -> Res {
        let i = CircularIndex::<12>::new(3)?;
        let j = CircularIndex::<12>::new(4)?;

        assert_ne!(i, j);

        Ok(())
    }

    #[test]
    fn the_lesser_than_operator_operates_on_the_contained_indexes() -> Res {
        let smaller = CircularIndex::<6>::new(2)?;
        let greater = CircularIndex::<6>::new(3)?;

        assert!(!(smaller < smaller));
        assert!(smaller < greater);
        assert!(!(greater < smaller));

        Ok(())
    }

    #[test]
    fn the_lesser_than_or_equal_to_operator_operates_on_the_contained_indexes() -> Res {
        let smaller = CircularIndex::<8>::new(1)?;
        let greater = CircularIndex::<8>::new(4)?;

        assert!(smaller <= smaller);
        assert!(smaller <= greater);
        assert!(!(greater <= smaller));

        Ok(())
    }

    #[test]
    fn the_greater_than_or_equal_to_operator_operates_on_the_contained_indexes() -> Res {
        let smaller = CircularIndex::<3>::new(0)?;
        let greater = CircularIndex::<3>::new(2)?;

        assert!(smaller >= smaller);
        assert!(!(smaller >= greater));
        assert!(greater >= smaller);

        Ok(())
    }

    #[test]
    fn the_greater_than_operator_operates_on_the_contained_indexes() -> Res {
        let smaller = CircularIndex::<11>::new(8)?;
        let greater = CircularIndex::<11>::new(9)?;

        assert!(!(smaller > smaller));
        assert!(!(smaller > greater));
        assert!(greater > smaller);

        Ok(())
    }
}

#[cfg(test)]
mod hashing {
    use super::*;

    #[test]
    const fn implements_the_hash_trait() {
        const fn assert_implements_hash<T: Hash>() {}

        assert_implements_hash::<CircularIndex<15>>();
    }

    #[test]
    fn hashes_equal_those_of_the_contained_indexes() -> Res {
        fn hash_of<T: Hash>(value: &T) -> u64 {
            let mut hasher = DefaultHasher::new();
            value.hash(&mut hasher);
            hasher.finish()
        }

        let i = CircularIndex::<10>::new(6)?;

        let hash = hash_of(&i);
        let hash_of_contained_index = hash_of(&i.get());

        assert_eq!(hash, hash_of_contained_index);

        Ok(())
    }
}

#[cfg(test)]
mod addition {
    use super::*;

    #[test]
    fn addition_with_a_multiple_of_n_leaves_the_index_unchanged() {
        {
            let i = CircularIndex::<4>::default();

            let j = i + (0 * 4);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<11>::default();

            let j = i + (1 * 11);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<6>::default();

            let j = i + (2 * 6);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<19>::default();

            let j = i + (15 * 19);

            assert_eq!(i, j);
        }
    }

    #[test]
    fn addition_assignment_is_circular() -> Res {
        {
            let mut i = CircularIndex::<4>::new(1)?;

            i += 2;

            assert_eq!(i.get(), 3);
        }
        {
            let mut i = CircularIndex::<18>::new(6)?;

            i += 14;

            assert_eq!(i.get(), 2);
        }
        {
            let mut i = CircularIndex::<18>::new(8)?;

            i += 22;

            assert_eq!(i.get(), 12);
        }
        {
            let mut i = CircularIndex::<10>::new(5)?;

            i += 45;

            assert_eq!(i.get(), 0);
        }

        Ok(())
    }

    #[test]
    fn addition_assignment_behaves_like_the_documented_formula() -> Res {
        {
            let mut i = CircularIndex::<7>::new(2)?;

            i += 4;

            assert_eq!(i.get(), (2 + 4) % 7);
        }
        {
            let mut i = CircularIndex::<13>::new(8)?;

            i += 9;

            assert_eq!(i.get(), (8 + 9) % 13);
        }
        {
            let mut i = CircularIndex::<8>::new(5)?;

            i += 22;

            assert_eq!(i.get(), (5 + 22) % 8);
        }

        Ok(())
    }

    #[test]
    fn addition_assignment_does_not_overflow() -> Res {
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(4)?;

            i += usize::MAX;

            assert_eq!(i.get(), 4);
        }
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(32768)?;

            i += usize::MAX - 1;

            assert_eq!(i.get(), 32767);
        }
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(usize::MAX / 2)?;

            i += usize::MAX;

            assert_eq!(i.get(), usize::MAX / 2);
        }

        Ok(())
    }

    #[test]
    fn addition_behaves_the_same_regardless_of_the_type_of_the_rhs() -> Res {
        {
            let lhs = CircularIndex::<8>::new(5)?;
            let rhs = 22;

            let sum1 = lhs + rhs;
            let sum2 = lhs + &rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<12>::new(9)?;
            let rhs = 7;

            let sum1 = lhs + rhs;
            let sum2 = &lhs + rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<3>::new(2)?;
            let rhs = 9;

            let sum1 = lhs + rhs;
            let sum2 = &lhs + &rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<15>::new(8)?;
            let rhs = CircularIndex::<15>::new(5)?;

            let sum1 = lhs + rhs.get();
            let sum2 = lhs + rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<6>::new(4)?;
            let rhs = CircularIndex::<6>::new(5)?;

            let sum1 = lhs + rhs.get();
            let sum2 = lhs + &rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<18>::new(17)?;
            let rhs = CircularIndex::<18>::new(3)?;

            let sum1 = lhs + rhs.get();
            let sum2 = &lhs + rhs;

            assert_eq!(sum1, sum2);
        }
        {
            let lhs = CircularIndex::<10>::new(6)?;
            let rhs = CircularIndex::<10>::new(1)?;

            let sum1 = lhs + rhs.get();
            let sum2 = &lhs + &rhs;

            assert_eq!(sum1, sum2);
        }

        Ok(())
    }

    #[test]
    fn addition_assignment_behaves_the_same_regardless_of_the_type_of_the_rhs() -> Res {
        {
            let mut i = CircularIndex::<16>::new(1)?;
            let mut j = i;
            let rhs = 7;

            i += rhs;
            j += &rhs;

            assert_eq!(i, j);
        }
        {
            let mut i = CircularIndex::<9>::new(3)?;
            let mut j = i;
            let rhs = CircularIndex::<9>::new(8)?;

            i += rhs.get();
            j += rhs;

            assert_eq!(i, j);
        }
        {
            let mut i = CircularIndex::<13>::new(11)?;
            let mut j = i;
            let rhs = CircularIndex::<13>::new(6)?;

            i += rhs.get();
            j += &rhs;

            assert_eq!(i, j);
        }

        Ok(())
    }

    #[test]
    fn addition_and_addition_assignment_behave_the_same() -> Res {
        let i = CircularIndex::<14>::new(13)?;
        let mut j = i;
        let rhs = 19;

        let k = i + rhs;
        j += rhs;

        assert_eq!(j, k);

        Ok(())
    }
}

#[cfg(test)]
mod subtraction {
    use super::*;

    #[test]
    fn subtraction_with_a_multiple_of_n_leaves_the_index_unchanged() {
        {
            let i = CircularIndex::<7>::default();

            let j = i - (0 * 7);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<5>::default();

            let j = i - (1 * 5);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<12>::default();

            let j = i - (2 * 12);

            assert_eq!(i, j);
        }
        {
            let i = CircularIndex::<14>::default();

            let j = i - (11 * 14);

            assert_eq!(i, j);
        }
    }

    #[test]
    fn subtraction_assignment_is_circular() -> Res {
        {
            let mut i = CircularIndex::<5>::new(3)?;

            i -= 2;

            assert_eq!(i.get(), 1);
        }
        {
            let mut i = CircularIndex::<17>::new(10)?;

            i -= 13;

            assert_eq!(i.get(), 14);
        }
        {
            let mut i = CircularIndex::<8>::new(5)?;

            i -= 15;

            assert_eq!(i.get(), 6);
        }
        {
            let mut i = CircularIndex::<14>::new(1)?;

            i -= 43;

            assert_eq!(i.get(), 0);
        }

        Ok(())
    }

    #[test]
    fn subtraction_assignment_behaves_like_the_documented_formula() -> Res {
        {
            let mut i = CircularIndex::<9>::new(7)?;

            i -= 5;

            assert_eq!(i.get(), (7 + 9 - (5 % 9)) % 9);
        }
        {
            let mut i = CircularIndex::<16>::new(4)?;

            i -= 11;

            assert_eq!(i.get(), (4 + 16 - (11 % 16)) % 16);
        }
        {
            let mut i = CircularIndex::<6>::new(1)?;

            i -= 19;

            assert_eq!(i.get(), (1 + 6 - (19 % 6)) % 6);
        }

        Ok(())
    }

    #[test]
    fn subtraction_assignment_does_not_overflow() -> Res {
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(10)?;

            i -= usize::MAX;

            assert_eq!(i.get(), 10);
        }
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(8192)?;

            i -= usize::MAX - 1;

            assert_eq!(i.get(), 8193);
        }
        {
            let mut i = CircularIndex::<{ usize::MAX }>::new(usize::MAX / 2)?;

            i -= usize::MAX;

            assert_eq!(i.get(), usize::MAX / 2);
        }

        Ok(())
    }

    #[test]
    fn subtraction_behaves_the_same_regardless_of_the_type_of_the_rhs() -> Res {
        {
            let lhs = CircularIndex::<11>::new(3)?;
            let rhs = 14;

            let diff1 = lhs - rhs;
            let diff2 = lhs - &rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<6>::new(4)?;
            let rhs = 9;

            let diff1 = lhs - rhs;
            let diff2 = &lhs - rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<2>::new(0)?;
            let rhs = 5;

            let diff1 = lhs - rhs;
            let diff2 = &lhs - &rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<8>::new(2)?;
            let rhs = CircularIndex::<8>::new(6)?;

            let diff1 = lhs - rhs.get();
            let diff2 = lhs - rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<18>::new(16)?;
            let rhs = CircularIndex::<18>::new(7)?;

            let diff1 = lhs - rhs.get();
            let diff2 = lhs - &rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<6>::new(1)?;
            let rhs = CircularIndex::<6>::new(5)?;

            let diff1 = lhs - rhs.get();
            let diff2 = &lhs - rhs;

            assert_eq!(diff1, diff2);
        }
        {
            let lhs = CircularIndex::<13>::new(5)?;
            let rhs = CircularIndex::<13>::new(8)?;

            let diff1 = lhs - rhs.get();
            let diff2 = &lhs - &rhs;

            assert_eq!(diff1, diff2);
        }

        Ok(())
    }

    #[test]
    fn subtraction_assignment_behaves_the_same_regardless_of_the_type_of_the_rhs() -> Res {
        {
            let mut i = CircularIndex::<10>::new(6)?;
            let mut j = i;
            let rhs = 5;

            i -= rhs;
            j -= &rhs;

            assert_eq!(i, j);
        }
        {
            let mut i = CircularIndex::<15>::new(11)?;
            let mut j = i;
            let rhs = CircularIndex::<15>::new(14)?;

            i -= rhs.get();
            j -= rhs;

            assert_eq!(i, j);
        }
        {
            let mut i = CircularIndex::<7>::new(1)?;
            let mut j = i;
            let rhs = CircularIndex::<7>::new(4)?;

            i -= rhs.get();
            j -= &rhs;

            assert_eq!(i, j);
        }

        Ok(())
    }

    #[test]
    fn subtraction_and_subtraction_assignment_behave_the_same() -> Res {
        let i = CircularIndex::<19>::new(12)?;
        let mut j = i;
        let rhs = 13;

        let k = i - rhs;
        j -= rhs;

        assert_eq!(j, k);

        Ok(())
    }
}

#[cfg(test)]
mod indexing {
    use super::*;

    #[test]
    fn is_zero_based() -> Res {
        let mut i = CircularIndex::<5>::new(4)?;

        i += 1;

        assert_eq!(i.get(), 0);

        Ok(())
    }

    #[test]
    fn can_index_into_arrays() -> Res {
        let array = [6, 8, 1, 3];
        let i = CircularIndex::<4>::new(2)?;

        let element = array[i];

        assert_eq!(element, 1);

        Ok(())
    }

    #[test]
    fn can_mutably_index_into_arrays() -> Res {
        let mut array = [5, 2, 11, 4, 9, 15];
        let i = CircularIndex::<6>::new(4)?;

        array[i] += 1;

        assert_eq!(array[i], 10);

        Ok(())
    }
}

#[cfg(test)]
mod multithreading {
    use super::*;

    #[test]
    const fn implements_the_send_trait() {
        const fn assert_implements_send<T: Send>() {}

        assert_implements_send::<CircularIndex<19>>();
    }

    #[test]
    const fn implements_the_sync_trait() {
        const fn assert_implements_sync<T: Sync>() {}

        assert_implements_sync::<CircularIndex<5>>();
    }
}

#[cfg(test)]
mod string_representation {
    use super::*;

    #[test]
    const fn implements_the_debug_trait() {
        const fn assert_implements_debug<T: Debug>() {}

        assert_implements_debug::<CircularIndex<7>>();
    }

    #[test]
    fn the_debug_string_is_developer_friendly() -> Res {
        let i = CircularIndex::<14>::new(6)?;
        let expected = "CircularIndex<14> { 6 }";

        let actual = format!("{:?}", i);

        assert_eq!(actual, expected);

        Ok(())
    }

    #[test]
    fn the_pretty_debug_string_is_developer_friendly() -> Res {
        let i = CircularIndex::<9>::new(2)?;
        let expected = "CircularIndex<9> {\n    2,\n}";

        let actual = format!("{:#?}", i);

        assert_eq!(actual, expected);

        Ok(())
    }
}

#[cfg(test)]
mod size {
    use super::*;

    #[test]
    fn is_of_the_same_size_as_usize() {
        let size_of_usize = size_of::<usize>();

        let size = size_of::<CircularIndex<4>>();

        assert_eq!(size, size_of_usize);
    }

    #[test]
    fn n_does_not_affect_the_size() {
        let size1 = size_of::<CircularIndex<1>>();
        let size2 = size_of::<CircularIndex<{ usize::MAX }>>();

        assert_eq!(size1, size2);
    }
}
