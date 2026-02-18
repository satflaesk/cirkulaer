use cirkulaer::{CircularIndex, ValueError, is_strictly_positive};

#[test]
fn zero_is_not_strictly_positive() {
    assert!(!is_strictly_positive(0));
}

#[test]
fn nonzero_numbers_are_strictly_positive() {
    assert!(is_strictly_positive(1));
    assert!(is_strictly_positive(1024));
    assert!(is_strictly_positive(usize::MAX));
}

#[test]
fn clones_compare_equal_to_their_source() {
    let i = CircularIndex::<7>::with_value(6).unwrap();

    let j = i.clone();

    assert_eq!(i, j);
}

#[test]
fn copies_compare_equal_to_their_source() {
    let i = CircularIndex::<8>::with_value(4).unwrap();

    let j = i;

    assert_eq!(i, j);
}

#[test]
fn defaults_to_zero() {
    let i = CircularIndex::<6>::default();

    assert_eq!(i.get(), 0);
}

#[test]
fn is_equatable() {
    let i = CircularIndex::<9>::with_value(2).unwrap();
    let j = CircularIndex::<9>::with_value(2).unwrap();
    let k = CircularIndex::<9>::with_value(3).unwrap();

    assert_eq!(i, i);
    assert_eq!(i, j);
    assert_ne!(i, k);
}

#[test]
fn is_orderable() {
    let i = CircularIndex::<5>::with_value(1).unwrap();
    let j = CircularIndex::<5>::with_value(4).unwrap();

    assert!(i <= i);
    assert!(i <= j);
    assert!(i < j);
    assert!(j > i);
    assert!(j >= i);
    assert!(j >= j);
}

#[test]
fn the_associated_constant_equals_n() {
    assert_eq!(CircularIndex::<2>::N, 2);
}

#[test]
fn is_zero_upon_calling_new_constructor() {
    let i = CircularIndex::<7>::new();

    assert_eq!(i.get(), 0);
}

#[test]
fn new_and_default_behave_the_same() {
    let i = CircularIndex::<2>::new();
    let j = CircularIndex::<2>::default();

    assert_eq!(i, j);
}

#[test]
fn with_value_returns_ok_given_a_value_strictly_less_than_n() {
    {
        let res = CircularIndex::<8>::with_value(0);

        assert!(res.is_ok());
    }

    {
        let res = CircularIndex::<4>::with_value(3);

        assert!(res.is_ok());
    }
}

#[test]
fn with_value_returns_err_given_a_value_greater_than_or_equal_to_n() {
    {
        let res = CircularIndex::<5>::with_value(6);

        assert!(res.is_err());
    }

    {
        let res = CircularIndex::<7>::with_value(7);

        assert!(res.is_err());
    }
}

#[test]
fn with_value_unchecked_behaves_as_expected() {
    let i = CircularIndex::<6>::with_value_unchecked(3);

    assert_eq!(i.get(), 3);
}

#[test]
fn get() {
    let i = CircularIndex::<4>::with_value(2).unwrap();

    assert_eq!(i.get(), 2);
}

#[test]
fn is_zero_upon_calling_zero_constructor() {
    let i = CircularIndex::<3>::zero();

    assert_eq!(i.get(), 0);
}

#[test]
fn lowest_constructor_behaves_identical_to_zero_constructor() {
    let i = CircularIndex::<5>::zero();

    let j = CircularIndex::<5>::lowest();

    assert_eq!(i, j);
}

#[test]
fn equals_n_minus_one_upon_calling_highest_constructor() {
    let i = CircularIndex::<9>::highest();

    assert_eq!(i.get(), 8);
}

#[test]
fn mid_floored_gives_the_lower_middlemost_index_for_even_n() {
    let i = CircularIndex::<6>::mid_floored();

    assert_eq!(i.get(), 2);
}

#[test]
fn mid_floored_gives_the_single_middlemost_index_for_odd_n() {
    let i = CircularIndex::<3>::mid_floored();

    assert_eq!(i.get(), 1);
}

#[test]
fn mid_ceiled_gives_the_higher_middlemost_index_for_even_n() {
    let i = CircularIndex::<4>::mid_ceiled();

    assert_eq!(i.get(), 2);
}

#[test]
fn mid_ceiled_gives_the_single_middlemost_index_for_odd_n() {
    let i = CircularIndex::<7>::mid_ceiled();

    assert_eq!(i.get(), 3);
}

#[test]
fn try_from_behaves_like_with_value() {
    {
        let i = CircularIndex::<3>::try_from(1);

        assert!(i.is_ok());
        assert_eq!(i.unwrap().get(), 1);
    }

    {
        let i = CircularIndex::<7>::try_from(9);

        assert!(i.is_err());
    }
}

#[test]
fn try_into_behaves_like_with_value() {
    {
        let i: Result<CircularIndex<7>, ValueError> = 4.try_into();

        assert!(i.is_ok());
        assert_eq!(i.unwrap().get(), 4);
    }

    {
        let i: Result<CircularIndex<5>, ValueError> = 5.try_into();

        assert!(i.is_err());
    }
}

#[test]
fn supports_addition_with_any_usize() {
    {
        let i = CircularIndex::<7>::with_value(2).unwrap();

        let j = i + 3;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<8>::with_value(6).unwrap();

        let j = i + 4;

        assert_eq!(j.get(), 2);
    }

    {
        let i = CircularIndex::<7>::with_value(1).unwrap();

        let j = i + 21;

        assert_eq!(j.get(), 1);
    }

    {
        let i = CircularIndex::<{ usize::MAX }>::with_value(9).unwrap();

        let j = i + usize::MAX;

        assert_eq!(j.get(), 9);
    }

    {
        let i = CircularIndex::<4>::with_value(1).unwrap();

        let j = i + &2;

        assert_eq!(j.get(), 3);
    }

    {
        let i = CircularIndex::<2>::with_value(0).unwrap();

        let j = &i + 1;

        assert_eq!(j.get(), 1);
    }

    {
        let i = CircularIndex::<4>::with_value(0).unwrap();

        let j = &i + &3;

        assert_eq!(j.get(), 3);
    }
}

#[test]
fn supports_addition_with_circular_index() {
    {
        let i = CircularIndex::<5>::with_value(1).unwrap();
        let j = CircularIndex::<5>::with_value(2).unwrap();

        let k = i + j;

        assert_eq!(k.get(), 3);
    }

    {
        let i = CircularIndex::<3>::with_value(1).unwrap();
        let j = CircularIndex::<3>::with_value(1).unwrap();

        let k = i + &j;

        assert_eq!(k.get(), 2);
    }

    {
        let i = CircularIndex::<5>::with_value(2).unwrap();
        let j = CircularIndex::<5>::with_value(1).unwrap();

        let k = &i + j;

        assert_eq!(k.get(), 3);
    }

    {
        let i = CircularIndex::<7>::with_value(3).unwrap();
        let j = CircularIndex::<7>::with_value(2).unwrap();

        let k = &i + &j;

        assert_eq!(k.get(), 5);
    }
}

#[test]
fn supports_subtraction_with_any_usize() {
    {
        let i = CircularIndex::<3>::with_value(1).unwrap();

        let j = i - 1;

        assert_eq!(j.get(), 0);
    }

    {
        let i = CircularIndex::<6>::with_value(4).unwrap();

        let j = i - 5;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<5>::with_value(3).unwrap();

        let j = i - 10;

        assert_eq!(j.get(), 3);
    }

    {
        let i = CircularIndex::<{ usize::MAX }>::with_value(7).unwrap();

        let j = i - usize::MAX;

        assert_eq!(j.get(), 7);
    }

    {
        let i = CircularIndex::<7>::with_value(4).unwrap();

        let j = i - &2;

        assert_eq!(j.get(), 2);
    }

    {
        let i = CircularIndex::<8>::with_value(6).unwrap();

        let j = &i - 1;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<7>::with_value(6).unwrap();

        let j = &i - &4;

        assert_eq!(j.get(), 2);
    }
}

#[test]
fn supports_subtraction_with_circular_index() {
    {
        let i = CircularIndex::<4>::with_value(3).unwrap();
        let j = CircularIndex::<4>::with_value(1).unwrap();

        let k = i - j;

        assert_eq!(k.get(), 2);
    }

    {
        let i = CircularIndex::<8>::with_value(6).unwrap();
        let j = CircularIndex::<8>::with_value(5).unwrap();

        let k = i - &j;

        assert_eq!(k.get(), 1);
    }

    {
        let i = CircularIndex::<3>::with_value(2).unwrap();
        let j = CircularIndex::<3>::with_value(1).unwrap();

        let k = &i - j;

        assert_eq!(k.get(), 1);
    }

    {
        let i = CircularIndex::<7>::with_value(5).unwrap();
        let j = CircularIndex::<7>::with_value(5).unwrap();

        let k = &i - &j;

        assert_eq!(k.get(), 0);
    }
}

#[test]
fn supports_addition_assignment_from_usize() {
    {
        let mut i = CircularIndex::<3>::with_value(1).unwrap();

        i += 1;

        assert_eq!(i.get(), 2);
    }

    {
        let mut i = CircularIndex::<7>::with_value(3).unwrap();

        i += &3;

        assert_eq!(i.get(), 6);
    }
}

#[test]
fn supports_addition_assignment_from_circular_index() {
    {
        let mut i = CircularIndex::<4>::with_value(2).unwrap();
        let j = CircularIndex::<4>::with_value(1).unwrap();

        i += j;

        assert_eq!(i.get(), 3);
    }

    {
        let mut i = CircularIndex::<9>::with_value(5).unwrap();
        let j = CircularIndex::<9>::with_value(2).unwrap();

        i += &j;

        assert_eq!(i.get(), 7);
    }
}

#[test]
fn supports_subtraction_assignment_from_usize() {
    {
        let mut i = CircularIndex::<9>::with_value(6).unwrap();

        i -= 3;

        assert_eq!(i.get(), 3);
    }

    {
        let mut i = CircularIndex::<9>::with_value(7).unwrap();

        i -= &7;

        assert_eq!(i.get(), 0);
    }
}

#[test]
fn supports_subtraction_assignment_from_circular_index() {
    {
        let mut i = CircularIndex::<7>::with_value(4).unwrap();
        let j = CircularIndex::<7>::with_value(2).unwrap();

        i -= j;

        assert_eq!(i.get(), 2);
    }

    {
        let mut i = CircularIndex::<4>::with_value(3).unwrap();
        let j = CircularIndex::<4>::with_value(2).unwrap();

        i -= &j;

        assert_eq!(i.get(), 1);
    }
}

#[test]
fn supports_indexing_into_primitive_arrays() {
    let array = [5, 8, 4, 3];
    let i = CircularIndex::<4>::with_value(2).unwrap();

    assert_eq!(array[i], 4);
}

#[test]
fn supports_mutable_indexing_into_primitive_arrays() {
    let mut array = [6, 9, 7, 2, 3, 8];
    let i = CircularIndex::<6>::with_value(5).unwrap();

    array[i] = 1;

    assert_eq!(array[i], 1);
}
