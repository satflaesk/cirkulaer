use cirkulaer::{CircularIndex, is_strictly_positive};

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
    let i = CircularIndex::<7>::new(6);

    let j = i.clone();

    assert_eq!(i, j);
}

#[test]
fn copies_compare_equal_to_their_source() {
    let i = CircularIndex::<8>::new(4);

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
    let i = CircularIndex::<9>::new(2);
    let j = CircularIndex::<9>::new(2);
    let k = CircularIndex::<9>::new(3);

    assert_eq!(i, i);
    assert_eq!(i, j);
    assert_ne!(i, k);
}

#[test]
fn is_orderable() {
    let i = CircularIndex::<5>::new(1);
    let j = CircularIndex::<5>::new(4);

    assert!(i <= i);
    assert!(i <= j);
    assert!(i < j);
    assert!(j > i);
    assert!(j >= i);
    assert!(j >= j);
}

#[test]
fn the_associated_constant_equals_the_modulus() {
    assert_eq!(CircularIndex::<2>::MODULUS, 2);
}

#[test]
fn is_constructible_from_any_usize() {
    {
        let i = CircularIndex::<4>::new(0);

        assert_eq!(i.get(), 0);
    }

    {
        let i = CircularIndex::<7>::new(3);

        assert_eq!(i.get(), 3);
    }

    {
        let i = CircularIndex::<5>::new(4);

        assert_eq!(i.get(), 4);
    }

    {
        let i = CircularIndex::<9>::new(9);

        assert_eq!(i.get(), 0);
    }

    {
        let i = CircularIndex::<6>::new(11);

        assert_eq!(i.get(), 5);
    }

    {
        let i = CircularIndex::<{ usize::MAX }>::new(usize::MAX);

        assert_eq!(i.get(), 0);
    }

    {
        let i = CircularIndex::<7>::from(3);

        assert_eq!(i.get(), 3);
    }

    {
        let i: CircularIndex<4> = 2.into();

        assert_eq!(i.get(), 2);
    }
}

#[test]
fn supports_addition_with_any_usize() {
    {
        let i = CircularIndex::<7>::new(2);

        let j = i + 3;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<8>::new(6);

        let j = i + 4;

        assert_eq!(j.get(), 2);
    }

    {
        let i = CircularIndex::<7>::new(1);

        let j = i + 21;

        assert_eq!(j.get(), 1);
    }

    {
        let i = CircularIndex::<{ usize::MAX }>::new(9);

        let j = i + usize::MAX;

        assert_eq!(j.get(), 9);
    }

    {
        let i = CircularIndex::<4>::new(1);

        let j = i + &2;

        assert_eq!(j.get(), 3);
    }

    {
        let i = CircularIndex::<2>::new(0);

        let j = &i + 1;

        assert_eq!(j.get(), 1);
    }

    {
        let i = CircularIndex::<4>::new(0);

        let j = &i + &3;

        assert_eq!(j.get(), 3);
    }
}

#[test]
fn supports_addition_with_circular_index() {
    {
        let i = CircularIndex::<5>::new(1);
        let j = CircularIndex::<5>::new(2);

        let k = i + j;

        assert_eq!(k.get(), 3);
    }

    {
        let i = CircularIndex::<3>::new(1);
        let j = CircularIndex::<3>::new(1);

        let k = i + &j;

        assert_eq!(k.get(), 2);
    }

    {
        let i = CircularIndex::<5>::new(2);
        let j = CircularIndex::<5>::new(1);

        let k = &i + j;

        assert_eq!(k.get(), 3);
    }

    {
        let i = CircularIndex::<7>::new(3);
        let j = CircularIndex::<7>::new(2);

        let k = &i + &j;

        assert_eq!(k.get(), 5);
    }
}

#[test]
fn supports_subtraction_with_any_usize() {
    {
        let i = CircularIndex::<3>::new(1);

        let j = i - 1;

        assert_eq!(j.get(), 0);
    }

    {
        let i = CircularIndex::<6>::new(4);

        let j = i - 5;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<5>::new(3);

        let j = i - 10;

        assert_eq!(j.get(), 3);
    }

    {
        let i = CircularIndex::<{ usize::MAX }>::new(7);

        let j = i - usize::MAX;

        assert_eq!(j.get(), 7);
    }

    {
        let i = CircularIndex::<7>::new(4);

        let j = i - &2;

        assert_eq!(j.get(), 2);
    }

    {
        let i = CircularIndex::<8>::new(6);

        let j = &i - 1;

        assert_eq!(j.get(), 5);
    }

    {
        let i = CircularIndex::<7>::new(6);

        let j = &i - &4;

        assert_eq!(j.get(), 2);
    }
}

#[test]
fn supports_subtraction_with_circular_index() {
    {
        let i = CircularIndex::<4>::new(3);
        let j = CircularIndex::<4>::new(1);

        let k = i - j;

        assert_eq!(k.get(), 2);
    }

    {
        let i = CircularIndex::<8>::new(6);
        let j = CircularIndex::<8>::new(5);

        let k = i - &j;

        assert_eq!(k.get(), 1);
    }

    {
        let i = CircularIndex::<3>::new(2);
        let j = CircularIndex::<3>::new(1);

        let k = &i - j;

        assert_eq!(k.get(), 1);
    }

    {
        let i = CircularIndex::<7>::new(5);
        let j = CircularIndex::<7>::new(5);

        let k = &i - &j;

        assert_eq!(k.get(), 0);
    }
}

#[test]
fn supports_addition_assignment_from_usize() {
    {
        let mut i = CircularIndex::<3>::new(1);

        i += 1;

        assert_eq!(i.get(), 2);
    }

    {
        let mut i = CircularIndex::<7>::new(3);

        i += &3;

        assert_eq!(i.get(), 6);
    }
}

#[test]
fn supports_addition_assignment_from_circular_index() {
    {
        let mut i = CircularIndex::<4>::new(2);
        let j = CircularIndex::<4>::new(1);

        i += j;

        assert_eq!(i.get(), 3);
    }

    {
        let mut i = CircularIndex::<9>::new(5);
        let j = CircularIndex::<9>::new(2);

        i += &j;

        assert_eq!(i.get(), 7);
    }
}

#[test]
fn supports_subtraction_assignment_from_usize() {
    {
        let mut i = CircularIndex::<9>::new(6);

        i -= 3;

        assert_eq!(i.get(), 3);
    }

    {
        let mut i = CircularIndex::<9>::new(7);

        i -= &7;

        assert_eq!(i.get(), 0);
    }
}

#[test]
fn supports_subtraction_assignment_from_circular_index() {
    {
        let mut i = CircularIndex::<7>::new(4);
        let j = CircularIndex::<7>::new(2);

        i -= j;

        assert_eq!(i.get(), 2);
    }

    {
        let mut i = CircularIndex::<4>::new(3);
        let j = CircularIndex::<4>::new(2);

        i -= &j;

        assert_eq!(i.get(), 1);
    }
}

#[test]
fn supports_indexing_into_primitive_arrays() {
    let array = [5, 8, 4, 3];
    let i = CircularIndex::<4>::new(2);

    assert_eq!(array[i], 4);
}

#[test]
fn supports_mutable_indexing_into_primitive_arrays() {
    let mut array = [6, 9, 7, 2, 3, 8];
    let i = CircularIndex::<6>::new(5);

    array[i] = 1;

    assert_eq!(array[i], 1);
}
