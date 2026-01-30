#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

//! Provides a circular index type suitable for indexing into primitive arrays
//! in a circular, automatically wrapping manner:
//!
//! ```rust
#![doc = include_str!("../examples/basic.rs")]
//! ```

use std::ops::{Add, AddAssign, Index, IndexMut, Sub, SubAssign};

/// A struct to help enforce that the modulus of a circular index is strictly
/// positive.
pub struct Bool<const BOOL: bool>;

/// A trait to help enforce that the modulus of a circular index is strictly
/// positive.
pub trait True {}

impl True for Bool<true> {}

/// Check if a number is strictly positive.
///
/// # Examples
///
/// ```rust
/// # fn main() {
/// # use cirkulaer::is_strictly_positive;
/// assert!(!is_strictly_positive(0));
/// assert!(is_strictly_positive(1));
/// # }
/// ```
#[must_use]
pub const fn is_strictly_positive(number: usize) -> bool {
    number >= 1
}

/// An error type to communicate that an attempt to construct a circular index
/// failed as a result of the provided value not being strictly lesser than the
/// circular index's modulus.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueError {
    modulus: std::num::NonZeroUsize,
    value: usize,
}

impl std::fmt::Display for ValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "Cannot create a circular index with a modulus of {modulus} from a value of {value}",
            modulus = self.modulus,
            value = self.value,
        )
    }
}

impl std::error::Error for ValueError {}

#[cfg(test)]
mod value_error_tests {
    use super::ValueError;

    #[test]
    fn derives_clone() {
        fn f<T: Clone>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(2).unwrap(),
            value: 3,
        };

        f(e);
    }

    #[test]
    fn derives_copy() {
        fn f<T: Copy>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(5).unwrap(),
            value: 9,
        };

        f(e);
    }

    #[test]
    fn derives_debug() {
        fn f<T: std::fmt::Debug>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(4).unwrap(),
            value: 4,
        };

        f(e);
    }

    #[test]
    fn derives_eq() {
        fn f<T: Eq>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(6).unwrap(),
            value: 8,
        };

        f(e);
    }

    #[test]
    fn derives_hash() {
        fn f<T: std::hash::Hash>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(3).unwrap(),
            value: 3,
        };

        f(e);
    }

    #[test]
    fn derives_partial_eq() {
        fn f<T: PartialEq>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(7).unwrap(),
            value: 9,
        };

        f(e);
    }

    #[test]
    fn the_display_trait_implementation_works_as_intended() {
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(4).unwrap(),
            value: 5,
        };

        let s = e.to_string();

        assert_eq!(
            s,
            "Cannot create a circular index with a modulus of 4 from a value of 5"
        );
    }

    #[test]
    fn implements_std_error_error() {
        fn f<T: std::error::Error>(_: T) {}
        let e = ValueError {
            modulus: std::num::NonZeroUsize::new(3).unwrap(),
            value: 7,
        };

        f(e);
    }
}

mod inner {
    use super::{Bool, True, ValueError, is_strictly_positive};

    /// A circular index type suitable for indexing into primitive arrays in a
    /// circular, automatically wrapping manner.
    ///
    /// In modular arithmetic, _n_ in _a (mod n)_ is referred to as the
    /// _modulus_; hence the name of the `MODULUS` const-generic argument.
    ///
    /// To help enforce that the modulus is strictly positive at compile time,
    /// the unstable `generic_const_exprs` feature is used; this enables
    /// enforcing strict positivity with a `Bool<{
    /// is_strictly_positive(MODULUS) }>: True` trait bound. Consequently,
    /// user code that parameterizes `CircularIndex` by its modulus must
    /// repeat this exact trait bound:
    ///
    /// ```rust
    /// #![allow(incomplete_features)]
    /// #![feature(generic_const_exprs)]
    ///
    /// use cirkulaer::{Bool, CircularIndex, True, is_strictly_positive};
    ///
    /// pub struct RingBuffer<T, const CAPACITY: usize>
    /// where
    ///     Bool<{ is_strictly_positive(CAPACITY) }>: True,
    /// {
    ///     buffer: [Option<T>; CAPACITY],
    ///     index_of_next: CircularIndex<CAPACITY>,
    ///     index_of_oldest: CircularIndex<CAPACITY>,
    /// }
    ///
    /// impl<T, const CAPACITY: usize> RingBuffer<T, CAPACITY>
    /// where
    ///     Bool<{ is_strictly_positive(CAPACITY) }>: True,
    /// {
    ///     // ...
    /// }
    /// ```
    ///
    /// # Examples
    ///
    /// Instances automatically wrap around and are guaranteed to stay within
    /// range:
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// const CAPACITY: usize = 3;
    ///
    /// let mut array = [0; CAPACITY];
    /// let mut ci = CircularIndex::<CAPACITY>::new(0).unwrap();
    ///
    /// array[ci] += 1;
    /// ci += 1;
    /// array[ci] += 2;
    /// ci += 1;
    /// array[ci] += 3;
    /// ci += 1;
    /// array[ci] += 4;
    ///
    /// assert_eq!(array, [5, 2, 3]);
    /// # }
    /// ```
    ///
    /// Addition and subtraction operations are guaranteed to not overflow:
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let mut ci = CircularIndex::<{ usize::MAX }>::new(7).unwrap();
    ///
    /// ci += usize::MAX;
    /// assert_eq!(ci.get(), 7);
    ///
    /// ci -= usize::MAX;
    /// assert_eq!(ci.get(), 7);
    /// # }
    /// ```
    ///
    /// If the modulus does not equal the array capacity, compilation fails:
    ///
    /// ```rust,compile_fail
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let array = [1, 2, 3, 4];
    /// let ci = CircularIndex::<5>::new(0);
    ///
    /// let element = array[ci]; // Fails to compile.
    /// # }
    /// ```
    ///
    /// If the modulus is zero, compilation fails:
    ///
    /// ```rust,compile_fail
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let size = std::mem::size_of::<CircularIndex::<0>>(); // Fails to compile.
    /// # }
    /// ```
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CircularIndex<const MODULUS: usize>
    where
        Bool<{ is_strictly_positive(MODULUS) }>: True,
    {
        value: usize,
        _seal: Seal,
    }

    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct Seal;

    impl<const MODULUS: usize> CircularIndex<MODULUS>
    where
        Bool<{ is_strictly_positive(MODULUS) }>: True,
    {
        /// Attempt to create a new instance.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # fn main() {
        /// # use cirkulaer::CircularIndex;
        /// let ci = CircularIndex::<4>::new(1);
        /// assert!(ci.is_ok());
        /// assert_eq!(ci.unwrap().get(), 1);
        ///
        /// let ci = CircularIndex::<5>::new(5);
        /// assert!(ci.is_err());
        ///
        /// let ci = CircularIndex::<8>::new(9);
        /// assert!(ci.is_err());
        /// # }
        /// ```
        ///
        /// # Errors
        ///
        /// Returns [`ValueError`] if `value` is not strictly lesser than
        /// [`Self::MODULUS`].
        pub const fn new(value: usize) -> Result<Self, ValueError> {
            if value >= MODULUS {
                return Err(ValueError {
                    // SAFETY: Thanks to the trait bound, `MODULUS` is guaranteed to be non-zero.
                    modulus: unsafe { std::num::NonZeroUsize::new_unchecked(MODULUS) },
                    value,
                });
            }

            Ok(Self { value, _seal: Seal })
        }

        /// Return the contained index as a primitive type.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # fn main() {
        /// # use cirkulaer::CircularIndex;
        /// let ci = CircularIndex::<4>::new(2).unwrap();
        /// assert_eq!(ci.get(), 2);
        /// # }
        /// ```
        #[must_use]
        pub const fn get(self) -> usize {
            self.value
        }
    }
}

pub use inner::CircularIndex;

impl<const MODULUS: usize> CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    /// The modulus; i.e., `MODULUS` in `CircularIndex<MODULUS>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// assert_eq!(CircularIndex::<8>::MODULUS, 8);
    /// # }
    /// ```
    pub const MODULUS: usize = MODULUS;
}

impl<const MODULUS: usize> TryFrom<usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Error = ValueError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl<const MODULUS: usize> Add<usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        let rhs = rhs % MODULUS;
        let min_rhs_that_entails_wrapping = MODULUS - self.get();

        let value = if rhs < min_rhs_that_entails_wrapping {
            self.get() + rhs
        } else {
            rhs - min_rhs_that_entails_wrapping
        };

        // TODO: Add `new_unchecked` and use it here.
        Self::new(value).unwrap()
    }
}

impl<const MODULUS: usize> Add<&usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        self + *rhs
    }
}

impl<const MODULUS: usize> Add<usize> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Add<usize>>::Output;

    fn add(self, rhs: usize) -> Self::Output {
        *self + rhs
    }
}

impl<const MODULUS: usize> Add<&usize> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        *self + *rhs
    }
}

impl<const MODULUS: usize> Add for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        self + rhs.get()
    }
}

impl<const MODULUS: usize> Add<&Self> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &Self) -> Self::Output {
        self + (*rhs).get()
    }
}

impl<const MODULUS: usize> Add<CircularIndex<MODULUS>> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Add<usize>>::Output;

    fn add(self, rhs: CircularIndex<MODULUS>) -> Self::Output {
        *self + rhs.get()
    }
}

impl<const MODULUS: usize> Add for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        *self + (*rhs).get()
    }
}

impl<const MODULUS: usize> Sub<usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        let rhs = rhs % MODULUS;

        self + (MODULUS - rhs)
    }
}

impl<const MODULUS: usize> Sub<&usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        self - *rhs
    }
}

impl<const MODULUS: usize> Sub<usize> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Sub<usize>>::Output;

    fn sub(self, rhs: usize) -> Self::Output {
        *self - rhs
    }
}

impl<const MODULUS: usize> Sub<&usize> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        *self - *rhs
    }
}

impl<const MODULUS: usize> Sub for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        self - rhs.get()
    }
}

impl<const MODULUS: usize> Sub<&Self> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &Self) -> Self::Output {
        self - (*rhs).get()
    }
}

impl<const MODULUS: usize> Sub<CircularIndex<MODULUS>> for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Sub<usize>>::Output;

    fn sub(self, rhs: CircularIndex<MODULUS>) -> Self::Output {
        *self - rhs.get()
    }
}

impl<const MODULUS: usize> Sub for &CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = <CircularIndex<MODULUS> as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        *self - (*rhs).get()
    }
}

impl<const MODULUS: usize> AddAssign<usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl<const MODULUS: usize> AddAssign<&usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn add_assign(&mut self, rhs: &usize) {
        *self = *self + *rhs;
    }
}

impl<const MODULUS: usize> AddAssign for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const MODULUS: usize> AddAssign<&Self> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn add_assign(&mut self, rhs: &Self) {
        *self = *self + *rhs;
    }
}

impl<const MODULUS: usize> SubAssign<usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl<const MODULUS: usize> SubAssign<&usize> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn sub_assign(&mut self, rhs: &usize) {
        *self = *self - *rhs;
    }
}

impl<const MODULUS: usize> SubAssign for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const MODULUS: usize> SubAssign<&Self> for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn sub_assign(&mut self, rhs: &Self) {
        *self = *self - *rhs;
    }
}

impl<T, const MODULUS: usize> Index<CircularIndex<MODULUS>> for [T; MODULUS]
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    type Output = T;

    fn index(&self, index: CircularIndex<MODULUS>) -> &Self::Output {
        // TODO: The indexing could be unchecked.
        &self[index.get()]
    }
}

impl<T, const MODULUS: usize> IndexMut<CircularIndex<MODULUS>> for [T; MODULUS]
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn index_mut(&mut self, index: CircularIndex<MODULUS>) -> &mut Self::Output {
        // TODO: The indexing could be unchecked.
        &mut self[index.get()]
    }
}

impl<const MODULUS: usize> std::fmt::Display for CircularIndex<MODULUS>
where
    Bool<{ is_strictly_positive(MODULUS) }>: True,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{value} (mod {modulus})",
            value = self.get(),
            modulus = MODULUS,
        )
    }
}

#[cfg(test)]
mod circular_index_tests {
    use super::*;

    #[test]
    fn derives_clone() {
        fn f<T: Clone>(_: T) {}

        f(CircularIndex::<7>::new(3).unwrap());
    }

    #[test]
    fn derives_copy() {
        fn f<T: Copy>(_: T) {}

        f(CircularIndex::<4>::new(2).unwrap());
    }

    #[test]
    fn derives_debug() {
        fn f<T: std::fmt::Debug>(_: T) {}

        f(CircularIndex::<6>::new(0).unwrap());
    }

    #[test]
    fn derives_default() {
        fn f<T: Default>(_: T) {}

        f(CircularIndex::<8>::new(5).unwrap());
    }

    #[test]
    fn derives_eq() {
        fn f<T: Eq>(_: T) {}

        f(CircularIndex::<7>::new(1).unwrap());
    }

    #[test]
    fn derives_hash() {
        fn f<T: std::hash::Hash>(_: T) {}

        f(CircularIndex::<4>::new(1).unwrap());
    }

    #[test]
    fn derives_ord() {
        fn f<T: Ord>(_: T) {}

        f(CircularIndex::<7>::new(3).unwrap());
    }

    #[test]
    fn derives_partial_eq() {
        fn f<T: PartialEq>(_: T) {}

        f(CircularIndex::<4>::new(2).unwrap());
    }

    #[test]
    fn derives_partial_ord() {
        fn f<T: PartialOrd>(_: T) {}

        f(CircularIndex::<5>::new(2).unwrap());
    }

    #[test]
    fn is_of_the_same_size_as_usize() {
        assert_eq!(
            std::mem::size_of::<CircularIndex::<9>>(),
            std::mem::size_of::<usize>(),
        );
    }

    #[test]
    fn the_modulus_does_not_affect_the_size() {
        assert_eq!(
            std::mem::size_of::<CircularIndex::<2>>(),
            std::mem::size_of::<CircularIndex::<8>>(),
        );
    }

    #[test]
    fn the_display_trait_implementation_works_as_intended() {
        let i = CircularIndex::<5>::new(3).unwrap();

        assert_eq!(i.to_string(), "3 (mod 5)");
    }
}
