#![cfg_attr(not(test), no_std)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

use core::clone::Clone;
use core::cmp::{Eq, Ord, PartialEq, PartialOrd};
use core::convert::TryFrom;
use core::default::Default;
use core::error::Error;
use core::fmt::{self, Debug, Display, Formatter};
use core::hash::Hash;
use core::marker::Copy;
use core::ops::{Add, AddAssign, Index, IndexMut, Sub, SubAssign};

/// A circular index for circular indexing into primitive, fixed-size [arrays](array).
///
/// The compile-time constant `N` corresponds to the array size `N` in `[T; N]`.
///
/// # Examples
///
/// Being a *circular* index, addition above `N` minus one wraps around as many times as needed:
///
/// ```rust
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// const N: usize = 4;
/// let mut array = [0; N];
///
/// let mut i = CircularIndex::<N>::zero();
/// array[i] = 1;
/// assert_eq!(array, [1, 0, 0, 0]);
///
/// i += 2;
/// array[i] = 3;
/// assert_eq!(array, [1, 0, 3, 0]);
///
/// i += N;
/// array[i] += 30;
/// assert_eq!(array, [1, 0, 33, 0]);
///
/// i += 10 * N;
/// array[i] += 300;
/// assert_eq!(array, [1, 0, 333, 0]);
/// # }
/// ```
///
/// Subtraction below zero behaves analogously:
///
/// ```rust
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// const N: usize = 2;
/// let mut array = [0; N];
///
/// let mut i = CircularIndex::<N>::zero();
/// array[i] = 1;
/// assert_eq!(array, [1, 0]);
///
/// i -= 1;
/// array[i] = 2;
/// assert_eq!(array, [1, 2]);
/// # }
/// ```
///
/// More formally, addition and subtraction behave as follows:
///
/// ```rust
/// # use cirkulaer::{CircularIndex, ValueError};
/// #
/// # fn main() -> Result<(), ValueError> {
/// const N: usize = 7;
/// let lhs = CircularIndex::<N>::new(3)?;
/// let rhs = 12;
///
/// let sum = lhs + rhs;
/// // Assuming that `lhs.get() + rhs` doesn't overflow, this holds:
/// assert_eq!(sum.get(), (lhs.get() + rhs) % N);
///
/// let difference = lhs - rhs;
/// // Assuming that `lhs.get() + N` doesn't overflow, this holds:
/// assert_eq!(difference.get(), (lhs.get() + N - (rhs % N)) % N);
/// #     Ok(())
/// # }
/// ```
///
/// Addition is guaranteed not to overflow; subtraction not to underflow:
///
/// ```rust
/// # use cirkulaer::{CircularIndex, ValueError};
/// #
/// # fn main() -> Result<(), ValueError> {
/// let mut i = CircularIndex::<{ usize::MAX }>::new(2)?;
///
/// i += usize::MAX;
/// assert_eq!(i.get(), 2);
///
/// i -= usize::MAX;
/// assert_eq!(i.get(), 2);
/// #
/// #     Ok(())
/// # }
/// ```
///
/// If `N` doesn't equal the array size, indexing operations fail to compile:
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// let array = [1, 2, 3];
/// let i = CircularIndex::<4>::zero();
///
/// let _ = array[i]; // `N` does not equal the array size, so this fails to compile.
/// # }
/// ```
///
/// Attempts to combine circular indexes having different `N`s fail to compile:
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() -> Result<(), ValueError> {
/// let i = CircularIndex::<7>::new(4)?;
/// let j = CircularIndex::<8>::new(1)?;
///
/// let _ = i + j; // `i` and `j` are of different types, so this fails to compile.
/// # }
/// ```
///
/// Naturally, the contained index must be strictly lesser than `N`, hence `N` cannot be zero.
/// Attempts to create a circular index with `N` equal to zero fail to compile:
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// let _ = CircularIndex::<0>::default(); // `N` cannot be zero, so this fails to compile.
/// # }
/// ```
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CircularIndex<const N: usize> {
    value: usize,
}

impl<const N: usize> CircularIndex<N> {
    /// The compile-time constant `N` in `CircularIndex<N>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::CircularIndex;
    /// #
    /// # fn main() {
    /// assert_eq!(CircularIndex::<7>::N, 7);
    /// # }
    /// ```
    pub const N: usize = N;

    /// Try to create a circular index with the contained index set to `value`.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError`] if `value` is not strictly lesser than `N`. While an alternative
    /// behavior where values greater than or equal to `N` silently get wrapped would have been
    /// possible, the more conservative approach of rejecting such values has been adopted since it
    /// could help detect bugs in user code.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::{CircularIndex, ValueError};
    /// #
    /// # fn main() -> Result<(), ValueError> {
    /// let i = CircularIndex::<4>::new(3);
    /// assert_eq!(i?.get(), 3);
    ///
    /// let i = CircularIndex::<6>::new(6);
    /// assert!(i.is_err());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub const fn new(value: usize) -> Result<Self, ValueError> {
        if value >= Self::N {
            return Err(ValueError { n: Self::N, value });
        }

        Ok(Self::new_unchecked(value))
    }

    /// Create a ciruclar index with the contained index set to `value`, *without* checking whether
    /// `value` is strictly lesser than `N`. If `value` is not strictly lesser than `N`, the
    /// behavior is *undefined*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::CircularIndex;
    /// #
    /// # fn main() {
    /// let i = CircularIndex::<8>::new_unchecked(1);
    /// assert_eq!(i.get(), 1);
    /// # }
    /// ```
    ///
    /// # Panics
    ///
    /// If *debug* assertions are enabled, panics if `value` is not strictly lesser than `N`.
    ///
    /// # Safety
    ///
    /// `value` must be strictly lesser than `N`.
    #[must_use]
    pub const fn new_unchecked(value: usize) -> Self {
        const {
            assert!(N != 0, "`N` in `CircularIndex<N>` cannot be zero");
        }

        debug_assert!(
            value < Self::N,
            "a `CircularIndex<N>` must only be created from a value strictly lesser than `N`"
        );

        Self { value }
    }

    /// Create a circular index with the contained index set to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::CircularIndex;
    /// #
    /// # fn main() {
    /// let i = CircularIndex::<5>::zero();
    /// assert_eq!(i.get(), 0);
    /// # }
    /// ```
    #[must_use]
    pub const fn zero() -> Self {
        Self::new_unchecked(0)
    }

    /// Return the contained index as a primitive type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::{CircularIndex, ValueError};
    /// #
    /// # fn main() -> Result<(), ValueError> {
    /// let i = CircularIndex::<4>::new(2)?;
    /// assert_eq!(i.get(), 2);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    #[must_use]
    pub const fn get(self) -> usize {
        self.value
    }
}

/// The error returned by [`CircularIndex::new`] when given a value not strictly lesser than the
/// compile-time constant `N`.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct ValueError {
    n: usize,
    value: usize,
}

impl Debug for ValueError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "ValueError {{\n    N: {N},\n    value: {value}\n}}",
                N = self.n,
                value = self.value,
            )
        } else {
            write!(
                f,
                "ValueError {{ N: {N}, value: {value} }}",
                N = self.n,
                value = self.value,
            )
        }
    }
}

impl Display for ValueError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "a `CircularIndex<{N}>` cannot be created from a value of {value}",
            N = self.n,
            value = self.value,
        )
    }
}

impl Error for ValueError {}

impl<const N: usize> Default for CircularIndex<N> {
    /// Create a circular index with the contained index set to zero. Identical to calling
    /// [`zero`](CircularIndex::zero).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use cirkulaer::CircularIndex;
    /// #
    /// # fn main() {
    /// let i = CircularIndex::<4>::default();
    /// assert_eq!(i.get(), 0);
    /// # }
    /// ```
    fn default() -> Self {
        Self::zero()
    }
}

impl<const N: usize> TryFrom<usize> for CircularIndex<N> {
    type Error = ValueError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl<const N: usize> Add<usize> for CircularIndex<N> {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        let rhs = rhs % Self::N;

        // SAFETY: By construction, `Self::N` is guaranteed to be strictly greater than
        //         `self.get()`, hence their difference is guaranteed not to underflow.
        debug_assert!(Self::N > self.get());
        let min_rhs_that_entails_wrapping = unsafe { Self::N.unchecked_sub(self.get()) };

        let value = if rhs < min_rhs_that_entails_wrapping {
            // SAFETY: Since `min_rhs_that_entails_wrapping` is equal to the difference between
            //         `Self::N` and `self.get()`, and since `rhs` is strictly lesser than
            //         `min_rhs_that_entails_wrapping`, it follows that the sum of `self.get()` and
            //         `rhs` is strictly lesser than `Self::N`. Consequently, this sum is guaranteed
            //         not to overflow.
            debug_assert!((self.get() + rhs) < Self::N);
            unsafe { self.get().unchecked_add(rhs) }
        } else {
            // SAFETY: Since `rhs` is greater than or equal to `min_rhs_that_entails_wrapping`,
            //         their difference is guaranteed not to underflow.
            debug_assert!(rhs >= min_rhs_that_entails_wrapping);
            unsafe { rhs.unchecked_sub(min_rhs_that_entails_wrapping) }
        };

        Self::new_unchecked(value)
    }
}

impl<const N: usize> Add<&usize> for CircularIndex<N> {
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        self + *rhs
    }
}

impl<const N: usize> Add<usize> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: usize) -> Self::Output {
        *self + rhs
    }
}

impl<const N: usize> Add<&usize> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        *self + *rhs
    }
}

impl<const N: usize> Add for CircularIndex<N> {
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        self + rhs.get()
    }
}

impl<const N: usize> Add<&Self> for CircularIndex<N> {
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &Self) -> Self::Output {
        self + (*rhs).get()
    }
}

impl<const N: usize> Add<CircularIndex<N>> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: CircularIndex<N>) -> Self::Output {
        *self + rhs.get()
    }
}

impl<const N: usize> Add for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        *self + (*rhs).get()
    }
}

impl<const N: usize> Sub<usize> for CircularIndex<N> {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        let rhs = rhs % Self::N;

        // SAFETY: The above modulus operation guarantees that `Self::N` is strictly greater than
        //         `rhs`, hence their difference is guaranteed not to underflow.
        debug_assert!(Self::N > rhs);
        self + unsafe { Self::N.unchecked_sub(rhs) }
    }
}

impl<const N: usize> Sub<&usize> for CircularIndex<N> {
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        self - *rhs
    }
}

impl<const N: usize> Sub<usize> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: usize) -> Self::Output {
        *self - rhs
    }
}

impl<const N: usize> Sub<&usize> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        *self - *rhs
    }
}

impl<const N: usize> Sub for CircularIndex<N> {
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        self - rhs.get()
    }
}

impl<const N: usize> Sub<&Self> for CircularIndex<N> {
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &Self) -> Self::Output {
        self - (*rhs).get()
    }
}

impl<const N: usize> Sub<CircularIndex<N>> for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: CircularIndex<N>) -> Self::Output {
        *self - rhs.get()
    }
}

impl<const N: usize> Sub for &CircularIndex<N> {
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        *self - (*rhs).get()
    }
}

impl<const N: usize> AddAssign<usize> for CircularIndex<N> {
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl<const N: usize> AddAssign<&usize> for CircularIndex<N> {
    fn add_assign(&mut self, rhs: &usize) {
        *self = *self + *rhs;
    }
}

impl<const N: usize> AddAssign for CircularIndex<N> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const N: usize> AddAssign<&Self> for CircularIndex<N> {
    fn add_assign(&mut self, rhs: &Self) {
        *self = *self + *rhs;
    }
}

impl<const N: usize> SubAssign<usize> for CircularIndex<N> {
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl<const N: usize> SubAssign<&usize> for CircularIndex<N> {
    fn sub_assign(&mut self, rhs: &usize) {
        *self = *self - *rhs;
    }
}

impl<const N: usize> SubAssign for CircularIndex<N> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const N: usize> SubAssign<&Self> for CircularIndex<N> {
    fn sub_assign(&mut self, rhs: &Self) {
        *self = *self - *rhs;
    }
}

impl<T, const N: usize> Index<CircularIndex<N>> for [T; N] {
    type Output = T;

    fn index(&self, index: CircularIndex<N>) -> &Self::Output {
        // SAFETY: By construction, `CircularIndex<N>` guarantees that its contained index is
        //         strictly lesser than `N`.
        debug_assert!(index.get() < N);
        unsafe { self.get_unchecked(index.get()) }
    }
}

impl<T, const N: usize> IndexMut<CircularIndex<N>> for [T; N] {
    fn index_mut(&mut self, index: CircularIndex<N>) -> &mut Self::Output {
        // SAFETY: By construction, `CircularIndex<N>` guarantees that its contained index is
        //         strictly lesser than `N`.
        debug_assert!(index.get() < N);
        unsafe { self.get_unchecked_mut(index.get()) }
    }
}

impl<const N: usize> Debug for CircularIndex<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "CircularIndex<{N}> {{\n    {value},\n}}",
                N = Self::N,
                value = self.value,
            )
        } else {
            write!(
                f,
                "CircularIndex<{N}> {{ {value} }}",
                N = Self::N,
                value = self.value,
            )
        }
    }
}

/// Ensure that no [`CircularIndex`] constructor accepts an `N` of zero, since only
/// [`new_unchecked`](CircularIndex::new_unchecked) asserts that `N` is not zero.
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
///
/// # fn main() {
/// let _ = CircularIndex::<0>::default();
/// # }
/// ```
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// let _ = CircularIndex::<0>::new(0);
/// # }
/// ```
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// let _ = CircularIndex::<0>::new_unchecked(0);
/// # }
/// ```
///
/// ```rust,compile_fail
/// # use cirkulaer::CircularIndex;
/// #
/// # fn main() {
/// let _ = CircularIndex::<0>::zero();
/// # }
/// ```
#[allow(dead_code)]
#[doc(hidden)]
struct _CompileFail;
