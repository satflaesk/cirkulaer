use crate::{Bool, True, ValueError, is_strictly_positive};
use std::ops::{Add, AddAssign, Index, IndexMut, Sub, SubAssign};

/// A module whose purpose is to reduce the risk of the invariants of [`CircularIndex`] being
/// violated.
mod inner {
    use super::{Bool, True, is_strictly_positive};

    /// A circular index type for circularly indexing into primitive, fixed-size
    /// [arrays](https://doc.rust-lang.org/std/primitive.array.html).
    ///
    /// The const-generic argument `N` corresponds to `N` in `[T; N]`. Since the contained index
    /// must be non-negative and strictly lesser than `N`, `N` must be strictly positive.
    ///
    /// To help enforce that `N` is strictly positive at compile time, the unstable
    /// `generic_const_exprs` feature is used; this enables enforcing strict positivity with a
    /// `Bool<{ is_strictly_positive(N) }>: True` trait bound. Consequently, user code that
    /// parameterizes `CircularIndex` over `N` must repeat this exact trait bound:
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
    /// Instances automatically wrap around and are guaranteed to stay within range:
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// const CAPACITY: usize = 3;
    /// let mut array = [0; CAPACITY];
    ///
    /// let mut i = CircularIndex::<CAPACITY>::zero();
    /// array[i] += 1;
    ///
    /// i += 1;
    /// array[i] += 2;
    ///
    /// i += 1;
    /// array[i] += 3;
    ///
    /// i += 1;
    /// array[i] += 4;
    ///
    /// i += 100 * CAPACITY;
    /// array[i] += 10;
    ///
    /// assert_eq!(array, [15, 2, 3]);
    /// # }
    /// ```
    ///
    /// Addition and subtraction operations are guaranteed not to overflow:
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let mut i = CircularIndex::<{ usize::MAX }>::with_value(7).unwrap();
    ///
    /// i += usize::MAX;
    /// assert_eq!(i.get(), 7);
    ///
    /// i -= usize::MAX;
    /// assert_eq!(i.get(), 7);
    /// # }
    /// ```
    ///
    /// If `N` does not equal the array capacity, compilation fails:
    ///
    /// ```rust,compile_fail
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let array = [1, 2, 3, 4];
    /// let i = CircularIndex::<5>::zero();
    ///
    /// let element = array[i]; // Fails to compile.
    /// # }
    /// ```
    ///
    /// If `N` is zero, compilation fails:
    ///
    /// ```rust,compile_fail
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let size = std::mem::size_of::<CircularIndex::<0>>(); // Fails to compile.
    /// # }
    /// ```
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CircularIndex<const N: usize>
    where
        Bool<{ is_strictly_positive(N) }>: True,
    {
        /// The contained index.
        value: usize,

        /// A private field whose purpose is to prevent [`CircularIndex`] from being constructed
        /// using `CircularIndex { ... }` struct literal syntax outside of the
        /// [`inner`](super::inner) module; its presence also forces code outside of
        /// [`inner`](super::inner) to access the [`value`](CircularIndex::value) field via the
        /// [`get`](CircularIndex::get) function.
        _seal: Seal,
    }

    /// A zero-sized type private to the [`inner`](super::inner) module.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct Seal;

    impl<const N: usize> CircularIndex<N>
    where
        Bool<{ is_strictly_positive(N) }>: True,
    {
        /// Create a new instance with the contained index set to `value`, without checking that
        /// `value` is strictly lesser than [`Self::N`]. If `value` is greater than or equal to
        /// [`Self::N`], the behavior is undefined.
        #[must_use]
        pub const fn with_value_unchecked(value: usize) -> Self {
            debug_assert!(value < Self::N);
            Self { value, _seal: Seal }
        }

        /// Return the contained index as a primitive type.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # fn main() {
        /// # use cirkulaer::CircularIndex;
        /// let i = CircularIndex::<4>::with_value(2).unwrap();
        /// assert_eq!(i.get(), 2);
        /// # }
        /// ```
        #[must_use]
        pub const fn get(self) -> usize {
            self.value
        }
    }
}

// Re-export `CircularIndex` for public use while intentionally omitting the `Seal` struct.
pub use inner::CircularIndex;

impl<const N: usize> CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    /// The const-generic argument `N` in `CircularIndex<N>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// assert_eq!(CircularIndex::<8>::N, 8);
    /// # }
    /// ```
    pub const N: usize = N;

    /// Create an instance with the index set to zero.
    #[must_use]
    pub const fn new() -> Self {
        Self::zero()
    }

    /// Attempt to create a new instance with the contained index set to `value`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let i = CircularIndex::<4>::with_value(1);
    /// assert!(i.is_ok());
    /// assert_eq!(i.unwrap().get(), 1);
    ///
    /// let i = CircularIndex::<5>::with_value(5);
    /// assert!(i.is_err());
    ///
    /// let i = CircularIndex::<8>::with_value(9);
    /// assert!(i.is_err());
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`ValueError`] if `value` is not strictly lesser than [`Self::N`].
    pub const fn with_value(value: usize) -> Result<Self, ValueError> {
        if value >= Self::N {
            // SAFETY: Thanks to the trait bound, `Self::N` is guaranteed not to be zero.
            debug_assert!(Self::N != 0);
            unsafe {
                return Err(ValueError {
                    n: std::num::NonZeroUsize::new_unchecked(Self::N),
                    value,
                });
            }
        }

        Ok(Self::with_value_unchecked(value))
    }

    /// Create an instance with the index set to zero.
    #[must_use]
    pub const fn zero() -> Self {
        Self::with_value_unchecked(0)
    }

    /// Create an instance with the index set to its lowest possible value; i.e., to zero. Identical
    /// to calling [`zero`](CircularIndex::zero).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let i = CircularIndex::<4>::lowest();
    /// assert_eq!(i.get(), 0);
    /// # }
    /// ```
    #[must_use]
    pub const fn lowest() -> Self {
        Self::zero()
    }

    /// Create an instance with the index set to its highest possible value; i.e., to `N` minus one.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let i = CircularIndex::<8>::highest();
    /// assert_eq!(i.get(), 7);
    /// # }
    /// ```
    #[must_use]
    pub const fn highest() -> Self {
        Self::with_value_unchecked(Self::N - 1)
    }

    /// If `N` is even, create an instance with the index at its "lower" middlemost value, else
    /// create an instance with the index at its single middlemost value. In case of the latter, the
    /// behavior is identical to that of [`mid_ceiled`](CircularIndex::mid_ceiled).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let i = CircularIndex::<6>::mid_floored();
    /// assert_eq!(i.get(), 2);
    ///
    /// let i = CircularIndex::<7>::mid_floored();
    /// assert_eq!(i.get(), 3);
    /// # }
    /// ```
    #[must_use]
    pub const fn mid_floored() -> Self {
        Self::with_value_unchecked((Self::N - 1) / 2)
    }

    /// If `N` is even, create an instance with the index at its "higher" middlemost value, else
    /// create an instance with the index at its single middlemost value. In case of the latter, the
    /// behavior is identical to that of [`mid_floored`](CircularIndex::mid_floored).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() {
    /// # use cirkulaer::CircularIndex;
    /// let i = CircularIndex::<6>::mid_ceiled();
    /// assert_eq!(i.get(), 3);
    ///
    /// let i = CircularIndex::<7>::mid_ceiled();
    /// assert_eq!(i.get(), 3);
    /// # }
    /// ```
    #[must_use]
    pub const fn mid_ceiled() -> Self {
        Self::with_value_unchecked(Self::N / 2)
    }
}

impl<const N: usize> TryFrom<usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Error = ValueError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::with_value(value)
    }
}

impl<const N: usize> Add<usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        let rhs = rhs % Self::N;

        // SAFETY: By construction, `Self::N` is guaranteed to be strictly greater than
        // `self.get()`, hence their difference is guaranteed not to underflow.
        debug_assert!(Self::N > self.get());
        let min_rhs_that_entails_wrapping = unsafe { Self::N.unchecked_sub(self.get()) };

        let value = if rhs < min_rhs_that_entails_wrapping {
            // SAFETY: Since `min_rhs_that_entails_wrapping` is equal to the difference between
            // `Self::N` and `self.get()`, and since `rhs` is strictly lesser than
            // `min_rhs_that_entails_wrapping`, it follows that the sum of `self.get()` and `rhs` is
            // strictly lesser than `Self::N`. Consequently, this sum is guaranteed not to overflow.
            debug_assert!((self.get() + rhs) < Self::N);
            unsafe { self.get().unchecked_add(rhs) }
        } else {
            // SAFETY: Since `rhs` is greater than or equal to `min_rhs_that_entails_wrapping`,
            // their difference is guaranteed not to underflow.
            debug_assert!(rhs >= min_rhs_that_entails_wrapping);
            unsafe { rhs.unchecked_sub(min_rhs_that_entails_wrapping) }
        };

        Self::with_value_unchecked(value)
    }
}

impl<const N: usize> Add<&usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        self + *rhs
    }
}

impl<const N: usize> Add<usize> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: usize) -> Self::Output {
        *self + rhs
    }
}

impl<const N: usize> Add<&usize> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: &usize) -> Self::Output {
        *self + *rhs
    }
}

impl<const N: usize> Add for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        self + rhs.get()
    }
}

impl<const N: usize> Add<&Self> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Add<usize>>::Output;

    fn add(self, rhs: &Self) -> Self::Output {
        self + (*rhs).get()
    }
}

impl<const N: usize> Add<CircularIndex<N>> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: CircularIndex<N>) -> Self::Output {
        *self + rhs.get()
    }
}

impl<const N: usize> Add for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Add<usize>>::Output;

    fn add(self, rhs: Self) -> Self::Output {
        *self + (*rhs).get()
    }
}

impl<const N: usize> Sub<usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        let rhs = rhs % Self::N;

        // SAFETY: The above modulus operation guarantees that `Self::N` is strictly greater than
        // `rhs`, hence their difference is guaranteed not to underflow.
        debug_assert!(Self::N > rhs);
        self + unsafe { Self::N.unchecked_sub(rhs) }
    }
}

impl<const N: usize> Sub<&usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        self - *rhs
    }
}

impl<const N: usize> Sub<usize> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: usize) -> Self::Output {
        *self - rhs
    }
}

impl<const N: usize> Sub<&usize> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: &usize) -> Self::Output {
        *self - *rhs
    }
}

impl<const N: usize> Sub for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        self - rhs.get()
    }
}

impl<const N: usize> Sub<&Self> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <Self as Sub<usize>>::Output;

    fn sub(self, rhs: &Self) -> Self::Output {
        self - (*rhs).get()
    }
}

impl<const N: usize> Sub<CircularIndex<N>> for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: CircularIndex<N>) -> Self::Output {
        *self - rhs.get()
    }
}

impl<const N: usize> Sub for &CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = <CircularIndex<N> as Sub<usize>>::Output;

    fn sub(self, rhs: Self) -> Self::Output {
        *self - (*rhs).get()
    }
}

impl<const N: usize> AddAssign<usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl<const N: usize> AddAssign<&usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn add_assign(&mut self, rhs: &usize) {
        *self = *self + *rhs;
    }
}

impl<const N: usize> AddAssign for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const N: usize> AddAssign<&Self> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn add_assign(&mut self, rhs: &Self) {
        *self = *self + *rhs;
    }
}

impl<const N: usize> SubAssign<usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl<const N: usize> SubAssign<&usize> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn sub_assign(&mut self, rhs: &usize) {
        *self = *self - *rhs;
    }
}

impl<const N: usize> SubAssign for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const N: usize> SubAssign<&Self> for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn sub_assign(&mut self, rhs: &Self) {
        *self = *self - *rhs;
    }
}

impl<T, const N: usize> Index<CircularIndex<N>> for [T; N]
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    type Output = T;

    fn index(&self, index: CircularIndex<N>) -> &Self::Output {
        // SAFETY: `CircularIndex<N>` guarantees that its contained index is strictly lesser than
        // `N`.
        debug_assert!(index.get() < N);
        unsafe { self.get_unchecked(index.get()) }
    }
}

impl<T, const N: usize> IndexMut<CircularIndex<N>> for [T; N]
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn index_mut(&mut self, index: CircularIndex<N>) -> &mut Self::Output {
        // SAFETY: `CircularIndex<N>` guarantees that its contained index is strictly lesser than
        // `N`.
        debug_assert!(index.get() < N);
        unsafe { self.get_unchecked_mut(index.get()) }
    }
}

impl<const N: usize> std::fmt::Display for CircularIndex<N>
where
    Bool<{ is_strictly_positive(N) }>: True,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{value} (N={n})", value = self.get(), n = Self::N)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(debug_assertions)]
    #[should_panic]
    #[test]
    fn with_value_unchecked_panics_if_given_a_value_not_strictly_lesser_than_n() {
        let _ = CircularIndex::<7>::with_value_unchecked(7);
    }

    #[test]
    fn is_of_the_same_size_as_usize() {
        assert_eq!(
            std::mem::size_of::<CircularIndex::<9>>(),
            std::mem::size_of::<usize>(),
        );
    }

    #[test]
    fn n_does_not_affect_the_size() {
        assert_eq!(
            std::mem::size_of::<CircularIndex::<2>>(),
            std::mem::size_of::<CircularIndex::<8>>(),
        );
    }

    #[test]
    fn the_display_trait_implementation_works_as_intended() {
        let i = CircularIndex::<5>::with_value(3).unwrap();

        assert_eq!(i.to_string(), "3 (N=5)");
    }

    #[test]
    fn is_send() {
        fn assert_is_send<T: Send>() {}

        assert_is_send::<CircularIndex<4>>();
    }

    #[test]
    fn is_sync() {
        fn assert_is_sync<T: Sync>() {}

        assert_is_sync::<CircularIndex<6>>();
    }
}
