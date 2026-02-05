/// A struct to help enforce that `N` in `CircularIndex<N>` is strictly
/// positive.
pub struct Bool<const BOOL: bool>;

/// A trait to help enforce that `N` in `CircularIndex<N>` is strictly positive.
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
