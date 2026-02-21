#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

/// The main module of this crate; implements the [`CircularIndex`] struct and functionality
/// associated with it.
mod circular_index;
pub use crate::circular_index::CircularIndex;

/// A module that implements the [`ValueError`] type returned by [`CircularIndex::with_value`] in
/// case of error.
mod error;
pub use crate::error::ValueError;
