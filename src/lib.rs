#![allow(incomplete_features)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]
#![feature(generic_const_exprs)]

/// The main module of this crate; implements the [`CircularIndex`] struct and functionality
/// associated with it.
mod circular_index;
pub use crate::circular_index::CircularIndex;

/// A module that implements the [`ValueError`] type returned by [`CircularIndex::with_value`] in
/// case of error.
mod error;
pub use crate::error::ValueError;

/// A module that implements the pieces needed for expressing the
/// `Bool< { is_strictly_positive(N) }>: True` trait bound relied on by [`CircularIndex`].
mod trait_bound;
pub use crate::trait_bound::{Bool, True, is_strictly_positive};
