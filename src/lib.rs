#![allow(incomplete_features)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]
#![feature(generic_const_exprs)]

mod error;
pub use crate::error::ValueError;

mod trait_bound;
pub use crate::trait_bound::{Bool, True, is_strictly_positive};

mod circular_index;
pub use crate::circular_index::CircularIndex;
