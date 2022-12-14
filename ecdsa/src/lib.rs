#![allow(clippy::needless_range_loop)]
#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub use num;

pub mod curve;
pub mod gadgets;
