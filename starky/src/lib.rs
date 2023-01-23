#![cfg_attr(not(feature = "std"), no_std)]
#![feature(generic_const_exprs)]

extern crate alloc;

mod get_challenges;

pub mod config;
pub mod consumer;
pub mod ir;
pub mod lookup;
pub mod permutation;
pub mod proof;
pub mod prover;
pub mod recursive_verifier;
pub mod stark;
pub mod stark_testing;
pub mod starks;
pub mod util;
pub mod vanishing_poly;
pub mod verifier;

#[cfg(test)]
pub mod fibonacci_stark;
