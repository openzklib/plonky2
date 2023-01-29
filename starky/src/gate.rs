//! Gate Descriptions

use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;

/// Gate Evaluation
pub trait Gate<T, COM = ()> {
    /// Evaluates the gate over `curr`, `next`, and `public_inputs` over `compiler`.
    fn eval(curr: &Self, next: &Self, public_inputs: &[T], compiler: &mut COM);

    /// Reads the gate data from `curr` and `next` and then runs [`Self::eval`] over them.
    #[inline]
    fn read_eval<'c, 'n>(
        curr: &mut &'c [T],
        next: &mut &'n [T],
        public_inputs: &[T],
        compiler: &mut COM,
    ) where
        Self: 'c + 'n + Read<T>,
    {
        let curr = Self::read(curr);
        let next = Self::read(next);
        Self::eval(curr, next, public_inputs, compiler);
    }
}

/// Read
pub trait Read<T> {
    /// Reads a value of type `Self` from `slice`.
    fn read<'t>(slice: &mut &'t [T]) -> &'t Self;

    /// Converts `self` into a slice.
    fn as_slice(&self) -> &[T];
}

/// Read Input
pub trait Input<'t, T> {
    /// Reads a value of type `R` from `self`.
    fn read<R>(&mut self) -> &'t R
    where
        R: Read<T>;
}

impl<'t, T> Input<'t, T> for &'t [T] {
    #[inline]
    fn read<R>(&mut self) -> &'t R
    where
        R: Read<T>,
    {
        R::read(self)
    }
}

/// Temporary macro for implementing [`Read`]. Will eventually be replaced by `derive` macro.
#[macro_export]
macro_rules! impl_read_body {
    ($T:ident) => {
        #[inline]
        fn read<'t>(slice: &mut &'t [$T]) -> &'t Self {
            if slice.len() < Self::SIZE {
                panic!("Size Mismatch");
            }
            let output = unsafe {
                $crate::util::transmute_no_compile_time_size_checks(&slice[0..Self::SIZE])
            };
            *slice = &slice[Self::SIZE..];
            output
        }

        #[inline]
        fn as_slice(&self) -> &[$T] {
            unsafe { $crate::util::transmute_no_compile_time_size_checks(self) }
        }
    };
}
