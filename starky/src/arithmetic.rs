//! Compiler Arithmetic

use core::borrow::Borrow;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

///
pub trait Add<L, R = L> {
    ///
    type Output;

    ///
    fn add(&mut self, lhs: L, rhs: R) -> Self::Output;
}

impl<P> Add<P> for ()
where
    P: PackedField,
{
    type Output = P;

    #[inline]
    fn add(&mut self, lhs: P, rhs: P) -> Self::Output {
        lhs + rhs
    }
}

impl<F, const D: usize> Add<Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = Target;

    #[inline]
    fn add(&mut self, lhs: Target, rhs: Target) -> Self::Output {
        self.add(lhs, rhs)
    }
}

impl<F, const D: usize> Add<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn add(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> Self::Output {
        self.add_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Add<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn add(&mut self, lhs: Target, rhs: ExtensionTarget<D>) -> Self::Output {
        let lhs = self.convert_to_ext(lhs);
        self.add_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Add<ExtensionTarget<D>, Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn add(&mut self, lhs: ExtensionTarget<D>, rhs: Target) -> Self::Output {
        let rhs = self.convert_to_ext(rhs);
        self.add_extension(lhs, rhs)
    }
}

///
pub trait Sub<L, R = L> {
    ///
    type Output;

    ///
    fn sub(&mut self, lhs: L, rhs: R) -> Self::Output;
}

impl<P> Sub<P> for ()
where
    P: PackedField,
{
    type Output = P;

    #[inline]
    fn sub(&mut self, lhs: P, rhs: P) -> Self::Output {
        lhs - rhs
    }
}

impl<F, const D: usize> Sub<Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = Target;

    #[inline]
    fn sub(&mut self, lhs: Target, rhs: Target) -> Self::Output {
        self.sub(lhs, rhs)
    }
}

impl<F, const D: usize> Sub<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn sub(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> Self::Output {
        self.sub_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Sub<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn sub(&mut self, lhs: Target, rhs: ExtensionTarget<D>) -> Self::Output {
        let lhs = self.convert_to_ext(lhs);
        self.sub_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Sub<ExtensionTarget<D>, Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn sub(&mut self, lhs: ExtensionTarget<D>, rhs: Target) -> Self::Output {
        let rhs = self.convert_to_ext(rhs);
        self.sub_extension(lhs, rhs)
    }
}

///
pub trait Mul<L, R = L> {
    ///
    type Output;

    ///
    fn mul(&mut self, lhs: L, rhs: R) -> Self::Output;
}

impl<P> Mul<P> for ()
where
    P: PackedField,
{
    type Output = P;

    #[inline]
    fn mul(&mut self, lhs: P, rhs: P) -> Self::Output {
        lhs * rhs
    }
}

impl<F, const D: usize> Mul<Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = Target;

    #[inline]
    fn mul(&mut self, lhs: Target, rhs: Target) -> Self::Output {
        self.mul(lhs, rhs)
    }
}

impl<F, const D: usize> Mul<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn mul(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> Self::Output {
        self.mul_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Mul<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn mul(&mut self, lhs: Target, rhs: ExtensionTarget<D>) -> Self::Output {
        let lhs = self.convert_to_ext(lhs);
        self.mul_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Mul<ExtensionTarget<D>, Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    type Output = ExtensionTarget<D>;

    #[inline]
    fn mul(&mut self, lhs: ExtensionTarget<D>, rhs: Target) -> Self::Output {
        let rhs = self.convert_to_ext(rhs);
        self.mul_extension(lhs, rhs)
    }
}

///
pub trait ScalarMulAdd<T, E> {
    ///
    fn scalar_mul_add(&mut self, lhs: E, scalar: T, rhs: E) -> E;
}

impl<P> ScalarMulAdd<P::Scalar, P> for ()
where
    P: PackedField,
{
    #[inline]
    fn scalar_mul_add(&mut self, lhs: P, scalar: P::Scalar, rhs: P) -> P {
        (lhs * scalar) + rhs
    }
}

impl<F, const D: usize> ScalarMulAdd<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn scalar_mul_add(
        &mut self,
        lhs: ExtensionTarget<D>,
        scalar: Target,
        rhs: ExtensionTarget<D>,
    ) -> ExtensionTarget<D> {
        self.scalar_mul_add_extension(scalar, lhs, rhs)
    }
}

///
pub trait Constant<T, Output> {
    ///
    fn constant(&mut self, value: T) -> Output;

    ///
    #[inline]
    fn constants<I>(&mut self, values: I) -> Vec<Output>
    where
        T: Clone,
        I: IntoIterator,
        I::Item: Borrow<T>,
    {
        values
            .into_iter()
            .map(move |v| self.constant(v.borrow().clone()))
            .collect()
    }
}

impl<P> Constant<P::Scalar, P> for ()
where
    P: PackedField,
{
    #[inline]
    fn constant(&mut self, value: P::Scalar) -> P {
        value.into()
    }
}

impl<F, const D: usize> Constant<F, Target> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn constant(&mut self, value: F) -> Target {
        self.constant(value)
    }
}

///
pub trait Arithmetic<T, E>:
    Add<T, T, Output = T>
    //+ Add<T, E>
    //+ Add<E, T>
    + Add<E, E, Output = E>
    + Sub<T, T, Output = T>
    //+ Sub<T, E>
    //+ Sub<E, T>
    + Sub<E, E, Output = E>
    + Mul<T, T, Output = T>
    //+ Mul<T, E>
    //+ Mul<E, T>
    + Mul<E, E, Output = E>
    + ScalarMulAdd<T, E>
{
}

impl<T, E, A> Arithmetic<T, E> for A where
    A: Add<T, T, Output = T>
        //+ Add<T, E>
        //+ Add<E, T>
        + Add<E, E, Output = E>
        + Sub<T, T, Output = T>
        //+ Sub<T, E>
        //+ Sub<E, T>
        + Sub<E, E, Output = E>
        + Mul<T, T, Output = T>
        //+ Mul<T, E>
        //+ Mul<E, T>
        + Mul<E, E, Output = E>
        + ScalarMulAdd<T, E>
{
}
