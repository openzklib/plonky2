//! STARK Language

/// Constraint
pub trait Constraint<T> {
    /// Asserts that `value == 0`.
    fn assert_zero(&mut self, value: T) -> &mut Self;

    /// Asserts that `lhs == rhs` by subtracting them and calling [`Self::assert_zero`].
    #[inline]
    fn assert_eq(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: Sub<T>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero(diff)
    }

    /// Asserts that `value == 1`.
    #[inline]
    fn assert_one(&mut self, value: T) -> &mut Self
    where
        Self: Sub<T> + One<T>,
    {
        let one = self.one();
        self.assert_eq(value, one)
    }
}

impl<T, C> Constraint<T> for &mut C
where
    C: Constraint<T>,
{
    #[inline]
    fn assert_zero(&mut self, value: T) -> &mut Self {
        (**self).assert_zero(value);
        self
    }
}

/// Constraint Filtered
pub trait ConstraintFiltered<T, Filter> {
    /// Asserts that `value == 0` whenever the `filter` is true.
    fn assert_zero_when(&mut self, filter: Filter, value: T) -> &mut Self;

    /// Asserts that `lhs == rhs` whenever the `filter` is true by subtracting them and calling
    /// [`Self::assert_zero_when`].
    #[inline]
    fn assert_eq_when(&mut self, filter: Filter, lhs: T, rhs: T) -> &mut Self
    where
        Self: Sub<T>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero_when(filter, diff)
    }

    /// Asserts that `value == 1` whenever the `filter` is true.
    #[inline]
    fn assert_one_when(&mut self, filter: Filter, value: T) -> &mut Self
    where
        Self: Sub<T> + One<T>,
    {
        let one = self.one();
        self.assert_eq_when(filter, value, one)
    }
}

/// All Rows Filter
pub struct All;

/// Transition Filter
pub struct Transition;

/// First Row Filter
pub struct FirstRow;

/// Last Row Filter
pub struct LastRow;

/// Zero
pub trait Zero<T> {
    /// Returns the additive identity over `T`.
    fn zero(&mut self) -> T;
}

impl<T, C> Zero<T> for &mut C
where
    C: Zero<T>,
{
    #[inline]
    fn zero(&mut self) -> T {
        (**self).zero()
    }
}

/// Addition
pub trait Add<T> {
    /// Adds `lhs` and `rhs` returning their sum.
    fn add(&mut self, lhs: T, rhs: T) -> T;

    ///
    #[inline]
    fn double(&mut self, value: T) -> T
    where
        T: Clone,
    {
        self.add(value.clone(), value)
    }

    /// Computes the sum over `iter`, returning [`Zero::zero`] if `iter` is empty.
    #[inline]
    fn sum<I>(&mut self, iter: I) -> T
    where
        Self: Zero<T>,
        I: IntoIterator<Item = T>,
    {
        iter.into_iter()
            .fold(self.zero(), |lhs, rhs| self.add(lhs, rhs))
    }
}

impl<T, C> Add<T> for &mut C
where
    C: Add<T>,
{
    #[inline]
    fn add(&mut self, lhs: T, rhs: T) -> T {
        (**self).add(lhs, rhs)
    }
}

/// Subtraction
pub trait Sub<T> {
    /// Subtracts `lhs` and `rhs` returning their difference.
    fn sub(&mut self, lhs: T, rhs: T) -> T;
}

impl<T, C> Sub<T> for &mut C
where
    C: Sub<T>,
{
    #[inline]
    fn sub(&mut self, lhs: T, rhs: T) -> T {
        (**self).sub(lhs, rhs)
    }
}

/// One
pub trait One<T> {
    /// Returns the multiplicative identity over `T`.
    fn one(&mut self) -> T;
}

impl<T, C> One<T> for &mut C
where
    C: One<T>,
{
    #[inline]
    fn one(&mut self) -> T {
        (**self).one()
    }
}

/// Multiplication
pub trait Mul<T> {
    /// Multiplies `lhs` and `rhs` returning their product.
    fn mul(&mut self, lhs: T, rhs: T) -> T;

    /// Computes the product over `iter`, returning [`One::one`] if `iter` is empty.
    #[inline]
    fn product<I>(&mut self, iter: I) -> T
    where
        Self: One<T>,
        I: IntoIterator<Item = T>,
    {
        iter.into_iter()
            .fold(self.one(), |lhs, rhs| self.mul(lhs, rhs))
    }
}

impl<T, C> Mul<T> for &mut C
where
    C: Mul<T>,
{
    #[inline]
    fn mul(&mut self, lhs: T, rhs: T) -> T {
        (**self).mul(lhs, rhs)
    }
}

/// Arithmetic over a Field
pub trait Arithmetic<T>: Add<T> + Mul<T> + One<T> + Sub<T> + Zero<T> {
    ///
    #[inline]
    fn two(&mut self) -> T {
        let lhs_one = self.one();
        let rhs_one = self.one();
        self.add(lhs_one, rhs_one)
    }

    ///
    #[inline]
    fn xor(&mut self, lhs: T, rhs: T) -> T
    where
        T: Clone,
    {
        let sum = self.add(lhs.clone(), rhs.clone());
        let product = self.mul(lhs, rhs);
        let double_product = self.double(product);
        self.sub(sum, double_product)
    }
}

impl<T, C> Arithmetic<T> for C where C: Add<T> + Mul<T> + One<T> + Sub<T> + Zero<T> {}

/// IR Assertions
pub trait Assertions<T>: Sized {
    ///
    #[inline]
    fn assert_zero_product(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero(product)
    }

    ///
    #[inline]
    fn assert_boolean(&mut self, value: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
    {
        let one = self.one();
        let one_minus_value = self.sub(one, value.clone());
        self.assert_zero_product(value, one_minus_value)
    }

    ///
    #[inline]
    fn assert_bit_decomposition<B>(&mut self, value: T, bits: B) -> &mut Self
    where
        Self: Add<T> + Constraint<T> + Mul<T> + One<T> + Sub<T> + Zero<T>,
        T: Clone,
        B: IntoIterator<Item = T>,
    {
        let two = self.two();
        let mut addends = vec![];
        let mut shift = self.one();
        for bit in bits {
            self.assert_boolean(bit.clone());
            addends.push(self.mul(shift.clone(), bit));
            shift = self.mul(two.clone(), shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, sum)
    }

    ///
    #[inline]
    fn assert_bit_decomposition_with_unchecked_bits<B>(&mut self, value: T, bits: B) -> &mut Self
    where
        Self: Add<T> + Constraint<T> + Mul<T> + One<T> + Sub<T> + Zero<T>,
        T: Clone,
        B: IntoIterator<Item = T>,
    {
        let two = self.two();
        let mut addends = vec![];
        let mut shift = self.one();
        for bit in bits {
            addends.push(self.mul(shift.clone(), bit));
            shift = self.mul(two.clone(), shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, sum)
    }

    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition>,
    {
        self.assert_zero_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T>,
    {
        self.assert_eq_when(Transition, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_transition(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T> + One<T>,
    {
        self.assert_one_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_zero_product_transition(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Mul<T>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero_transition(product)
    }

    ///
    #[inline]
    fn assert_increments_by(&mut self, curr: T, next: T, step: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T>,
    {
        let diff = self.sub(next, curr);
        self.assert_eq_transition(diff, step)
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow>,
    {
        self.assert_zero_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow> + Sub<T>,
    {
        self.assert_eq_when(FirstRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_first_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow> + Sub<T> + One<T>,
    {
        self.assert_one_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow>,
    {
        self.assert_zero_when(LastRow, value)
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow> + Sub<T>,
    {
        self.assert_eq_when(LastRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_last_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow> + Sub<T> + One<T>,
    {
        self.assert_one_when(LastRow, value)
    }

    ///
    #[inline]
    fn assert_all_zero<I>(&mut self, iter: I) -> &mut Self
    where
        Self: Constraint<T>,
        I: IntoIterator<Item = T>,
    {
        for item in iter {
            self.assert_zero(item);
        }
        self
    }

    ///
    #[inline]
    fn assert_valid_zero_check(&mut self, is_zero: T, value: T, inverse: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
    {
        let prod = self.mul(value.clone(), inverse.clone());
        self.when(is_zero)
            .assert_zero(value)
            .assert_zero(inverse)
            .otherwise()
            .assert_one(prod);
        self
    }

    ///
    #[inline]
    fn when(&mut self, condition: T) -> Branch<T, Self> {
        Branch {
            condition,
            compiler: self,
        }
    }

    ///
    #[inline]
    fn when_all<I>(&mut self, conditions: I) -> Branch<T, Self>
    where
        Self: Mul<T> + One<T>,
        I: IntoIterator<Item = T>,
    {
        let condition = self.product(conditions);
        self.when(condition)
    }
}

impl<T, COM> Assertions<T> for COM {}

/// Branching Compiler
pub struct Branch<'c, T, COM> {
    /// Condition
    condition: T,

    /// Base Compiler
    compiler: &'c mut COM,
}

impl<'c, T, COM> Branch<'c, T, COM> {
    ///
    #[inline]
    pub fn otherwise(&mut self) -> &mut Self
    where
        T: Clone,
        COM: Sub<T> + One<T>,
    {
        let one = self.compiler.one();
        self.condition = self.compiler.sub(one, self.condition.clone());
        self
    }
}

impl<'c, T, COM> Add<T> for Branch<'c, T, COM>
where
    COM: Add<T>,
{
    #[inline]
    fn add(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.add(lhs, rhs)
    }
}

impl<'c, T, COM> Sub<T> for Branch<'c, T, COM>
where
    COM: Sub<T>,
{
    #[inline]
    fn sub(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.sub(lhs, rhs)
    }
}

impl<'c, T, COM> Zero<T> for Branch<'c, T, COM>
where
    COM: Zero<T>,
{
    #[inline]
    fn zero(&mut self) -> T {
        self.compiler.zero()
    }
}

impl<'c, T, COM> Mul<T> for Branch<'c, T, COM>
where
    COM: Mul<T>,
{
    #[inline]
    fn mul(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.mul(lhs, rhs)
    }
}

impl<'c, T, COM> One<T> for Branch<'c, T, COM>
where
    COM: One<T>,
{
    #[inline]
    fn one(&mut self) -> T {
        self.compiler.one()
    }
}

impl<'c, T, COM> Constraint<T> for Branch<'c, T, COM>
where
    T: Clone,
    COM: Constraint<T> + Mul<T>,
{
    #[inline]
    fn assert_zero(&mut self, value: T) -> &mut Self {
        let filtered_value = self.compiler.mul(self.condition.clone(), value);
        self.compiler.assert_zero(filtered_value);
        self
    }
}

impl<'c, T, Filter, COM> ConstraintFiltered<T, Filter> for Branch<'c, T, COM>
where
    T: Clone,
    COM: ConstraintFiltered<T, Filter> + Mul<T>,
{
    #[inline]
    fn assert_zero_when(&mut self, filter: Filter, value: T) -> &mut Self {
        let filtered_value = self.compiler.mul(self.condition.clone(), value);
        self.compiler.assert_zero_when(filter, filtered_value);
        self
    }
}

///
pub trait Variable<COM = ()>
where
    COM: ?Sized,
{
    ///
    fn create(compiler: &mut COM) -> Self;
}

///
pub trait Allocator {
    ///
    #[inline]
    fn allocate<V>(&mut self) -> V
    where
        V: Variable<Self>,
    {
        V::create(self)
    }

    ///
    #[inline]
    fn allocate_vec<V>(&mut self, len: usize) -> Vec<V>
    where
        V: Variable<Self>,
    {
        (0..len).map(|_| V::create(self)).collect()
    }
}

impl<COM> Allocator for COM where COM: ?Sized {}

/// Target
#[derive(Clone, Copy, Debug)]
pub struct Target(());

/// Register
#[derive(Clone, Copy, Debug)]
pub struct Register {
    /// Current Row Target
    pub curr: Target,

    /// Next Row Target
    pub next: Target,
}

impl<COM> Variable<COM> for Register {
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        let _ = compiler;
        todo!()
    }
}

/// Boolean Register
#[derive(Clone, Copy, Debug)]
pub struct Bool(Register);

impl Bool {
    ///
    #[inline]
    pub fn register(self) -> Register {
        self.0
    }

    ///
    #[inline]
    pub fn curr(self) -> Target {
        self.0.curr
    }

    ///
    #[inline]
    pub fn next(self) -> Target {
        self.0.next
    }

    ///
    #[inline]
    pub fn create_unchecked<COM>(compiler: &mut COM) -> Self {
        Self(compiler.allocate())
    }

    ///
    #[inline]
    pub fn create_unchecked_vec<COM>(len: usize, compiler: &mut COM) -> Vec<Self> {
        (0..len).map(|_| Self::create_unchecked(compiler)).collect()
    }

    ///
    #[inline]
    pub fn create_vec<COM>(len: usize, compiler: &mut COM) -> Vec<Self>
    where
        COM: Constraint<Target> + Mul<Target> + One<Target> + Sub<Target>,
    {
        compiler.allocate_vec(len)
    }

    ///
    #[inline]
    pub fn from_register<COM>(register: Register, compiler: &mut COM) -> Self
    where
        COM: Constraint<Target> + Mul<Target> + One<Target> + Sub<Target>,
    {
        compiler.assert_boolean(register.curr);
        Self(register)
    }

    /// Returns the negation of `self`.
    #[inline]
    pub fn not<COM>(self, compiler: &mut COM) -> Self
    where
        COM: One<Target> + Sub<Target>,
    {
        let one = compiler.one();
        Self(Register {
            curr: compiler.sub(one, self.curr()),
            next: compiler.sub(one, self.next()),
        })
    }
}

impl<COM> Variable<COM> for Bool
where
    COM: Constraint<Target> + Mul<Target> + One<Target> + Sub<Target>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self::from_register(compiler.allocate(), compiler)
    }
}

/// Defines an opcode structure.
#[macro_export]
macro_rules! define_opcode {
    ($(#[$meta:meta])* $vis:vis $name:ident { $head:ident, $($tail:ident),+ $(,)? }) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug)]
        $vis struct $name {
            #[doc = "Opcode `"]
            #[doc = stringify!($head)]
            #[doc = "`"]
            pub $head: Bool,

            $(
                #[doc = "Opcode `"]
                #[doc = stringify!($tail)]
                #[doc = "`"]
                pub $tail: Bool
            ),+,

            /// Opcode Bit Sum
            pub bit_sum: Bool,
        }

        impl core::ops::Index<usize> for $name {
            type Output = Bool;

            #[inline]
            fn index(&self, index: usize) -> &Self::Output {
                [&self.$head, $(&self.$tail),+][index]
            }
        }

        impl<COM> Variable<COM> for $name
        where
            COM: Add<Target> + Constraint<Target> + Mul<Target> + One<Target> + Sub<Target> + Zero<Target>,
        {
            #[inline]
            fn create(compiler: &mut COM) -> Self {
                struct TailOpcodes {
                    $($tail: Bool),+
                }
                let tail_opcodes = TailOpcodes { $($tail: compiler.allocate()),+ };
                let bit_sum =  Bool::from_register(
                    Register {
                        curr: compiler.sum([$(tail_opcodes.$tail.curr()),+]),
                        next: compiler.sum([$(tail_opcodes.$tail.next()),+]),
                    },
                    compiler
                );
                Self {
                    $head: bit_sum.not(compiler),
                    $($tail: tail_opcodes.$tail),+,
                    bit_sum
                }
            }
        }
    };
}

/// Asserts a valid lookup over `curr_input`, `next_input`, and `next_table` in the `compiler`.
#[inline]
pub fn assert_lookup<T, COM>(curr_input: T, next_input: T, next_table: T, compiler: &mut COM)
where
    T: Clone,
    COM: Constraint<T> + ConstraintFiltered<T, LastRow> + Mul<T> + Sub<T>,
{
    // A "vertical" diff between the local and next permuted inputs.
    let diff_input_prev = compiler.sub(next_input.clone(), curr_input);

    // A "horizontal" diff between the next permuted input and permuted table value.
    let diff_input_table = compiler.sub(next_input, next_table);

    compiler.assert_zero_product(diff_input_prev, diff_input_table.clone());

    // This is actually constraining the first row, as per the spec, since `diff_input_table`
    // is a diff of the next row's values. In the context of `constraint_last_row`, the next
    // row is the first row.
    compiler.assert_zero_last_row(diff_input_table);
}

///
pub struct Lookup {
    ///
    pub input: Register,

    ///
    pub table: Register,

    ///
    pub permuted_input: Register,

    ///
    pub permuted_table: Register,
}

impl Lookup {
    ///
    #[inline]
    pub fn assert<COM>(self, compiler: &mut COM)
    where
        COM: Constraint<Target> + ConstraintFiltered<Target, LastRow> + Mul<Target> + Sub<Target>,
    {
        assert_lookup(
            self.permuted_input.curr,
            self.permuted_input.next,
            self.permuted_table.next,
            compiler,
        )
    }
}

///
#[derive(Clone, Debug)]
pub struct FilterColumns(Vec<Bool>);

///
#[derive(Clone, Copy, Debug)]
pub struct Timestamp(Register);

impl Timestamp {
    ///
    #[inline]
    pub fn register(self) -> Register {
        self.0
    }
}

impl<COM> Variable<COM> for Timestamp
where
    COM: Constraint<Target>
        + ConstraintFiltered<Target, FirstRow>
        + ConstraintFiltered<Target, Transition>
        + One<Target>
        + Sub<Target>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        let one = compiler.one();
        let timestamp = compiler.allocate::<Register>();
        compiler.assert_eq_first_row(timestamp.curr, one);
        compiler.assert_increments_by(timestamp.curr, timestamp.next, one);
        Self(timestamp)
    }
}

define_opcode!(pub RwMemoryOpcode { read, write });

/// Read-Write Memory
pub struct RwMemory {
    /// Address
    pub addr: Register,

    /// Sorted Address
    pub addr_sorted: Register,

    /// Value
    pub value: Register,

    /// Sorted Values
    pub value_sorted: Register,

    /// Opcode
    pub opcode: RwMemoryOpcode,

    /// Sorted Read/Write Flag
    pub is_write_sorted: Bool,

    /// Sorted Timestamp
    pub timestamp_sorted: Register,

    /// Timestamp
    pub timestamp: Timestamp,

    /// Used to range check addresses and timestamp differenes
    pub timestamp_permuted: Register,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff: Register,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff_permuted: Register,
}

impl RwMemory {
    ///
    #[inline]
    pub fn permutations(&self) -> Vec<(Register, Register)> {
        vec![
            (self.addr, self.addr_sorted),
            (self.value, self.value_sorted),
            (
                self.opcode.write.register(),
                self.is_write_sorted.register(),
            ),
            (self.timestamp.register(), self.timestamp_sorted),
        ]
    }

    ///
    #[inline]
    pub fn lookups(&self) -> Vec<Lookup> {
        vec![Lookup {
            input: self.timestamp_sorted_diff,
            table: self.timestamp.register(),
            permuted_input: self.timestamp_sorted_diff_permuted,
            permuted_table: self.timestamp_permuted,
        }]
    }

    ///
    #[inline]
    fn assert<COM>(self, compiler: &mut COM) -> Self
    where
        COM: Constraint<Target>
            + ConstraintFiltered<Target, FirstRow>
            + ConstraintFiltered<Target, Transition>
            + ConstraintFiltered<Target, LastRow>
            + Add<Target>
            + Mul<Target>
            + One<Target>
            + Sub<Target>
            + Zero<Target>,
    {
        let one = compiler.one();

        let address_changed = compiler.sub(self.addr_sorted.next, self.addr_sorted.curr);
        let timestamp_changed =
            compiler.sub(self.timestamp_sorted.next, self.timestamp_sorted.curr);

        let address_unchanged = compiler.sub(one, address_changed);

        // ADDRESSES =====================================================================

        // Check that sorted addresses are monotonic, continuous, and start at 0.
        //
        // We do this by ensuring either the sorted address increases by 0 or 1 at each curr_row and at
        // the first curr_row, the sorted addr is 0.

        compiler.assert_zero_first_row(self.addr_sorted.curr);
        compiler.assert_zero_product_transition(address_changed, address_unchanged);

        // TIMESTAMPS ====================================================================

        // Check timestamps are increasing using a range check.
        //
        // This works as follows:
        // 1. Range check every timestamp to be in [1..num_rows].
        // 2. Range check the *difference* between the current and next timestamp to be in
        //    [1..num_rows] if address hasn't changed (i.e. we only care about timestamps for
        //    a particular address)
        // 3. This is enough. Let x, y be subsequent timestamps for a given address. x, y, and
        //    y - x are all in [1..num_rows]. Suppose "x > y" in the field. Then y - x > num_rows -><-
        //
        // This argument works as long as the number of rows is less than half of the field order, which
        // is very true for this library because we can only use up to 2^TWO_ADICITY rows and this is
        // usually far below the field size.
        //
        // We do this by enforcing the "unsorted" timestamps start at 1 and increment by 1 each row.
        // Then we apply a lookup against that col to check that the timestamp diffs are in [1..num_rows]
        // since timestamp_sorted is a permutation of timestamp, timestamp_sorted is guaranteed to be in
        // that range lookups are applied at the end of this function.

        compiler
            .when(address_unchanged)
            .assert_eq_transition(self.timestamp_sorted_diff.next, timestamp_changed);

        // Set the timestamp difference to 1 if the address changed as a dummy to indicate we don't care
        // (our range check doesn't include 0 because timestamps have to be unique).

        compiler
            .when(address_changed)
            .assert_eq_transition(self.timestamp_sorted_diff.next, one);

        // MEMORY TRACE ==================================================================

        // Check that the sorted memory trace is valid.
        //
        // To do this, we check the following at each step:
        // 1. If the address has changed, the memory trace is valid at this step
        // 2. If the address has not changed and the current operation is a write, the memory trace is
        //    valid at this step
        // 3. If the address has not changed and the current operation is a read, the memory trace is
        //    valid at this step iff the value is the same

        let next_is_not_write = compiler.sub(one, self.is_write_sorted.next());
        compiler
            .when_all([address_unchanged, next_is_not_write])
            .assert_eq_transition(self.value_sorted.next, self.value_sorted.curr);

        // LOOKUPS =======================================================================

        for lookup in self.lookups() {
            lookup.assert(compiler);
        }

        self
    }

    /* TODO:
    ///
    #[inline]
    pub fn read(&self, addr: T) -> T {
        // TRACE:
        value = memory.read(addr);

        // STARK:
        curr.value = value;
        curr.addr = addr;
        curr.is_write = false;
        next.timestamp = curr.timestamp + 1; // shared among all parts

        todo!()
    }

    ///
    #[inline]
    pub fn write(&self, addr: T, value: T) {
        // TRACE:
        memory.write(addr, value);

        // STARK:
        curr.addr = addr;
        curr.value = value;
        curr.is_write = true;
        next.timestamp = curr.timestamp + 1; // shared among all parts

        todo!()
    }
    */
}

impl<COM> Variable<COM> for RwMemory
where
    COM: Constraint<Target>
        + ConstraintFiltered<Target, FirstRow>
        + ConstraintFiltered<Target, Transition>
        + ConstraintFiltered<Target, LastRow>
        + Add<Target>
        + Mul<Target>
        + One<Target>
        + Sub<Target>
        + Zero<Target>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self {
            addr: compiler.allocate(),
            addr_sorted: compiler.allocate(),
            value: compiler.allocate(),
            value_sorted: compiler.allocate(),
            opcode: compiler.allocate(),
            is_write_sorted: compiler.allocate(),
            timestamp_sorted: compiler.allocate(),
            timestamp: compiler.allocate(),
            timestamp_permuted: compiler.allocate(),
            timestamp_sorted_diff: compiler.allocate(),
            timestamp_sorted_diff_permuted: compiler.allocate(),
        }
        .assert(compiler)
    }
}

///
pub struct Stack {
    /// Stack Pointer
    pub sp: Register,

    /// Push/Pop Flag
    pub is_pop: Register,

    /// Read/Write Memory Gate
    pub rw_memory: RwMemory,
}

impl Stack {
    ///
    #[inline]
    pub fn permutations(&self) -> Vec<(Register, Register)> {
        self.rw_memory.permutations()
    }

    ///
    #[inline]
    pub fn lookups(&self) -> Vec<Lookup> {
        self.rw_memory.lookups()
    }

    ///
    #[inline]
    fn assert<COM>(self, compiler: &mut COM) -> Self
    where
        COM: Constraint<Target>
            + ConstraintFiltered<Target, FirstRow>
            + ConstraintFiltered<Target, Transition>
            + ConstraintFiltered<Target, LastRow>
            + Add<Target>
            + Mul<Target>
            + One<Target>
            + Sub<Target>
            + Zero<Target>,
    {
        let one = compiler.one();
        let is_push = compiler.sub(one, self.is_pop.curr);
        let sp_add_one = compiler.add(self.sp.curr, one);
        let sp_sub_one = compiler.sub(self.sp.curr, one);

        // Stack Semantics ===============================================================

        // Check that is_pop is binary (only operations are pop and push)
        compiler.assert_boolean(self.is_pop.curr);

        // Check SP starts at 0.
        compiler.assert_zero_first_row(self.sp.curr);

        // If the current operation is a push, the following should be true:
        // 1. addr should be sp
        // 2. next sp should be sp + 1
        // 3. is_write should be 1

        compiler
            .when(is_push)
            .assert_eq(self.rw_memory.addr.curr, self.sp.curr)
            .assert_eq_transition(self.sp.next, sp_add_one)
            .assert_one(self.rw_memory.opcode.write.curr());

        // If the current operation is a pop, the following should be true:
        //
        // 1. addr should be sp - 1
        // 2. next sp should be sp - 1
        // 3. is_write should be 0
        //
        // A corrolary of this is stack underflows (pop when sp is 0) can't happen since
        // then the addresses wouldn't satisfy the continuity requirement.

        compiler
            .when(self.is_pop.curr)
            .assert_eq(self.rw_memory.addr.curr, sp_sub_one)
            .assert_eq_transition(self.sp.next, sp_sub_one)
            .assert_zero(self.rw_memory.opcode.write.curr());

        self
    }

    /* TODO:
    ///
    #[inline]
    pub fn push(&self, value: T) {
        // TRACE:
        stack.push(value);
        curr.rw_memory.value = value;

        // STARK:
        curr.is_pop = false;
        curr.rw_memory.addr = curr.sp + 1;
        curr.rw_memory.is_write = true;
        next.timestamp = curr.timestamp + 1;
        next.sp = curr.sp + 1;

        todo!()
    }

    ///
    #[inline]
    pub fn pop(&self) -> T {
        // TRACE:
        value = stack.pop();
        curr.rw_memory.value = value;

        // STARK:
        curr.is_pop = true;
        curr.rw_memory.addr = curr.sp - 1;
        curr.rw_memory.is_write = false;
        next.timestamp = curr.timestamp + 1;
        next.sp = curr.sp - 1;

        todo!()
    }
    */
}

impl<COM> Variable<COM> for Stack
where
    COM: Constraint<Target>
        + ConstraintFiltered<Target, FirstRow>
        + ConstraintFiltered<Target, Transition>
        + ConstraintFiltered<Target, LastRow>
        + Add<Target>
        + Mul<Target>
        + One<Target>
        + Sub<Target>
        + Zero<Target>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self {
            sp: compiler.allocate(),
            is_pop: compiler.allocate(),
            rw_memory: compiler.allocate(),
        }
        .assert(compiler)
    }
}
