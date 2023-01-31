use core::borrow::{Borrow, BorrowMut};
use core::mem::{size_of, transmute};
use core::ops::Range;

use memoffset::{offset_of, span_of};

use crate::consumer::Compiler;
use crate::gate::{Gate, Read};
use crate::ir::{Arithmetic, Assertions, Constraint};
use crate::stark::{StandardConstraint, StandardConsumer, Stark, StarkConfiguration};
use crate::util::{
    is_power_of_two, trace_rows_to_poly_values, transmute_no_compile_time_size_checks,
};

// TODO: use crate::cross_table_lookup::{CtlColSet, TableID};

/// RLP Row
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RlpRow<T> {
    // register state
    pub op_id: T,
    pub pc: T,
    pub count: T,
    pub content_len: T,
    pub list_count: T,
    pub depth: T,
    pub next: T,
    pub is_last: T,

    /// Opcode
    ///
    /// ```
    /// 00000000: NewEntry
    /// 00000001: List
    /// 00000010: Recurse
    /// 00000100: Return
    /// 00001000: StrPush
    /// 00010000: StrPrefix
    /// 00100000: ListPrefix
    /// 01000000: EndEntry
    /// 10000000: Halt
    /// ```
    pub opcode: [T; 8],

    // advice columns for checking register state / transitions
    // for checking if depth is 0
    pub depth_is_zero: T,
    pub depth_inv: T,

    // for checking if content len is 0
    pub content_len_is_zero: T,
    pub content_len_inv: T,

    // for checking if list count is 0
    pub list_count_is_zero: T,
    pub list_count_inv: T,

    // for chcecking if count == content.len
    pub content_len_minus_count_is_zero: T,
    pub content_len_minus_count_inv: T,

    // for checking if  list_count == content.len()
    pub content_len_minus_list_count_is_zero: T,
    pub content_len_minus_list_count_inv: T,

    // for checking prefix cases
    // 0000: single byte in [0x00..0x7F]
    // 0001: string <=55 bytes long
    // 0010: string >55 bytes long
    // 0100: list whose inner encodings total <=55 bytes long
    // 1000: list whose inner encodings total >55 bytes long
    pub prefix_case_flags: [T; 4],

    // byte range checks via LUT
    // there are 5 rc'd cells - one is for
    // bytes read from input memory
    // the other are for the byte decomposition of count
    // used to calculate the ceil(log_256(count))
    pub rc_u8s: [T; 5],
    pub rc_u8_permuted: [T; 5],
    pub lut_u8_permuteds: [T; 5],

    // range checking for prefix calculation
    pub rc_56_limbs: [T; 6],
    pub rc_56_limbs_permuted: [T; 6],
    pub lut_56_permuted_limbs: [T; 6],

    // range checking for special case where
    // it's a single-byte string in 0x00..0x7F
    pub rc_127_permuted: T,
    pub lut_127_permuted: T,
    pub rc_127: T,

    // advice for checks applied when the prover claims
    // count is greater than 55
    pub upper_limbs_sum_inv: T,
    pub count_in_range: T,
    // advice for counting length of length in bytes
    // 0000: 0,
    // 0001: 1,
    // 0010: 2,
    // 0100: 3,
    // 1000: 4,
    pub log256_flags: [T; 4],
    pub top_byte_inv: T,

    // other bytes for prefix calculation
    pub count_is_one: T,
    pub count_minus_one_inv: T,

    // can probably loose 1-2 of these
    pub prefix_case_tmp: T,
    pub prefix_case_tmp_2: T,
    pub prefix_case_tmp_3: T,
    pub prefix_case_tmp_4: T,
    pub end_entry_tmp: T,

    // advice for checking LUT contents
    pub count_127: T,
    pub count_127_minus_127_inv: T,
    pub count_127_is_127: T,
    pub count_u8: T,
    pub count_u8_minus_255_inv: T,
    pub count_u8_is_255: T,
    pub count_56: T,
    pub count_56_minus_55_inv: T,
    pub count_56_is_55: T,

    // 5-channel CTL to the input memory
    // each represented as [addr, val]
    pub input_memory: [[T; 2]; 5],
    pub input_memory_filters: [T; 5],

    // 3-channel CTL to the call stack
    // each represented as [is_pop, val, timestamp]
    pub call_stack: [[T; 3]; 3],
    pub call_stack_filters: [T; 3],

    // 5-channel CTL to the output "stack" (actually a read-only memory)
    // each represented as [addr, val]
    pub output_stack: [[T; 2]; 5],
    pub output_stack_filters: [T; 5],
}

impl<T> RlpRow<T> {
    /// Gate Size
    pub const SIZE: usize = core::mem::size_of::<RlpRow<u8>>();
}

impl<T> Read<T> for RlpRow<T> {
    crate::impl_read_body!(T);
}

impl<T, COM> Gate<T, COM> for RlpRow<T>
where
    COM: Arithmetic<T> + StandardConstraint<T>,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, public_inputs: &[T], compiler: &mut COM) {
        let one = compiler.one();

        compiler.assert_zero_first_row(&curr.op_id);
        compiler.assert_zero_first_row(&curr.pc);
        compiler.assert_zero_first_row(&curr.count);

        for bit in &curr.opcode {
            compiler.assert_boolean(bit);
        }

        // Check at-most-one-hot encoding
        let opcode_bit_sum = compiler.sum(&curr.opcode);
        compiler.assert_boolean(&opcode_bit_sum);

        // unpack opcodes
        let opcode_is_new_entry = compiler.sub(&one, &opcode_bit_sum);
        let opcode_is_list = &curr.opcode[0];
        let opcode_is_recurse = &curr.opcode[1];
        let opcode_is_return = &curr.opcode[2];
        let opcode_is_str_push = &curr.opcode[3];
        let opcode_is_str_prefix = &curr.opcode[4];
        let opcode_is_list_prefix = &curr.opcode[5];
        let opcode_is_end_entry = &curr.opcode[6];
        let opcode_is_halt = &curr.opcode[7];

        let next_opcode_bit_sum = compiler.sum(&next.opcode);
        let next_opcode_is_new_entry = compiler.sub(&one, &next_opcode_bit_sum);
        let next_opcode_is_list = &next.opcode[0];
        let next_opcode_is_recurse = &next.opcode[1];
        let next_opcode_is_return = &next.opcode[2];
        let next_opcode_is_str_push = &next.opcode[3];
        let next_opcode_is_str_prefix = &next.opcode[4];
        let next_opcode_is_list_prefix = &next.opcode[5];
        let next_opcode_is_end_entry = &next.opcode[6];
        let next_opcode_is_halt = &next.opcode[7];

        // initial opcode is new entry
        compiler.assert_one_first_row(&opcode_is_new_entry);

        for filter in &curr.input_memory_filters {
            compiler.assert_boolean(filter);
        }

        // set input memory filters according to current opcode
        // NewEntry: 0..5
        // List: 0
        // Recurse: None
        // Return: None
        // StrPush: 0
        // StrPrefix: None
        // ListPrefix: None
        // EndEntry: None
        // Halt: None
        let set_filter_0 = compiler.sum([&opcode_is_new_entry, opcode_is_list, opcode_is_str_push]);
        let set_all_filters = opcode_is_new_entry;

        compiler.assert_eq(&set_filter_0, &curr.input_memory_filters[0]);
        for i in 1..5 {
            compiler.assert_eq(&set_all_filters, &curr.input_memory_filters[i]);
        }

        // set call stack filters according to current opcode
        // NewEntry: None,
        // List: 0..1,
        // Recurse: 0..2,
        // Return: 0..2,
        // StrPush: None,
        // StrPrefix: None,
        // ListPrefix: None,
        // EndEntry: None,
        // Halt: None
        let set_filters_0_and_1 =
            compiler.sum([opcode_is_list, opcode_is_recurse, opcode_is_return]);
        let set_filter_2 = compiler.add(opcode_is_recurse, opcode_is_return);
        compiler.assert_eq(&set_filters_0_and_1, &curr.call_stack_filters[0]);
        compiler.assert_eq(&set_filters_0_and_1, &curr.call_stack_filters[1]);
        compiler.assert_eq(&set_filter_2, &curr.call_stack_filters[2]);

        // check call stack timestamp starts at 1
        compiler.assert_one_first_row(&curr.call_stack[0][2]);

        /* TODO:
        // check call stack timestamps increment properly
        compiler.assert_zero_product_transition(
            next.call_stack[0][2] - curr.call_stack[2][2] - one,
            next.call_stack_filters[0],
        );
        compiler.assert_zero_product_transition(
            next.call_stack[0][2] - curr.call_stack[2][2],
            one - next.call_stack_filters[0],
        );
        for i in 1..3 {
            compiler.assert_zero_product(
                curr.call_stack[i][2] - curr.call_stack[i - 1][2] - one,
                curr.call_stack_filters[i],
            );
            compiler.assert_zero_product(
                curr.call_stack[i][2] - curr.call_stack[i - 1][2],
                one - curr.call_stack_filters[i],
            );
        }
        */

        /* TODO:
        // set output "stack" filters according to current opcode
        // NewEntry: None,
        // List: None,
        // Recurse: None,
        // Return: None,
        // StrPush: 0,
        // StrPrefix: filters checked separately
        // ListPrefix: filters checked separately
        // EndEntry: 0..1 if depth_is_zero (checked below)
        // Halt: None
        let is_end_entry_and_depth_is_zero =
            compiler.mul(opcode_is_end_entry, curr_row.depth_is_zero);
        let set_filter_0 = compiler.add(opcode_is_str_push, is_end_entry_and_depth_is_zero);
        let set_filter_1 = is_end_entry_and_depth_is_zero;
        compiler.assert_zero_product(one - curr_row.output_stack_filters[0], set_filter_0);
        compiler.assert_zero_product(one - curr_row.output_stack_filters[1], set_filter_1);
        // turn off other output stack filters for all non-prefix opcodes
        let opcode_is_not_prefix = one - opcode_is_str_prefix - opcode_is_list_prefix;
        compiler.assert_zero_product(&curr_row.output_stack_filters[2], opcode_is_not_prefix);
        compiler.assert_zero_product(&curr_row.output_stack_filters[3], opcode_is_not_prefix);
        compiler.assert_zero_product(&curr_row.output_stack_filters[4], opcode_is_not_prefix);
        */

        // check output "stack" addresses start at 0. It is incremented before written, so address 0
        // won't be checked until the halt state below
        compiler.assert_zero_first_row(&curr_row.output_stack[0][0]);

        /* TODO:
        // check output "stack" addresses increment properly, but ignore these checks during the halt state
        compiler.assert_zero_product_transition(
            next.output_stack[0][0] - curr.output_stack[4][0] - one,
            next.output_stack_filters[0] * (one - next_opcode_is_halt),
        );
        compiler.assert_zero_product_transition(
            next.output_stack[0][0] - curr.output_stack[4][0],
            (one - next.output_stack_filters[0]) * (one - next_opcode_is_halt),
        );
        for i in 1..5 {
            compiler.assert_zero_product(
                curr.output_stack[i][0] - curr.output_stack[i - 1][0] - one,
                curr.output_stack_filters[i],
            );
            compiler.assert_zero_product(
                curr.output_stack[i][0] - curr.output_stack[i - 1][0],
                one - curr.output_stack_filters[i],
            );
        }
        */

        // NewEntry

        /* TODO:
        // read entry metadata from input memory
        // next next = [pc] if depth_is_zero
        compiler.assert_zero_product(curr.input_memory[0][0] - curr.pc, opcode_is_new_entry);
        compiler.assert_zero_product_transition(
            curr.input_memory[0][1] - next.next,
            opcode_is_new_entry * curr.depth_is_zero,
        );
        // next is_last = [pc + 1] if depth_is_zero
        let mut offset = one;
        compiler.assert_zero_product(
            curr.input_memory[1][0] - (curr.pc + offset),
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            curr.input_memory[1][1] - next.is_last,
            opcode_is_new_entry * curr.depth_is_zero,
        );
        // is_list = [pc + 2]
        offset += one;
        compiler.assert_zero_product(
            curr.input_memory[2][0] - (curr.pc + offset),
            opcode_is_new_entry,
        );
        let is_list = curr.input_memory[2][1];
        // next op_id = [pc + 3]
        // note that we *also* check op_id doesn't change here below. This amounts to checking that the op_id read from memory is the one the state machine expects
        offset += one;
        compiler.constraint_transition_filtered(
            curr.input_memory[3][0] - (curr.pc + offset),
            opcode_is_new_entry,
        );
        compiler.constraint_transition_filtered(
            curr.input_memory[3][1] - next.op_id,
            opcode_is_new_entry,
        );
        // next content_len = [pc + 4]
        offset += one;
        compiler.constraint_transition_filtered(
            curr_row.input_memory[4][0] - (curr_row.pc + offset),
            opcode_is_new_entry,
        );
        compiler.constraint_transition_filtered(
            curr_row.input_memory[4][1] - next_row.content_len,
            opcode_is_new_entry,
        );
        */

        /* TODO:
        // set next pc to pc + 5
        offset += one;
        compiler.constraint_transition_filtered(
            next_row.pc - (curr_row.pc + offset),
            opcode_is_new_entry,
        );
        // next count = 0
        compiler.constraint_transition_filtered(next_row.count, opcode_is_new_entry);
        // next list_count = 0
        compiler.constraint_transition_filtered(next_row.list_count, opcode_is_new_entry);

        // binary check is_list
        compiler.assert_zero_product((one - is_list) * is_list, opcode_is_new_entry);
        // if is_list and content len read from memory is 0, then transition to ListPrefix
        // else if is_list, transition to List
        // else if not is_list and content len is zero, transition to StrPrefix
        // else transition to StrPush
        let is_list_and_content_len_is_zero = is_list * next_row.content_len_is_zero;
        let is_list_and_content_len_is_nonzero = is_list * (one - next_row.content_len_is_zero);
        let is_not_list_and_content_len_is_zero =
            (one - is_list) * next_row.content_len_is_zero;
        let is_not_list_and_content_len_is_nonzero =
            (one - is_list) * (one - next_row.content_len_is_zero);
        compiler.constraint_transition_filtered(
            next_opcode_is_list_prefix - is_list_and_content_len_is_zero,
            opcode_is_new_entry,
        );
        compiler.constraint_transition_filtered(
            next_opcode_is_list - is_list_and_content_len_is_nonzero,
            opcode_is_new_entry,
        );
        compiler.constraint_transition_filtered(
            next_opcode_is_str_prefix - is_not_list_and_content_len_is_zero,
            opcode_is_new_entry,
        );
        compiler.constraint_transition_filtered(
            next_opcode_is_str_push - is_not_list_and_content_len_is_nonzero,
            opcode_is_new_entry,
        );

        // check content_len_is_zero via content_len_inv
        let prod = curr_row.content_len * curr_row.content_len_inv;
        // binary check content_len_is_zero
        compiler
            .constraint((one - curr_row.content_len_is_zero) * curr_row.content_len_is_zero);
        // if content_len_is_zero is set, then content_len and content_len_inv must both be zero
        compiler.assert_zero_product(curr_row.content_len, curr_row.content_len_is_zero);
        compiler.assert_zero_product(curr_row.content_len_inv, curr_row.content_len_is_zero);

        // if content_len_is_zero is not set, then prod must be 1
        compiler.assert_zero_product(one - prod, one - curr_row.content_len_is_zero);
        */

        // List ==========================================================================

        /* TODO:
        // push current list count onto the stack
        compiler.assert_zero_product(curr_row.call_stack[0][0] - stack_push, opcode_is_list);
        compiler.assert_zero_product(
            curr_row.call_stack[0][1] - curr_row.list_count,
            opcode_is_list,
        );
        // read child addr from the table, push it on the stack
        compiler.assert_zero_product(curr_row.input_memory[0][0] - curr_row.pc, opcode_is_list);
        let child_addr = curr_row.input_memory[0][1];
        compiler.assert_zero_product(curr_row.call_stack[1][0] - stack_push, opcode_is_list);
        compiler.assert_zero_product(curr_row.call_stack[1][1] - child_addr, opcode_is_list);

        // increment pc
        compiler.constraint_transition_filtered(next_row.pc - (curr_row.pc + one), opcode_is_list);
        // increment list count
        compiler.constraint_transition_filtered(
            next_row.list_count - (curr_row.list_count + one),
            opcode_is_list,
        );

        // if next_row.list_count == next_row.content_len (next_row.content_len_minus_list_count_is_zero),
        // then transition to Recurse otherwise, transition to List
        compiler.constraint_transition_filtered(
            next_opcode_is_recurse - next_row.content_len_minus_list_count_is_zero,
            opcode_is_list,
        );
        compiler.constraint_transition_filtered(
            next_opcode_is_list - (one - next_row.content_len_minus_list_count_is_zero),
            opcode_is_list,
        );

        // check content_len_minus_list_count_is_zero via content_len_minus_list_count_inv
        let content_len_minus_list_count = curr_row.content_len - curr_row.list_count;
        let prod = content_len_minus_list_count * curr_row.content_len_minus_list_count_inv;
        // binary check content_len_minus_list_count_is_zero
        compiler.assert_zero_product(
            (one - curr_row.content_len_minus_list_count_is_zero),
            curr_row.content_len_minus_list_count_is_zero,
        );
        // if content_len_minus_list_count_is_zero is set, then content_len_minus_list_count and
        // content_len_minus_list_count_inv must both be zero
        compiler.assert_zero_product(
            content_len_minus_list_count,
            curr_row.content_len_minus_list_count_is_zero,
        );
        compiler.assert_zero_product(
            curr_row.content_len_minus_list_count_inv,
            curr_row.content_len_minus_list_count_is_zero,
        );
        // otherwise, prod must be 1
        compiler.assert_zero_product(
            one - prod,
            one - curr_row.content_len_minus_list_count_is_zero,
        );
        */

        todo!()
    }
}

/*
pub fn input_memory_ctls(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    type R = RlpRow<u8>;
    (0..5).map(move |i| CtlColSet {
        tid,
        colset: vec![
            offset_of!(R, input_memory) + 2 * i,
            offset_of!(R, input_memory) + 2 * i + 1,
        ],
        filter_col: Some(offset_of!(R, input_memory_filters) + i),
    })
}

pub fn call_stack_ctls(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    type R = RlpRow<u8>;
    (0..3).map(move |i| CtlColSet {
        tid,
        colset: vec![
            offset_of!(R, call_stack) + 3 * i,
            offset_of!(R, call_stack) + 3 * i + 1,
            offset_of!(R, call_stack) + 3 * i + 2,
        ],
        filter_col: Some(offset_of!(R, call_stack_filters) + i),
    })
}

pub fn output_stack_ctls(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    type R = RlpRow<u8>;
    (0..5).map(move |i| CtlColSet {
        tid,
        colset: vec![
            offset_of!(R, output_stack) + 2 * i,
            offset_of!(R, output_stack) + 2 * i + 1,
        ],
        filter_col: Some(offset_of!(R, output_stack_filters) + i),
    })
}

*/

/*

pub fn rc_56_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, rc_56_limbs)
}
pub fn lut_56_col() -> usize {
    offset_of!(RlpRow<u8>, count_56)
}
pub fn rc_56_permuted_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, rc_56_limbs_permuted)
}
pub fn lut_56_permuted_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, lut_56_permuted_limbs)
}

pub fn rc_u8_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, rc_u8s)
}
pub fn lut_u8_col() -> usize {
    offset_of!(RlpRow<u8>, count_u8)
}
pub fn rc_u8_permuted_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, rc_u8_permuted)
}
pub fn lut_u8_permuted_cols() -> Range<usize> {
    span_of!(RlpRow<u8>, lut_u8_permuteds)
}

pub fn rc_127_col() -> usize {
    offset_of!(RlpRow<u8>, rc_127)
}
pub fn lut_127_col() -> usize {
    offset_of!(RlpRow<u8>, count_127)
}
pub fn rc_127_permuted_col() -> usize {
    offset_of!(RlpRow<u8>, rc_127_permuted)
}
pub fn lut_127_permuted_col() -> usize {
    offset_of!(RlpRow<u8>, lut_127_permuted)
}

pub const RLP_NUM_COLS: usize = size_of::<RlpRow<u8>>();

impl<T: Copy + Default> RlpRow<T> {
    pub fn new() -> Self {
        [T::default(); RLP_NUM_COLS].into()
    }
}

impl<T: Copy + Default> Default for RlpRow<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy> From<[T; RLP_NUM_COLS]> for RlpRow<T> {
    fn from(value: [T; RLP_NUM_COLS]) -> Self {
        unsafe { transmute_no_compile_time_size_checks(value) }
    }
}

impl<T: Copy> From<RlpRow<T>> for [T; RLP_NUM_COLS] {
    fn from(value: RlpRow<T>) -> Self {
        unsafe { transmute_no_compile_time_size_checks(value) }
    }
}

impl<T: Copy> Borrow<RlpRow<T>> for [T; RLP_NUM_COLS] {
    fn borrow(&self) -> &RlpRow<T> {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> BorrowMut<RlpRow<T>> for [T; RLP_NUM_COLS] {
    fn borrow_mut(&mut self) -> &mut RlpRow<T> {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> Borrow<[T; RLP_NUM_COLS]> for RlpRow<T> {
    fn borrow(&self) -> &[T; RLP_NUM_COLS] {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> BorrowMut<[T; RLP_NUM_COLS]> for RlpRow<T> {
    fn borrow_mut(&mut self) -> &mut [T; RLP_NUM_COLS] {
        unsafe { transmute(self) }
    }
}

*/
