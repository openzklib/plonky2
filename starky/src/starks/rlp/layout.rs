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
    T: Copy,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, public_inputs: &[T], compiler: &mut COM) {
        let zero = compiler.zero();
        let one = compiler.one();

        let stack_pop = one;
        let stack_push = zero;

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

        // check call stack timestamps increment properly
        compiler
            .when(next.call_stack_filters[0])
            .assert_increments_by(&curr.call_stack[2][2], &next.call_stack[0][2], &one)
            .otherwise()
            .assert_eq_transition(&curr.call_stack[2][2], &next.call_stack[0][2]);
        for i in 1..3 {
            compiler
                .when(curr.call_stack_filters[i])
                .assert_increments_by(&curr.call_stack[i][2], &curr.call_stack[i - 1][2], &one)
                .otherwise()
                .assert_eq_transition(&curr.call_stack[i][2], &curr.call_stack[i - 1][2]);
        }

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
        let is_end_entry_and_depth_is_zero = compiler.mul(opcode_is_end_entry, &curr.depth_is_zero);
        let set_filter_0 = compiler.add(opcode_is_str_push, &is_end_entry_and_depth_is_zero);
        let set_filter_1 = is_end_entry_and_depth_is_zero;
        let not_curr_output_stack_filters_0 = compiler.sub(&one, &curr.output_stack_filters[0]);
        let not_curr_output_stack_filters_1 = compiler.sub(&one, &curr.output_stack_filters[1]);
        compiler.assert_zero_product(&not_curr_output_stack_filters_0, &set_filter_0);
        compiler.assert_zero_product(&not_curr_output_stack_filters_1, &set_filter_1);
        // turn off other output stack filters for all non-prefix opcodes
        let opcode_is_not_prefix = {
            let one_minus_opcode_is_str_prefix = compiler.sub(&one, opcode_is_str_prefix);
            compiler.sub(&one_minus_opcode_is_str_prefix, opcode_is_list_prefix)
        };
        compiler.when(opcode_is_not_prefix).assert_all_zero([
            &curr.output_stack_filters[2],
            &curr.output_stack_filters[3],
            &curr.output_stack_filters[4],
        ]);

        // check output "stack" addresses start at 0. It is incremented before written, so address 0
        // won't be checked until the halt state below
        compiler.assert_zero_first_row(&curr.output_stack[0][0]);

        /* TODO:
        // check output "stack" addresses increment properly, but ignore these checks during the halt state
        let one_minus_next_opcode_is_halt = compiler.sub(&one, &next_opcode_is_halt);
        compiler.assert_zero_product_transition(
            next.output_stack[0][0] - curr.output_stack[4][0] - one,
            next.output_stack_filters[0] * one_minus_next_opcode_is_halt,
        );
        compiler.assert_zero_product_transition(
            next.output_stack[0][0] - curr.output_stack[4][0],
            (one - next.output_stack_filters[0]) * one_minus_next_opcode_is_halt,
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

        // NewEntry ======================================================================

        /* TODO:
        // read entry metadata from input memory
        // next next = [pc] if depth_is_zero
        compiler
            .when(opcode_is_new_entry)
            .assert_eq(&curr.input_memory[0][0], &curr.pc);
        compiler.assert_zero_product_transition(
            curr.input_memory[0][1] - next.next,
            opcode_is_new_entry * curr.depth_is_zero,
        );
        // next is_last = [pc + 1] if depth_is_zero
        let mut offset = one;
        compiler
            .when(opcode_is_new_entry)
            .assert_eq(&curr.input_memory[1][0], curr.pc + offset);
        compiler.assert_zero_product_transition(
            curr.input_memory[1][1] - next.is_last,
            opcode_is_new_entry * curr.depth_is_zero,
        );
        // is_list = [pc + 2]
        offset += one;
        compiler
            .when(opcode_is_new_entry)
            .assert_eq(curr.input_memory[2][0], curr.pc + offset);
        let is_list = curr.input_memory[2][1];
        // next op_id = [pc + 3]
        // note that we *also* check op_id doesn't change here below. This amounts to checking that
        // the op_id read from memory is the one the state machine expects
        offset += one;
        compiler
            .when(opcode_is_new_entry)
            .assert_eq_transition(&curr.input_memory[3][0], curr.pc + offset)
            .assert_eq_transition(&curr.input_memory[3][1], next.op_id);

        // next content_len = [pc + 4]
        offset += one;
        compiler
            .when(opcode_is_new_entry)
            .assert_eq_transition(&curr.input_memory[4][0], curr.pc + offset)
            .assert_eq_transition(&curr.input_memory[4][1], next.content_len);

        // set next pc to pc + 5
        offset += one;
        compiler
            .when(opcode_is_new_entry)
            .assert_eq_transition(&next.pc, curr.pc + offset)
            .assert_zero_transition(&next.count)
            .assert_zero_transition(&next.list_count)
            .assert_boolean(is_list);

        // if is_list and content len read from memory is 0, then transition to ListPrefix
        // else if is_list, transition to List
        // else if not is_list and content len is zero, transition to StrPrefix
        // else transition to StrPush
        let is_list_and_content_len_is_zero = is_list * next.content_len_is_zero;
        let is_list_and_content_len_is_nonzero = is_list * (one - next.content_len_is_zero);
        let is_not_list_and_content_len_is_zero = (one - is_list) * next.content_len_is_zero;
        let is_not_list_and_content_len_is_nonzero =
            (one - is_list) * (one - next.content_len_is_zero);
        compiler
            .when(opcode_is_new_entry)
            .assert_eq_transition(next_opcode_is_list_prefix, is_list_and_content_len_is_zero)
            .assert_eq_transition(next_opcode_is_list, is_list_and_content_len_is_nonzero)
            .assert_eq_transition(
                next_opcode_is_str_prefix,
                is_not_list_and_content_len_is_zero,
            )
            .assert_eq_transition(
                next_opcode_is_str_push,
                is_not_list_and_content_len_is_nonzero,
            );
        */

        // binary check content_len_is_zero
        // check content_len_is_zero via content_len_inv
        // if content_len_is_zero is set, then content_len and content_len_inv must both be zero
        compiler.assert_boolean(&curr.content_len_is_zero);
        compiler.assert_valid_zero_check(
            curr.content_len_is_zero,
            &curr.content_len,
            &curr.content_len_inv,
        );

        // List ==========================================================================

        // push current list count onto the stack
        // read child addr from the table, push it on the stack
        // increment pc
        // increment list count
        let child_addr = curr.input_memory[0][1];
        compiler
            .when(*opcode_is_list)
            .assert_eq(&curr.call_stack[0][0], &stack_push)
            .assert_eq(&curr.call_stack[0][1], &curr.list_count)
            .assert_eq(&curr.input_memory[0][0], &curr.pc)
            .assert_eq(&curr.call_stack[1][0], &stack_push)
            .assert_eq(&curr.call_stack[1][1], &child_addr)
            .assert_increments_by(&curr.pc, &next.pc, &one)
            .assert_increments_by(&curr.list_count, &next.list_count, &one);

        /* TODO:
        // if next.list_count == next.content_len (next.content_len_minus_list_count_is_zero),
        // then transition to Recurse otherwise, transition to List
        compiler.assert_zero_product_transition(
            next_opcode_is_recurse - next.content_len_minus_list_count_is_zero,
            opcode_is_list,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_list - (one - next.content_len_minus_list_count_is_zero),
            opcode_is_list,
        );
        */

        // check content_len_minus_list_count_is_zero via content_len_minus_list_count_inv
        // binary check content_len_minus_list_count_is_zero
        // if content_len_minus_list_count_is_zero is set, then content_len_minus_list_count and
        // content_len_minus_list_count_inv must both be zero
        // otherwise, prod must be 1
        let content_len_minus_list_count = compiler.sub(&curr.content_len, &curr.list_count);
        compiler.assert_boolean(&curr.content_len_minus_list_count_is_zero);
        compiler.assert_valid_zero_check(
            curr.content_len_minus_list_count_is_zero,
            &content_len_minus_list_count,
            &curr.content_len_minus_list_count_inv,
        );

        // Recurse =======================================================================

        // pop the "dst" address to jump to from the call stack
        // push count to the call stack
        // push pc to the call stack
        // set next pc to dst
        // increment depth
        // transition to NewEntry
        compiler
            .when(*opcode_is_recurse)
            .assert_eq(&curr.call_stack[0][0], &stack_pop)
            .assert_eq(&curr.call_stack[1][0], &stack_push)
            .assert_eq(&curr.call_stack[1][1], &curr.count)
            .assert_eq(&curr.call_stack[2][0], &stack_push)
            .assert_eq(&curr.call_stack[2][1], &curr.pc)
            .assert_eq_transition(&next.pc, &curr.call_stack[0][1])
            .assert_increments_by(&curr.depth, &next.depth, &one)
            .assert_eq_transition(&next_opcode_is_new_entry, &one);

        // Return ========================================================================

        // pop "old_pc" from the call stack
        // pop "old count" from the call stack
        // pop "old list count" from the call stack
        // add "old count" to count
        // set list_count to old_list_count
        // set pc to old_pc
        // decrement depth

        let old_pc = curr.call_stack[0][1];
        let old_count = curr.call_stack[1][1];
        let old_list_count = curr.call_stack[2][1];
        compiler
            .when(*opcode_is_return)
            .assert_eq(&curr.call_stack[0][0], &stack_pop)
            .assert_eq(&curr.call_stack[1][0], &stack_pop)
            .assert_eq(&curr.call_stack[2][0], &stack_pop)
            .assert_increments_by(&curr.count, &next.count, &old_count)
            .assert_eq_transition(&next.list_count, &old_list_count)
            .assert_eq_transition(&next.pc, &old_pc)
            .assert_increments_by(&curr.depth, &next.depth, &one);

        /* TODO:
        // if next row's list count (i.e. the one that was popped) is zero, then transition to ListPrefix
        // otherwise, transition to recurse
        compiler.assert_zero_product_transition(
            next_opcode_is_list_prefix - next.list_count_is_zero,
            opcode_is_return,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_recurse - (one - next.list_count_is_zero),
            opcode_is_return,
        );
        */

        // check list_count_is_zero via list_count_inv
        // if list_count_is_zero is set, then list_count and list_count_inv must both be zero
        // otherwise, prod must be 1
        compiler.assert_valid_zero_check(
            curr.list_count_is_zero,
            &curr.list_count,
            &curr.list_count_inv,
        );

        // StrPush =======================================================================

        // read val from input_memory at pc
        // range check val to be a u8 by copying it into a range-checked cell
        // increment pc
        // push val to output stack
        // increment count
        let val = curr.input_memory[0][1];
        compiler
            .when(*opcode_is_str_push)
            .assert_eq(&curr.input_memory[0][0], &curr.pc)
            .assert_eq(&curr.rc_u8s[0], &val)
            .assert_increments_by(&curr.pc, &next.pc, &one)
            .assert_eq(&curr.output_stack[0][1], &val)
            .assert_increments_by(&curr.count, &next.count, &one);

        /* TODO:
        // if content_len = next row's count (i.e. content_len_minus_count_is_zero),
        // then transition to StrPrefix, otherwise, transition to StrPush
        compiler.assert_zero_product_transition(
            next_opcode_is_str_prefix - next.content_len_minus_count_is_zero,
            opcode_is_str_push,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_str_push - (one - next.content_len_minus_count_is_zero),
            opcode_is_str_push,
        );
        */

        // check content_len_minus_count_is_zero via content_len_minus_count_inv
        // binary check content_len_minus_count_is_zero
        // if content_len_minus_count_is_zero is set, then content_len_minus_count
        // and content_len_minus_count_inv must both be zero otherwise, prod must be 1
        let content_len_minus_count = compiler.sub(&curr.content_len, &curr.count);
        compiler.assert_boolean(&curr.content_len_minus_count_is_zero);
        compiler.assert_valid_zero_check(
            curr.content_len_minus_count_is_zero,
            &content_len_minus_count,
            &curr.content_len_minus_count_inv,
        );

        // prefix case flags
        // binary check flags
        for i in 0..4 {
            compiler.assert_boolean(&curr.prefix_case_flags[i]);
        }
        // binary check their sum
        let prefix_case_flag_sum = compiler.sum((0..4).map(|i| curr.prefix_case_flags[i]));
        let next_prefix_case_flag_sum = compiler.sum((0..4).map(|i| next.prefix_case_flags[i]));
        compiler.assert_boolean(&prefix_case_flag_sum);

        // unpack
        let next_prefix_single_byte_case = compiler.sub(&one, &next_prefix_case_flag_sum);
        let prefix_string_in_range_case = &curr.prefix_case_flags[0];
        let prefix_string_out_of_range_case = &curr.prefix_case_flags[1];
        let prefix_list_in_range_case = &curr.prefix_case_flags[2];

        // check if count <= 55 using base-56 decomp
        let upper_limb_sum = compiler.sum((1..6).map(|i| curr.rc_56_limbs[i]));
        compiler.assert_boolean(&curr.count_in_range);
        compiler.assert_valid_zero_check(
            curr.count_in_range,
            &upper_limb_sum,
            &curr.upper_limbs_sum_inv,
        );

        // binary check log256 flags
        for i in 0..4 {
            compiler.assert_boolean(&curr.log256_flags[i]);
        }
        // binary check their sum
        let log256_flag_sum = compiler.sum((0..4).map(|i| curr.log256_flags[i]));
        compiler.assert_boolean(&log256_flag_sum);

        // unpack log256 flags
        let len_len_is_0 = compiler.sub(&one, &log256_flag_sum);
        let len_len_is_1 = &curr.log256_flags[0];
        let len_len_is_2 = &curr.log256_flags[1];
        let len_len_is_3 = &curr.log256_flags[2];
        let len_len_is_4 = &curr.log256_flags[3];

        /* TODO:
        let is_calculating_prefix = opcode_is_str_prefix + opcode_is_list_prefix;
        // check len lens
        // if len len is 0, then count must be zero when calculating a prefix
        compiler.assert_zero_product(curr.count, len_len_is_0 * is_calculating_prefix);
        // if len len is 0, then every limb must be zero
        for i in 1..5 {
            compiler.assert_zero_product(curr.rc_u8s[i], len_len_is_0 * is_calculating_prefix);
        }
        // if len len is 1, then every limb but the least-significant one must be zero when calculating a prefix
        // AND the least-significant limb must be nonzero (checked via inverse)
        for i in 1..4 {
            compiler.assert_zero_product(curr.rc_u8s[i + 1], len_len_is_1 * is_calculating_prefix);
        }
        compiler.assert_zero_product(one - curr.rc_u8s[1] * curr.top_byte_inv, len_len_is_1);

        // if len len is 2, then the upper two limbs must be zero when calculating a prefix
        // AND the second-least-significant limb must be nonzero (checked via inverse)
        for i in 2..4 {
            compiler.assert_zero_product(curr.rc_u8s[i + 1], len_len_is_2 * is_calculating_prefix);
        }
        compiler.assert_zero_product(one - curr.rc_u8s[2] * curr.top_byte_inv, len_len_is_2);

        // if len len is 3, then the most significant limb must be zero
        // AND the second-most-significant limb must be nonzero (checked via inverse)
        compiler.assert_zero_product(curr.rc_u8s[4], len_len_is_3 * is_calculating_prefix);
        compiler.assert_zero_product(one - curr.rc_u8s[3] * curr.top_byte_inv, len_len_is_3);

        // if len len is 4, then the most significant limb must be nonzero
        compiler.assert_zero_product(one - curr.rc_u8s[4] * curr.top_byte_inv, len_len_is_4);

        // set tmps for str_prefix and list_prefix
        compiler.assert_zero(
            curr.prefix_case_tmp_3 - opcode_is_str_prefix * prefix_string_out_of_range_case,
        );
        */

        // StrPrefix =====================================================================

        /* TODO:
        // check that count = content_len
        compiler
            .assert_zero_product(curr.count - curr.content_len, opcode_is_str_prefix);
        // prefix len cases:
        // if count is 1 and first byte in range 0..127: no prefix
        compiler.assert_zero_product(curr.count - one, curr.count_is_one);
        compiler.assert_zero_product_transition(
            one - next.count_is_one,
            next_opcode_is_str_prefix * next_prefix_single_byte_case,
        );
        let first_byte = curr.input_memory[0][1];
        compiler.assert_zero_product_transition(
            next.rc_127 - first_byte,
            next_opcode_is_str_prefix * next_prefix_single_byte_case,
        );
        // to prevent the prover from claiming it's the next case (not single byte) when it's actually this case
        // we place first_byte - 127 into the rc'd cell if the prover claims it's the next case AND count is 1
        compiler.constraint(
            curr.prefix_case_tmp
                - opcode_is_str_prefix * prefix_string_in_range_case * curr.count_is_one,
        );
        compiler.assert_zero_product_transition(
            next.rc_127 - (first_byte - FE::from_canonical_u8(0x80)),
            curr.prefix_case_tmp,
        );
        // check count_is_1 via inverse
        let count_minus_one = curr.count - one;
        let prod = count_minus_one * curr.count_minus_one_inv;
        // if count_is_one, then count_minus_1 = 0 and count_minus_1_inv = 0
        compiler.assert_zero_product(count_minus_one, curr.count_is_one);
        compiler.assert_zero_product(curr.count_minus_one_inv, curr.count_is_one);
        // if not count_is_one, then prod = 1
        compiler.assert_zero_product(one - prod, one - curr.count_is_one);

        // else if count <=55 then prefix is 1 byte with value 0x80 + count
        // ensure count is in range if this mode is selected
        compiler.assert_zero_product(
            one - curr.count_in_range,
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        // set stack filters
        compiler.assert_zero_product(
            one - curr.output_stack_filters[4],
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[3],
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[2],
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[1],
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[0],
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        // push prefix to output stack
        let prefix = curr.count + FE::from_canonical_u8(0x80);
        compiler.assert_zero_product(
            curr.output_stack[4][1] - prefix,
            opcode_is_str_prefix * prefix_string_in_range_case,
        );

        // else if count >55 and log256_is_1 then prefix is 2 bytes with value 0xB8, count. log256_is_2 => 3 bytes, etc
        // ensure count is not in range if this mode is selected
        compiler.assert_zero_product(curr.count_in_range, curr.prefix_case_tmp_3);
        // ensure log256_is_1 if this mode is selected
        compiler.assert_zero_product(one - len_len_is_1, curr.prefix_case_tmp_3);
        // set stack filters
        compiler.assert_zero_product(
            one - curr.output_stack_filters[4],
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            one - curr.output_stack_filters[3],
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[2] - len_len_is_2 - len_len_is_3 - len_len_is_4,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[1] - len_len_is_3 - len_len_is_4,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[0] - len_len_is_4,
            curr.prefix_case_tmp_3,
        );
        // push prefix to output stack
        let first_byte = len_len_is_1 * FE::from_canonical_u8(0xB8)
            + len_len_is_2 * FE::from_canonical_u8(0xB9)
            + len_len_is_3 * FE::from_canonical_u8(0xBA)
            + len_len_is_4 * FE::from_canonical_u8(0xBB);
        let second_byte = len_len_is_1 * curr.rc_u8s[1]
            + len_len_is_2 * curr.rc_u8s[2]
            + len_len_is_3 * curr.rc_u8s[3]
            + len_len_is_4 * curr.rc_u8s[4];
        let third_byte = len_len_is_2 * curr.rc_u8s[1]
            + len_len_is_3 * curr.rc_u8s[2]
            + len_len_is_4 * curr.rc_u8s[3];
        let fourth_byte = len_len_is_3 * curr.rc_u8s[1] + len_len_is_4 * curr.rc_u8s[2];
        let fifth_byte = len_len_is_4 * curr.rc_u8s[1];
        compiler.assert_zero_product(
            curr.output_stack[0][1] - fifth_byte,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack[1][1] - fourth_byte,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack[2][1] - third_byte,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack[3][1] - second_byte,
            curr.prefix_case_tmp_3,
        );
        compiler.assert_zero_product(
            curr.output_stack[4][1] - first_byte,
            curr.prefix_case_tmp_3,
        );

        // increment count by number of bytes in prefix
        // since we need to distinguish between the single byte case and the <=55 case, we appyl this constraint via the "next" row
        let prefix_len = len_len_is_1 * FE::from_canonical_u8(2)
            + len_len_is_2 * FE::from_canonical_u8(3)
            + len_len_is_3 * FE::from_canonical_u8(4)
            + len_len_is_4 * FE::from_canonical_u8(5);
        let next_prefix_string_in_range_case = next.prefix_case_flags[0];
        compiler.constraint_transition(
            next.prefix_case_tmp_2
                - next_opcode_is_str_prefix
                    * (one - next_prefix_single_byte_case)
                    * (one - next_prefix_string_in_range_case),
        );
        compiler.assert_zero_product_transition(
            next.count - (curr.count + prefix_len),
            curr.prefix_case_tmp_2,
        );
        compiler.assert_zero_product_transition(
            next.count - (curr.count + one),
            opcode_is_str_prefix * prefix_string_in_range_case,
        );
        // don't change count in single byte case
        */

        // ListPrefix ====================================================================

        // if count is <= 55 then prefix is 0xC0 + count
        // set stack filters

        compiler
            .when_all([opcode_is_list_prefix, prefix_list_in_range_case])
            .assert_eq(&curr.count_in_range, &one)
            .assert_eq(&curr.output_stack_filters[4], &one)
            .assert_eq(&curr.output_stack_filters[3], &zero)
            .assert_eq(&curr.output_stack_filters[2], &zero)
            .assert_eq(&curr.output_stack_filters[1], &zero)
            .assert_eq(&curr.output_stack_filters[0], &zero);

        /* TODO:
        // push prefix to output stack
        let prefix = curr.count + FE::from_canonical_u8(0xC0);
        compiler.assert_zero_product(
            curr.output_stack[4][1] - prefix,
            opcode_is_list_prefix * prefix_list_in_range_case,
        );

        // else if count >55 and log256_is_1 then prefix is 2 bytes with value 0xF8, count. log256_is_2 => 3 bytes, etc
        // ensure count not in range if this mode is selected
        compiler.assert_zero_product(curr.count_in_range, curr.prefix_case_tmp_4);
        // set stack filters
        compiler.assert_zero_product(
            one - curr.output_stack_filters[4],
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            one - curr.output_stack_filters[3],
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[2] - len_len_is_2 - len_len_is_3 - len_len_is_4,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[1] - len_len_is_3 - len_len_is_4,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[0] - len_len_is_4,
            curr.prefix_case_tmp_4,
        );
        // push prefix to output stack
        let first_byte = len_len_is_1 * FE::from_canonical_u8(0xF8)
            + len_len_is_2 * FE::from_canonical_u8(0xF9)
            + len_len_is_3 * FE::from_canonical_u8(0xFA)
            + len_len_is_4 * FE::from_canonical_u8(0xFB);
        compiler.assert_zero_product(
            curr.output_stack[0][1] - fifth_byte,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack[1][1] - fourth_byte,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack[2][1] - third_byte,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack[3][1] - second_byte,
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product(
            curr.output_stack[4][1] - first_byte,
            curr.prefix_case_tmp_4,
        );

        // increment count by number of bytes in prefix
        compiler.assert_zero_product_transition(
            next.count - (curr.count + prefix_len),
            curr.prefix_case_tmp_4,
        );
        compiler.assert_zero_product_transition(
            next.count - (curr.count + one),
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        // don't change count in single byte case
        */

        // EndEntry ======================================================================

        // binary check depth_is_zero
        // check depth_is_zero via inv check
        // if depth_is_zero, then both depth and depth_inv must be zero
        // otherwise, prod must be 1
        compiler.assert_boolean(&curr.depth_is_zero);
        compiler.assert_valid_zero_check(curr.depth_is_zero, &curr.depth, &curr.depth_inv);

        // if depth is zero, push count and op_id to the stack
        compiler
            .when(is_end_entry_and_depth_is_zero)
            .assert_eq(&curr.count, &curr.output_stack[0][1])
            .assert_eq(&curr.op_id, &curr.output_stack[1][1]);

        // increment op_id
        compiler
            .when(is_end_entry_and_depth_is_zero)
            .assert_increments_by(&curr.op_id, &next.op_id, &one)
            .otherwise()
            .assert_eq_transition(&curr.op_id, &next.op_id);

        // binary check is_last
        compiler.assert_boolean(&curr.is_last);

        /* TODO:
        // if depth is not zero, transition to Return
        // else if depth is is_last, then transition to Halt
        // else, set pc to next and transition to NewEntry
        compiler.assert_eq(curr.end_entry_tmp, is_end_entry_and_depth_is_zero);
        compiler.assert_zero_product_transition(
            one - next_opcode_is_return,
            (one - curr.depth_is_zero) * opcode_is_end_entry,
        );
        compiler.assert_zero_product_transition(
            one - next_opcode_is_halt,
            curr.end_entry_tmp * curr.is_last,
        );
        compiler.assert_zero_product_transition(
            next.pc - curr.next,
            curr.end_entry_tmp * (one - curr.is_last),
        );
        */

        // Halt ==========================================================================

        // nothing should change during halt
        // EXCEPT for the first halt row, during which we set the output_stack[0] = curr_output_stack.len() - 1.
        // so that the consumer can consume the output as a "stack" and be guaranteed that the "len" is set correctly
        let next_is_first_halt = {
            let one_minus_opcode_is_halt = compiler.sub(&one, opcode_is_halt);
            compiler.mul(&one_minus_opcode_is_halt, next_opcode_is_halt)
        };

        compiler
            .when(next_is_first_halt)
            .assert_eq_transition(&next.output_stack_filters[0], &one)
            .assert_zero_transition(&next.output_stack[0][0])
            .assert_eq_transition(&next.output_stack[0][1], &curr.output_stack[4][0]);

        compiler
            .when(*opcode_is_halt)
            .assert_eq_transition(&curr.op_id, &next.op_id)
            .assert_eq_transition(&curr.pc, &next.pc)
            .assert_eq_transition(&curr.count, &next.count)
            .assert_eq_transition(&curr.content_len, &next.content_len)
            .assert_eq_transition(&curr.list_count, &next.list_count)
            .assert_eq_transition(&curr.depth, &next.depth)
            .assert_eq_transition(&curr.next, &next.next);

        for i in 0..8 {
            compiler
                .when(*opcode_is_halt)
                .assert_eq_transition(&curr.opcode[i], &next.opcode[i]);
        }

        /*
        // base-56 decomp
        let recomp = (0..6).rev().fold(P::ZEROS, |acc, i| {
            acc * FE::from_canonical_u8(56) + curr.rc_56_limbs[i]
        });
        compiler.constraint(curr.count - recomp);
        for (i, j) in rc_56_permuted_cols().zip(lut_56_permuted_cols()) {
            eval_lookups(&vars, compiler, i, j);
        }

        // byte decomp
        let recomp = (0..4)
            .map(|i| curr.rc_u8s[i + 1] * FE::from_canonical_u64(1 << (i * 8)))
            .sum::<P>();
        compiler.constraint(curr.count - recomp);
        for (i, j) in rc_u8_permuted_cols().zip(lut_u8_permuted_cols()) {
            eval_lookups(&vars, compiler, i, j);
        }

        // 7-bit (127) lookup
        eval_lookups(
            &vars,
            compiler,
            rc_127_permuted_col(),
            lut_127_permuted_col(),
        );
        */

        // build luts

        // counters start at 0
        compiler.assert_zero_first_row(&curr.count_127);
        compiler.assert_zero_first_row(&curr.count_u8);
        compiler.assert_zero_first_row(&curr.count_56);

        // if count_127_is_127, set it to 0, otherwise increment it
        compiler
            .when(curr.count_127_is_127)
            .assert_zero_transition(&next.count_127)
            .otherwise()
            .assert_increments_by(&curr.count_127, &next.count_127, &one);

        // if count_u8_is_255, set it to 0, otherwise increment it
        compiler
            .when(curr.count_u8_is_255)
            .assert_zero_transition(&next.count_u8)
            .otherwise()
            .assert_increments_by(&curr.count_u8, &next.count_u8, &one);

        // if count_56_is_55, set it to 0, otherwise increment it
        compiler
            .when(curr.count_56_is_55)
            .assert_zero_transition(&next.count_56)
            .otherwise()
            .assert_increments_by(&curr.count_56, &next.count_56, &one);

        /* TODO:
        // binary check count_127_is_127
        // check count_127_is_127 via inv
        // if count_127_is_127 is set, then both count_127_minus_127 and its inv must be zero
        // otherwise, prod must be one
        let count_127_minus_127 = curr.count_127 - FE::from_canonical_u64(127);
        compiler.assert_boolean(&curr.count_127_is_127);
        compiler.assert_valid_zero_check(
            curr.count_127_is_127,
            count_127_minus_127,
            &curr.count_127_minus_127_inv,
        );
        */

        /* TODO:
        // binary count_u8_is_255
        // check count_u8_is_255 via inv
        // if count_u8_is_255 is set, then both count_u8_minus_255 and its inv must be zero
        // otherwise, prod must be one
        let count_u8_minus_255 = curr.count_u8 - FE::from_canonical_u8(255);
        compiler.assert_boolean(&curr.count_u8_is_255);
        compiler.assert_valid_zero_check(
            curr.count_u8_is_255,
            &count_u8_minus_255,
            &curr.count_u8_minus_255_inv,
        );
        */

        /* TODO:
        // binary check count_56_is_55
        // check count_56_is_55 via inv
        // if count_56_is_55 is set, then both count_56_minus_55 and its inv must be zero
        // otherwise, prod must be one
        let count_56_minus_55 = curr.count_56 - FE::from_canonical_u8(55);
        compiler.assert_boolean(&curr.count_56_is_55);
        compiler.assert_valid_zero_check(
            curr.count_56_is_55,
            &count_56_minus_55,
            &curr.count_56_minus_55_inv,
        );
        */

        // ensure things that shouldn't change stay the same

        // NewEntry
        // depth should stay the same
        compiler
            .when(opcode_is_new_entry)
            .assert_eq(&curr.depth, &next.depth);

        // List
        // count should stay the same
        // content_len should stay the same
        // depth should stay the same
        // next should stay the same
        // is_last should stay the same
        compiler
            .when(*opcode_is_list)
            .assert_eq(&curr.count, &next.count)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.depth, &next.depth)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last);

        // StrPush
        // content_len should tsay the same
        // depth should stay the same
        // list_count should stay the same
        // next should stay the same
        // is_last should stay the same
        compiler
            .when(*opcode_is_str_push)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.depth, &next.depth)
            .assert_eq(&curr.list_count, &next.list_count)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last);

        // ListPrefix
        // pc should stay the same
        // content_len should stay the same
        // depth should stay the same
        // next should stay the same
        // is_last should stay the same
        // list_count should stay the same
        compiler
            .when(*opcode_is_list_prefix)
            .assert_eq(&curr.pc, &next.pc)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.depth, &next.depth)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last)
            .assert_eq(&curr.list_count, &next.list_count);

        // StrPrefix
        // pc should stay the same
        // content_len should stay the same
        // depth should stay the same
        // next should stay the same
        // is_last should stay the same
        // list_count should stay the same
        compiler
            .when(*opcode_is_str_prefix)
            .assert_eq(&curr.pc, &next.pc)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.depth, &next.depth)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last)
            .assert_eq(&curr.list_count, &next.list_count);

        // Recurse
        // content_len should stay the same
        // list_count should stay the same
        // next should stay the same
        // is_last should stay the same
        compiler
            .when(*opcode_is_recurse)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.list_count, &next.list_count)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last);

        // Return
        // content_len should stay the same
        // next should stay the same
        // is_last should stay the same
        compiler
            .when(*opcode_is_return)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last);

        // EndEntry
        // content_len should stay the same
        // count should stay the same
        // next should stay the same
        // is_last should stay the same
        // depth should stay the same
        // list_count should stay the same
        compiler
            .when(*opcode_is_end_entry)
            .assert_eq(&curr.content_len, &next.content_len)
            .assert_eq(&curr.count, &next.count)
            .assert_eq(&curr.next, &next.next)
            .assert_eq(&curr.is_last, &next.is_last)
            .assert_eq(&curr.depth, &next.depth)
            .assert_eq(&curr.list_count, &next.list_count);

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
