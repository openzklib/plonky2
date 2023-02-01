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
            compiler.mul(opcode_is_end_entry, curr.depth_is_zero);
        let set_filter_0 = compiler.add(opcode_is_str_push, is_end_entry_and_depth_is_zero);
        let set_filter_1 = is_end_entry_and_depth_is_zero;
        compiler.assert_zero_product(one - curr.output_stack_filters[0], set_filter_0);
        compiler.assert_zero_product(one - curr.output_stack_filters[1], set_filter_1);
        // turn off other output stack filters for all non-prefix opcodes
        let opcode_is_not_prefix = one - opcode_is_str_prefix - opcode_is_list_prefix;
        compiler.assert_zero_product(&curr.output_stack_filters[2], opcode_is_not_prefix);
        compiler.assert_zero_product(&curr.output_stack_filters[3], opcode_is_not_prefix);
        compiler.assert_zero_product(&curr.output_stack_filters[4], opcode_is_not_prefix);
        */

        // check output "stack" addresses start at 0. It is incremented before written, so address 0
        // won't be checked until the halt state below
        compiler.assert_zero_first_row(&curr.output_stack[0][0]);

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
        compiler.assert_zero_product_transition(
            curr.input_memory[3][0] - (curr.pc + offset),
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            curr.input_memory[3][1] - next.op_id,
            opcode_is_new_entry,
        );
        // next content_len = [pc + 4]
        offset += one;
        compiler.assert_zero_product_transition(
            curr.input_memory[4][0] - (curr.pc + offset),
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            curr.input_memory[4][1] - next.content_len,
            opcode_is_new_entry,
        );
        */

        /* TODO:
        // set next pc to pc + 5
        offset += one;
        compiler.assert_zero_product_transition(
            next.pc - (curr.pc + offset),
            opcode_is_new_entry,
        );
        // next count = 0
        compiler.assert_zero_product_transition(next.count, opcode_is_new_entry);
        // next list_count = 0
        compiler.assert_zero_product_transition(next.list_count, opcode_is_new_entry);

        // binary check is_list
        compiler.assert_zero_product((one - is_list) * is_list, opcode_is_new_entry);
        // if is_list and content len read from memory is 0, then transition to ListPrefix
        // else if is_list, transition to List
        // else if not is_list and content len is zero, transition to StrPrefix
        // else transition to StrPush
        let is_list_and_content_len_is_zero = is_list * next.content_len_is_zero;
        let is_list_and_content_len_is_nonzero = is_list * (one - next.content_len_is_zero);
        let is_not_list_and_content_len_is_zero =
            (one - is_list) * next.content_len_is_zero;
        let is_not_list_and_content_len_is_nonzero =
            (one - is_list) * (one - next.content_len_is_zero);
        compiler.assert_zero_product_transition(
            next_opcode_is_list_prefix - is_list_and_content_len_is_zero,
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_list - is_list_and_content_len_is_nonzero,
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_str_prefix - is_not_list_and_content_len_is_zero,
            opcode_is_new_entry,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_str_push - is_not_list_and_content_len_is_nonzero,
            opcode_is_new_entry,
        );

        // check content_len_is_zero via content_len_inv
        let prod = curr.content_len * curr.content_len_inv;
        // binary check content_len_is_zero
        compiler
            .constraint((one - curr.content_len_is_zero) * curr.content_len_is_zero);
        // if content_len_is_zero is set, then content_len and content_len_inv must both be zero
        compiler.assert_zero_product(curr.content_len, curr.content_len_is_zero);
        compiler.assert_zero_product(curr.content_len_inv, curr.content_len_is_zero);

        // if content_len_is_zero is not set, then prod must be 1
        compiler.assert_zero_product(one - prod, one - curr.content_len_is_zero);
        */

        // List ==========================================================================

        /* TODO:
        // push current list count onto the stack
        compiler.assert_zero_product(curr.call_stack[0][0] - stack_push, opcode_is_list);
        compiler.assert_zero_product(
            curr.call_stack[0][1] - curr.list_count,
            opcode_is_list,
        );
        // read child addr from the table, push it on the stack
        compiler.assert_zero_product(curr.input_memory[0][0] - curr.pc, opcode_is_list);
        let child_addr = curr.input_memory[0][1];
        compiler.assert_zero_product(curr.call_stack[1][0] - stack_push, opcode_is_list);
        compiler.assert_zero_product(curr.call_stack[1][1] - child_addr, opcode_is_list);

        // increment pc
        compiler.assert_zero_product_transition(next.pc - (curr.pc + one), opcode_is_list);
        // increment list count
        compiler.assert_zero_product_transition(
            next.list_count - (curr.list_count + one),
            opcode_is_list,
        );

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

        // check content_len_minus_list_count_is_zero via content_len_minus_list_count_inv
        let content_len_minus_list_count = curr.content_len - curr.list_count;
        let prod = content_len_minus_list_count * curr.content_len_minus_list_count_inv;
        // binary check content_len_minus_list_count_is_zero
        compiler.assert_zero_product(
            (one - curr.content_len_minus_list_count_is_zero),
            curr.content_len_minus_list_count_is_zero,
        );
        // if content_len_minus_list_count_is_zero is set, then content_len_minus_list_count and
        // content_len_minus_list_count_inv must both be zero
        compiler.assert_zero_product(
            content_len_minus_list_count,
            curr.content_len_minus_list_count_is_zero,
        );
        compiler.assert_zero_product(
            curr.content_len_minus_list_count_inv,
            curr.content_len_minus_list_count_is_zero,
        );
        // otherwise, prod must be 1
        compiler.assert_zero_product(
            one - prod,
            one - curr.content_len_minus_list_count_is_zero,
        );
        */

        // Recurse =======================================================================

        /* TODO:
        // pop the "dst" address to jump to from the call stack
        compiler.assert_zero_product(curr.call_stack[0][0] - stack_pop, opcode_is_recurse);
        let dst = curr.call_stack[0][1];

        // push count to the call stack
        compiler.assert_zero_product(curr.call_stack[1][0] - stack_push, opcode_is_recurse);
        compiler.assert_zero_product(curr.call_stack[1][1] - curr.count, opcode_is_recurse);

        // push pc to the call stack
        compiler.assert_zero_product(curr.call_stack[2][0] - stack_push, opcode_is_recurse);
        compiler.assert_zero_product(curr.call_stack[2][1] - curr.pc, opcode_is_recurse);

        // set next pc to dst
        compiler.assert_zero_product_transition(next.pc - dst, opcode_is_recurse);
        // increment depth
        compiler.assert_zero_product_transition(next.depth - (curr.depth + one), opcode_is_recurse);
        // transition to NewEntry
        compiler.assert_zero_product_transition(one - next_opcode_is_new_entry, opcode_is_recurse);
        */

        // Return ========================================================================

        /* TODO:
        // pop "old_pc" from the call stack
        compiler.assert_zero_product(curr.call_stack[0][0] - stack_pop, opcode_is_return);
        let old_pc = curr.call_stack[0][1];

        // pop "old count" from the call stack
        compiler.assert_zero_product(curr.call_stack[1][0] - stack_pop, opcode_is_return);
        let old_count = curr.call_stack[1][1];

        // pop "old list count" from the call stack
        compiler.assert_zero_product(curr.call_stack[2][0] - stack_pop, opcode_is_return);
        let old_list_count = curr.call_stack[2][1];

        // add "old count" to count
        compiler.assert_zero_product_transition(
            next.count - (curr.count + old_count),
            opcode_is_return,
        );
        // set list_count to old_list_count
        compiler
            .assert_zero_product_transition(next.list_count - old_list_count, opcode_is_return);
        // set pc to old_pc
        compiler.assert_zero_product_transition(next.pc - old_pc, opcode_is_return);
        // decrement depth
        compiler.assert_zero_product_transition(
            next.depth - (curr.depth - one),
            opcode_is_return,
        );

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

        // check list_count_is_zero via list_count_inv
        let list_count = curr.list_count;
        let prod = list_count * curr.list_count_inv;
        // if list_count_is_zero is set, then list_count and list_count_inv must both be zero
        compiler.assert_zero_product(list_count, curr.list_count_is_zero);
        compiler.assert_zero_product(curr.list_count_inv, curr.list_count_is_zero);
        // otherwise, prod must be 1
        compiler.assert_zero_product(one - prod, one - curr.list_count_is_zero);
        */

        // StrPush =======================================================================

        /* TODO:
        // read val from input_memory at pc
        compiler.assert_zero_product(
            curr.input_memory[0][0] - curr.pc,
            opcode_is_str_push,
        );
        let val = curr.input_memory[0][1];
        // range check val to be a u8 by copying it into a range-checked cell
        compiler.assert_zero_product(curr.rc_u8s[0] - val, opcode_is_str_push);
        // increment pc
        compiler.assert_zero_product(next.pc - (curr.pc + one), opcode_is_str_push);
        // push val to output stack
        compiler.assert_zero_product(curr.output_stack[0][1] - val, opcode_is_str_push);
        // increment count
        compiler.assert_zero_product_transition(
            next.count - (curr.count + one),
            opcode_is_str_push,
        );
        // if content_len = next row's count (i.e. content_len_minus_count_is_zero), then transition to StrPrefix
        // otherwise, transition to StrPush
        compiler.assert_zero_product_transition(
            next_opcode_is_str_prefix - next.content_len_minus_count_is_zero,
            opcode_is_str_push,
        );
        compiler.assert_zero_product_transition(
            next_opcode_is_str_push - (one - next.content_len_minus_count_is_zero),
            opcode_is_str_push,
        );

        // check content_len_minus_count_is_zero via content_len_minus_count_inv
        let content_len_minus_count = curr.content_len - curr.count;
        let prod = content_len_minus_count * curr.content_len_minus_count_inv;
        // binary check content_len_minus_count_is_zero
        compiler.constraint(
            curr.content_len_minus_count_is_zero
                * (one - curr.content_len_minus_count_is_zero),
        );
        // if content_len_minus_count_is_zero is set, then content_len_minus_count and content_len_minus_count_inv must both be zero
        compiler.assert_zero_product(
            content_len_minus_count,
            curr.content_len_minus_count_is_zero,
        );
        compiler.assert_zero_product(
            curr.content_len_minus_count_inv,
            curr.content_len_minus_count_is_zero,
        );
        // otherwise, prod must be 1
        compiler.assert_zero_product(
            one - prod,
            one - curr.content_len_minus_count_is_zero,
        );

        // prefix case flags
        // binary check flags
        for i in 0..4 {
            compiler.constraint(
                (one - curr.prefix_case_flags[i]) * curr.prefix_case_flags[i],
            );
        }
        // binary check their sum
        let prefix_case_flag_sum = (0..4).map(|i| curr.prefix_case_flags[i]).sum::<P>();
        let next_prefix_case_flag_sum = (0..4).map(|i| next.prefix_case_flags[i]).sum::<P>();
        compiler.constraint((one - prefix_case_flag_sum) * prefix_case_flag_sum);

        // unpack
        let next_prefix_single_byte_case = one - next_prefix_case_flag_sum;
        let prefix_string_in_range_case = curr.prefix_case_flags[0];
        let prefix_string_out_of_range_case = curr.prefix_case_flags[1];
        let prefix_list_in_range_case = curr.prefix_case_flags[2];

        // check if count <= 55 using base-56 decomp
        let upper_limb_sum = (1..6).map(|i| curr.rc_56_limbs[i]).sum::<P>();
        let prod = upper_limb_sum * curr.upper_limbs_sum_inv;
        compiler.constraint((one - curr.count_in_range) * curr.count_in_range);
        compiler.assert_zero_product(upper_limb_sum, curr.count_in_range);
        compiler.assert_zero_product(curr.upper_limbs_sum_inv, curr.count_in_range);
        compiler.assert_zero_product(one - prod, one - curr.count_in_range);

        // binary check log256 flags
        for i in 0..4 {
            compiler
                .constraint((one - curr.log256_flags[i]) * curr.log256_flags[i]);
        }
        // binary check their sum
        let log256_flag_sum = (0..4).map(|i| curr.log256_flags[i]).sum::<P>();
        compiler.constraint((one - log256_flag_sum) * log256_flag_sum);

        // unpack log256 flags
        let len_len_is_0 = one - log256_flag_sum;
        let len_len_is_1 = curr.log256_flags[0];
        let len_len_is_2 = curr.log256_flags[1];
        let len_len_is_3 = curr.log256_flags[2];
        let len_len_is_4 = curr.log256_flags[3];

        let is_calculating_prefix = opcode_is_str_prefix + opcode_is_list_prefix;
        // check len lens
        // if len len is 0, then count must be zero when calculating a prefix
        compiler.assert_zero_product(curr.count, len_len_is_0 * is_calculating_prefix);
        // if len len is 0, then every limb must be zero
        for i in 1..5 {
            compiler
                .assert_zero_product(curr.rc_u8s[i], len_len_is_0 * is_calculating_prefix);
        }
        // if len len is 1, then every limb but the least-significant one must be zero when calculating a prefix
        // AND the least-significant limb must be nonzero (checked via inverse)
        for i in 1..4 {
            compiler
                .assert_zero_product(curr.rc_u8s[i + 1], len_len_is_1 * is_calculating_prefix);
        }
        compiler.assert_zero_product(
            one - curr.rc_u8s[1] * curr.top_byte_inv,
            len_len_is_1,
        );

        // if len len is 2, then the upper two limbs must be zero when calculating a prefix
        // AND the second-least-significant limb must be nonzero (checked via inverse)
        for i in 2..4 {
            compiler
                .assert_zero_product(curr.rc_u8s[i + 1], len_len_is_2 * is_calculating_prefix);
        }
        compiler.assert_zero_product(
            one - curr.rc_u8s[2] * curr.top_byte_inv,
            len_len_is_2,
        );

        // if len len is 3, then the most significant limb must be zero
        // AND the second-most-significant limb must be nonzero (checked via inverse)
        compiler.assert_zero_product(curr.rc_u8s[4], len_len_is_3 * is_calculating_prefix);
        compiler.assert_zero_product(
            one - curr.rc_u8s[3] * curr.top_byte_inv,
            len_len_is_3,
        );

        // if len len is 4, then the most significant limb must be nonzero
        compiler.assert_zero_product(
            one - curr.rc_u8s[4] * curr.top_byte_inv,
            len_len_is_4,
        );

        // set tmps for str_prefix and list_prefix
        compiler.constraint(
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

        /* TODO:
        // if count is <= 55 then prefix is 0xC0 + count
        compiler.assert_zero_product(
            one - curr.count_in_range,
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        // set stack filters
        compiler.assert_zero_product(
            one - curr.output_stack_filters[4],
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[3],
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[2],
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[1],
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
        compiler.assert_zero_product(
            curr.output_stack_filters[0],
            opcode_is_list_prefix * prefix_list_in_range_case,
        );
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

        /* TODO:
        // check depth_is_zero via inv check
        // binary check depth_is_zero
        compiler.constraint((one - curr.depth_is_zero) * curr.depth_is_zero);
        let prod = curr.depth * curr.depth_inv;
        // if depth_is_zero, then both depth and depth_inv must be zero
        compiler.assert_zero_product(curr.depth, curr.depth_is_zero);
        compiler.assert_zero_product(curr.depth_inv, curr.depth_is_zero);
        // otherwise, prod must be 1
        compiler.assert_zero_product(one - prod, one - curr.depth_is_zero);

        // if depth is zero, push count and op_id to the stack
        compiler.assert_zero_product(
            curr.output_stack[0][1] - curr.count,
            is_end_entry_and_depth_is_zero,
        );
        compiler.assert_zero_product(
            curr.output_stack[1][1] - curr.op_id,
            is_end_entry_and_depth_is_zero,
        );
        // increment op_id
        compiler.assert_zero_product_transition(
            next.op_id - (curr.op_id + one),
            is_end_entry_and_depth_is_zero,
        );
        // otherwisem, op_id should stay the same
        compiler.assert_zero_product_transition(
            next.op_id - curr.op_id,
            one - is_end_entry_and_depth_is_zero,
        );
        // binary check is_last
        compiler.constraint((one - curr.is_last) * curr.is_last);

        // if depth is not zero, transition to Return
        // else if depth is is_last, then transition to Halt
        // else, set pc to next and transition to NewEntry
        compiler.constraint(curr.end_entry_tmp - is_end_entry_and_depth_is_zero);
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

        /* TODO:
        // nothing should change during halt
        // EXCEPT for the first halt row, during which we set the output_stack[0] = curr_output_stack.len() - 1. so that the consumer can consume the output as a "stack"
        // and be guaranteed that the "len" is set correctly
        let next_is_first_halt = (one - opcode_is_halt) * next_opcode_is_halt;
        compiler.assert_zero_product_transition(
            one - next.output_stack_filters[0],
            next_is_first_halt,
        );
        compiler
            .assert_zero_product_transition(next.output_stack[0][0], next_is_first_halt);
        compiler.assert_zero_product_transition(
            next.output_stack[0][1] - curr.output_stack[4][0],
            next_is_first_halt,
        );

        compiler
            .assert_zero_product_transition(curr.op_id - next.op_id, opcode_is_halt);
        compiler.assert_zero_product_transition(curr.pc - next.pc, opcode_is_halt);
        compiler
            .assert_zero_product_transition(curr.count - next.count, opcode_is_halt);
        compiler.assert_zero_product_transition(
            curr.content_len - next.content_len,
            opcode_is_halt,
        );
        compiler.assert_zero_product_transition(
            curr.list_count - next.list_count,
            opcode_is_halt,
        );
        compiler
            .assert_zero_product_transition(curr.depth - next.depth, opcode_is_halt);
        compiler.assert_zero_product_transition(curr.next - next.next, opcode_is_halt);
        for i in 0..8 {
            compiler.assert_zero_product_transition(
                curr.opcode[i] - next.opcode[i],
                opcode_is_halt,
            );
        }

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

        // build luts

        // counters start at 0
        compiler.assert_zero_first_row(curr.count_127);
        compiler.assert_zero_first_row(curr.count_u8);
        compiler.assert_zero_first_row(curr.count_56);

        // if count_127_is_127, set it to 0, otherwise increment it
        compiler.assert_zero_product_transition(next.count_127, curr.count_127_is_127);
        compiler.assert_zero_product_transition(
            next.count_127 - curr.count_127 - one,
            one - curr.count_127_is_127,
        );

        // if count_u8_is_255, set it to 0, otherwise increment it
        compiler.assert_zero_product_transition(next.count_u8, curr.count_u8_is_255);
        compiler.assert_zero_product_transition(
            next.count_u8 - curr.count_u8 - one,
            one - curr.count_u8_is_255,
        );

        // if count_56_is_55, set it to 0, otherwise increment it
        compiler.assert_zero_product_transition(next.count_56, curr.count_56_is_55);
        compiler.assert_zero_product_transition(
            next.count_56 - curr.count_56 - one,
            one - curr.count_56_is_55,
        );

        // check count_127_is_127 via inv
        let count_127_minus_127 = curr.count_127 - FE::from_canonical_u64(127);
        let prod = count_127_minus_127 * curr.count_127_minus_127_inv;
        // binary check count_127_is_127
        compiler.constraint((one - curr.count_127_is_127) * curr.count_127_is_127);

        // if count_127_is_127 is set, then both count_127_minus_127 and its inv must be zero
        compiler.assert_zero_product(count_127_minus_127, curr.count_127_is_127);
        compiler
            .assert_zero_product(curr.count_127_minus_127_inv, curr.count_127_is_127);
        // otherwise, prod must be one
        compiler.assert_zero_product(one - prod, one - curr.count_127_is_127);

        // check count_u8_is_255 via inv
        let count_u8_minus_255 = curr.count_u8 - FE::from_canonical_u8(255);
        let prod = count_u8_minus_255 * curr.count_u8_minus_255_inv;
        // binary count_u8_is_255
        compiler.constraint((one - curr.count_u8_is_255) * curr.count_u8_is_255);
        // if count_u8_is_255 is set, then both count_u8_minus_255 and its inv must be zero
        compiler.assert_zero_product(count_u8_minus_255, curr.count_u8_is_255);
        compiler.assert_zero_product(curr.count_u8_minus_255_inv, curr.count_u8_is_255);
        // otherwise, prod must be one
        compiler.assert_zero_product(one - prod, one - curr.count_u8_is_255);

        // check count_56_is_55 via inv
        let count_56_minus_55 = curr.count_56 - FE::from_canonical_u8(55);
        let prod = count_56_minus_55 * curr.count_56_minus_55_inv;
        // binary check count_56_is_55
        compiler.constraint((one - curr.count_56_is_55) * curr.count_56_is_55);
        // if count_56_is_55 is set, then both count_56_minus_55 and its inv must be zero
        compiler.assert_zero_product(count_56_minus_55, curr.count_56_is_55);
        compiler.assert_zero_product(curr.count_56_minus_55_inv, curr.count_56_is_55);
        // otherwise, prod must be one
        compiler.assert_zero_product(one - prod, one - curr.count_56_is_55);
        */

        // ensure things that shouldn't change stay the same

        /*
        // NewEntry
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_new_entry);
        */

        /*
        // List
        // count should stay the same
        compiler.assert_zero_product(curr.count - next.count, opcode_is_list);
        // content_len should stay the same
        compiler
            .assert_zero_product(curr.content_len - next.content_len, opcode_is_list);
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_list);
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_list);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_list);
        */

        /*
        // StrPush
        // content_len should tsay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_str_push,
        );
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_str_push);
        // list_count should stay the same
        compiler.assert_zero_product(
            curr.list_count - next.list_count,
            opcode_is_str_push,
        );
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_str_push);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_str_push);
        */

        /*
        // ListPrefix
        // pc should stay the same
        compiler.assert_zero_product(curr.pc - next.pc, opcode_is_list_prefix);
        // content_len should stay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_list_prefix,
        );
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_list_prefix);
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_list_prefix);
        // is_last should stay the same
        compiler
            .assert_zero_product(curr.is_last - next.is_last, opcode_is_list_prefix);
        // list_count should stay the same
        compiler.assert_zero_product(
            curr.list_count - next.list_count,
            opcode_is_list_prefix,
        );
        */

        /*
        // StrPrefix
        // pc should stay the same
        compiler.assert_zero_product(curr.pc - next.pc, opcode_is_str_prefix);
        // content_len should stay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_str_prefix,
        );
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_str_prefix);
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_str_prefix);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_str_prefix);
        // list_count should stay the same
        compiler.assert_zero_product(
            curr.list_count - next.list_count,
            opcode_is_str_prefix,
        );
        */

        /*
        // Recurse
        // content_len should stay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_recurse,
        );
        // list_count should stay the same
        compiler
            .assert_zero_product(curr.list_count - next.list_count, opcode_is_recurse);
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_recurse);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_recurse);
        */

        /*
        // Return
        // content_len should stay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_return,
        );
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_return);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_return);
        */

        /*
        // EndEntry
        // content_len should stay the same
        compiler.assert_zero_product(
            curr.content_len - next.content_len,
            opcode_is_end_entry,
        );
        // count should stay the same
        compiler.assert_zero_product(curr.count - next.count, opcode_is_end_entry);
        // next should stay the same
        compiler.assert_zero_product(curr.next - next.next, opcode_is_end_entry);
        // is_last should stay the same
        compiler.assert_zero_product(curr.is_last - next.is_last, opcode_is_end_entry);
        // depth should stay the same
        compiler.assert_zero_product(curr.depth - next.depth, opcode_is_end_entry);
        // list_count should stay the same
        compiler.assert_zero_product(
            curr.list_count - next.list_count,
            opcode_is_end_entry,
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
