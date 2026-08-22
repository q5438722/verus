#![allow(dead_code, unused_imports, unused_variables, unused_mut)]
// Target-specific Verus implementation harness.
// Target: core::slice::make_ascii_uppercase
// Source: core/src/slice/ascii.rs:173-181
// Source item sha256: 27e449dd46ebb3c67e4e390a7ea84e40a3065861456b65c55bee8f0bf208205f
// Dependency manifest: proof_manifests/064_core_slice_make_ascii_uppercase/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn ascii_is_lowercase(byte: u8) -> bool {
    0x61 <= (byte as int) && (byte as int) <= 0x7a
}

pub open spec fn ascii_upper_byte(byte: u8) -> u8 {
    if ascii_is_lowercase(byte) {
        ((byte as int) - 0x20) as u8
    } else {
        byte
    }
}

pub open spec fn ascii_upper_seq(seq: Seq<u8>) -> Seq<u8> {
    Seq::new(seq.len(), |i: int| ascii_upper_byte(seq[i]))
}

const ASCII_CASE_MASK: u8 = 0b0010_0000;

const fn byte_is_ascii_lowercase(byte: u8) -> (ret: bool)
    ensures
        ret <==> ascii_is_lowercase(byte),
{
    matches!(byte, 0x61u8..=0x7au8)
}

const fn byte_to_ascii_uppercase(byte: u8) -> (ret: u8)
    ensures
        ret == ascii_upper_byte(byte),
{
    let is_lowercase = byte_is_ascii_lowercase(byte);
    let mask = (is_lowercase as u8) * ASCII_CASE_MASK;
    let ret = byte ^ mask;
    proof {
        if is_lowercase {
            assert(0x61u8 <= byte && byte <= 0x7au8);
            assert(mask == ASCII_CASE_MASK);
            assert(
                (0x61u8 <= byte && byte <= 0x7au8)
                    ==> byte ^ 0x20u8 == sub(byte, 0x20u8)
            ) by (bit_vector);
            assert(byte ^ 0x20u8 == sub(byte, 0x20u8));
            assert(sub(byte, 0x20u8) == byte - 0x20u8);
            assert((byte - 0x20u8) as int == (byte as int) - 0x20);
            assert(ret == ((byte as int) - 0x20) as u8);
        } else {
            assert(mask == 0u8);
            assert(byte ^ 0u8 == byte) by (bit_vector);
            assert(ret == byte);
        }
    }
    ret
}

const fn byte_make_ascii_uppercase(byte: &mut u8)
    ensures
        *final(byte) == ascii_upper_byte(*old(byte)),
{
    *byte = byte_to_ascii_uppercase(*byte);
}

pub const fn make_ascii_uppercase(slice: &mut [u8])
    ensures
        final(slice)@ == ascii_upper_seq(old(slice)@),
{
    let mut i = 0;
    while i < slice.len()
        invariant
            0 <= i <= slice@.len(),
            slice@.len() == old(slice)@.len(),
            forall|j: int| #![auto] 0 <= j < i ==> slice@[j] == ascii_upper_byte(old(slice)@[j]),
            forall|j: int| #![auto] i <= j < slice@.len() ==> slice@[j] == old(slice)@[j],
        decreases slice.len() - i
    {
        let byte = &mut slice[i];
        byte_make_ascii_uppercase(byte);
        i += 1;
    }
}

}
