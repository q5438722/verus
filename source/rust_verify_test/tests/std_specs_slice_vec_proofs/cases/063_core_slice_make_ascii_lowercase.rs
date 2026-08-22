#![allow(dead_code, unused_imports, unused_variables, unused_mut)]
// Target-specific Verus implementation harness.
// Target: core::slice::make_ascii_lowercase
// Source: core/src/slice/ascii.rs:195-203
// Source item sha256: 99b4bddf55d14d92fa75efad7c8d9ef8f8c913fc37ddb27890837fe3c0209f26
// Dependency manifest: proof_manifests/063_core_slice_make_ascii_lowercase/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn ascii_is_uppercase(byte: u8) -> bool {
    0x41 <= (byte as int) && (byte as int) <= 0x5a
}

pub open spec fn ascii_lower_byte(byte: u8) -> u8 {
    if ascii_is_uppercase(byte) {
        ((byte as int) + 0x20) as u8
    } else {
        byte
    }
}

pub open spec fn ascii_lower_seq(seq: Seq<u8>) -> Seq<u8> {
    Seq::new(seq.len(), |i: int| ascii_lower_byte(seq[i]))
}

const ASCII_CASE_MASK: u8 = 0b0010_0000;

const fn byte_is_ascii_uppercase(byte: u8) -> (ret: bool)
    ensures
        ret <==> ascii_is_uppercase(byte),
{
    matches!(byte, 0x41u8..=0x5au8)
}

const fn byte_to_ascii_lowercase(byte: u8) -> (ret: u8)
    ensures
        ret == ascii_lower_byte(byte),
{
    let is_uppercase = byte_is_ascii_uppercase(byte);
    let mask = (is_uppercase as u8) * ASCII_CASE_MASK;
    let ret = byte | mask;
    proof {
        if is_uppercase {
            assert(0x41u8 <= byte && byte <= 0x5au8);
            assert(mask == ASCII_CASE_MASK);
            assert(
                (0x41u8 <= byte && byte <= 0x5au8)
                    ==> byte | 0x20u8 == add(byte, 0x20u8)
            ) by (bit_vector);
            assert(byte | 0x20u8 == add(byte, 0x20u8));
            assert(add(byte, 0x20u8) == byte + 0x20u8);
            assert((byte + 0x20u8) as int == (byte as int) + 0x20);
            assert(ret == ((byte as int) + 0x20) as u8);
        } else {
            assert(mask == 0u8);
            assert(byte | 0u8 == byte) by (bit_vector);
            assert(ret == byte);
        }
    }
    ret
}

const fn byte_make_ascii_lowercase(byte: &mut u8)
    ensures
        *final(byte) == ascii_lower_byte(*old(byte)),
{
    *byte = byte_to_ascii_lowercase(*byte);
}

pub const fn make_ascii_lowercase(slice: &mut [u8])
    ensures
        final(slice)@ == ascii_lower_seq(old(slice)@),
{
    let mut i = 0;
    while i < slice.len()
        invariant
            0 <= i <= slice@.len(),
            slice@.len() == old(slice)@.len(),
            forall|j: int| #![auto] 0 <= j < i ==> slice@[j] == ascii_lower_byte(old(slice)@[j]),
            forall|j: int| #![auto] i <= j < slice@.len() ==> slice@[j] == old(slice)@[j],
        decreases slice.len() - i
    {
        let byte = &mut slice[i];
        byte_make_ascii_lowercase(byte);
        i += 1;
    }
}

}
