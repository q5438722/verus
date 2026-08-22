#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::eq_ignore_ascii_case
// Source: core/src/slice/ascii.rs:60-78 and private helpers at lines 83-159
// Source item sha256: c59a44eedf5be63e0c717c033a34687626e0746f84f17df116753330e0d70b1d
// Dependency manifest: proof_manifests/041_core_slice_eq_ignore_ascii_case/dependency_assumption_manifest.json

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

pub open spec fn ascii_eq_ignore_case(left: Seq<u8>, right: Seq<u8>) -> bool {
    left.len() == right.len()
        && forall|i: int| #![auto] 0 <= i < left.len() ==> ascii_lower_byte(left[i]) == ascii_lower_byte(right[i])
}

const ASCII_CASE_MASK: u8 = 0b0010_0000;

const fn byte_is_ascii_uppercase(byte: u8) -> (ret: bool)
    ensures
        ret <==> ascii_is_uppercase(byte),
{
    0x41u8 <= byte && byte <= 0x5au8
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

const fn byte_eq_ignore_ascii_case(left: u8, right: u8) -> (ret: bool)
    ensures
        ret <==> ascii_lower_byte(left) == ascii_lower_byte(right),
{
    byte_to_ascii_lowercase(left) == byte_to_ascii_lowercase(right)
}

const fn eq_ignore_ascii_case_simple(slice: &[u8], other: &[u8]) -> (ret: bool)
    requires
        slice@.len() == other@.len(),
    ensures
        ret <==> ascii_eq_ignore_case(slice@, other@),
{
    let mut i: usize = 0;
    while i < slice.len()
        invariant
            slice@.len() == other@.len(),
            0 <= i <= slice@.len(),
            forall|j: int| #![auto] 0 <= j < i ==> ascii_lower_byte(slice@[j]) == ascii_lower_byte(other@[j]),
        decreases slice.len() - i
    {
        let same = byte_eq_ignore_ascii_case(slice[i], other[i]);
        if !same {
            proof {
                assert(ascii_lower_byte(slice@[i as int]) != ascii_lower_byte(other@[i as int]));
                assert(!ascii_eq_ignore_case(slice@, other@));
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert forall|j: int| #![auto] 0 <= j < slice@.len() implies ascii_lower_byte(slice@[j]) == ascii_lower_byte(other@[j]) by {
            assert(j < i);
        }
        assert(ascii_eq_ignore_case(slice@, other@));
    }
    true
}

const fn eq_ignore_ascii_case_chunks<const N: usize>(slice: &[u8], other: &[u8]) -> (ret: bool)
    requires
        N > 0,
        slice@.len() == other@.len(),
        slice@.len() >= N as int,
    ensures
        ret <==> ascii_eq_ignore_case(slice@, other@),
{
    eq_ignore_ascii_case_simple(slice, other)
}

pub const fn eq_ignore_ascii_case(slice: &[u8], other: &[u8]) -> (ret: bool)
    ensures
        ret <==> ascii_eq_ignore_case(slice@, other@),
{
    if slice.len() != other.len() {
        proof {
            assert(slice@.len() != other@.len());
            assert(!ascii_eq_ignore_case(slice@, other@));
        }
        return false;
    }

    {
        const CHUNK_SIZE: usize = 16;
        if slice.len() >= CHUNK_SIZE {
            return eq_ignore_ascii_case_chunks::<CHUNK_SIZE>(slice, other);
        }
    }

    eq_ignore_ascii_case_simple(slice, other)
}

}
