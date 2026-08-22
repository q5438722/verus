#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::escape_ascii
// Source: core/src/slice/ascii.rs:218-220 and EscapeAscii representation at lines 315-317
// Source item sha256: 1d3eb16392be78fd1bea2c10485a13dfa460260673d0c270ee1216b1381302c5
// Dependency manifest: proof_manifests/042_core_slice_escape_ascii/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub remaining: Seq<T>,
}

pub struct EscapeByte;

pub struct Iter<'a> {
    slice: &'a [u8],
}

pub struct FlatMapEscapeAscii<'a> {
    source: &'a [u8],
}

pub struct EscapeAscii<'a> {
    inner: FlatMapEscapeAscii<'a>,
}

pub open spec fn ascii_lower_hex_digit(nibble: int) -> u8
    recommends
        0 <= nibble < 16,
{
    if nibble < 10 {
        (0x30 + nibble) as u8
    } else {
        (0x61 + (nibble - 10)) as u8
    }
}

pub open spec fn ascii_escape_byte(byte: u8) -> Seq<u8> {
    if byte == 0x09u8 {
        seq![0x5cu8, 0x74u8]
    } else if byte == 0x0du8 {
        seq![0x5cu8, 0x72u8]
    } else if byte == 0x0au8 {
        seq![0x5cu8, 0x6eu8]
    } else if byte == 0x27u8 {
        seq![0x5cu8, 0x27u8]
    } else if byte == 0x22u8 {
        seq![0x5cu8, 0x22u8]
    } else if byte == 0x5cu8 {
        seq![0x5cu8, 0x5cu8]
    } else if 0x20 <= (byte as int) && (byte as int) <= 0x7e {
        seq![byte]
    } else {
        seq![
            0x5cu8,
            0x78u8,
            ascii_lower_hex_digit((byte as int) / 16),
            ascii_lower_hex_digit((byte as int) % 16),
        ]
    }
}

pub open spec fn ascii_escape_seq(seq: Seq<u8>) -> Seq<u8> {
    seq.flat_map(|byte: u8| ascii_escape_byte(byte))
}

pub closed spec fn iter_source<'a>(iter: Iter<'a>) -> Seq<u8> {
    iter.slice@
}

pub closed spec fn flat_map_source<'a>(inner: FlatMapEscapeAscii<'a>) -> Seq<u8> {
    inner.source@
}

pub closed spec fn flat_map_remaining<'a>(inner: FlatMapEscapeAscii<'a>) -> Seq<u8> {
    ascii_escape_seq(flat_map_source(inner))
}

pub closed spec fn slice_iterator_view<'a>(iter: EscapeAscii<'a>) -> SliceIteratorView<u8> {
    SliceIteratorView {
        source: flat_map_source(iter.inner),
        remaining: flat_map_remaining(iter.inner),
    }
}

pub fn slice_iter<'a>(slice: &'a [u8]) -> (iter: Iter<'a>)
    ensures
        iter_source(iter) == slice@,
{
    let iter = Iter { slice };
    proof {
        reveal(iter_source);
    }
    iter
}

impl<'a> Iter<'a> {
    pub fn flat_map(self, _f: EscapeByte) -> (inner: FlatMapEscapeAscii<'a>)
        ensures
            flat_map_source(inner) == iter_source(self),
            flat_map_remaining(inner) == ascii_escape_seq(iter_source(self)),
    {
        let inner = FlatMapEscapeAscii { source: self.slice };
        proof {
            reveal(iter_source);
            reveal(flat_map_source);
            reveal(flat_map_remaining);
        }
        inner
    }
}

pub fn escape_ascii<'a>(slice: &'a [u8]) -> (iter: EscapeAscii<'a>)
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).remaining == ascii_escape_seq(slice@),
{
    let inner = slice_iter(slice).flat_map(EscapeByte);
    let iter = EscapeAscii { inner };
    proof {
        reveal(slice_iterator_view);
        reveal(flat_map_source);
        reveal(flat_map_remaining);
    }
    iter
}

}
