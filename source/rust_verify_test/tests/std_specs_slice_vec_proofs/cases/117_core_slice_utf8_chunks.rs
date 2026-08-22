#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::utf8_chunks
// Source: core/src/str/lossy.rs:45-47
// Source item sha256: ffddce1e771b6d0e7d63cffd793ae4558987bf1d182ac0eb439ecb87171dd2e8
// Dependency manifest: proof_manifests/117_core_slice_utf8_chunks/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub remaining: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct Utf8Chunks<'a> {
    source: &'a [u8],
}

pub closed spec fn slice_iterator_view<'a>(iter: Utf8Chunks<'a>) -> SliceIteratorView<u8> {
    SliceIteratorView {
        source: iter.source@,
        remaining: iter.source@,
        yielded_prefix: Seq::empty(),
        remainder: Seq::empty(),
        chunk_size: 0,
        reverse: false,
    }
}

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn utf8_chunk_partition<'a>(iter: Utf8Chunks<'a>, source: Seq<u8>) -> bool {
    let view = slice_iterator_view(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix.len() == 0
        && view.remainder.len() == 0
        && view.chunk_size == 0
        && !view.reverse
}

pub fn utf8_chunks<'a>(slice: &'a [u8]) -> (iter: Utf8Chunks<'a>)
    ensures
        utf8_chunk_partition(iter, slice@),
{
    let iter = Utf8Chunks { source: slice };
    proof {
        reveal(slice_iterator_view);
    }
    iter
}

}
