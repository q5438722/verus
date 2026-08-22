#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::chunks
// Source: core/src/slice/mod.rs:1155-1158 and core/src/slice/iter.rs:1480-1488
// Source item sha256: 8a32e5bfe63897bfe90ee26ef2bb93442cde9eb73fe17cd209fc7ffe7ec50dae
// Dependency manifest: proof_manifests/033_core_slice_chunks/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remaining: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct Chunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: Chunks<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: Seq::empty(),
        chunk_size: iter.chunk_size as int,
        reverse: false,
    }
}

impl<'a, T> Chunks<'a, T> {
    pub const fn new(slice: &'a [T], size: usize) -> (ret: Self)
        ensures
            slice_iterator_view(ret).source == slice@,
            slice_iterator_view(ret).remaining == slice@,
            slice_iterator_view(ret).yielded_prefix.len() == 0,
            slice_iterator_view(ret).remainder.len() == 0,
            slice_iterator_view(ret).chunk_size == size as int,
            !slice_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice, chunk_size: size };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn chunks<'a, T>(slice: &'a [T], chunk_size: usize) -> (iter: Chunks<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).remaining == slice@,
        slice_iterator_view(iter).yielded_prefix.len() == 0,
        slice_iterator_view(iter).remainder.len() == 0,
        slice_iterator_view(iter).chunk_size == chunk_size as int,
        !slice_iterator_view(iter).reverse,
{
    assert(chunk_size != 0);
    Chunks::new(slice, chunk_size)
}

}
